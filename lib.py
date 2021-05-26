#!/usr/bin sage
"""
A library to find secure parameter sets of popular versions of lattice problems (LWE and SIS in their integer, ring, and module versions) given various p-norms.
This script assumes that the estiamte-all-the-lwe-ntru-schemes commit 2bf02cc is present in a subdirectory `estimate_all` and within that subdirectory the LWE estimator commit 9302d42 in a subdirectory `estimator`.

NOTATION:

    LWE
    n       lwe secret dimension
    k       mlwe rank
    q       lwe modulo
    sd      lwe error standard deviation (if secret is normal form, also the secret standard devation)
    m       number of lwe samples

AUTHOR:
    Nicolai Krebs - 2021

Literature:
    [KNK20b]
"""


import os
import sys
import traceback
from attr.validators import instance_of
import fire
import sympy
import random
import time
from datetime import timedelta
import bisect
from collections import deque
import multiprocessing
from sage.all import *
from collections import OrderedDict
from functools import partial
from sage.arith.srange import srange
from sage.calculus.var import var
from sage.functions.log import exp, log
from sage.functions.other import ceil, sqrt, floor, binomial
from sage.all import erf
from sage.interfaces.magma import magma
from sage.misc.all import cached_function
from sage.misc.all import prod
from sage.numerical.optimize import find_root
from sage.rings.all import QQ, RR, ZZ, RealField, PowerSeriesRing, RDF
from sage.rings.infinity import PlusInfinity
from sage.structure.element import parent
from sage.symbolic.all import pi, e
from sage import random_prime as make_prime
from scipy.optimize import newton
import sage.crypto.lwe
sys.path.append(os.path.dirname(__file__) + "/estimate_all")
from estimator import estimator
from estimator.estimator import *
import cost_asymptotics
import logging

oo = PlusInfinity()

# TODO: import sigma/alpha conversion functions from estimator?
# TODO: logging

# Utility #
def number_of_bits(v):
    if v == oo or v == -oo:
        return oo
    else:
        return ceil(log(abs(v), 2).n())


# SIS attacks#
def SIS_lattice_reduce(q, n, m, beta, secret_distribution, reduction_cost_model):
    # d is lattice dimesion (number of samples)
    # beta is norm of solution
    # k is block size (also beta in other sources)
    # B is bitsize of entries


    if beta > 1: # not a requirement for [RR10] but we would divide by log(beta) which is <= 0
        assert(n > 128) # Requirement of [RR10, Proposition 1]
        assert(q >= n * n) # Requirement of [RR10, Proposition 1]
        ## [RR10, Proposition 1]
        ## d = min{x : q ^ (2n /x) <= beta}
        ## q ^ (2n / x) <= beta
        ## 2n / x log q <= log beta
        ## x => 2n log q / log beta
        d = ceil(2 * n * log(q, 2) / log(beta, 2)) 
        if d > m:
            d = m
        delta_0 = RR((beta / (q ** (n / d))) ** (1 / d))
        log_delta_0 = log(delta_0, 2)
    else:
        ## [APS15, 3.3]
        ## abs(x) = delta_0 ^ m  vol(L) ^ (1 / m) # x is SIS solution, L is lattice
        ##        = delta_0 ^ m  q ^ (n / m) # "in many applications"
        ## beta   = delta_0 ^ m  q ^ (n / m)
        ## delta_0 ^ m = beta / q ^ (n / m)
        ## m log delta_0 = log beta - n / m log q
        ## log delta_0 = log beta / m  - n / m^2 log q

        ## optimal dimension m = sqrt(n log q / log delta_0)
        ## log delta_0 = log beta / m  - n / m^2 log q
        ## log delta_0 = log beta / sqrt(n log q / log delta_0) - n / (n log q / log delta_0) log q
        ## log delta_0 = log beta / sqrt(n log q / log delta_0) - log delta_0
        ## 2 log delta_0 = log beta / sqrt(n log q / log delta_0)
        ## 4 log^2 delta_0 = log^2 beta / (n log q / log delta_0) 
        ## 4 log delta_0 = log^2 beta / (n log q)
        ## log delta_0 = log^2 beta / (4n log q)
        log_delta_0 = log(beta, 2) ** 2 / (4 * n * log(q, 2))
        d = sqrt(n * log(q, 2) / log_delta_0) 
        if d > m:
            d = m
            log_delta_0 = log(beta, 2) / m - n * log(q, 2) / (m ** 2)


    if delta_0 < 1: # not useful
        ret = None # estimator.Cost([("rop", estimator.oo)])
    elif beta < q: # standard case
        def g(x, i):
            y = RR(2)
            for _ in range(i):
                y = RR(x * log(y, 2))
            return y
        ## [APS15]
        ## delta_0 = k ^ (1 / 2k)
        ## k / log k = 1 / 2 log delta_0
        ## [APS15, Lemma 5]
        ## log(k) >= 1: k >= g_n(1 / 2 log delta_0)
        ## log(k) >  2: k = g_oo(1 / 2 log delta_0)
        

        k = estimator.betaf(2**log_delta_0)
        B = log(q, 2)
        cost = reduction_cost_model(k, d, B)
        ret = estimator.Cost([("rop", cost)])
    else: # not a hard problem
        ret = estimator.Cost([("rop", min(n, d) ** 2.376)])
    return ret

def SIS_combinatorial(q, n, m, beta, secret_distribution, reduction_cost_model):
    # beta here is range of gaussian?
    ## [MR08, p. 7]
    def L(k):
        return (2 * beta + 1) ** (m / (2 ** k))

    ## n = (k + 1) logq L
    ## n = (k + 1) logq (2 beta + 1) ^ (m / 2 ^ k)
    ## n = (k + 1) * m / (2 ^ k) logq (2  beta + 1)
    ## 2 ^ k / (k + 1) = m / n logq (2 beta + 1)
    if beta < q:
        k = 1
        difference = estimator.oo
        failed, max_failures = 0, 10
        while failed < max_failures:
            log_Lk = log(L(k), q)
            new_difference = abs(n - (k + 1) * log_Lk)
            if new_difference < difference:
                difference = new_difference
                closest_k = k
                failed = 0
            else:
                failed += 1
            k += 1
        k = closest_k

        L = L(k)
        list_element_cost = log(q, 2) * n
        lists = (2 ** k) * L
        cost = lists * list_element_cost # create initial lists
        # for i in range(k): # binary reduction:
        #     cost += ((2 ** (k - i) / 2) # for each pair 
        #             * (L * list_element_cost # add the list up 
        #                 + log(L, q))) # and check the ith block if coordinates for zero
        last_coordinates = n - k * log(L, q)
        success_probability = 1 / q
        return estimator.Cost([("rop", cost)])
    else: # not a hard problem
        ret = estimator.Cost([("rop", min(n, m) ** 2.376)])

# Distributions # # TODO: necessary to implement here? More needed?
class UniformDistribution():
    def __init__(self, a, b=None):
        if b is None:
            b = a
            a = -a

        self.range = (a, b)

    def Alpha(self, q):
        v = estimator.SDis.variance(self.range)
        s = sqrt(v)
        return estimator.alphaf(s, q, sigma_is_stddev=True)

    def Range(self, q):
        return self.range

class GaussianDistributionWithStdDev():
    def __init__(self, stddev):
        self.stddev = stddev

    def Alpha(self, q):
        return estimator.alphaf(self.stddev, q, sigma_is_stddev=True)

    def Range(self, q):
        return GaussianDistributionWithParameter(sqrt(2 * pi) * self.stddev).Range(q)

class GaussianDistributionWithParameter():
    def __init__(self, s):
        self.s = s

    def Alpha(self, q):
        return estimator.alphaf(self.s, q, sigma_is_stddev=False)

    def Range(self, q):
        # Pr[X >= t] <= 2 exp(-pi t^2 / s^2)
        # Pr[X >= ts] <= 2 exp(-pi t^2)
        # Pr[X >= ts pi^{-1/2}] <= 2 exp(-t^2)
        # Pr[X >= sqrt(t) s pi^{-1/2}] <= 2 exp(-t)
        sec = 100
        b = sqrt(sec) * self.s * sqrt(pi)
        return (-b, b)

class NoiseRateDistribution():
    def __init__(self, alpha):
        self.alpha = alpha

    def Alpha(self, q):
        return self.alpha

    def Range(self, sec):
        return GaussianDistributionWithParameter(self.alpha * q).Range(q)


# Problem Variants # 
class LindnerPeikert:
    """
    Calculate parameters of LWE as in [LP11] 
    """

class Regev:
    """
    Calculate parameters of LWE as in [Reg09]
    """

class Problem:
    """
    Namespace for processing problem instance parameter sets.
    """
    class LWE():
        def __init__(self, n, alpha=None, q=None, m=None, model=None, all_attacks=False): 
            # TODO: which parameters can be specified? Do we need to specify approximation factor beta/gamma?
            """
            :param q: modulus
            :param n: secret dimension
            :param m: number of samples
            :param alpha: noise rate
            :param all_attacks (bool, optional): specify used attacks TODO
            """
            self.n = n
            if model:
                if isinstance(model, LindnerPeikert):
                    lwe = estimator.Param.LindnerPeikert(n, m, dict=True)
                elif isinstance(model, Regev):
                    lwe = estimator.Param.Regev(n, m, dict=True)
                else:
                    raise ValueError("specified model currently not supported")
            else:                    
                if not alpha or not q or not m:
                    raise ValueError("alpha, q and m must be specified")
                self.alpha = alpha
                self.q = q
                self.m = m
                
            self.q = lwe["q"]
            self.alpha = lwe["alpha"]
            self.m = lwe["m"]

            
            self.strategies = {}
            self.strategies["usvp"] = estimator.primal_usvp
            if all_attacks:
                self.strategies["usvp-drop"] = estimator.partial(
                    estimator.drop_and_solve, estimator.primal_usvp, postprocess=False, decision=False, rotations=False)
                self.strategies["usvp-guess"] = estimator.partial(
                    estimator.guess_and_solve, estimator.primal_usvp)
                self.strategies["dual"] = estimator.dual_scale
                self.strategies["dual-drop-lll"] = estimator.partial(
                    estimator.drop_and_solve, estimator.dual_scale, postprocess=True, use_lll=True)
                self.strategies["dual-drop"] = estimator.partial(
                    estimator.drop_and_solve, estimator.dual_scale, postprocess=True, use_lll=False)
                self.strategies["dual-guess"] = estimator.partial(
                    estimator.guess_and_solve, estimator.dual_scale)
                self.strategies["decode"] = estimator.primal_decode
            self.costless_strategies = {}
            if all_attacks:
                self.costless_strategies["mitm"] = estimator.mitm

        def cost_search(self, tag, errorDistribution, secretDistribution=None):
            if secretDistribution is None:
                secretDistribution = errorDistribution

            secretDistribution=True

            arguments = [(tag, "LWE", strategy_name, estimator.partial(solver, q=self.Modulus, n=self.SecretDimension, m=self.ErrorDimension, alpha=errorDistribution.Alpha(self.Modulus), secret_distribution=secretDistribution), cost_asymptotic) for strategy_name, solver in self.strategies.items() for cost_asymptotic in range(len(cost_asymptotics.BKZ_COST_ASYMPTOTICS))]
            arguments += [(tag, "LWE", strategy_name, estimator.partial(solver, q=self.Modulus, n=self.SecretDimension, m=self.ErrorDimension, alpha=errorDistribution.Alpha(self.Modulus), secretDistribution=secretDistribution), None) for strategy_name, solver in self.costless_strategies.items()]

            return arguments

        def __str__(self):
            return f"TODO"

    class RLWE(LWE):
        def __init__(self, n, q, m, alpha, all_attacks=False):
            """
            :param q: modulus
            :param N: degree of polynomial
            :param n: secret dimension
            :param m: number of samples
            :param sigma: Gaussian width parameter (not standard deviation)
            :param all_attacks (bool, optional): specify used attacks TODO
            """
            # interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
            # TODO: is this correct? 
            super().__init__(n=n, q=q, alpha=alpha, m=N*m, all_attacks=all_attacks)
    
    class MLWE(RLWE):
        def __init__(self, n, q, m, sigma, d, all_attacks=False):
            """
            :param q: modulus
            :param N: degree of polynomial
            :param n: secret dimension
            :param m: number of samples
            :param d: rank of module
            :param sigma: Gaussian width parameter (not standard deviation)
            :param all_attacks (bool, optional): specify used attacks TODO
            """
            # TODO: alpha or sigma? other params needed?

            # TODO: check if correct
            # [AD17 Corollary 1 and p. 21]
            # Psi =< alpha * n^(c+1/2) * sqrt(d) for some constant c
            # [KNK20b p. 2 (Corollary 1 contains an error)] 
            # Psi =< alpha * n^2 * sqrt(d)
            # Where do KNK get factor 2 in the exponent from?

            alpha_MLWE = estimator.alphaf(sigma, q)
            alpha_RLWE = alpha_MLWE * n**2 * sqrt(d)
            q_RLWE = q**d
            # Note that the secret distribution in MLWE can be arbitrary,
            # reduction to RLWE leads to uniform secret distribution U(R^V_q)
            # Also note that the reduction only works for search-MLWE
            # TODO: find reduction for decision-MLWE?
            super().__init__(n=n, q=q_RLWE, alpha=alpha_RLWE, m=m, all_attacks=all_attacks)

    class Statistical_MLWE():
        pass

    class SIS():
        """
            :param q: modulus
            :param n: secret dimension
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param all_attacks (bool, optional): specify used attacks TODO
        """
        def __init__(self, n, q, m, all_attacks=False):
            self.q = q
            self.n = n
            self.m = m
            self.strategies = {}
            self.strategies["reduction"] = SIS_lattice_reduce
            if all_attacks:
                # TODO: add more attacks
                pass
            self.costless_strategies = {}
            if all_attacks:
                self.costless_strategies["combinatorial"] = SIS_combinatorial
                # TODO: maybe add something like BKW-cost from [ACFFP12] but it needs unlimited m

        def cost_search(self, tag, errorDistribution, secretDistribution=None):
            n, k = self.Dimensions
            N = self.PolynomialDegree

            secretDistribution=True

            arguments = [(tag, "SIS", strategy_name, estimator.partial(solver, q=self.Modulus, n=n, m=k, beta=errorDistribution.Range(self.Modulus)[1], secret_distribution=secretDistribution), cost_asymptotic) for strategy_name, solver in self.strategies.items() for cost_asymptotic in range(len(cost_asymptotics.BKZ_COST_ASYMPTOTICS))]
            arguments += [(tag, "SIS", strategy_name, estimator.partial(solver, q=self.Modulus, n=n, m=k, beta=errorDistribution.Range(self.Modulus)[1], secret_distribution=secretDistribution), None) for strategy_name, solver in self.costless_strategies.items()]

            return arguments

    class RSIS(SIS):
        def __init__(self, n, q, beta, m, all_attacks=False):
            """
            :param q: modulus
            :param n: degree of polynomial
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param all_attacks (bool, optional): specify used attacks TODO
            """
            # interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
            # TODO: is this correct? 
            super().__init__(n=n, q=q, beta=beta, m=m, all_attacks=all_attacks)

    class MSIS(RSIS):
        def __init__(self, n, q, beta, m, d, all_attacks=False):
            """
            :param q: modulus
            :param n: degree of polynomial
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param d: rank of module
            :param all_attacks (bool, optional): specify used attacks TODO
            """
            # TODO: perhaps simpler approach as simply viewing MSIS as SIS instance? 
            # we could take n_SIS = n * d
            # what about number of samples?


            # TODO: other params needed?
            # [KNK20b Corollary 2] 
            # Needs L2 norm
            # Conditions
            # rank d:           sqrt(n * m) * q^(1/m) < (q/sqrt(m)^(d-1))^(1/(2*d-1))
            # norm constraint:  sqrt(n * m) * q^(1/m) =< beta < (q/sqrt(m)^(d-1))^(1/(2*d-1))
            # k positive integer > 1 => choose k = 2
            # Calculation
            # q = q_RSIS^k => q_RSIS = q^(1/k)
            # m = m_RSIS^k => m_RSIS = m^(1/k)
            # beta = m_RSIS^(k*(d-1)/2) * beta_RSIS^(k*(2*d - 1)) = m^((d-1)/2) * beta_RSIS^(k*(2*d - 1))
            #   => beta_RSIS = (beta / (m^((d - 1) / 2)))^(1 / (k * (2 * d - 1)))
            k = 2
            lower = sqrt(n * m) * q**(1 / m)
            upper = (q / sqrt(m)**(d-1))**(1 / (2 * d - 1))
            if lower <= beta and beta < upper:
                q_RSIS = round(q**(1/k))
                m_RSIS = round(m**(1/k))
                beta_RSIS = (beta / (m**((d - 1) / 2)))**(1 / (k * (2 * d - 1)))
            else:
                # TODO: find other estimates? For now not supported
                raise NotImplementedError(f"Error. This function does not support the input parameter set: \
                                          ({n}, {q}, {m}, {beta}).")
            super().__init__(n=n, q=q_RSIS, beta=beta_RSIS, m=m, all_attacks=all_attacks)


    # TODO: secret_distribution? e.g. binary/ternary

def is_secure(problem, sec):
    if estimate(problem) < sec:
        return True
    else:
        return False

def estimate(problem):
    # TODO run cost estimation for given parameter set of problem
    sec = None
    return sec

def unit_cost(*argv):
    """
    Unit cost for given parameter set
    """
    # TODO: how to set cost? perhaps memory size of matrix
    # TODO: how to extract parameters? fix sequence or use keywords?
    cost = 0
    return cost

def generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem):
    """[summary]

    :param sec: required security level in bits
    :param initial_parameters: 
    :param next_parameters: [description]
    :param parameter_cost: [description]
    :param parameter_problem: [description]

    Returns:
        [type]: [description]
    """
    # TODO: check validity of parameters given the problem?
    # check functions?

    current_parameter_sets = [initial_parameters]
    current_sec = 0
    while True:
        for current_parameter_set in current_parameter_sets:

            i = 0; secure = True
            for problem_instance in parameter_problem(*current_parameter_set): 
                i += 1
                current_sec = estimate(problem_instance)
                if current_sec < sec:
                    # "early" termination
                    secure = false; break

            if secure and i > 0:
                # Only if all problem instances of a parameter set pass
                # TODO: return only one or multiple options? 
                return current_parameter_set + current_sec # TODO: change to dictionary?
            
        current_parameter_sets = [x for params in current_parameter_sets for x in next_parameters(*params)]
        current_parameter_sets.sort(key=lambda params : parameter_cost(*params))

        # TODO: parameter_cost function only affects the current parameters candidates in the list of next parameters