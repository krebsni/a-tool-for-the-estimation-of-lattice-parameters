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
from sage.all import *
import sympy
import random
import time
from datetime import timedelta
import bisect
from collections import deque
import multiprocessing
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
from scipy.optimize import newton
import sage.crypto.lwe
sys.path.append(os.path.dirname(__file__) + "/estimate_all")
from estimator import estimator
from estimator.estimator import *
import cost_asymptotics
import logging

oo = PlusInfinity()

# TODO: logging

# Utility #
def number_of_bits(v):
    if v == oo or v == -oo:
        return oo
    else:
        return ceil(log(abs(v), 2).n())
        

# SIS attacks#
def SIS_lattice_reduce(n, q, m, beta, secret_distribution, reduction_cost_model):
    """ 
    Finds optimal lattice subdimension d and root-Hermite factor delta_0 for lattice reduction.

    :param n: height of matrix
    :param m: width of matrix
    :param q: modulus
    :param beta: L2-norm bound of solution TODO: [RS10] works with L2-norm. What about [APS15]?
    """
    if beta > 1: # Condition is not a requirement for [RS10] but we would divide by log(beta) which is <= 0
        # TODO: RS10 assumes delta-SVP solver => ensure that solver used here is indeed delta-HSVP
        ## [RS10, Proposition 1]
        ## d = min{x : q ^ (2n /x) =< beta}
        ## q ^ (2n / x) =< beta
        ## 2n / x log q =< log beta
        ## x >= 2n log q / log beta

        # Requirements
        if n < 128 or q < n*n: 
            raise ValueError("Violation of requirements of [RS10, Proposition 1] during SIS lattice reduction.")
        # Calculate optimal dimension for delta-HSVP solver
        d = ceil(2 * n * log(q, 2) / log(beta, 2)) 
        if d > m:
            d = m
        
        ## [RS10, Conjecture 2]
        # Requirements
        if q < n**2 or m <= n * log(log(q, 2), 2): # second condition to ensure that m = Omega(n log q)
            raise ValueError("Violation of requirements of [RS10, Conjecture 2] during SIS lattice reduction.")
        # Calculate approximation factor for delta-HSVP solver
        delta_0 = RR((beta / (q ** (n / d))) ** (1 / d))
        log_delta_0 = log(delta_0, 2)

    else: # TODO: beta = 1 in L2-norm would only hold for vectors with exactly one 1 entry (all others 0)!? 
        # TODO: trivial, solution in linear time...
        ## [APS15, 3.3]
        ## abs(x) = delta_0 ^ m  vol(L) ^ (1 / m)
        ##        = delta_0 ^ m  q ^ (n / m) # "in many applications" 
        #       TODO: what if not in the given application? 
        #       cf. [Pla18, p. 66] here vol(L(A)) = q^(m-n)!
        ## beta   = delta_0 ^ m  q ^ (n / m)
        ## log delta_0 = log beta / m  - n / m^2 log q          (I)

        ## optimal dimension m = sqrt(n log q / log delta_0)    (II)
        ## (II) in (I):
        ##      log delta_0 = log beta / sqrt(n log q / log delta_0) - n / (n log q / log delta_0) log q
        ##      log delta_0 = log beta / sqrt(n log q / log delta_0) - log delta_0
        ##      log delta_0 = log beta / (2 sqrt(n log q / log delta_0))
        ##      log delta_0 = log^2 beta / (4n log q) 
        
        log_delta_0 = RR(log(beta, 2)**2 / (4 * n * log(q, 2)))
        d = sqrt(n * log(q, 2) / log_delta_0)
        if d > m:
            d = m
            log_delta_0 = log(beta, 2) / m - n * log(q, 2) / (m**2) # (I)

    if delta_0 < 1: # intractable
        ret = None # estimator.Cost([("rop", estimator.oo)]) # TODO: what to return?

    elif beta < q: # standard case
        k = estimator.betaf(2**log_delta_0) # block size k [APS15, lattice rule of thumb and Lemma 5]
        B = log(q, 2)

        cost = reduction_cost_model(k, d, B) 
        ret = estimator.Cost([("rop", cost)])

    else: # not a hard problem, trivial solution exists
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

# Norms # 
class Norm:
    """
    Namespace for norms
    """
    # TODO: transformations
    class L1:
        pass
    class L2:
        pass
    class Loo:
        pass

# Error Parameter Conversion (Addition to functions in estimator.py)
def alpha_to_stddevf(alpha, q):
    """
    noise rate α, modulus q → standard deviation

    :param alpha: noise rate
    :param q: modulus `0 < q`

    :returns: σ = α/q 
    """
    return RR(alpha * q)


# Distributions # 
class Gaussian():
    
    def get_alpha(self):
        return self.alpha
    
    def get_q(self):
        return self.q

    def get_sigma(self):
        return self.sigma

class Gaussian_alpha(Gaussian):
    def __init__(self, alpha, q):
        self.alpha = RR(alpha)
        self.q = q
        self.stddev = stddevf(self.alpha, q)
        self.sigma = sigmaf(self.stddev)

class Gaussian_stddev(Gaussian):
    """
    Helper class for Gaussian distribution that takes standard deviation as input.
    """
    def __init__(self, stddev, q):
        self.stddev = RR(stddev)
        self.sigma = sigmaf(self.stddev)
        self.alpha = alphaf(self.sigma, q)
        self.q = q

class Gaussian_sigma(Gaussian):
    """
    Helper class for Gaussian distribution that takes sigma as input (sigma is not standard deviation).
    stddev = σ/sqrt(2π)
    """
    def __init__(self, sigma, q):
        self.sigma = sigma
        self.sigma = stddevf(sigma)
        self.alpha = alphaf(sigma, q)
        self.q = q


# Problem Variants # 
class Problem:
    """
    Namespace for processing problem instance parameter sets.
    """
    # TODO: perhaps create error distribution class with flexibility for user to decide whether alpha/sigma...
    class LWE():
        def __init__(self, n, q=None, m=None, alpha=None, sigma=None, sigma_is_stddev=False): 
            # TODO: parameter all_attacks in estimate function...
            # TODO: which parameters can be specified? Do we need to specify approximation factor beta/gamma?
            """
            :param q: modulus
            :param n: secret dimension
            :param m: number of samples
            :param alpha: noise rate
            """
            # check soundness of parameters
            if (not sigma and not alpha) or not n or not q or not m or n<0 or q<0 or m<0:
                raise ValueError("Parameters not specified correctly")

            self.n = n
            self.q = q
            self.m = m
            if alpha:
                self.alpha = alpha
            else:
                self.alpha = alphaf(sigma, q, sigma_is_stddev=sigma_is_stddev)

        def __str__(self):
            return f"TODO"

    class MLWE(LWE):
        def __init__(self, n, d, q, m, alpha=None, sigma=None, sigma_is_stddev=False):
            """
            :param q: modulus
            :param N: degree of polynomial
            :param n: secret dimension
            :param m: number of samples
            :param d: rank of module
            :param sigma: Gaussian width parameter (not standard deviation)
            """
            # # TODO: check if correct
            use_reduction = False
            if use_reduction:
                ## [AD17 Corollary 1 and p. 21]
                ## Psi =< alpha * n^(c+1/2) * sqrt(d) for some constant c
                ## [KNK20b p. 2 (Corollary 1 contains an error)] 
                ## Psi =< alpha * n^2 * sqrt(d)
                # TODO: Where do KNK get factor 2 in the exponent from?
                alpha_MLWE = estimator.alphaf(sigma, q)
                alpha_RLWE = RR(alpha_MLWE * n**2 * sqrt(d))
                q_RLWE = q**d
                ## Note that the secret distribution in MLWE can be arbitrary,
                ## reduction to RLWE leads to uniform secret distribution U(R^V_q)
                ## Also note that the reduction only works for search-MLWE
                # TODO: find reduction for decision-MLWE?
                super().__init__(n=n, q=q_RLWE, alpha=alpha_RLWE, m=m)
            
            super().__init__(n=n*d, q=q, m=m, alpha=alpha, sigma=sigma, sigma_is_stddev=sigma_is_stddev)

    class RLWE(MLWE):
        def __init__(self, n, q, m, alpha, sigma=None, sigma_is_stddev=False):
            """
            :param q: modulus
            :param n: degree of polynomial
            :param m: number of samples
            :param sigma: Gaussian width parameter (not standard deviation)
            """
            ## interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
            # TODO: is this correct? 
            super().__init__(n=n, d=1, q=q, m=m, alpha=alpha, sigma=sigma, sigma_is_stddev=sigma_is_stddev)

    class Statistical_Gaussian_MLWE(MLWE):
        """
        Statistically secure MLWE over Gaussian distribution [LPR13, Corollary 7.5]
        """
        def __init__(self, n, q, m, d):
            """
            :param sec: required bit security of MLWE instance
            :param q: modulus
            :param n: degree of polynomial
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param d: rank of module
            """
            
            # Holds for normal form? What if not normal form?
            ## Corollary 7.5 (variant of regularity theorem)
            ## For k is height, l width of matrix A, n degree, and q modulus:
            ##   if x is distributed according to Gaussian of width r > (2n * q^(k/l + 2/(nl)))
            ##   then Ax is within statistical distance 2^-n of uniform distribution over R_q^k
            # TODO: check if this is correct
            gaussian_width = RR(2 * n * q**(d / m + 2 / (n * m)))
            # gaussian_width is not standard deviation
            alpha = alphaf(gaussian_width, q)
            
            # TODO: should we require n > 128 or n > 256 to ensure unconditional hardness or check if n > sec?
            super().__init__(n=n, d=d, q=q, m=m, alpha=alpha)

    class Statistical_Uniform_MLWE(MLWE):
        """
        Statistically secure MLWE over Uniform distribution with invertible elements [BDLOP16]

        MLWE problem instance where samples (A', h_A'(y)) are within statistical distance 2^(-128) of (A', u) for uniform u.   
        """
        def __init__(self, n, q, m, d, d_2):
            """
            :param sec: required bit security of MLWE instance
            :param q: modulus (prime congruent to 2d_2 + 1(mod 4d_2))
            :param n: degree of polynomial
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param d: rank of module
            :param d_2: 1 < d_2 < N and d_2 is a power of 2
            """
            ## [BDLOP16, Lemma 4]
            ## Map of parameters in Lemma to use here:
            ##   q => q
            ##   k => m
            ##   n => d
            ##   d => d_2
            ##   N => n
            ## Then the lemma reads as follows:
            ##   q^(d_2/m) * 2^(256/(m*n)) =< 2beta < 1/sqrt(d_2) * q^(1/d_2)
            ## Prerequisites: 1 < d_2 < N must a power of 2 and q must be a prime congruent to 2d_2 + 1(mod 4d_2)
            # TODO: check prerequisites?
            lower = RR(q**(d_2 / m) * 2**(256 / (m * n)))
            upper = RR(1 / sqrt(d_2) * q**(1 / d_2))
            beta = None # TODO
            alpha = None # TODO
            raise NotImplementedError("Currently not supported.")

            super().__init__(n=n, d=d, q=q, m=m, alpha=alpha)

    class SIS():
        def __init__(self, n, q, m, beta, norm):
            """
            :param q: modulus
            :param n: secret dimension
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param norm: used norm of upper bound
            """
            self.q = q
            self.n = n
            self.m = m
            self.beta = beta
            # TODO: norm transformation

    class MSIS(SIS):
        def __init__(self, n, d, q, m, beta, norm):
            """
            :param q: modulus
            :param d: rank of module
            :param n: degree of polynomial
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param norm: used norm of upper bound
            """
            # TODO: parameter if beta is not given but instead gaussian/uniform distribution? or helper function?
            
            use_reduction = False
            if use_reduction:
                ## [KNK20b Corollary 2] Reduction from M-SIS_(q^k, m^k, beta') to R-SIS_(q, m, beta)
                ## TODO: Needs L2 norm
                ## Conditions
                ## rank d:           sqrt(n * m) * q^(1/m) < (q/sqrt(m)^(d-1))^(1/(2*d-1))
                ## norm constraint:  sqrt(n * m) * q^(1/m) =< beta < (q/sqrt(m)^(d-1))^(1/(2*d-1))
                ## k positive integer > 1 => choose k = 2
                ## Calculation
                ## q = q_RSIS^k => q_RSIS = q^(1/k)
                ## m = m_RSIS^k => m_RSIS = m^(1/k)
                ## beta = m_RSIS^(k*(d-1)/2) * beta_RSIS^(k*(2*d - 1)) = m^((d-1)/2) * beta_RSIS^(k*(2*d - 1))
                ##   => beta_RSIS = (beta / (m^((d - 1) / 2)))^(1 / (k * (2 * d - 1)))
                # TODO: transform beta to L2 norm
                k = 2
                lower = RR(sqrt(n * m) * q**(1 / m))
                upper = RR((q / sqrt(m)**(d-1))**(1 / (2 * d - 1)))
                if lower <= beta and beta < upper:
                    q_RSIS = RR(round(q**(1/k)))
                    m_RSIS = RR(round(m**(1/k)))
                    beta_RSIS = RR((beta / (m**((d - 1) / 2)))**(1 / (k * (2 * d - 1))))
                super().__init__(n=n, q=q_RSIS, beta=beta_RSIS, m=m, norm=L2)
            
            else:
                super().__init__(n=n*d, q=q, m=m, beta=beta, norm=norm)


    class Statistical_MSIS(MSIS):
        """
        Statistically secure MSIS [DOTT21, section 4.1]
        """
        def __init__(self, sec, n, d, q, m):
            """
            :param sec: required bit security of MLWE instance
            :param q: modulus
            :param n: degree of polynomial
            :param m: number of samples (or width of matrix)
            :param beta: upper bound on norm of solution
            :param d: rank of module (or height of matrix)
            """
            
            ## [DOTT21, section 4.1]
            ## Parameters used:
            ##   m': width of matrix A_1
            ##   m:  height of matrix A_1
            ##   B:  bound of secret
            ##   sigma:  Gaussian parameter (not stddev)
            ## Map of parameters in section to parameters in this function:
            ##   s => sigma
            ##   N => n
            ##   m' => m
            ##   m => d
            ##   d => d_2
            ## bound B: 
            ##   +----------------------+
            ##   |  B = s*sqrt(m' * N)  |
            ##   +----------------------+
            ## Euclidean ball of radius 2B in R_q^m':
            ##   B_m'(0, 2B) << (2*pi*e/(m' * N))^(m' * N/2) * (2*B)^(m' * N)
            ##   
            ## Scheme is statistically binding if:
            ##   |B_m'(0, 2B)|/q^(mN) = 2^(-sec)
            ##   ((2*pi*e/(m' * N))^(1/2) * (2*B))^(m' * N) = 2^(-sec) * q^(m*N)
            ##   B = 2^(-sec/(m' * N)) * q^(m/m')/2 * (m' * N / (2 * pi * e))^(1/2)
            ##   +------------------------------------------------------------------------------------+
            ##   |  s = 2^(-sec/(m' * N)) * q^(m/m')/2 * (m' * N / (2 * pi * e))^(1/2) / sqrt(m' * N) |
            ##   +------------------------------------------------------------------------------------+
            ##
            ## Mapping of formula to parameters in this function
            ##   sigma = 2^(-sec/(m * n)) * q^(d/m)/2 * (m * n / (2 * pi * e))^(1/2) / sqrt(m * n)

            # TODO: use sage for increased precision?
            sigma = RR(2**(-sec / (m * n)) * q**(d / m) / 2 * (m * n / (2 * pi * e))**(1 / 2) / sqrt(m * n))
            alpha = alphaf(sigma, q)
            super().__init__(n=n, d=d, q=q, m=m, alpha=alpha)


    class RSIS(MSIS):
        def __init__(self, n, q, m, beta, norm):
            """
            :param q: modulus
            :param n: degree of polynomial
            :param m: number of samples
            :param beta: upper bound on norm of solution
            """
            ## We interpret the coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
            super().__init__(n=n, d=1, q=q, m=m, beta=beta, norm=norm)


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

def unit_cost():
    """
    Unit cost for given parameter set
    """
    return 0 # ensure that new ones are added at the end
    # TODO: perhaps another generic search without unit cost

class Parameter_Set:
    """
    Helper class to order parameter sets in list 
    """
    parameter_cost = unit_cost
    def __init__(self, parameters):
        self.parameters = parameters
    
    def __lt__(self, other):
        # reversed sorting to pop from sorted list
        return self.parameter_cost(*self.parameters) > self.parameter_cost(*self.parameters)


def generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem):
    """TODO: summary

    :param sec: required security level in bits
    :param initial_parameters: initial parameter set of search
    :param next_parameters: function yielding possibly multiple new parameter sets with previous parameter set as input
    :param parameter_cost: cost function of a parameter set used in the scheme to determine to order currently queued parameter sets. Use lib.unit_cost if sequence does not matter
    :param parameter_problem: function yielding possibly multiple problem instances with a paramter set as input

    :returns: parameter set fulfulling security condition
    """
    # TODO: check validity of parameters
    # TODO: test
    # TODO: search vs decision?
    Parameter_Set.parameter_cost = parameter_cost

    current_parameter_sets = [Parameter_Set(initial_parameters)]
    current_sec = 0
    while current_parameter_sets:

        current_parameter_set = current_parameter_sets.pop().parameters # remove last
        i = 0; secure = True
        for problem_instance in parameter_problem(*current_parameter_set): 
            current_sec = estimate(problem_instance)
            if current_sec < sec:
                # "early" termination
                secure = false; break

        if secure and i > 0:
            # Only if all problem instances of a parameter set pass
            # TODO: possibly extra class/dict with additional information...
            return (current_parameter_set, current_sec) 
            
        # TODO: check if correct
        for parameter_set in next_parameters(*current_parameter_set):
            bisect.insort_left(current_parameter_sets, Parameter_Set(parameter_set))