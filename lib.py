#!/usr/bin sage
r"""
A library to find secure parameter sets of popular versions of lattice problems (LWE and SIS in their integer, ring, and module versions) given various p-norms.
This script assumes that the estiamte-all-the-lwe-ntru-schemes commit 2bf02cc is present in a subdirectory `estimate_all` and within that subdirectory the LWE estimator commit 9302d42 in a subdirectory `estimator`.

NOTATION:
    LWE
    n       lwe secret dimension
    k       mlwe rank
    q       lwe modulo
    sigma   standard deviation :math:`\sigma` (if secret is normal form, also the secret standard devation)
    s       :math:`\sigma \cdot \sqrt{2\pi}`
    m       number of lwe samples

AUTHOR:
    Nicolai Krebs - 2021

"""

try: # sage-related imports do not work with sphinx for documentation
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
    from collections import OrderedDict
    from functools import partial
    from scipy.optimize import newton
    from abc import ABC, abstractmethod
    # from sage.all import *
    # from sage.symbolic.constants import Pi
    # from sage.arith.srange import srange
    # from sage.calculus.var import var
    # from sage.functions.log import exp, log
    # from sage.functions.other import ceil, sqrt, floor, binomial
    # from sage.all import erf
    # from sage.interfaces.magma import magma
    # from sage.misc.all import cached_function
    # from sage.misc.all import prod
    # from sage.numerical.optimize import find_root
    # from sage.rings.all import QQ, RR, ZZ, RealField, PowerSeriesRing, RDF
    # from sage.rings.infinity import PlusInfinity
    # from sage.structure.element import parent
    # from sage.symbolic.all import pi, e
    # from sage import random_prime as make_prime
    # import sage.crypto.lwe
    # from sage.misc.functional import N
    sys.path.append(os.path.dirname(__file__) + "/estimate_all")
    from estimator import estimator
    from estimator.estimator import *
    import cost_asymptotics
    import logging

    oo = PlusInfinity()
except:
    pass

# TODO: logging

# Utility #
def number_of_bits(v):
    if v == oo or v == -oo:
        return oo
    else:
        return ceil(log(abs(v), 2).n())
        

# SIS attacks #
class Attacks:
    """
    Namespace for attacks 
    """
    class Attack_Configuration():
        # TODO: documentation
        def __init__(self, classical, quantum, sieving, enumeration):
            if not classical and not quantum:
                raise ValueError("At least one of classical or quantum must be True")
            if not sieving and not enumeration:
                raise ValueError("At least one of sieving or enumeration must be True")

            self.classical = classical
            self.quantum = quantum
            self.sieving = sieving
            self.enumeration = enumeration


    def reduction_cost_models(attack_configuration):
        """
        Returns filtered list of reduction cost models from `cost_asymptotics.py <https://github.com/estimate-all-the-lwe-ntru-schemes/estimate-all-the-lwe-ntru-schemes.github.io/blob/master/cost_asymptotics.py>`__ 

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        """
        if not isinstance(attack_configuration, Attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attacks.Attack_Configuration")

        bkz_cost_models = cost_asymptotics.BKZ_COST_ASYMPTOTICS
        if attack_configuration.quantum and not attack_configuration.classical:
            bkz_cost_models = [c for c in bkz_cost_models if "Quantum" in c["group"]]
        elif attack_configuration.classical and not attack_configuration.quantum:
            bkz_cost_models = [c for c in bkz_cost_models if "Classical" in c["group"]]
        if attack_configuration.sieving and not attack_configuration.enumeration:
            bkz_cost_models = [c for c in bkz_cost_models if "sieving" in c["group"]]
        elif attack_configuration.enumeration and not attack_configuration.sieving:
            bkz_cost_models = [c for c in bkz_cost_models if "enumeration" in c["group"]]
        return bkz_cost_models
        # TODO: other cost models?
    

    class SIS:
        """
        Namespace for SIS attacks
        """
        def lattice_reduction(n, q, m, bound, reduction_cost_model):
            r""" 
            TODO: description

            Finds optimal lattice subdimension :math:`d` and root-Hermite factor :math:`\delta_0` for lattice reduction.

            To calculate d, we use :cite:p:`RS10` Proposition 1 (Normalization of q-ary Lattices):

            Let :math:`n \geq 128, q \geq n^2,` and :math:`\beta < q`. Let :math:`S` be a :math:`\delta`-HSVP solver for variable :math:`\delta`. The optimal dimension for solving SIS(:math:`n, m, q, \beta`) with :math:`S` is :math:`d = \min(x : q^{2n/x} \leq \beta)`.

            .. math::

                q^{2n / d} &\leq \beta \\
                \frac{2n}{d \log(q)} &\leq \beta \\
                d &\geq \frac{2n \log(q)}{\log(\beta)}

            To calculate :math:`\delta_0` we use :cite:p:`RS10` Conjecture 2:

            For every :math:`n \geq 128,` constant :math:`c \geq 2, q \geq n^c, m = \Omega(n \log_2(q)` and :math:`\beta < q`, the best known approach to solve SIS with parameters (:math:`n, m, q, \beta`) involves solving :math:`\delta`-HSVP in dimension :math:`d = \min(x : q^{2n/x} \leq \beta)` with :math:`\delta = \sqrt[d]{\beta / q^{n/d}}`.

            :param n: height of matrix
            :param m: width of matrix
            :param q: modulus
            :param bound: bound of solution, must be instance of :class:`Norm.Base_norm` 
            """
            beta = bound.to_L2() # we need L2 norm TODO: check
            if 1 < beta < q: # Condition is not a requirement for [RS10] but we would divide by log(beta) which is <= 0
                # TODO: RS10 assumes delta-SVP solver => ensure that solver used here is indeed delta-HSVP

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

                if delta_0 < 1: # intractable
                    ret = estimator.Cost([("rop", oo)]) # TODO: what to return?

                else: # standard case
                    k = estimator.betaf(2**log_delta_0) # block size k [APS15, lattice rule of thumb and Lemma 5]
                    B = log(q, 2)

                    # TODO: is that all we need?
                    cost = reduction_cost_model(k, d, B) 
                    ret = estimator.Cost([("rop", cost)]) # TODO

            else: # not a hard problem, trivial solution exists
                ret = estimator.Cost([("rop", 0), ("trivial", True)]) # TODO
                
            return ret

        def combinatorial(q, n, m, bound, reduction_cost_model=None):
            r""" 
            TODO: description

            Search for optimal k such that combinatorial method can divide columns of :math:`A` into :math:`2^k` groups as described in :cite:`MR09`, p. 7. :math:`k` is chosen such that :math:`n \approx (k + 1) \log_q (L)`, where :math:`L = (2\beta + 1)^{m/2^k}` describes the number of vectors per list. Equivalently, we have 

            .. math::
                \frac{2^k}{k+1} &\approx \frac{m \log(2\beta + 1)}{n \log(q)}\\
                \text{diff} &= \text{abs}\left(\frac{2^k}{k+1} - \frac{m \log(2\beta + 1)}{n \log(q)}\right)

            To find an optimal :math:`k`, we iterate over :math:`k` starting from :math:`k=1` and calculate the difference :math:`\text{diff}`. When :math:`\text{diff}` does not decrease for 10 iteration steps, we stop and take the current :math:`k`.

            We make a conservative estimate of the cost by estimating the number of operations needed to create the initial lists. Each of the :math:`2^k` lists contains :math:`L` vectors. The cost for any operation on a list element is at least :math:`\log_2(q) * n`. Hence, the total cost is :math:`2^k * L * \log_2(q) * n`.

            :param n: height of matrix
            :param m: width of matrix
            :param q: modulus
            :param bound: bound of solution, must be instance of :class:`Norm.Base_norm`
            """
            beta = bound.to_Loo() # we need Loo norm
            if beta < q:
                # find optimal k
                k = 1
                difference = oo
                failed, max_failures = 0, 10
                while failed < max_failures:
                    left = 2**k / (k + 1)
                    right = m / n * log(2 * beta + 1, q)
                    new_difference = abs(left - right)
                    if new_difference < difference:
                        difference = new_difference
                        closest_k = k
                        failed = 0
                    else:
                        failed += 1
                    k += 1
                k = closest_k

                # cost of creating initial lists
                L = (2 * beta + 1)**(m / 2**k)
                list_element_cost = log(q, 2) * n
                lists = (2 ** k) * L
                cost = lists * list_element_cost

                return estimator.Cost([("rop", cost)]) # TODO other information?

            else: # not a hard problem, trivial solution exists
                ret = estimator.Cost([("rop", 0), ("trivial", True)]) # TODO

# Norms # 
class Norm:
    r"""
    Namespace for norms and norm transformation.

    Let :math:`n` be the dimension of the vector and with a slight abuse of notation :math:`L_i` represent the value of :math:`L_i`-norm of the vector. From section 2.1 in :cite:`BDLOP18` we have:
    
    #. :math:`\;\;L_1 \leq \sqrt{n} L_2`
    #. :math:`\;\;L_1 \leq n L_\infty`
    #. :math:`\;\;L_2 \leq \sqrt{n} L_\infty \;\;\;(\text{since }  \sqrt{n} L_2 \leq n L_\infty)`
    #. :math:`\;\;L_\infty \leq L_1`

    
    And from Theorem 7 in :cite:`DPSZ12`:
    
    5. :math:`\;\;L_\infty \leq C_\infty`
    6. :math:`\;\;C_\infty \leq L_1`

    # TODO: norm transformations documentation
    """
    class Base_Norm():
        pass


    class Lp(Base_Norm):
        # TODO: inform user about how to use norm on vector in ring/module? I.e. multiply dimension with degree
        def __init__(self, value, dimension, p):
            """
            :param value: value of :math:`L_p`-norm of a vector
            :param dimension: dimension of the vector
            :param p: specifies :math:`L_p`-norm, only values 1, 2, oo are supported
            """
            self.p = p
            self.value = value
            self.dimension = dimension

        def to_L1(self):
            """
            :returns: upper bound of :math:`L_1`-norm of the vector
            """
            if self.p == 1:
                return Norm.Lp(self.value, self.dimension, 1)
            elif self.p == 2:
                return Norm.Lp(self.value * sqrt(self.dimension), self.dimension, 1)
            elif self.p == oo:
                return Norm.Lp(self.value * self.dimension, self.dimension, 1)
            else:
                raise ValueError(f"L{self.p}-norm not supported")

        def to_L2(self, n=None):
            """
            :returns: upper bound of :math:`L_2`-norm of the vector
            """
            if self.p == 1:
                return Norm.Lp(self.value * sqrt(self.dimension), self.dimension, 2)
            elif self.p == 2:
                return Norm.Lp(self.value, self.dimension, 2)
            elif self.p == oo:
                return Norm.Lp(self.value * sqrt(self.dimension), self.dimension, 2)
            else:
                raise ValueError(f"L{self.p}-norm not supported")

        def to_Loo(self):
            """
            :returns: upper bound of :math:`L_\infty`-norm of the vector
            """
            if self.p == 1:
                return Norm.Lp(self.value, self.dimension, oo)
            elif self.p == 2:
                return Norm.Lp(self.value * sqrt(self.dimension), self.dimension, oo)
            elif self.p == oo:
                return Norm.Lp(self.value, self.dimension, oo)
            else:
                raise ValueError(f"L{self.p}-norm not supported")

        def to_Coo(self):
            """
            :returns: upper bound of :math:`C_\infty`-norm of the vector
            """
            if self.p == 1:
                return Norm.Coo(self.value, self.dimension)
            elif self.p == 2:
                return Norm.Coo(self.value * sqrt(self.dimension), self.dimension)
            elif self.p == oo:
                return Norm.Coo(self.value * self.dimension, self.dimension)
            else:
                raise ValueError(f"L{self.p}-norm not supported")

    class Coo(Base_Norm):
        """
        Infinity norm of canonical embedding.
        """
        def __init__(self, value, dimension):
            """
            :param value: value of :math:`C_\infty`-norm of a vector
            :param dimension: dimension of the vector
            """
            self.value = value
            self.dimension = dimension

        def to_L1(self):
            """
            :returns: upper bound of :math:`L_1`-norm of the vector
            """
            return Norm.Lp(self.value * self.dimension, self.dimension, 1)

        def to_L2(self):
            """
            :returns: upper bound of :math:`L_2`-norm of the vector
            """
            return Norm.Lp(self.value * sqrt(self.dimension), self.dimension, 2)

        def to_Loo(self):
            """
            :returns: upper bound of :math:`L_\infty`-norm of the vector
            """
            return Norm.Lp(self.value, self.dimension, oo)
        
        def to_Coo(self):
            """
            :returns: upper bound of :math:`C_\infty`-norm of the vector
            """
            return Norm.Coo(self.value, self.dimension)


# Error Parameter Conversion (extension to functions in estimator.py)
def alpha_to_stddevf(alpha, q):
    r"""
    noise rate :math:`\alpha`, modulus q → standard deviation :math:`\sigma`

    :param alpha: noise rate
    :param q: modulus `0 < q`

    :returns: :math:`\sigma = \alpha \cdot q / \sqrt{2\pi}` 
    """
    return stddevf(RR(alpha * q))


# TODO: if we change q (e.g. in reduction), what values change?
class Distributions:
    """
    Namespace for distributions
    """
    class Uniform():
        def __init__(self, a=None, b=None, h=None, uniform_mod_q=False):
            """
            :param a: lower bound if b is specified, else take range [-a, a]
            :param b: upper bound, optional
            :param h: exactly :math:`h` components are :math:`\in [a,…,b]∖\{0\}`, all other components are zero
            :param uniform_mod_q: uniform mod q, if True no other value must be specified
            """
            if (not a and not uniform_mod_q) or (a and uniform_mod_q):
                raise ValueError("Either a must have a value or uniform must be True.")
            self.uniform_mod_q = uniform_mod_q
            if not uniform_mod_q:
                if b is None:
                    b = a
                    a = -a
                self.range = (a, b)
                self.h = h

        def get_alpha(self, q, n=None):
            r"""
            Calculates noise rate :math:`\alpha` of approximately equivalent Gaussian distribution.

            TODO: describe how it is calculated?

            :param q: modulus
            :param n: secret dimension, only needed for uniform mod q and sparse secrets
            :returns: noise rate :math:`\alpha`
            """
            variance = SDis.variance(self._convert_for_lwe_estimator(), q=q, n=n)
            return alphaf(sqrt(variance), q, sigma_is_stddev=True)

        def get_range(self, q=None):
            """
            :param q: only needed for uniform mod q
            """
            if self.uniform_mod_q:
                return (0, q)
            else:
                return self.range

        def _convert_for_lwe_estimator(self):
            """
            Convert uniform distribution into format accepted by the lwe-estimator 
            """
            if self.uniform_mod_q:
                return "uniform"
            elif self.h:
                return (self.range, self.h)
            else:
                return self.range()


    class Gaussian(Norm.Base_Norm, ABC):
        @abstractmethod
        def __init__(self):
            # TODO: bad style, parent class accesses child attributes
            pass

        def get_alpha(self): # TODO: perhaps calculate alpha via q and sigma
            r"""
            :returns: noise rate :math:`\alpha`
            """
            return self.alpha
        
        def get_stddev(self):
            """
            :returns: standard deviation :math:`\sigma`
            """
            return self.sigma

        def get_s(self):
            """
            :returns: Gaussian width parameter :math:`s = \sigma \cdot \sqrt{2\pi}`
            """
            return self.s

        def to_L1(self):
            r"""
            Transforms Gaussian width into norm :math:`L_1`-norm of a vector whose coefficients are distributed according to a Gaussian. Before the function call the dimension attribute of the object must be set manually (e.g. 'secret_distribution.dimension = n'). 
            
            TODO: what if sampling is not component-wise?

            .. _to_L1:

            For a Gaussian distribution, we have that: 

            .. math::
                \text{Pr}\left[ |X| \geq x\right] &\leq 2 e^{-\pi x^2/s^2}\\
                \text{Pr}\left[ |X| \geq x s\right] &\leq 2 e^{-\pi x^2}\\
                \text{Pr}\left[ |X| \geq \frac{x s}{\sqrt{\pi}}\right] &\leq 2 e^{-x^2}\\
                \text{Pr}\left[ |X| \geq \frac{\sqrt{x} s}{\sqrt{\pi}}\right] &\leq 2 e^{-x}

            We require :math:`2 e^{-x} \approx 2^{-128}` and obtain :math:`x = 90`. Hence, we can estimate our bound as :math:`\sqrt{90} s / \sqrt{\pi}`.

            :returns: upper bound of :math:`L_1`-norm of vector
            """
            try:
                dimension = self.dimension
            except:
                raise AttributeError("Dimension must be set before calling norm transformations (e.g. 'secret_distribution.dimension = n'")
            bound = sqrt(90) * self.s / sqrt(pi)
            return Norm.Lp(bound, dimension, oo).to_L1()

        def to_L2(self):
            r"""
            Transforms Gaussian width into norm :math:`L_2`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_L1`_). Before the function call the dimension attribute of the object must be set manually (e.g. 'secret_distribution.dimension = n'). 

            :returns: upper bound of :math:`L_2`-norm of vector
            """
            try:
                dimension = self.dimension
            except:
                raise AttributeError("Dimension must be set before calling norm transformations (e.g. 'secret_distribution.dimension = n'")
            bound = sqrt(90) * self.s / sqrt(pi)
            return Norm.Lp(bound, dimension, oo).to_L2()

        def to_Loo(self):
            r"""
            Transforms Gaussian width into norm :math:`L_\infty`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_L1`_). Before the function call the dimension attribute of the object must be set manually (e.g. 'secret_distribution.dimension = n'). 

            :returns: upper bound of :math:`L_\infty`-norm of vector
            """
            try:
                dimension = self.dimension
            except:
                raise AttributeError("Dimension must be set before calling norm transformations (e.g. 'secret_distribution.dimension = n'")
            bound = sqrt(90) * self.s / sqrt(pi)
            return Norm.Lp(bound, dimension, oo).to_Loo()

        def to_Coo(self):
            r"""
            Transforms Gaussian width into norm :math:`C_\infty`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_L1`_). Before the function call the dimension attribute of the object must be set manually (e.g. 'secret_distribution.dimension = n'). 

            :returns: upper bound of :math:`C_\infty`-norm of vector
            """
            try:
                dimension = self.dimension
            except:
                raise AttributeError("Dimension must be set before calling norm transformations (e.g. 'secret_distribution.dimension = n'")
            bound = sqrt(90) * self.s / sqrt(pi)
            return Norm.Lp(bound, dimension, oo).to_Coo()

        def _convert_for_lwe_estimator(self):
            """
            For secret distribution, implies that secret distribution follows error distribution (others not supported)
            """
            return "normal" 
            # TODO what happens if both secret and error distribution are Gaussian but not the same?


    class Gaussian_alpha(Gaussian):
        """
        Helper class for Gaussian distribution. 
        """
        def __init__(self, alpha, q):
            r"""
            :param sigma: noise rate :math:`\alpha`
            :param q: modulus
            """
            self.alpha = RR(alpha)
            # TODO: Do we actually need stddev/sigma?
            self.sigma = stddevf(self.alpha, q)
            self.s = sigmaf(self.stddev)

    class Gaussian_sigma(Gaussian):
        """
        Helper class for Gaussian distribution.
        """
        def __init__(self, sigma, q):
            """
            :param sigma: standard deviation :math:`\sigma`
            :param q: modulus
            """
            self.sigma = RR(sigma)
            self.s = sigmaf(self.sigma)
            self.alpha = alphaf(self.sigma, q)

    class Gaussian_s(Gaussian):
        """
        Helper class for Gaussian distribution.
        """
        def __init__(self, s, q):
            """
            :param sigma: Gaussian width :math:`s = \sigma \cdot \sqrt{2\pi}`
            :param q: modulus
            """
            self.s = s
            self.sigma = stddevf(self.s)
            self.alpha = alphaf(s, q)


# Problem Variants # 
class Problem:
    """
    Namespace for processing problem instance parameter sets.
    """
    class LWE():
        def __init__(self, n, q, m, secret_distribution, error_distribution): 
            """
            :param q: modulus
            :param n: secret dimension
            :param m: number of samples
            :param alpha: noise rate
            """
            # TODO: check soundness of parameters
            if not secret_distribution or not error_distribution or not n or not q or not m or n<0 or q<0 or m<0:
                raise ValueError("Parameters not specified correctly")

            self.n = n
            self.q = q
            self.m = m
            self.secret_distribution = secret_distribution
            self.error_distribution = error_distribution
        
        def estimate_cost(self, attack_configuration):
            """
            :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
            """
            ## Overview over algorithms in estimator:
            
            # combinatorial algorithms for sparse (and small?) secrets:
            #   condition:
            #       is_sparse and is_small secret (SDis)
            #   algorithms:
            #       guess_and_solve [?]: guesses components of the secret, e.g. partial(guess_and_solve, dual_scale)
            #       drop_and_solve [Alb17]: used for example in arora-gb if secret is sparse

            # combinatorial algorithms for small secrets?
            #   condition:
            #       is_small
            #   switch_modulus [?] e.g. partial(switch_modulus, arora_gb)

            # primal attack 
            #   uSVP [ADPS16, BG14]
            #       primal_usvp
            #
            #   enumeration
            #       primal_decode [LP11] 
            #           uses enumeration_cost: what does that do? Why not just enumeration estimates?
            #           uses rinse_and_repeat (what does that do?)

            # dual attack 
            #   _dual_scale_factor: scale factor for dual attack [BG14?] to exploit unusually small secret
            #   dual: dual attack (uses dual_ and rinse_and_repeat) as in [MR09]
            #   dual_scale: finding small `(y,x/c)` such that `y ⋅ A ≡ c ⋅ x \bmod q` as in [Alb17]
            
            # Combinatorial
            #   mitm: meet-in-the-mittle as in [APS15]
            #   bkw_coded: coded-BKW [GJS15]

            # Algebraic
            #   gb_cost: cost of computing Gröbner basis
            #   arora_gb: [AG11, ACFP14]
            

            # TODO: attack_configuration could contain: 
            #   - q_sieving, sieving, q_enum, enum (like in cost_asymptotics) as boolean values
            #       estimator also includes various sive/enum estimates
            #   - primal_usvp, dual_scale (not applicable for NTRU assumption)
            #   - dual_use_lll

            if not isinstance(attack_configuration, Attacks.Attack_Configuration):
                raise ValueError("attack_configuration must be instance of Attack_Configuration")

            sec_distribution = self.secret_distribution._convert_for_lwe_estimator()            

            cost_models = Attacks.reduction_cost_models()
            skip_list = ["mitm", "arora-gb", "bkw"] # TODO: change list/add to attack_configuration

            # TODO: run in parallel? same in Problem.SIS.estimate_cost()
            # best_result is tuple of form (('alg_name', cost_dict), cost_model_dict)
            best_result = ((None, {"rop": oo}), None)
            for cost_model in cost_models:
                results = estimate_lwe(n=self.n, alpha=self.error_distribution.get_alpha(), q=self.q, 
                                secret_distribution=sec_distribution, m=self.m, reduction_cost_model=cost_model["reduction_cost_model"], 
                                skip=skip_list)
                # TODO: estimate_lwe function does not take success_probability into account, but is set to 0.99 anyways (all estimates in cost_asymptotics use same value)
                best = min(results.items(), key=lambda res: res[1]["rop"])
                if best[1]["rop"] < best_result[0][1]["rop"]:
                    best_result = (best, cost_model)

            # TODO: what to do with the other results?
            # TODO: return nice dict representation of results
            return best_result[0][1]["rop"]

            # TODO: test!


    class MLWE():
        def __init__(self, n, d, q, m, secret_distribution, error_distribution):
            """
            :param n: degree of polynomial
            :param d: rank of module
            :param q: modulus
            :param m: number of samples
            :param secret_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
            :param error_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
            """
            # TODO: check soundness of parameters
            self.n = n
            self.d = d
            self.q = q
            self.m = m
            self.secret_distribution = secret_distribution
            self.error_distribution = error_distribution

            
        def estimate_cost(self, attack_configuration, use_reduction=False):
            r""" 
            Estimates cost of MLWE instance.

            If use_reduction is `False`, the cost is estimated for an LWE instance with dimension :math:`n=n \cdot d`. Else, the MLWE instance will be reduced to RLWE according to :cite:`KNK20b` as follows:

            Corollary (:cite:`KNK20b` Corollary 1, note: :cite:`KNK20b` contains error in exponent of q):

            If we take :math:`k = d`, then there exists an efficient reduction from :math:`\textit{M-SLWE}_{m,q, \Psi \leq \alpha}^{R^d}\left(\chi^d\right)` to :math:`\textit{R-SLWE}_{m,q^d, \Psi \leq \alpha\cdot n^2\cdot\sqrt{d}}^{R}\left(U(R_q^\vee)\right)` with controlled error rate :math:`\alpha`.

            Note that the reduction only works for Search-MLWE TODO: find reduction for decision-MLWE?

            :param cost_model: cost model for cost estimation
            :param attack_configuration: TODO
            :param use_reduction: specify if reduction to RLWE is used
            """
            # TODO: check if correct
            use_reduction = False
            if use_reduction:
                alpha_MLWE = self.error_distribution.get_alpha()
                alpha_RLWE = RR(alpha_MLWE * self.n**2 * sqrt(self.d))
                q_RLWE = self.q**self.d
                secret_distribution_RLWE = Distributions.Uniform(0, self.q) # TODO: is this correct?
                error_distribution_RLWE = Distributions.Gaussian_alpha(alpha_RLWE, q_RLWE)
                rlwe = Problem.RLWE(n=self.n, q=q_RLWE, m=self.m, secret_distribution=secret_distribution_RLWE, 
                                   error_distribution=error_distribution_RLWE)

                return rlwe.estimate_cost(attack_configuration=attack_configuration,     
                                          use_reduction=use_reduction)
                
            else:
                lwe = Problem.LWE(n=self.n*self.d, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                                  error_distribution=self.error_distribution)
                return lwe.estimate_cost(attack_configuration)


    class RLWE():
        def __init__(self, n, q, m, secret_distribution, error_distribution):
            """
            :param n: degree of polynomial
            :param q: modulus
            :param m: number of samples
            :param secret_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
            :param error_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
            """
            ## interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
            # TODO: is this correct? 
            self.n = n
            self.q = q
            self.m = m
            self.secret_distribution = secret_distribution
            self.error_distribution = error_distribution

        def estimate_cost(self, attack_configuration, use_reduction=False):
            """ 
            Estimates cost of MLWE instance.

            :param cost_model: cost model for cost estimation
            :param attack_configuration: TODO
            :param use_reduction: specify if reduction to RLWE is used
            """
            pass
            lwe = Problem.LWE(n=self.n, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                                  error_distribution=self.error_distribution)
            return lwe.estimate_cost(attack_configuration=attack_configuration)


    class Statistical_Gaussian_MLWE(MLWE):
        r"""
        Statistically secure MLWE over Gaussian distribution according to :cite:`LPR13`.
        
        Mapping of parameters in paper to use here:

        ============================= =========== ====================
        Parameters in :cite:`LPR13`   Use Here    Represents
        ============================= =========== ====================
        :math:`q`                     :math:`q`   modulus
        :math:`l`                     :math:`m`   width of matrix
        :math:`k`                     :math:`d`   height of matrix
        :math:`n`                     :math:`n`   degree of polynomial
        ============================= =========== ====================

        Then Corollary 7.5 combined with Theorem 7.4 in :cite:`LPR13` reads as follows:
        Let :math:`R` be the ring of integers in the :math:`m'`th cyclotomic number field :math:`K` of degree :math:`n`, and :math:`q \geq 2` an integer. For positive integers :math:`d \leq m \leq poly(n)`, let :math:`A = [ I_{[d]} \mid \bar{A}] \in (R_q)^{[d] \times [m]}`, where :math:`I_{[d]} \in (R_q)^{[d] \times [d]}` is the identity matrix and :math:`\bar{A} \in (R_q)^{[d] \times [m-d]}` is uniformly random. Then with probability :math:`1 - 2^{-\Omega(n)}` over the choice of :math:`\bar{A}`, the distribution of :math:`A\mathbf{x} \in (R_q)^{[d]}` where each coordinate of :math:`\mathbf{x} \in (R_q)^{[m]}` is chosen from a discrete Gaussian distribution of paramete :math:`r > 2n \cdot q^{d / m + 2/(n m)}` over :math:`R`, satisfies that the probability of each of the :math:`q^{n d}` possible outcomes is in the interval :math:`(1 \pm 2^{-\Omega(n)}) q^{-n d}` (and in particular is within statistical distance :math:`2^{-\Omega(n)}` of the uniform distribution over :math:`(R_q)^{[d]}`).
        """
        def __init__(self, n, d, q, m):
            """
            :param sec: required bit security of MLWE instance
            :param n: degree of polynomial
            :param d: rank of module
            :param q: modulus
            :param m: number of samples
            :param beta: upper bound on norm of solution
            """
            
            # Holds for normal form? What if not normal form?
            ## Corollary 7.5 (variant of regularity theorem)
            ## For k is height, l width of matrix A, n degree, and q modulus:
            ##   if x is distributed according to Gaussian of width r > (2n * q^(k/l + 2/(nl)))
            ##   then Ax is within statistical distance 2^-n of uniform distribution over R_q^k
            # TODO: check if this is correct
            s = RR(2 * n * q**(d / m + 2 / (n * m)))
            # gaussian_width is not standard deviation
            alpha = alphaf(s, q)
            
            # TODO: should we require n > 128 or n > 256 to ensure unconditional hardness or check if n > sec?
            super().__init__(n=n, d=d, q=q, m=m, alpha=alpha)


    class Statistical_Uniform_MLWE():
        r"""
        Statistically secure MLWE over Uniform distribution with invertible elements :cite:`BDLOP18`.

        MLWE problem instance where samples :math:`(A', h_A'(y))` are within statistical distance :math:`2^{-128}` of :math:`(A', u)` for uniform :math:`u`.

        Mapping of parameters in paper to use here:

        ============================= =========== ====================
        Parameters in :cite:`BDLOP18` Use Here    Represents
        ============================= =========== ====================
        :math:`q`                     :math:`q`   modulus
        :math:`k`                     :math:`m`   width of matrix
        :math:`n`                     :math:`d`   height of matrix
        :math:`d`                     :math:`d_2` variable
        :math:`N`                     :math:`n`   degree of polynomial
        ============================= =========== ====================

        Lemma (cite:`BDLOP18` Lemma 4): Let :math:`1 < d_2 < n` be a power of 2. If :math:`q` is a prime congruent to :math:`2 d_2 + 1(\mod 4 d_2)` and 

        .. math::
            q^{d/m} \cdot 2^{256/(m\cdot n)} \leq 2 \beta < \frac{1}{\sqrt{d_2}} \cdot q^{1/d_2}

        then any (all-powerful) algorithm :math:`\mathcal{A}` has advantage at most :math:`2^{-128}` in solving :math:`\text{DKS}_{d,m,\beta}^\infty`, where :math:`\text{DKS}` is the decisional knapsack problem. 

        """
        def __init__(self, n, d, q, m, d_2):
            """
            :param sec: required bit security of MLWE instance # TODO
            :param n: degree of polynomial
            :param d: rank of module
            :param q: modulus (must be prime congruent to 2d_2 + 1(mod 4d_2))
            :param m: number of samples
            :param d_2: 1 < d_2 < N and d_2 is a power of 2
            """
            # TODO: check prerequisites?
            lower = RR(q**(d_2 / m) * 2**(256 / (m * n)))
            upper = RR(1 / sqrt(d_2) * q**(1 / d_2))
            beta = None # TODO
            alpha = None # TODO
            raise NotImplementedError("Currently not supported.")

            self.n = n
            self.q = q
            self.m = m
            self.d = d
            self.d_2 = d_2
            self.alpha = alpha

    class SIS():
        # TODO: value in norm, perhaps extra convenience when gaussian => transformation in norm
        # TODO: bound is instance of norm class, value is beta
        # TODO: change Gaussian distro that it has to_L_i norm => call right functions 
        def __init__(self, n, q, m, bound):
            """
            :param q: modulus
            :param n: secret dimension
            :param m: number of samples
            :param beta: upper bound on norm of solution
            :param norm: used norm of upper bound, must be instance of subclass of :class:`Norm.Base_Norm`
            """
            self.q = q
            self.n = n
            self.m = m
            if not issubclass(bound, Norm.Base_Norm):
                raise ValueError("Norm must be subclass of Base_Norm.")
            self.bound = bound
        
        def estimate_cost(self, attack_configuration):
            """ 
            Estimates cost of the SIS instance.

            :param attack_configuration: TODO
            :param use_reduction: specify if reduction to RLWE is used
            """
            
            lattice_reduction = True # TODO: add to attack_configuration
            combinatorial = True # TODO: add to attack_configuration
            cost_models = Attacks.reduction_cost_models(attack_configuration) # TODO

            best_result = (None, {"rop": oo}, None)
            if lattice_reduction:
                # TODO: run in parallel? same in Problem.LWE.estimate_cost()
                for cost_model in cost_models:
                    result = Attacks.SIS.lattice_reduction(n=self.n, q=self.q, m=self.m, bound=self.bound, 
                                                            reduction_cost_model=cost_model["reduction_cost_model"])
                    if result["rop"] < best_result[1]["rop"]:
                        best_result = ("lattice_reduction", result, cost_model)
            if combinatorial:
                result = Attacks.SIS.combinatorial(n=self.n, q=self.q, m=self.m, bound=self.bound)
                if result["rop"] < best_result[1]["rop"]:
                    best_result = ("combinatorial", result, None) # TODO: handle cost_model in case that is used for output
            
            # TODO: what to do with the other results?
            # TODO: return nice dict representation of results
            return best_result[1]["rop"]

            # TODO: test!


    class MSIS(SIS):
        def __init__(self, n, d, q, m, bound):
            """
            :param q: modulus
            :param d: rank of module
            :param n: degree of polynomial
            :param m: number of samples
            :param bound: upper bound on norm of solution, must be subclass of :class:`Norm.Base_Norm`
            """
            # TODO: parameter if beta is not given but instead gaussian/uniform distribution? or helper function?
            self.n = n
            self.d = d
            self.q = q
            self.m = m
            if not issubclass(bound, Norm.Base_Norm):
                raise ValueError("Norm must be subclass of Base_Norm.")
            self.bound = bound
        
        def estimate_cost(self, attack_configuration, use_reduction=False):
            r""" 
            Estimates cost of MSIS instance.

            If use_reduction is `False`, the cost is estimated for an SIS instance with dimension :math:`n=n \cdot d`. Else, the MSIS instance will be reduced to RSIS according to :cite:`KNK20b` as follows:

            Corollary (:cite:`KNK20b` Corollary 2):

            Let :math:`k = 2` and :math:`q` be a prime. Let a positive real number :math:`\beta` be an upper bound on the :math:`L_2`-norm of the solution of :math:`\text{R-SIS}_{q,m,\beta}` and :math:`d \in \mathbb{N}` be a module rank such that

            .. math:: \sqrt{n m} \cdot q^{1/m} \leq \beta < \sqrt[2d-1]{q / (\sqrt{m}^{d-1})}.
            
            Then there exists a reduction from :math:`\text{M-SIS}_{q^k,m^k,\beta'}` to :math:`\text{R-SIS}_{q,m,\beta}` with :math:`\beta' = m^{k(d-1)/2} \cdot \beta^{k(2d-1)}`.

            :param attack_configuration: TODO
            :param use_reduction: specify if reduction to RLWE is used
            """
            # TODO
            use_reduction = False
            if use_reduction:
                # transform to L2-norm
                self.beta = self.bound.to_L2().value

                # TODO: check preconditions
                k = 2
                lower = RR(sqrt(self.n * self.m) * self.q**(1 / self.m))
                upper = RR((self.q / sqrt(self.m)**(self.d-1))**(1 / (2 * self.d - 1)))
                if lower <= self.beta and self.beta < upper:
                    q_RSIS = RR(round(self.q**(1/k)))
                    m_RSIS = RR(round(self.m**(1/k)))
                    beta_RSIS = RR((self.beta / (self.m**((self.d - 1) / 2)))**(1 / (k * (2 * self.d - 1))))
                    bound = Norm.Lp(beta_RSIS, self.n, 2) # new dimension of input vector (instead of n * d in M-SIS)

                rsis = Problem.RSIS(n=self.n, q=q_RSIS, bound=bound, m=m_RSIS)
                return rsis.estimate_cost(attack_configuration=attack_configuration,     
                                          use_reduction=use_reduction) # TODO: use_reduction makes sense?

            else:
                sis = Problem.SIS(n=self.n*self.d, q=self.q, m=self.m, beta=self.beta, norm=self.norm)
                return sis.estimate_cost(attack_configuration=attack_configuration, 
                                         use_reduction=use_reduction)


    class Statistical_MSIS(MSIS):
        r"""
        Statistically secure MSIS :cite:`DOTT21`, section 4.1

        MLWE problem instance where the probability that non zero elements :math:`\mathbf{r}` in the Euclidean ball :math:`B_{m}(0, 2B)` satisfy :math:`\hat{\mathbf{A}}_1 \cdot \mathbf{r} = \mathbf{0}` is :math:`2^{-\text{sec}}`.

        Mapping of parameters in :cite:`DOTT21` to use here:

        ============================ ============= ====================
        Parameters in :cite:`DOTT21` Use Here      Represents
        ============================ ============= ====================
        :math:`m'`                   :math:`m`     width of matrix :math:`A_1`
        :math:`m`                    :math:`d`     height of matrix :math:`A_1`
        :math:`B`                    :math:`B`     norm-bound of secret
        :math:`s`                    :math:`s`     Gaussian width (not stddev)
        :math:`N`                    :math:`n`     degree of polynomial
        ============================ ============= ====================

        We choose bound :math:`B = s \cdot \sqrt{m \cdot n}` to ensure that the retry probability in the committing algorithm is negligible. The number of elements in :math:`B_{m}(0, 2B)` can be estimated from above as :math:`|B_{m}(0, 2B)| \ll (2 \pi e /(m n))^{m n/2} \cdot (2 B)^{m n}`. The scheme is statistically binding if the probability that non zero elements in :math:`B_{m}(0, 2B)` of radius :math:`2B` in :math:`R_q^{m}` map to :math:`\mathbf{0}` in :math:`R_q^{d}` is negligible. Hence, it must hold that :math:`|B_m(0, 2B)|/q^{d n} = 2^{-\text{sec}}` and we get:
         
        .. math::
            ((2 \pi e/(m n))^{1/2} * (2 B))^{m n} &= 2^{-\text{sec}} * q^{d n} \\
            B &= 2^{-\text{sec} / (m n)} \cdot \frac{q^{d / m}}{2} \cdot (m n / (2 \pi e))^{1/2}\\
            s &= 2^{-\text{sec} / (m n)} \cdot \frac{q^{d / m}}{2} \cdot \frac{(m n / (2 \pi e))^{1/2}}{\sqrt(m n)}

        """
        def __init__(self, sec, n, d, q, m):
            """
            :param sec: required bit security of MSIS instance
            :param q: modulus
            :param n: degree of polynomial
            :param m: number of samples (or width of matrix)
            :param beta: upper bound on norm of solution
            :param d: rank of module (or height of matrix)
            """
            # TODO: use sage for increased precision?
            sigma = RR(2**(-sec / (m * n)) * q**(d / m) / 2 * (m * n / (2 * pi * e))**(1 / 2) / sqrt(m * n))
            alpha = alphaf(sigma, q)
            # TODO: Do we need alpha or beta here?
            secret_distribution = Distributions.Gaussian_alpha(alpha, q)
            super().__init__(n=n, d=d, q=q, m=m, secret_distribution=secret_distribution)
        
        def get_alpha(self):
            return self.secret_distribution.get_alpha()


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
                secure = False; break

        if secure and i > 0:
            # Only if all problem instances of a parameter set pass
            # TODO: possibly extra class/dict with additional information...
            return (current_parameter_set, current_sec) 
            
        # TODO: check if correct
        for parameter_set in next_parameters(*current_parameter_set):
            bisect.insort_left(current_parameter_sets, Parameter_Set(parameter_set))



if __name__ == "__main__":
    class Commandline:
        def doc(self):
            # requires sphinx (e.g. "pip install sphinx")
            os.system("sphinx-apidoc -o doc . usage_example.py") # EXCLUDE usage_example for now as it does not "compile" at all
            os.system("sphinx-build doc doc/html")

    fire.Fire(Commandline)

