r""" 
TODO: documentation
"""


try: # sage-related imports do not work with sphinx for documentation
    from abc import ABC, abstractmethod
    import distributions
    from collections import OrderedDict
    import time
    import attacks
    import norm
    import sys
    import os
    import logging
    import traceback
    from multiprocessing import Value
    from attacks import Attack_Configuration
    from distributions import Distribution, Gaussian_s, Gaussian_sigma
    from functools import partial
    import sage.all 
    from sage.functions.log import exp, log
    from sage.functions.other import ceil, sqrt, floor, binomial
    from sage.rings.all import QQ, RR
    from sage.symbolic.all import pi, e
    from sage.misc.functional import round
    sys.path.append(os.path.dirname(__file__) + "/estimate_all")
    from estimator import estimator as est
    oo = est.PlusInfinity()
    import param_search
except:
    pass


## Logging ##
logger = logging.getLogger(__name__)


statistical_sec = 128 #: for statistical security


# Helper class
class Estimate_Res():
    """
    Type of return value needed for overloaded lt-operator :class:`Problem` instances.

    :param is_secure: true if Problem instance satisfies security requirment
    :param results: result object
    """
    def __init__(self, is_secure, results):
        self.is_secure = is_secure
        self.results = results

    def __bool__(self):
        return self.is_secure

class Base_Problem(ABC):
    @abstractmethod
    def __init__(self):
        pass

    @abstractmethod
    def estimate_cost(self, sec=None, attack_configuration=None) -> Estimate_Res:
        pass

    @abstractmethod
    def __lt__(self, sec) -> Estimate_Res:
        pass

    @abstractmethod
    def __str__(self):
        pass


## LWE and its variants ##
class LWE(Base_Problem):
    # TODO: docstring (also other variants)

    def __init__(self, n, q, m, secret_distribution : Distribution, error_distribution : Distribution): 
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        """
        # check soundness of parameters
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def estimate_cost(self, attack_configuration, sec=None) -> Estimate_Res:
        """
        Estimates the cost of an attack on the LWE instance, lazy evaluation if `sec` is set.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """ 
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        
        secret_distribution = self.secret_distribution._convert_for_lwe_estimator() 
        logger.debug(str(secret_distribution))           
        alpha = self.error_distribution.get_alpha()
        # TODO: if secret is normal, but doesn't follow noise distribution, not supported by estimator => convert to uniform?
        if secret_distribution == "normal" and self.secret_distribution.get_alpha() != alpha:
            ValueError("If secret distribution is Gaussian it must follow the error distribution. Different Gaussians not supported by lwe-estimator.") # TODO: perhaps change

        cost_models = attack_configuration.reduction_cost_models()
        dual_use_lll = attack_configuration.dual_use_lll 
        
        cname = ""
        attack_name = ""
        is_secure = True  
        dropped = False
        best_cost = {"rop": oo}

        # TODO: parallel execution? perhaps split not by cost models but algorithms
        # TODO: run in parallel? same in Problem.SIS.estimate_cost()
        #   test first.. one might be quite slow => waiting takes too long. Find a way of stopping the one that runs longer?
        #   TODO: lazy parameter => if true extra object for running when compare operator is applied... only run when needed, otherwise no early termination... 
        # TODO: sec parameter to gaussian bound trafo... 
        # TODO: add logging and statistics for runtime?
        for reduction_cost_model in cost_models:
            cost_model = reduction_cost_model["reduction_cost_model"]
            success_probability = reduction_cost_model["success_probability"]
            logger.info("Cost model: " + reduction_cost_model["name"])
            # TODO: refractor
            # Estimate attacks. Similar to estimate_lwe function in estimator.py
            algorithms = OrderedDict()
            
            if "mitm" not in attack_configuration.skip:
                algorithms["mitm"] = est.mitm
                
            if "usvp" not in attack_configuration.skip:
                if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                    # Try guessing secret entries via drop_and_solve
                    algorithms["primal-usvp-drop"] = est.partial(est.drop_and_solve, est.primal_usvp, postprocess=False, 
                                                            decision=False, rotations=False, 
                                                            reduction_cost_model=cost_model)
                else: # TODO: can drop and solve yield worse results than standard decode?
                    algorithms["primal-usvp"] = est.partial(est.primal_usvp, 
                                                            reduction_cost_model=cost_model)            
            
            if "decode" not in attack_configuration.skip:
                if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                    algorithms["primal-decode-drop"] = est.partial(est.drop_and_solve, est.primal_decode, 
                                                                    postprocess=False, decision=False, 
                                                                    rotations=False, 
                                                                    reduction_cost_model=cost_model)
                else: # TODO: can drop and solve yield worse results than standard decode?
                    algorithms["primal-decode"] = est.partial(est.primal_decode,   
                                                                reduction_cost_model=cost_model)  
            
            if "dual" not in attack_configuration.skip:
                if est.SDis.is_ternary(secret_distribution): # TODO can drop and solve yield worse results than standard?
                    # Try guessing secret entries via drop_and_solve
                    algorithms["dual-scale-drop"] = est.partial(est.drop_and_solve, est.dual_scale, postprocess=True,
                                                            rotations=False, use_lll=dual_use_lll, 
                                                            reduction_cost_model=cost_model)

                elif est.SDis.is_small(secret_distribution):
                    algorithms["dual-scale"] = est.partial(est.dual_scale, use_lll=dual_use_lll,      
                                                        reduction_cost_model=cost_model)
                else:
                    algorithms["dual"] = est.partial(est.dual, reduction_cost_model=cost_model)

            if "coded-bkw" not in attack_configuration.skip:
                algorithms["dual"] = est.bkw_coded

            if "arora-gb" not in attack_configuration.skip:
                if est.SDis.is_sparse(secret_distribution) and est.SDis.is_small(secret_distribution):
                    algorithms["arora-gb-drop"] = partial(est.drop_and_solve, est.arora_gb,         
                                                            reduction_cost_model=cost_model, 
                                                            rotations=False)
                elif est.SDis.is_small(secret_distribution):
                    algorithms["arora-gb-switch-modulus"] = partial(est.switch_modulus, est.arora_gb,
                                                                    reduction_cost_model=cost_model)
                else:
                        algorithms["arora-gb"] = partial(est.arora_gb, reduction_cost_model=cost_model)

            for alg in algorithms:
                algf = algorithms[alg]
                try:
                    start = time.time()
                    cost = algf(n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                secret_distribution=secret_distribution, 
                                success_probability=success_probability)
                    duration = time.time() - start
                    logger.info(f'Algorithm "{alg}" (took {duration:.3f} s): result={cost}')
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = reduction_cost_model["name"]; attack_name = alg
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break
                except Exception:
                    logger.debug(traceback.format_exc())

        if best_cost["rop"] == oo:
            # no estimate successful
            result = OrderedDict([("error", "All estimates failed")])
            is_secure = False

        else:
            result = OrderedDict([
                ("attack", attack_name), 
                ("cost_model", cname), 
                ("dim", int(best_cost["d"])), 
                ("beta", int(best_cost["beta"])), 
                ("rop", int(round(log(best_cost["rop"], 2)))), 
                ("inst", self)
            ])
            
                    
        return Estimate_Res(is_secure, result)
        
    def __lt__(self, sec) -> Estimate_Res:
        attack_configuration = Attack_Configuration() # use default config
        return self.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __str__(self):
        # TODO
        return "LWE instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m) + \
            ", secret_distribution=" + str(self.secret_distribution)  + ", error_distribution=" + str(self.error_distribution) + ")"


class MLWE(Base_Problem):

    def __init__(self, n, d, q, m, secret_distribution, error_distribution):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        """
        # check soundness of parameters
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def estimate_cost(self, attack_configuration, sec=None, use_reduction=False) -> Estimate_Res:
        r""" 
        Estimates cost of MLWE instance.

        If use_reduction is `False`, the cost is estimated for an LWE instance with dimension :math:`n=n \cdot d`. Else, the MLWE instance will be reduced to RLWE according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 1, note: :cite:`KNK20b` contains error in exponent of q):

        If we take :math:`k = d`, then there exists an efficient reduction from :math:`\textit{M-SLWE}_{m,q, \Psi \leq \alpha}^{R^d}\left(\chi^d\right)` to :math:`\textit{R-SLWE}_{m,q^d, \Psi \leq \alpha\cdot n^2\cdot\sqrt{d}}^{R}\left(U(R_q^\vee)\right)` with controlled error rate :math:`\alpha`.

        Note that the reduction only works for Search-MLWE TODO: find reduction for decision-MLWE?

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param use_reduction: specify if reduction to RLWE is used

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        # TODO: check if correct
        use_reduction = False
        if use_reduction:
            alpha_MLWE = self.error_distribution.get_alpha()
            alpha_RLWE = RR(alpha_MLWE * self.n**2 * sqrt(self.d))
            q_RLWE = self.q**self.d
            secret_distribution_RLWE = distributions.Uniform(0, self.q) # TODO: is this correct?
            error_distribution_RLWE = distributions.Gaussian_alpha(alpha_RLWE, q_RLWE) # TODO: componentwise or L2?
            # TODO how to do RLWE?
            rlwe = RLWE(n=self.n, q=q_RLWE, m=self.m, secret_distribution=secret_distribution_RLWE, 
                                error_distribution=error_distribution_RLWE)

            return rlwe.estimate_cost(sec=sec, attack_configuration=attack_configuration,       
                                        use_reduction=use_reduction)
            
        else:
            lwe = LWE(n=self.n*self.d, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                        error_distribution=self.error_distribution)
            return lwe.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __lt__(self, sec) -> Estimate_Res:
        attack_configuration = Attack_Configuration() # default config
        return self.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __str__(self):
        # TODO
        return "MLWE instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution)  \
            + ", error_distribution=" + str(self.error_distribution) + ")"


class RLWE(Base_Problem):

    def __init__(self, n, q, m, secret_distribution, error_distribution):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")

        ## interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6] TODO: check 
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def estimate_cost(self, attack_configuration, sec=None, use_reduction=False) -> Estimate_Res:
        """ 
        Estimates cost of MLWE instance by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6. 

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param use_reduction: specify if reduction to RLWE is used

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        lwe = LWE(n=self.n, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                    error_distribution=self.error_distribution)
        return lwe.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __lt__(self, sec) -> Estimate_Res:
        attack_configuration = Attack_Configuration() # default config
        return self.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __str__(self):
        # TODO
        return "RLWE instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution)  \
            + ", error_distribution=" + str(self.error_distribution) + ")"


class Statistical_Gaussian_MLWE():
    r"""
    Statistically secure MLWE over Gaussian distribution according to :cite:`LPR13`.
    
    Mapping of parameters in paper to use here:
    
    ============================= =========== ========================================
    Parameters in :cite:`LPR13`   Use Here    Represents
    ============================= =========== ========================================
    :math:`q`                     :math:`q`   modulus
    :math:`l`                     :math:`m+d` width of matrix :math:`\mathbf{A}`
    :math:`k`                     :math:`m`   height of matrix :math:`\mathbf{A}`
    :math:`n`                     :math:`n`   degree of polynomial
    ============================= =========== ========================================

    Then Corollary 7.5 combined with Theorem 7.4 in :cite:`LPR13` reads as follows:
    Let :math:`\mathcal{R}` be the ring of integers in the :math:`m'`th cyclotomic number field :math:`K` of degree :math:`n`, and :math:`q \geq 2` an integer. 
    For positive integers :math:`m \leq m + d \leq \text{poly}(n)`, let :math:`\mathbf{A} = [ \mathbf{I}_{[m]} \mid \bar{\mathbf{A}}] \in (\mathcal{R}_q)^{[m] \times [m+d]}`, where :math:`\mathbf{I}_{[m]} \in (\mathcal{R}_q)^{[m] \times [m]}` is the identity matrix and :math:`\bar{\mathbf{A}} \in (\mathcal{R}_q)^{[m] \times [d]}` is uniformly random. 
    Then with probability :math:`1 - 2^{-\Omega(n)}` over the choice of :math:`\bar{\mathbf{A}}`, the distribution of :math:`\mathbf{A}\mathbf{x} \in (\mathcal{R}_q)^{[m]}` where each coordinate of :math:`\mathbf{x} \in (\mathcal{R}_q)^{[m+d]}` is chosen from a discrete Gaussian distribution of paramete :math:`r > 2n \cdot q^{m / (m+d) + 2/(n (m+d))}` over :math:`\mathcal{R}`, satisfies that the probability of each of the :math:`q^{n m}` possible outcomes is in the interval :math:`(1 \pm 2^{-\Omega(n)}) q^{-n }` (and in particular is within statistical distance :math:`2^{-\Omega(n)}` of the uniform distribution over :math:`(\mathcal{R}_q)^{[m]}`). 
    
    :ivar min_sigma: minimum :math:`\sigma` (standard deviation) required for statistically secure MLWE
    :ivar sec: set to parameter sec if sec is specified in constructor, else set to n
    """

    def __init__(self, n, d, q, m, sec=None):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        # TODO check parameters
        if sec and sec > n:
            raise ValueError("sec parameter must be greater than degree of polynomial n. Given parameters are not statistically secure.")

        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.sec = sec
        min_s = RR(2 * n * q**(m / (m + d) + 2 / (n * (m + d))))
        self.min_sigma = est.stddevf(min_s)
        
        if self.sec:
            self.sec = sec # we choose sec, not n as we possibly need it for Gaussian to bound conversion
        else:
            self.sec = n
        
    def get_secret_distribution_min_width(self):
        # TODO: auch bei Statistical_MSIS
        return Gaussian_sigma(self.min_sigma, q=self.q, componentwise=True, sec=self.sec) 


class Statistical_Gaussian_RLWE(Statistical_Gaussian_MLWE):
    r"""
    Statistically secure RLWE over Gaussian distribution with invertible elements :cite:`LPR13`. 
    
    For details, see :class:`Statistical_Gaussian_MLWE` with module dimension :math:`d=1`.

    :ivar min_sigma: minimum :math:`\sigma` (standard deviation) required for statistically secure MLWE
    :ivar sec: set to parameter sec if sec is specified in constructor, else set to n
    """
    def __init__(self, n, q, m, sec=None):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, d=1, q=q, m=m, sec=sec)


class Statistical_Uniform_MLWE():
    r"""
    Statistically secure MLWE over Uniform distribution with invertible elements :cite:`BDLOP18`. Attributes 

    MLWE problem instance where samples :math:`(\mathbf{A}', h_{\mathbf{A}'}(y))` are within statistical distance :math:`2^{-sec}` of :math:`(\mathbf{A}', \mathbf{u})` for uniform :math:`\mathbf{u}`.

    Mapping of parameters in paper to use here:

    ============================= =========== ============================================================
    Parameters in :cite:`BDLOP18` Use Here    Represents
    ============================= =========== ============================================================
    :math:`q`                     :math:`q`   modulus
    :math:`k`                     :math:`m+d` width of matrix :math:`[ \mathbf{I}_n \; \mathbf{A}' ]` 
    :math:`n`                     :math:`m`   height of matrix :math:`[ \mathbf{I}_n \; \mathbf{A}' ]` 
    :math:`d`                     :math:`d_2` variable
    :math:`N`                     :math:`n`   degree of polynomial
    ============================= =========== ============================================================

    Lemma (:cite:`BDLOP18` Lemma 4): Let :math:`1 < d_2 < n` be a power of 2. If :math:`q` is a prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)` and 

    .. math::

        q^{m/(m+d)} \cdot 2^{2 sec/((m+d)\cdot n)} \leq 2 \beta < \frac{1}{\sqrt{d_2}} \cdot q^{1/d_2}

    then any (all-powerful) algorithm :math:`\mathcal{A}` has advantage at most :math:`2^{-sec}` in solving :math:`\text{DKS}_{m,m+d,\beta}^\infty`, where :math:`\text{DKS}^\infty` is the decisional knapsack problem in :math:`L_\infty`-norm. 

    Hence, we have: 

    .. math::

        \beta_{min} = \frac{q^{m/(m+d)} \cdot 2^{2 sec/((m+d)\cdot n)}}{2}

        \beta_{max} = \frac{1}{2\sqrt{d_2}} \cdot q^{1/d_2} - 1

    TODO: explain ho to arrive at 2*sec instead of 256 

    :ivar min_beta: :math:`\beta_{min}`
    :ivar max_beta: :math:`\beta_{max}`
    """
    def __init__(self, sec, n, d, q, m, d_2=None):
        r"""
        :param sec: required bit security of MLWE instance
        :param n: degree of polynomial
        :param d: rank of module (width of matrix :math:`\mathbf{A}'` in :cite:`BDLOP18`)
        :param q: modulus, must be prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)`
        :param m: number of samples (height of matrix :math:`\mathbf{A}'` in :cite:`BDLOP18`)
        :param d_2: :math:`1 < d_2 < N` and :math:`d_2` is a power of 2
        """
        if d_2 is None:
            d_2 = self.find_d(q, n)

        # TODO: check prerequisites?
        self.n = n
        self.q = q
        self.m = m
        self.d = d
        self.d_2 = d_2

        min_beta = RR(q**(m / (m + d)) * 2**(2 * sec / ((m + d) * n)) / 2)
        max_beta = RR(1 / (2 * sqrt(d_2)) * q**(1 / d_2)) - 1
        self.min_beta = norm.Lp(min_beta, oo, n * d)
        self.max_beta = norm.Lp(max_beta, oo, n * d)

    def get_beta_bounds(self):
        """
        :returns: tuple (min_beta, max_beta), betas are instances of :class:`norm.Lp`
        """
        return (self.min_beta, self.max_beta)

    def find_d(q, n):
        r"""
        Find :math:`d` that is a power of 2 and satisfies :math:`1 < d < n`  such that the prime :math:`q` is congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)`  
        
        :param q: prime
        :param n: upper bound of d (degree of polynomial)
        """
        d = 2
        while d < n:
            if q % (4 * d) == 2 * d + 1:
                return d
            else:
                d *= 2
        raise ValueError("Could not find d such that 1 < d < n power of 2 and q congruent to 2d + 1 (mod 4d). q=" + str(q) + ", n=" + str(n))    


class Statistical_Uniform_RLWE(Statistical_Uniform_MLWE):
    r"""
    Statistically secure RLWE over Uniform distribution with invertible elements :cite:`BDLOP18`. 
    
    For details, see :class:`Statistical_Uniform_MLWE` with module dimension :math:`d=1`.

    :ivar min_beta: :math:`\beta_{min}`
    :ivar max_beta: :math:`\beta_{max}`
    """
    def __init__(self, sec, n, q, m, d_2=None):
        r"""
        :param sec: required bit security of MLWE instance
        :param n: degree of polynomial
        :param q: modulus, must be prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)`
        :param m: number of samples (height of matrix :math:`\mathbf{A}'` in :cite:`BDLOP18`)
        :param d_2: :math:`1 < d_2 < N` and :math:`d_2` is a power of 2
        """
        super().__init__(sec=sec, n=n, d=1, q=q, m=m, d_2=d_2)


## SIS and its variants ##
class SIS(Base_Problem):
        
    def __init__(self, n, q, m, bound):
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param bound: upper bound on norm of secret distribution, must be instance of subclass of :class:`Norm.Base_Norm`. TODO
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        self.q = q
        self.n = n
        self.m = m
        self.bound = bound
    
    def estimate_cost(self, attack_configuration, sec=None) -> Estimate_Res:
        """
        Estimates the cost of an attack on the SIS instance, lazy evaluation if `sec` is set.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")

        cost_models = attack_configuration.reduction_cost_models() # TODO

        attack_name = ""
        is_secure = True  
        best_cost = {"rop": oo}

        # TODO: refractor (see LWE) once more attacks have been added
        # TODO: run parallel?
        for reduction_cost_model in cost_models:
            cost_model = reduction_cost_model["reduction_cost_model"]
            logger.info("Cost model: " + reduction_cost_model["name"])

            if "lattice-reduction" not in attack_configuration.skip:
                try:    
                    start = time.time()
                    cost = attacks.SIS.lattice_reduction(n=self.n, q=self.q, m=self.m, bound=self.bound, 
                                                            reduction_cost_model=cost_model)
                    duration = time.time() - start
                    logger.info(f'Algorithm "lattice-reduction" (took {duration:.3f} s): result={cost}')
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = reduction_cost_model["name"]; attack_name = "lattice-reduction"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break
                except Exception:
                    logger.debug(traceback.format_exc())

        if "combinatorial" not in attack_configuration.skip:
            try:
                start = time.time()
                cost = attacks.SIS.combinatorial(n=self.n, q=self.q, m=self.m, bound=self.bound)
                duration = time.time() - start
                logger.info(f'Algorithm "combinatorial" (took {duration:.3f} s): result={cost}')
                if cost["rop"] < best_cost["rop"]:
                    best_cost = cost; attack_name = "combinatorial"
                    if sec and round(log(cost["rop"], 2)) < sec:
                        is_secure = False
            except Exception:
                logger.debug(traceback.format_exc())
        
        # TODO: result as OrderedDict?
        if "error" in best_cost: 
            # TODO: does combinatorial
            # TODO: error handling, intractable "delta_0 < 1" or "trivial"
            result = OrderedDict([
                ("attack", attack_name), 
                ("error", best_cost["error"]),
                ("inst", self)
            ])

        elif best_cost["rop"] == oo: # all estimates failed
            result = OrderedDict(["error", "All estimates failed"])
        
        else:
            if attack_name == "lattice-reduction":
                result = OrderedDict([
                    ("attack", attack_name), 
                    ("cost_model", cname), 
                    ("dim", int(best_cost["dim"])), 
                    ("beta", int(best_cost["beta"])), 
                    ("rop", int(round(log(best_cost["rop"], 2)))), 
                    ("inst", self)
                ])
            else:
                result = OrderedDict([
                    ("attack", attack_name), 
                    ("column_groups", "2^" + str(best_cost["k"])),
                    ("rop", int(round(log(best_cost["rop"], 2)))), 
                    ("inst", self)
                ])

        return Estimate_Res(is_secure, result)

    def __lt__(self, sec) -> Estimate_Res:
        attack_configuration = Attack_Configuration()
        return self.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __str__(self):
        return "SIS instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m) + ", bound=" + str(self.bound)  + ")"


class MSIS(Base_Problem):

    def __init__(self, n, d, q, m, bound):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :class:`Norm.Base_Norm`
        """
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.bound = bound
    
    def estimate_cost(self, attack_configuration, sec=None, use_reduction=False) -> Estimate_Res:
        r""" 
        Estimates cost of MSIS instance.

        If use_reduction is `False`, the cost is estimated for an SIS instance with dimension :math:`n=n \cdot d`. Else, the MSIS instance will be reduced to RSIS according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 2):

        Let :math:`k = 2` and :math:`q` be a prime. Let a positive real number :math:`\beta` be an upper bound on the :math:`L_2`-norm of the solution of :math:`\text{R-SIS}_{q,m,\beta}` and :math:`d \in \mathbb{N}` be a module rank such that

        .. math:: \sqrt{n m} \cdot q^{1/m} \leq \beta < \sqrt[2d-1]{q / (\sqrt{m}^{d-1})}.
        
        Then there exists a reduction from :math:`\text{M-SIS}_{q^k,m^k,\beta'}` to :math:`\text{R-SIS}_{q,m,\beta}` with :math:`\beta' = m^{k(d-1)/2} \cdot \beta^{k(2d-1)}`.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param use_reduction: specify if reduction to RSIS is used

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        # TODO
        if use_reduction:
            # transform to L2-norm
            self.beta = self.bound.to_L2(self.n * self.d).value # TODO: check dimension

            # TODO: check preconditions
            k = 2
            lower = RR(sqrt(self.n * self.m) * self.q**(1 / self.m))
            upper = RR((self.q / sqrt(self.m)**(self.d-1))**(1 / (2 * self.d - 1)))
            if lower <= self.beta and self.beta < upper:
                q_RSIS = RR(round(self.q**(1/k)))
                m_RSIS = RR(round(self.m**(1/k)))
                beta_RSIS = RR((self.beta / (self.m**((self.d - 1) / 2)))**(1 / (k * (2 * self.d - 1))))
                bound = norm.Lp(beta_RSIS, self.n, 2) # new dimension of input vector (instead of n * d in M-SIS)

            rsis = RSIS(n=self.n, q=q_RSIS, bound=bound, m=m_RSIS)
            return rsis.estimate_cost(sec=sec, attack_configuration=attack_configuration,     
                                        use_reduction=use_reduction) # TODO: use_reduction makes sense?

        else:
            sis = SIS(n=self.n*self.d, q=self.q, m=self.m, bound=self.bound)
            return sis.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __lt__(self, sec):
        attack_configuration = Attack_Configuration()
        return self.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __str__(self):
        return "MSIS instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) + ", m=" + str(self.m) + ", bound=" + str(self.bound)  + ")"


class RSIS(Base_Problem):

    def __init__(self, n, q, m, bound):
        """
        :param q: modulus
        :param n: degree of polynomial
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :class:`Norm.Base_Norm`
        """
        ## We interpret the coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        self.n = n
        self.q = q
        self.m = m
        self.bound = bound

    def estimate_cost(self, attack_configuration, sec=None) -> Estimate_Res:
        r""" 
        Estimates cost of RSIS instance by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6. 

        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        sis = SIS(n=self.n, q=self.q, m=self.m, bound=self.bound)
        return sis.estimate_cost(sec=sec, attack_configuration=attack_configuration)
    
    def __lt__(self, sec) -> Estimate_Res:
        attack_configuration = Attack_Configuration()
        return self.estimate_cost(sec=sec, attack_configuration=attack_configuration)

    def __str__(self):
        # TODO
        return "RSIS instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m.n()) + ", bound=" + str(self.bound.value)  + ")"


class Statistical_MSIS():
    r"""
    Statistically secure MSIS according to :cite:`DOTT21`, section 4.1.

    MLWE problem instance where the probability that non zero elements :math:`\mathbf{r}` in the Euclidean ball :math:`B_{m}(0, 2B)` satisfy :math:`\hat{\mathbf{A}}_1 \cdot \mathbf{r} = \mathbf{0}` is smaller than :math:`2^{-sec}`.

    Mapping of parameters in :cite:`DOTT21` to use here:
    
    ============================ ============= ============================================
    Parameters in :cite:`DOTT21` Use Here      Represents
    ============================ ============= ============================================
    :math:`m'`                   :math:`m+d`   width of matrix :math:`\hat{\mathbf{A}}_1`
    :math:`m`                    :math:`m`     height of matrix :math:`\hat{\mathbf{A}}_1`
    :math:`B`                    :math:`B`     norm-bound of secret
    :math:`s`                    :math:`s`     Gaussian width (not stddev)
    :math:`N`                    :math:`n`     degree of polynomial
    ============================ ============= ============================================

    The number of elements in :math:`B_{m+d}(0, 2B)` can be estimated from above as :math:`|B_{m+d}(0, 2B)| \ll (2 \pi e /((m+d) n))^{(m+d) n/2} \cdot (2 B)^{(m+d) n}`. The scheme is statistically binding if the probability that non zero elements in :math:`B_{m+d}(0, 2B)` of radius :math:`2B` in :math:`\mathcal{R}_q^{m+d}` map to :math:`\mathbf{0}` in :math:`\mathcal{R}_q^{m}` is negligible. Hence, it must hold that :math:`|B_{m+d}(0, 2B)|/q^{m n} \leq 2^{-sec}` and we get:
    
    TODO: look for bound of ball without o(...)
        
    .. math::
        \left(\sqrt{\frac{2 \pi e}{(m+d) \cdot n}} \cdot 2 B\right)^{(m+d) \cdot n} &\leq 2^{-sec} \cdot q^{m\cdot n} \\
        B &\leq 2^{\frac{-sec}{(m+d)\cdot n} - 1} \cdot q^\frac{m}{m+d} \cdot \sqrt{\frac{(m+d)\cdot n}{2 \pi e}}\\
    
    We convert the bound :math:`B` to a Gaussian over :math:`L_2`-norm by following the procedure described in :ref:`to_Lp <to_Lp>`:

    .. math::
        s  \approx x \sqrt{\frac{\pi}{(sec + 1) \ln(2)}}

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """

    def __init__(self, sec, n, d, q, m):
        """
        :param sec: required bit security of MSIS instance
        :param n: degree of polynomial
        :param d: rank of module (or height of matrix)
        :param q: modulus
        :param m: number of samples (or width of matrix)
        """
        # TODO: check paramters
        max_beta = RR(2**(-sec / ((m + d) * n)  - 1) * q**(m / (m + d)) * sqrt((m + d) * n / (2 * pi * e)))
        # convert beta bound to Gaussian width parameter
        self.max_s = max_beta * sqrt(pi / ((sec + 1) * log(2.0)))
        
        self.max_sigma =  est.stddevf(self.max_s)
        self.max_beta = norm.Lp(max_beta, 2, n * d) # TODO: is the dimension correct?
        self.sec = sec
        self.n = n
        self.d = d
        self.q = q
        self.m = m
    
    def get_secret_distribution_max_width(self):
        return Gaussian_sigma(sigma=self.max_sigma, q=self.q, componentwise=False, sec=self.sec) # TODO check, specify dimensions? or not needed?


class Statistical_RSIS(Statistical_MSIS):
    r"""
    Statistically secure RSIS according to :cite:`DOTT21`, section 4.1.
    
    For details, see :class:`Statistical_MSIS` with module dimension :math:`d=1`.

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """
    def __init__(self, sec, n, q, m):
        """
        :param sec: required bit security of MSIS instance
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples (or width of matrix)
        """
        super().__init__(sec=sec, n=n, d=1, q=q, m=m) # TODO: check Gaussian

class Statistical_SIS(Statistical_MSIS):
    r"""
    Statistically secure RSIS according to :cite:`DOTT21`, section 4.1.
    
    For details, see :class:`Statistical_MSIS` with degree of polynomial dimension :math:`n=1`, height of matrix becomes rank of modulus (i.e. :math:`d=n`).

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """
    def __init__(self, sec, n, q, m):
        """
        :param sec: required bit security of MSIS instance
        :param n: secret dimension
        :param q: modulus
        :param m: number of samples (or width of matrix)
        """
        super().__init__(sec=sec, n=1, d=n, q=q, m=m)