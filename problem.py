r""" 
TODO: documentation
"""

from abc import ABC, abstractmethod

from attacks import Attack_Configuration
from distributions import Distribution


try: # sage-related imports do not work with sphinx for documentation
    import distributions
    import attacks
    import norm
    import sys
    import os
    from functools import partial
    from sage.functions.log import exp, log
    from sage.functions.other import ceil, sqrt, floor, binomial
    from sage.rings.all import QQ, RR
    from sage.symbolic.all import pi, e
    sys.path.append(os.path.dirname(__file__) + "/estimate_all")
    from estimator import estimator as est
    oo = est.PlusInfinity()
except:
    pass

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
    def estimate_cost(self, sec=None, attack_configuration=None, debug=False):
        pass

    @abstractmethod
    def __lt__(self, sec):
        pass

    @abstractmethod
    def __str__(self):
        pass


## LWE and its variants ##
class LWE(Base_Problem):
    # TODO: docstring (also other variants)

    def __init__(self, n, q, m, secret_distribution : Distribution, error_distribution : Distribution, attack_configuration : Attack_Configuration, debug=False): 
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: foward exceptions if set to `True`
        """
        # check soundness of parameters
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution
        self.attack_configuration = attack_configuration
        self.debug = debug

    def estimate_cost(self, sec=None, attack_configuration=None, debug=False):
        """
        Estimates the cost of an attack on the LWE instance, lazy evaluation if `sec` is set.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param debug: if `True`, an exception is passed, else result field of return value contains entry `"error"` with exception message

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        if not attack_configuration:
            attack_configuration = self.attack_configuration          
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        
        # TODO: if secret distro is gaussian check that secret distro follow error distro!
        secret_distribution = self.secret_distribution._convert_for_lwe_estimator()            
        alpha = self.error_distribution.get_alpha()
        # TODO: if secret is normal, but doesn't follow noise distribution, not supported by estimator => convert to uniform?
        if secret_distribution == "normal" and self.secret_distribution.get_alpha() != alpha:
            ValueError("If secret distribution is Gaussian it must follow the error distribution. Different Gaussians not supported by lwe-estimator.") # TODO: perhaps change

        cost_models = attacks.reduction_cost_models()
        dual_use_lll = attack_configuration.dual_use_lll 
        
        cname = ""
        attack_name = ""
        is_secure = True  
        dropped = False
        best_cost = {"rop": oo}

        # TODO: parallel execution?
        # TODO: run in parallel? same in Problem.SIS.estimate_cost()
        #   test first.. one might be quite slow => waiting takes too long. Find a way of stopping the one that runs longer?
        #   TODO: lazy parameter => if true extra object for running when compare operator is applied... only run when needed, otherwise no early termination... 
        # TODO: sec parameter to gaussian bound trafo... 
        # TODO: add logging and statistics for runtime?
        try:
            for cost_model in cost_models:
                cname = cost_model["name"]
                reduction_cost_model = cost_model["reduction_cost_model"]
                success_probability = cost_model["success_probability"]

                # Estimate attacks. Similar to estimate_lwe function in estimator.py
                if "mitm" not in attack_configuration.skip:
                    cost = est.mitm(self.n, alpha, self.q, secret_distribution, self.m, success_probability)
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = cost_model["name"]; dropped = False; attack_name = "mitm"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break

                if "usvp" not in attack_configuration.skip:
                    if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                        cost = est.primal_usvp(self.n, alpha, self.q, secret_distribution=secret_distribution,
                                                    m=self.m,  success_probability=success_probability,
                                                    reduction_cost_model=reduction_cost_model)
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = cost_model["name"]; dropped = False; attack_name = "usvp"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break

                    if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                        # Try guessing secret entries via drop_and_solve
                        primald = est.partial(est.drop_and_solve, est.primal_usvp, postprocess=False, decision=False)
                        cost = primald(self.n, alpha, self.q, secret_distribution=secret_distribution,
                                                m=self.m,  success_probability=success_probability,
                                                reduction_cost_model=reduction_cost_model, rotations=False)
                        if cost["rop"] < best_cost["rop"]:
                            best_cost = cost; cname = cost_model["name"]; dropped = True; attack_name = "usvp"
                            if sec and round(log(cost["rop"], 2)) < sec:
                                is_secure = False; break
                
                if "decode" not in attack_configuration.skip:
                    cost = est.primal_decode(self.n, alpha, self.n, alpha, self.q, m=self.m,
                                                    success_probability=success_probability,
                                                    secret_distribution=secret_distribution,
                                                    reduction_cost_model=reduction_cost_model)
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = cost_model["name"]; dropped = False; attack_name = "decode"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break

                    if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                        # Try guessing secret entries via drop_and_solve
                        primaldecd = est.partial(est.drop_and_solve, est.primal_decode, postprocess=False, decision=False)
                        cost = primaldecd(self.n, alpha, self.q, m=self.m,  
                                            secret_distribution=secret_distribution, 
                                            success_probability=success_probability,
                                            reduction_cost_model=reduction_cost_model, rotations=False)
                        if cost["rop"] < best_cost["rop"]:
                            best_cost = cost; cname = cost_model["name"]; dropped = True; attack_name = "decode"
                            if sec and round(log(cost["rop"], 2)) < sec:
                                is_secure = False; break
                
                if "dual" not in attack_configuration.skip:
                    if est.SDis.is_small(secret_distribution):
                        cost = est.dual_scale(self.n, alpha, self.n, alpha, self.q, m=self.m, 
                                                    success_probability=success_probability,
                                                    secret_distribution=secret_distribution,
                                                    reduction_cost_model=reduction_cost_model, use_lll=dual_use_lll)
                    else:
                        cost = est.dual(self.n, alpha, self.n, alpha, self.q, m=self.m,
                                                success_probability=success_probability,
                                                secret_distribution=secret_distribution,
                                                reduction_cost_model=reduction_cost_model)
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = cost_model["name"]; dropped = False; attack_name = "dual"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break

                    if est.SDis.is_ternary(secret_distribution):
                        # Try guessing secret entries via drop_and_solve
                        duald = est.partial(est.drop_and_solve, est.dual_scale, postprocess=True)
                        cost = duald(self.n, alpha, self.q, secret_distribution=secret_distribution,
                                        m=self.m,  success_probability=success_probability,
                                        reduction_cost_model=reduction_cost_model, rotations=False, use_lll=dual_use_lll)
                        if cost["rop"] < best_cost["rop"]:
                            best_cost = cost; cname = cost_model["name"]; dropped = True; attack_name = "dual"
                            if sec and round(log(cost["rop"], 2)) < sec:
                                is_secure = False; break

                if "coded-bkw" not in attack_configuration.skip:
                    cost = est.bkw_coded(self.n, alpha, self.q, secret_distribution, self.m, success_probability)
                    if cost < best_cost:
                        best_cost = cost; cname = cost_model["name"]; dropped = False; attack_name = "coded-bkw"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break

                if "arora_gb" not in attack_configuration.skip:
                    if est.SDis.is_small(secret_distribution):
                        aroras = partial(est.switch_modulus, est.arora_gb)
                        cost = aroras(self.n, alpha, self.q, secret_distribution=secret_distribution,
                                            m=self.m,  success_probability=success_probability,
                                            reduction_cost_model=reduction_cost_model)
                    else:
                        cost = est.arora_gb(self.n, alpha, self.q, secret_distribution=secret_distribution,
                                        m=self.m,  success_probability=success_probability,
                                        reduction_cost_model=reduction_cost_model)
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = cost_model["name"]; dropped = False; attack_name = "arora-gb"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break

                    if est.SDis.is_sparse(secret_distribution) and est.SDis.is_small(secret_distribution):
                        arorad = partial(est.drop_and_solve, est.arora_gb)
                        cost = arorad(self.n, alpha, self.q, secret_distribution=secret_distribution,
                                            m=self.m,  success_probability=success_probability,
                                            reduction_cost_model=reduction_cost_model, rotations=False)
                        if cost["rop"] < best_cost["rop"]:
                            best_cost = cost; cname = cost_model["name"]; dropped = True; attack_name = "arora-gb"
                            if sec and round(log(cost["rop"], 2)) < sec:
                                is_secure = False; break
            result = {
                "attack": attack_name,
                "cost_model": cname,
                "dim":  int(cost["d"]),
                "beta": int(cost["beta"]),
                "rop":  int(round(log(cost["rop"], 2))),
                "drop": dropped,
                "inst": self,
            }

        except Exception as e:
            result = {}
            result["error"] = str(e) # TODO more info?
            is_secure = False # TODO
            if debug:
                raise
        
        return Estimate_Res(is_secure, result)
        
    def __lt__(self, sec):
        attack_configuration = self.attack_configuration
        debug = self.debug
        return self.estimate_cost(sec=sec, attack_configuration=attack_configuration, debug=debug)

    def __str__(self):
        # TODO
        return "LWE instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m) + \
            ", secret_distribution=" + str(self.secret_distribution)  + ", error_distribution=" + str(self.error_distribution) + ")"


class MLWE(Base_Problem):

    def __init__(self, n, d, q, m, secret_distribution, error_distribution, attack_configuration, debug=False):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: foward exceptions if set to `True`
        """
        # check soundness of parameters
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution
        self.attack_configuration = attack_configuration
        self.debug = debug
        
    def estimate_cost(self, sec=None, attack_configuration=None, use_reduction=False, debug=False):
        r""" 
        Estimates cost of MLWE instance.

        If use_reduction is `False`, the cost is estimated for an LWE instance with dimension :math:`n=n \cdot d`. Else, the MLWE instance will be reduced to RLWE according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 1, note: :cite:`KNK20b` contains error in exponent of q):

        If we take :math:`k = d`, then there exists an efficient reduction from :math:`\textit{M-SLWE}_{m,q, \Psi \leq \alpha}^{R^d}\left(\chi^d\right)` to :math:`\textit{R-SLWE}_{m,q^d, \Psi \leq \alpha\cdot n^2\cdot\sqrt{d}}^{R}\left(U(R_q^\vee)\right)` with controlled error rate :math:`\alpha`.

        Note that the reduction only works for Search-MLWE TODO: find reduction for decision-MLWE?

        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param attack_configuration: TODO
        :param use_reduction: specify if reduction to RLWE is used
        :param debug: if `True`, an exception is passed, else result field of return value contains entry `"error"` with exception message

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
                                        use_reduction=use_reduction, debug=debug)
            
        else:
            lwe = LWE(n=self.n*self.d, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                        error_distribution=self.error_distribution, debug=debug)
            return lwe.estimate_cost(sec=sec, attack_configuration=attack_configuration, debug=debug)

    def __lt__(self, sec):
        return self.estimate_cost(sec=sec, attack_configuration=self.attack_configuration, debug=self.debug)

    def __str__(self):
        # TODO
        return "MLWE instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution)  \
            + ", error_distribution=" + str(self.error_distribution) + ")"


class RLWE(Base_Problem):

    def __init__(self, n, q, m, secret_distribution, error_distribution, attack_configuration, debug=False):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: foward exceptions if set to `True`
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")

        ## interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6] TODO: check 
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution
        self.attack_configuration = attack_configuration
        self.debug = debug

    def estimate_cost(self, sec=None, attack_configuration=None, use_reduction=False, debug=False):
        """ 
        Estimates cost of MLWE instance by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6. 

        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param use_reduction: specify if reduction to RLWE is used
        :param debug: if `True`, an exception is passed, else result field of return value contains entry `"error"` with exception message

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        lwe = LWE(n=self.n, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                    error_distribution=self.error_distribution, attack_configuration=attack_configuration, 
                    debug=debug)
        return lwe.estimate_cost(sec=sec, attack_configuration=attack_configuration, debug=debug)

    def __lt__(self, sec):
        return self.estimate_cost(sec=sec, attack_configuration=self.attack_configuration, debug=self.debug)

    def __str__(self):
        # TODO
        return "RLWE instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution)  \
            + ", error_distribution=" + str(self.error_distribution) + ")"


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
        # TODO: is this s here component-wise or for L2?
        # gaussian_width is not standard deviation
        alpha = est.alphaf(s, q)
        
        # TODO: should we require n > 128 or n > 256 to ensure unconditional hardness or check if n > sec?
        # TODO set class attributes
        self.sec = n # TODO: document how to get, for consistency do the same with other satisticals...
        # TODO: min_sigma? depends on r... document attibutes of object (also other statistical...)


class Statistical_Uniform_MLWE():
    r"""
    Statistically secure MLWE over Uniform distribution with invertible elements :cite:`BDLOP18`. Attributes 

    MLWE problem instance where samples :math:`(A', h_A'(y))` are within statistical distance :math:`2^{-sec}` of :math:`(A', u)` for uniform :math:`u`.

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

    Lemma (:cite:`BDLOP18` Lemma 4): Let :math:`1 < d_2 < n` be a power of 2. If :math:`q` is a prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)` and 

    .. math::

        q^{d/m} \cdot 2^{2 sec/(m\cdot n)} \leq 2 \beta < \frac{1}{\sqrt{d_2}} \cdot q^{1/d_2}

    then any (all-powerful) algorithm :math:`\mathcal{A}` has advantage at most :math:`2^{-sec}` in solving :math:`\text{DKS}_{d,m,\beta}^\infty`, where :math:`\text{DKS}^\infty` is the decisional knapsack problem in :math:`L_\infty`-norm. 

    Hence, we have: 

    .. math::

        \beta_{min} = \frac{q^{d/m} \cdot 2^{2 sec/(m\cdot n)}}{2}

        \beta_{max} = \frac{1}{2\sqrt{d_2}} \cdot q^{1/d_2} - 1

    TODO: do I have to adapt the proof (at least the part where the Leftover Hash Lemma is applied) to show how I arrived at 2*sec instead of 256? 

    :ivar min_beta: :math:`\beta_{min}`
    :ivar max_beta: :math:`\beta_{max}`
    """
    def __init__(self, sec, n, d, q, m, d_2=None):
        r"""
        :param sec: required bit security of MLWE instance # TODO
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus, must be prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)`
        :param m: number of samples
        :param d_2: :math:`1 < d_2 < N` and :math:`d_2` is a power of 2
        """
        if not d_2:
            d_2 = self.find_d(q, n)

        # TODO: check prerequisites?
        self.n = n
        self.q = q
        self.m = m
        self.d = d
        self.d_2 = d_2

        min_beta = RR(q**(d / m) * 2**(2 * sec / (m * n)) / 2)
        max_beta = RR(1 / (2 * sqrt(d_2)) * q**(1 / d_2)) - 1
        self.min_beta = norm.Lp(min_beta, oo, n * d)
        self.max_beta = norm.Lp(max_beta, oo, n * d)

    def get_beta_bounds(self):
        """
        :returns: tuple (min_beta, max_beta), betas are instances of :class:`norm.Lp`
        """
        return (self.min_beta, self.max_beta)
    
    def get_sigma_bounds(self):
        """ 
        :returns: tuple (min_sigma, max_sigma), sigmas are standard devation
        """
        min_alpha = distributions.Uniform(a=self.min_beta.value).get_alpha(q=self.q)
        max_alpha = distributions.Uniform(a=self.max_beta.value).get_alpha(q=self.q)
        min_sigma = distributions.alpha_to_stddevf(min_alpha, self.q)
        max_sigma = distributions.alpha_to_stddevf(max_alpha, self.q)
        return (min_sigma, max_sigma)

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


## SIS and its variants ##
class SIS(Base_Problem):
        
    def __init__(self, n, q, m, bound, attack_configuration, debug=False):
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param bound: upper bound on norm of secret distribution, must be instance of subclass of :class:`Norm.Base_Norm`. TODO
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: foward exceptions if set to `True`
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        self.q = q
        self.n = n
        self.m = m
        self.bound = bound
        self.attack_configuration = attack_configuration
        self.debug = debug
    
    def estimate_cost(self, sec=None, attack_configuration=None, debug=False):
        """
        Estimates the cost of an attack on the SIS instance, lazy evaluation if `sec` is set.

        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: if `True`, an exception is passed, else result field of return value contains entry `"error"` with exception message

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        if not attack_configuration:
            attack_configuration = self.attack_configuration          
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")

        cost_models = attacks.reduction_cost_models(attack_configuration) # TODO

        attack_name = ""
        is_secure = True  
        best_cost = {"rop": oo}

        # TODO: run parallel?
        try:
            if "lattice-reduction" not in attack_configuration.skip:
                for cost_model in cost_models:
                    cost = attacks.SIS.lattice_reduction(n=self.n, q=self.q, m=self.m, bound=self.bound, 
                                                            reduction_cost_model=cost_model["reduction_cost_model"])
                    if cost["rop"] < best_cost["rop"]:
                        best_cost = cost; cname = cost_model["name"]; attack_name = "lattice-reduction"
                        if sec and round(log(cost["rop"], 2)) < sec:
                            is_secure = False; break

            if "combinatorial" not in attack_configuration.skip:
                cost = attacks.SIS.combinatorial(n=self.n, q=self.q, m=self.m, bound=self.bound)
                if cost["rop"] < best_cost["rop"]:
                    best_cost = cost; cname = cost_model["name"]; attack_name = "lattice-reduction"
                    if sec and round(log(cost["rop"], 2)) < sec:
                        is_secure = False
            
            # TODO: result as OrderedDict?
            if "error" in cost.keys():
                # TODO: error handling, intractable "delta_0 < 1" or "trivial"
                result = {
                    "attack": attack_name,
                    "cost_model": cname,
                    "rop":  int(round(log(cost["rop"], 2))),
                    "error": cost["error"],
                    "inst": self, # TODO return instance instead of string?
                }
            
            else:
                if attack_name == "lattice-reduction":
                    result = {
                        "attack": attack_name,
                        "cost_model": cname,
                        "dim":  int(cost["d"]),
                        "beta": int(cost["beta"]),
                        "rop":  int(round(log(cost["rop"], 2))),
                        "inst": self,
                    }
                else:
                    result = {
                        "attack": attack_name,
                        "column_groups":  "2^" + cost["k"],
                        "rop":  int(round(log(cost["rop"], 2))),
                        "inst": self,
                    }
        
        except Exception as e:
            result = {}
            result["error"] = str(e) # TODO more info?
            is_secure = False # TODO
            if debug:
                raise
        
        return Estimate_Res(is_secure, result)
        # TODO: test!

    def __lt__(self, sec):
        return self.estimate_cost(sec=sec, attack_configuration=self.attack_configuration, debug=self.debug)

    def __str__(self):
        return "SIS instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m) + ", bound=" + str(self.bound)  + ")"


class MSIS(Base_Problem):

    def __init__(self, n, d, q, m, bound, attack_configuration, debug=False):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :class:`Norm.Base_Norm`
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: foward exceptions if set to `True`
        """
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.bound = bound
        self.attack_configuration = attack_configuration
        self.debug = debug
    
    def estimate_cost(self, sec=None, attack_configuration=None, use_reduction=False, debug=False):
        r""" 
        Estimates cost of MSIS instance.

        If use_reduction is `False`, the cost is estimated for an SIS instance with dimension :math:`n=n \cdot d`. Else, the MSIS instance will be reduced to RSIS according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 2):

        Let :math:`k = 2` and :math:`q` be a prime. Let a positive real number :math:`\beta` be an upper bound on the :math:`L_2`-norm of the solution of :math:`\text{R-SIS}_{q,m,\beta}` and :math:`d \in \mathbb{N}` be a module rank such that

        .. math:: \sqrt{n m} \cdot q^{1/m} \leq \beta < \sqrt[2d-1]{q / (\sqrt{m}^{d-1})}.
        
        Then there exists a reduction from :math:`\text{M-SIS}_{q^k,m^k,\beta'}` to :math:`\text{R-SIS}_{q,m,\beta}` with :math:`\beta' = m^{k(d-1)/2} \cdot \beta^{k(2d-1)}`.

        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param use_reduction: specify if reduction to RSIS is used
        :param debug: foward exceptions if set to `True`

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
                                        use_reduction=use_reduction, debug=debug) # TODO: use_reduction makes sense?

        else:
            sis = SIS(n=self.n*self.d, q=self.q, m=self.m, bound=self.bound, 
                        attack_configuration=attack_configuration, debug=debug)
            return sis.estimate_cost(sec=sec, attack_configuration=attack_configuration, debug=debug)

    def __lt__(self, sec):
        return self.estimate_cost(sec=sec, attack_configuration=self.attack_configuration, debug=self.debug)

    def __str__(self):
        return "MSIS instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) + ", m=" + str(self.m) + ", bound=" + str(self.bound)  + ")"


class Statistical_MSIS():
    r"""
    Statistically secure MSIS :cite:`DOTT21`, section 4.1

    MLWE problem instance where the probability that non zero elements :math:`\mathbf{r}` in the Euclidean ball :math:`B_{m}(0, 2B)` satisfy :math:`\hat{\mathbf{A}}_1 \cdot \mathbf{r} = \mathbf{0}` is smaller than :math:`2^{-sec}`.

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

    We choose bound :math:`B = s \cdot \sqrt{m \cdot n}` to ensure that the retry probability in the committing algorithm is negligible. The number of elements in :math:`B_{m}(0, 2B)` can be estimated from above as :math:`|B_{m}(0, 2B)| \ll (2 \pi e /(m n))^{m n/2} \cdot (2 B)^{m n}`. The scheme is statistically binding if the probability that non zero elements in :math:`B_{m}(0, 2B)` of radius :math:`2B` in :math:`R_q^{m}` map to :math:`\mathbf{0}` in :math:`R_q^{d}` is negligible. Hence, it must hold that :math:`|B_m(0, 2B)|/q^{d n} \leq 2^{-sec}` and we get:
        
    .. math::
        ((2 \pi e/(m n))^{1/2} * (2 B))^{m n} &\leq 2^{-sec} * q^{d n} \\
        B &\leq 2^{-sec / (m n)} \cdot \frac{q^{d / m}}{2} \cdot (m n / (2 \pi e))^{1/2}\\
        s &\leq 2^{-sec / (m n)} \cdot \frac{q^{d / m}}{2} \cdot \frac{(m n / (2 \pi e))^{1/2}}{\sqrt{m n}}

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
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
        # self check paramters
        # TODO: include sec parameter in bound estimate? How?
        max_beta = RR(2**(-sec / (m * n)) * q**(d / m) / 2 * (m * n / (2 * pi * e))**(1 / 2))
        self.max_sigma =  est.stddevf(max_beta / sqrt(m * n)) # TODO: include sec parameter in bound to Gaussian trafo?
        self.max_beta = norm.Lp(max_beta, 2, n * d) # TODO: is the dimension correct?
        self.sec = sec # TODO needed?
        self.n = n
        self.d = d
        self.q = q
        self.m = m


class RSIS(Base_Problem):

    def __init__(self, n, q, m, bound, attack_configuration, debug=False):
        """
        :param q: modulus
        :param n: degree of polynomial
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :class:`Norm.Base_Norm`
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: foward exceptions if set to `True`
        """
        ## We interpret the coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        self.n = n
        self.q = q
        self.m = m
        self.bound = bound
        self.attack_configuration = attack_configuration
        self.debug = debug

    def estimate_cost(self, sec=None, attack_configuration=None, debug=False):
        r""" 
        Estimates cost of RSIS instance by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6. 

        :param sec: optional required bit-security for lazy cost evaluation. If set, early termination once security requirement is violated.
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param debug: foward exceptions if set to `True`

        :returns: instance :class:`Estimate_Res`. If `sec=None`, :attr:`Estimate_Res.is_secure` is `True` by default and can be ignored.
        """
        sis = SIS(n=self.n, q=self.q, m=self.m, bound=self.bound, attack_configuration=attack_configuration, 
                    debug=debug)
        return sis.estimate_cost(sec=sec, attack_configuration=attack_configuration, debug=debug)
    
    def __lt__(self, sec):
        return self.estimate_cost(sec=sec, attack_configuration=self.attack_configuration, debug=self.debug)

    def __str__(self):
        # TODO
        return "RSIS instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m) + ", bound=" + str(self.bound)  + ")"