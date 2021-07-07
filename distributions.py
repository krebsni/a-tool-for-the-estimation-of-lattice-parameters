r""" 
TODO: documentation
"""

try: # sage-related imports do not work with sphinx for documentation
    import norm
    import problem
    import sys
    import os
    from abc import ABC, abstractmethod
    from sage.functions.log import log
    from sage.functions.other import ceil, sqrt
    from sage.rings.all import QQ, RR
    from sage.symbolic.all import pi
    sys.path.append(os.path.dirname(__file__) + "/estimate_all")
    from estimator import estimator as est
    oo = est.PlusInfinity()
except:
    pass



# Error Parameter Conversion (extension to functions in estimator.py)
def alpha_to_stddevf(alpha, q):
    r"""
    noise rate :math:`\alpha`, modulus q → standard deviation :math:`\sigma`

    :param alpha: noise rate
    :param q: modulus `0 < q`

    :returns: :math:`\sigma = \alpha \cdot q / \sqrt{2\pi}` 
    """
    return est.stddevf(RR(alpha * q))    


class Distribution():
    pass

# TODO: if we change q (e.g. in reduction), what values change?
# TODO: perhaps don't include 
class Uniform(norm.Base_Norm, Distribution):

    def __init__(self, a=None, b=None, h=None, uniform_mod_q=False, q=None):
        """
        :param a: lower bound if b is specified, else take range [-a, a]
        :param b: upper bound, optional
        :param h: exactly :math:`h` components are :math:`\in [a,…,b]∖\{0\}`, all other components are zero
        :param uniform_mod_q: uniform mod q, if True no other value must be specified, if True, q must be set
        :param q: only needed for uniform_mod_q
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
        else:
            if not q:
                raise ValueError("q must be set for uniform_mod_q uniform distribution.")
            else:
                self.range = (0, q)

    def get_alpha(self, q, n=None):
        r"""
        Calculates noise rate :math:`\alpha` of approximately equivalent Gaussian distribution.

        TODO: describe how it is calculated?

        :param q: modulus
        :param n: secret dimension, only needed for uniform mod q and sparse secrets
        :returns: noise rate :math:`\alpha`
        """
        # TODO: inverse of Gaussian to bounds? with sec parameter? currently via variance
        variance = est.SDis.variance(self._convert_for_lwe_estimator(), q=q, n=n)
        return est.alphaf(sqrt(variance), q, sigma_is_stddev=True)

    def get_range(self):
        """
        """
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
    
    # TODO: is normal trafo always componentwise?
    def to_L1(self, dimension):
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension).to_L1()
    
    def to_L2(self, dimension):
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension).to_L2()
    
    def to_Loo(self, dimension):
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension)
    
    def to_Coo(self, dimension):
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension).to_Coo()



class Gaussian(norm.Base_Norm, ABC, Distribution):
    # TODO: add parameter, gaussian over L2 or gaussian over coefficients => change to_Lp
    # TODO: if gaussian over L2 also alpha has to be converted...

    @abstractmethod
    def __init__(self):
        pass

    def get_alpha(self, q=None, n=None): # TODO: perhaps calculate alpha via q and sigma
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

    def to_L1(self, dimension):
        r"""
        Transforms Gaussian width into norm :math:`L_1`-norm of a vector whose coefficients are distributed according to a Gaussian. 
        
        .. _to_L1:

        For a Gaussian distribution, we have that: 

        .. math::
            \text{Pr}\left[ |X| \geq x\right] &\leq 2 e^{-\pi x^2/s^2}\\
            \text{Pr}\left[ |X| \geq x s\right] &\leq 2 e^{-\pi x^2}\\
            \text{Pr}\left[ |X| \geq \frac{x s}{\sqrt{\pi}}\right] &\leq 2 e^{-x^2}\\
            \text{Pr}\left[ |X| \geq \frac{\sqrt{x} s}{\sqrt{\pi}}\right] &\leq 2 e^{-x}

        We require :math:`2 e^{-x} \approx 2^{-sec}` and obtain :math:`x = \lceil\ln 2^{sec + 1}\rceil`. Hence, we can estimate our bound as :math:`\sqrt{90} s / \sqrt{\pi}`.

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_1`-norm of vector
        """
        # TODO: global constant gaussian_statistical_sec oder so, optional parameter, default auf global, durchschleifen, ...
        if self.sec:
            sec = self.sec
        else:
            sec = problem.statistical_sec # TODO

        # TODO: check
        bound = sqrt(ceil(log(2**(sec + 1)))) * self.s / sqrt(pi)
        if self.componentwise:
            return norm.Lp(bound, dimension, oo).to_L1(dimension)
        else:
            return norm.Lp(bound, dimension, 2).to_L1(dimension)
        

    def to_L2(self, dimension): # TODO
        r"""
        Transforms Gaussian width into norm :math:`L_2`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_L1`_). 
        
        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_2`-norm of vector
        """
        try:
            dimension = self.dimension
        except:
            raise AttributeError("Dimension must be set before calling norm transformations (e.g. 'secret_distribution.dimension = n'")
        bound = sqrt(90) * self.s / sqrt(pi)
        if self.componentwise:
            return norm.Lp(bound, dimension, oo).to_L2(dimension)
        else:
            return norm.Lp(bound, dimension, 2).to_L2(dimension)

    def to_Loo(self, dimension):
        r"""
        Transforms Gaussian width into norm :math:`L_\infty`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_L1`_). 

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_\infty`-norm of vector
        """
        try:
            dimension = self.dimension
        except:
            raise AttributeError("Dimension must be set before calling norm transformations (e.g. 'secret_distribution.dimension = n'")
        bound = sqrt(90) * self.s / sqrt(pi)
        if self.componentwise:
            return norm.Lp(bound, dimension, oo).to_Loo(dimension)
        else:
            return norm.Lp(bound, dimension, 2).to_Loo(dimension)

    def to_Coo(self, dimension):
        r"""
        Transforms Gaussian width into norm :math:`C_\infty`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_L1`_).

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`C_\infty`-norm of vector
        """
        bound = sqrt(90) * self.s / sqrt(pi)
        if self.componentwise:
            return norm.Lp(bound, dimension, oo).to_Coo(dimension)
        else:
            return norm.Lp(bound, dimension, 2).to_Coo(dimension)

    def _convert_for_lwe_estimator(self):
        """
        For secret distribution, implies that secret distribution follows error distribution (others not supported)
        """
        return "normal" 


class Gaussian_alpha(Gaussian):
    """
    Helper class for Gaussian distribution. 
    """
    def __init__(self, alpha, q, componentwise=True, sec=None):
        r"""
        :param sigma: noise rate :math:`\alpha`
        :param q: modulus
        :param componentwise: if `True`, Gaussian over coefficients, else over :math:`L_2`-norm
        :param sec: required security for statistical Gaussian to Lp-bound transformation
        """
        self.alpha = RR(alpha)
        # TODO: Do we actually need stddev/sigma?
        self.sigma = est.stddevf(self.alpha, q)
        self.s = est.sigmaf(self.stddev)
        self.componentwise = componentwise
        self.sec = sec


class Gaussian_sigma(Gaussian):
    """
    Helper class for Gaussian distribution.
    """
    def __init__(self, sigma, q, componentwise=True, sec=None):
        """
        :param sigma: standard deviation :math:`\sigma`
        :param q: modulus
        :param componentwise: if `True`, Gaussian over coefficients, else over :math:`L_2`-norm
        :param sec: required security for statistical Gaussian to Lp-bound transformation
        """
        self.sigma = RR(sigma)
        self.s = est.sigmaf(self.sigma)
        self.alpha = est.alphaf(self.sigma, q)
        self.componentwise = componentwise
        self.sec = sec


class Gaussian_s(Gaussian):
    """
    Helper class for Gaussian distribution.
    """
    def __init__(self, s, q, componentwise=True, sec=None):
        """
        :param sigma: Gaussian width :math:`s = \sigma \cdot \sqrt{2\pi}`
        :param q: modulus
        :param componentwise: if `True`, Gaussian over coefficients, else over :math:`L_2`-norm
        :param sec: required security for statistical Gaussian to Lp-bound transformation
        """
        self.s = s
        self.sigma = est.stddevf(self.s)
        self.alpha = est.alphaf(s, q)
        self.componentwise = componentwise
        self.sec = sec