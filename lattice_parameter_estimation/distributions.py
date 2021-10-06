r""" 
Module for distributions to specify secret and error distributions. 

Contains Uniform and Gaussian distributions with various constructors and utility methods. Instances can be transformed to bounds in various norms and a Gaussian width parameter :math:`alpha`. 
"""
from abc import ABC, abstractmethod
from . import norm
import sys
import os
import sage.all
from sage.functions.log import log
from sage.functions.other import ceil, sqrt
from sage.rings.all import QQ, RR
from sage.symbolic.all import pi
import estimator as est

oo = est.PlusInfinity()


# Error Parameter Conversion (extension to functions in estimator.py)
def alpha_to_stddevf(alpha, q):
    r"""
    noise rate :math:`\alpha`, modulus q → standard deviation :math:`\sigma`

    :param alpha: noise rate
    :param q: modulus `0 < q`

    :returns: :math:`\sigma = \alpha \cdot q / \sqrt{2\pi}`
    """
    return est.stddevf(alpha * q)


class Distribution:
    def get_alpha(self, q=None, n=None):
        pass


class Uniform(norm.BaseNorm, Distribution):
    """
    Uniform distribution.

    Can be specified via bound :math:`(a, b)` and optional number of non-zero components :math:`h` or uniformly :math:`\mod q`
    """

    def __init__(
        self, a=None, b=None, h=None, uniform_mod_q=False, q=None, dimension=None
    ):
        r"""
        :param a: lower bound if b is specified, else take range [-a, a]
        :param b: upper bound, optional
        :param h: exactly :math:`h` components are :math:`\in [a,…,b]\setminus\{0\}`, all other components are zero
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
            if q is None:
                raise ValueError(
                    "q must be set for uniform_mod_q uniform distribution."
                )
            else:
                self.range = (0, q)
        self.dimension = dimension

    def get_alpha(self, q, n=None):
        r"""
        Calculates noise rate :math:`\alpha` of approximately equivalent discrete Gaussian distribution.

        :param q: modulus
        :param n: secret dimension, only needed for uniform mod q and sparse secrets

        :returns: noise rate :math:`\alpha`
        """
        if n is None:
            n = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with dimension."
                )
        variance = est.SDis.variance(self._convert_for_lwe_estimator(), q=q, n=n)
        return est.alphaf(sqrt(variance), q, sigma_is_stddev=True)

    def get_range(self):
        """ """
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
            return self.range

    def to_L1(self, dimension=None):
        """
        Convert bound (maximum of :math:`(|a|, |b|)`) to :math:`L_1`-norm.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with dimension."
                )
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension).to_L1()

    def to_L2(self, dimension=None):
        """
        Convert bound (maximum of :math:`(|a|, |b|)`) to :math:`L_2`-norm.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with dimension."
                )
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension).to_L2()

    def to_Loo(self, dimension=None):
        """
        Convert bound (maximum of :math:`(|a|, |b|)`) to :math:`L_\infty`-norm.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with dimension."
                )
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension)

    def to_Coo(self, dimension=None):
        """
        Convert bound (maximum of :math:`(|a|, |b|)`) to :math:`C_\infty`-norm.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with dimension."
                )
        bound = max(abs(self.range[0]), abs(self.range[1]))
        return norm.Lp(value=bound, p=oo, dimension=dimension).to_Coo()

    def __str__(self) -> str:
        return "Uniform [" + str(self._convert_for_lwe_estimator()) + "]"


class Gaussian(norm.BaseNorm, ABC, Distribution):
    r"""
    Gaussian distribution.

    Includes various constructors (in subclasses) :class:`GaussianS` for Gaussian width parameter :math:`s = \sigma \cdot \sqrt{2\pi}`, :class:`GaussianSigma` for standard deviation :math:`\sigma` and :class:`GaussianAlpha :math:`\alpha = s / q`. Gaussian can be converted to bounds in various norms with statistical security parameter ``sec``.
    """

    @abstractmethod
    def __init__(self):
        pass

    def get_alpha(self, q=None, n=None):
        r"""
        :returns: noise rate :math:`\alpha = s / q`
        """
        if self.alpha is not None:
            return self.alpha
        else:
            return est.alphaf(self.s, q, sigma_is_stddev=False)

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

    def to_Lp(self, sec=None, dimension=None):
        r"""
        Transforms Gaussian width into norm :math:`L_p`-norm of a vector whose coefficients are distributed according to a Gaussian. 
        
        .. _to_Lp:

        For a Gaussian distribution, we have that: 

        .. math::
            \text{Pr}\left[ |X| \geq x\right] &\leq 2 e^{-\pi x^2/s^2}\\

        We require :math:`2 e^{-\pi x^2/s^2} \approx 2^{-sec}`, hence

        .. math::
            2 e^{-\pi x^2/s^2} &\approx 2^{-sec}\\
            -\pi \frac{x^2}{s^2} &\approx (-sec - 1)\ln (2)\\
            x  &\approx s \sqrt{\frac{(sec + 1) \ln(2)}{\pi}}\\
        
        :param sec: required security for statistical Gaussian to Lp-bound transformation
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        
        :returns: upper bound of :math:`L_2`-norm of vector
        """
        if sec is None:
            if self.sec:
                sec = self.sec
            else:
                raise ValueError("sec parameter must be specified")

        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with a dimension."
                )

        bound = self.s * sqrt(log(2.0) * (sec + 1) / pi)
        return norm.Lp(value=bound, p=2, dimension=dimension)

    def to_L1(self, sec=None, dimension=None):
        r"""
        Transforms Gaussian width into norm :math:`L_1`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_Lp`_).

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_1`-norm of vector
        """
        return self.to_Lp(sec=sec, dimension=dimension).to_L1(dimension=dimension)

    def to_L2(self, sec=None, dimension=None):
        r"""
        Transforms Gaussian width into norm :math:`L_2`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_Lp`_).

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_2`-norm of vector
        """
        return self.to_Lp(sec=sec, dimension=dimension).to_L2(dimension=dimension)

    def to_Loo(self, sec=None, dimension=None):
        r"""
        Transforms Gaussian width into norm :math:`L_\infty`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_Lp`_).

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_\infty`-norm of vector
        """
        return self.to_Lp(sec=sec, dimension=dimension).to_Loo(dimension=dimension)

    def to_Coo(self, sec=None, dimension=None):
        r"""
        Transforms Gaussian width into norm :math:`C_\infty`-norm of a vector whose coefficients are distributed according to a Gaussian (see `to_Lp`_).

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`C_\infty`-norm of vector
        """
        return self.to_Lp(sec=sec, dimension=dimension).to_Coo(dimension=dimension)

    def _convert_for_lwe_estimator(self):
        """
        For secret distribution, implies that secret distribution follows error distribution (others not supported)
        """
        return "normal"

    def __str__(self) -> str:
        return f"Gaussian [sigma={self.sigma}, s={self.s}, alpha={self.alpha}, sec={self.sec}"


class GaussianAlpha(Gaussian):
    r"""
    Helper class for Gaussian distribution with input parameter :math:`\alpha`.
    """

    def __init__(self, alpha, q, sec=None, dimension=None):
        r"""
        :param sigma: noise rate :math:`\alpha`
        :param q: modulus
        :param sec: required security for statistical Gaussian to Lp-bound transformation
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        self.alpha = alpha
        self.sigma = alpha_to_stddevf(self.alpha, q)
        self.s = est.sigmaf(self.sigma)
        self.sec = sec
        self.dimension = dimension


class GaussianSigma(Gaussian):
    """
    Helper class for Gaussian distribution with input parameter :math:`\sigma` (standard deviation).
    """

    def __init__(self, sigma, q=None, sec=None, dimension=None):
        """
        :param sigma: standard deviation :math:`\sigma`
        :param q: modulus
        :param sec: required security for statistical Gaussian to Lp-bound transformation
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        self.sigma = sigma
        self.s = est.sigmaf(self.sigma)
        if q is not None:
            self.alpha = est.alphaf(self.sigma, q, sigma_is_stddev=True)
        else:
            self.alpha = None
            self.q = q
        self.sec = sec
        self.dimension = dimension


class GaussianS(Gaussian):
    """
    Helper class for Gaussian distribution with input parameter :math:`s = \sigma \cdot \sqrt{2\pi}` where :math:`\sigma` is the standard deviation.
    """

    def __init__(self, s, q=None, sec=None, dimension=None):
        """
        :param sigma: Gaussian width :math:`s = \sigma \cdot \sqrt{2\pi}`
        :param q: modulus
        :param sec: required security for statistical Gaussian to Lp-bound transformation
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        self.s = s
        self.sigma = est.stddevf(self.s)
        if q is not None:
            self.alpha = est.alphaf(s, q)
        else:
            self.alpha = None
            self.q = q
        self.sec = sec
        self.dimension = dimension
