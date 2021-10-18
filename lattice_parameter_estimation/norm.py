r"""
Module for norms and norm bound conversions.

Let :math:`\mathcal{R}_q` be a ring as defined in :cite:`BDLOP18` and :math:`f \in \mathcal{R}_q` with :math:`f = \sum_i f_i X^i`. 

It is easy to see that for any :math:`p, q \in \mathbb{N}` with :math:`\infty \geq p \geq q \geq 1` the following inequation holds:

.. math::
    \begin{align}
        \| f \|_p & \leq \| f \|_q \label{norm1}. \tag{1}
    \end{align}
In addition, if we apply Hölder's inequality to finite vector spaces as in `Relations between p-norms<https://math.stackexchange.com/questions/218046/relations-between-p-norms>`_, the following holds:

For :math:`1 \leq p \leq q \leq \infty` it holds that

.. math::
    \begin{align}
        \lim_{q' \rightarrow q}\| f \|_p & \leq \lim_{q' \rightarrow q} n^{\frac{1}{p} - \frac{1}{q'}}\| f \|_q'. \label{norm2} \tag{2}
    \end{align}


From :cite:`DPSZ12`, Theorem 7: Let :math:`\mathcal{O}_K` be the ring of integers of a number field :math:`K=\mathbb{Q}(\theta)`, where :math:`\theta` is an algebraic number and :math:`\sigma` denote the canonical embedding as defined in :cite:`DPSZ12`. Then, for :math:`x, y \in \mathcal{O}_K` it holds the following inequations hold (we assume that :math:`C_m` in :cite:`DPSZ12` is :math:`1` due to :math:`m` power of :math:`2`):

.. math::
    \begin{align}
        \| f \|_p \leq n^{\frac{1}{p}} \| f \|_\infty &\leq n^{\frac{1}{p}} \| \sigma(f) \|_\infty \label{norm3} \tag{3}\\
        \| \sigma(f) \|_\infty &\leq \| f \|_1 \leq n^{1 - \frac{1}{p}}\| f \|_p \label{norm4} \tag{4}
    \end{align}

AUTHOR:
    Nicolai Krebs - 2021
"""

from multiprocessing.sharedctypes import Value
import sys
import os
from abc import ABC
from abc import abstractmethod
import sage.all
from sage.functions.other import sqrt
import estimator as est

oo = est.PlusInfinity()


class BaseNorm(ABC):
    """
    Provides norm transformations and property access to value in norm and dimension.
    """

    @abstractmethod
    def to_L1(self, dimension=None):
        pass

    @abstractmethod
    def to_L2(self, dimension=None):
        pass

    @abstractmethod
    def to_Loo(self, dimension=None):
        pass

    @abstractmethod
    def to_Coo(self, dimension=None):
        pass


class Lp(BaseNorm):
    def __init__(self, value, p, dimension):
        """
        :param value: value of :math:`\ell_p`-norm of a vector
        :param p: specifies :math:`\ell_p`-norm, must be positive integer or ``oo``
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        self.p = p
        self.value = value
        if dimension is None:
            raise ValueError("Dimension must be specified.")
        self.dimension = dimension

    def to_Lp(self, p, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_p`-norm for a given norm bound in some :math:`\ell_q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param p: norm parameter of target norm, must be positive integer or ``oo``
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_p`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with a dimension."
                )

        if p >= self.p:
            return Lp(value=self.value, p=p, dimension=dimension)
        else:
            return Lp(
                value=self.value * dimension ** (1 / p - 1 / self.p),
                p=p,
                dimension=dimension,
            )

    def to_L1(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_1`-norm for a given norm bound in some :math:`\ell_q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_1`-norm of the vector
        """
        return self.to_Lp(self, p=1, dimension=dimension)

    def to_L2(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_2`-norm for a given norm bound in some :math:`\ell_q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_2`-norm of the vector
        """
        return self.to_Lp(self, p=2, dimension=dimension)

    def to_Loo(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_\infty`-norm for a given norm bound in some :math:`\ell_q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_\infty`-norm of the vector
        """
        return self.to_Lp(self, p=oo, dimension=dimension)

    def to_Coo(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_\infty`-norm for a given norm bound in some :math:`\ell_q`-norm by using Equations :math:`\ref{norm3}`:

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\mathcal{C}_\infty`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with a dimension."
                )

        return Cp(
            value=self.value * dimension ** (1 - 1 / self.p), p=oo, dimension=dimension
        )

    def to_Cp(self, p, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_p`-norm for a given norm bound in some :math:`q`-norm by using Equations :math:`\ref{norm3}`:

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\mathcal{C}_p`-norm of the vector
        """
        return self.to_Coo().to_Cp(p, dimension=dimension)

    def to_C1(self, p, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_1`-norm for a given norm bound in some :math:`q`-norm by using Equations :math:`\ref{norm3}`:

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\mathcal{C}_1`-norm of the vector
        """
        return self.to_Coo().to_Cp(1, dimension=dimension)

    def to_C2(self, p, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_2`-norm for a given norm bound in some :math:`q`-norm by using Equations :math:`\ref{norm3}`:

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\mathcal{C}_2`-norm of the vector
        """
        return self.to_Coo().to_Cp(2, dimension=dimension)

    def to(self, target_norm: BaseNorm):
        """
        Convert norm bound in given :math:`\ell_p`-norm into same norm as ``target_norm``.

        :param target_norm: instance with target norm of norm transformation
        """
        if isinstance(target_norm, Lp):
            return self.to_Lp(target_norm.p, self.dimension)
        elif isinstance(target_norm, Cp):
            return self.to_Cp(target_norm.p, self.dimension)
        else:
            ValueError("target_norm could not be identified (not Lp or Coo).")

    def __add__(self, other: BaseNorm):
        """
        Addition of two norm instances by converting ``other`` to norm of ``self``.
        """
        if not isinstance(other, BaseNorm):
            TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")
        val = other.to_Lp(self.p, self.dimension)
        return Lp(value=self.value + val, p=self.p, dimension=self.dimension)

    def __sub__(self, other):
        return self.__add__(other)

    def __mul__(self, other):
        r"""
        Multiply :math:`\ell_p`-norm with ``other``. ``other`` can be a scalar or an instance of :class:`BaseNorm`.

        From :cite:`BDLOP18`: Let :math:`\mathcal{R}_q` be a ring as defined in :cite:`BDLOP18` and :math:`f, g \in \mathcal{R}_q`

        1. If :math:`\|f\|_\infty \leq \beta, \|g\|_1 \leq \gamma` then :math:`\|f \cdot g\|_\infty \leq \beta \cdot \gamma`.
        2. If :math:`\|f\|_2 \leq \beta, \|g\|_2 \leq \gamma` then :math:`\|f \cdot g\|_\infty \leq \beta \cdot \gamma`.

        And from :cite:`DPSZ12`: Let :math:`\mathcal{O}_K` be the ring of integers of a number field :math:`K=\mathbb{Q}(\theta)`, where :math:`\theta` is an algebraic number. Then, for :math:`x, y \in \mathcal{O}_K` it holds that

        .. math::
            \| \sigma(x \cdot y) \|_\infty \leq \| \sigma(x) \|_\infty \cdot \| \sigma(y) \|_\infty \label{norm5}\tag{5}
            \| x \cdot y \|_\infty         & \leq n^2 \cdot \| x \|_\infty \cdot \| y \|_\infty

        (We assume that :math:`C_m = 1` in the original statement from the paper.)
        :returns: norm bound in some :math:`\ell_p`-norm or `\mathcal{C}_\infty`-norm
        """
        if not isinstance(other, BaseNorm):
            try:
                return Lp(value=self.value * other, p=self.p, dimension=self.dimension)
            except:
                raise TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")
        if isinstance(other, Lp):
            if self.p == oo and other.p == oo:
                return Lp(
                    value=self.dimension ** 2 * self.value * other.value,
                    p=oo,
                    dimension=self.dimension,
                )
            elif (
                (self.p == 1 and other.p == oo)
                or (self.p == oo and other.p == 1)
                or (self.p == 2 and other.p == 2)
            ):
                return Lp(
                    value=self.value * other.value, p=oo, dimension=self.dimension
                )

        return self.to_Coo() * other.to_Coo()

    def __rmul__(self, other):
        return self * other

    def __str__(self) -> str:
        return f"{self.value} (L{self.p}-norm)"


def L1(value, dimension) -> Lp:
    r"""Alias for :math:`\ell_p`-norm with p=1. See :class:`Lp`."""
    return Lp(value=value, p=1, dimension=dimension)


def L2(value, dimension) -> Lp:
    r"""Alias for :math:`\ell_p` with p=2. See :class:`Lp`."""
    return Lp(value=value, p=2, dimension=dimension)


def Loo(value, dimension) -> Lp:
    r"""Alias for :math:`\ell_p` with p=oo. See :class:`Lp`."""
    return Lp(value=value, p=oo, dimension=dimension)


class Cp(BaseNorm):
    """
    Canonical embedding norm :math:`\mathcal{C}_p`.
    """

    def __init__(self, value, p, dimension):
        r"""
        :param value: value of :math:`\mathcal{C}_p`-norm of a vector
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        self.p = p
        self.value = value
        if dimension is None:
            raise ValueError("Dimension must be specified.")
        self.dimension = dimension

    def to_Cp(self, p, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_p`-norm for a given norm bound in some :math:`\mathcal{C}_q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param p: norm parameter of target norm, must be positive integer or ``oo``
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_2`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with a dimension."
                )

        if p >= self.p:
            return Cp(value=self.value, p=p, dimension=dimension)
        else:
            return Cp(
                value=self.value * dimension ** (1 / p - 1 / self.p),
                p=p,
                dimension=dimension,
            )

    def to_C1(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_1`-norm for a given norm bound in some :math:`q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\mathcal{C}_1`-norm of the vector
        """
        return self.to_Cp(self, p=1, dimension=dimension)

    def to_C2(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_2`-norm for a given norm bound in some :math:`q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\mathcal{C}_2`-norm of the vector
        """
        return self.to_Cp(self, p=2, dimension=dimension)

    def to_Coo(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\mathcal{C}_\infty`-norm for a given norm bound in some :math:`q`-norm by using Equations :math:`\ref{norm1}` and :math:`\ref{norm2}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\mathcal{C}_\infty`-norm of the vector
        """
        return self.to_Cp(self, p=oo, dimension=dimension)

    def to_Lp(self, p, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_p`-norm for a given norm bound in :math:`\mathcal{C}_p`-norm by using Equations :math:`\ref{norm4}`. We first convert the :math:`\mathcal{C}_p`-norm bound into the :math:`\mathcal{C}_\infty`-norm.

        :param p: norm parameter of target norm
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_2`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError(
                    "Dimension must be specified as the object has not be initialized with a dimension."
                )
        return Lp(
            value=self.to_Coo().value * dimension ** (1 / p),
            p=p,
            dimension=dimension,
        )

    def to_L1(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_p`-norm for a given norm bound in :math:`\mathcal{C}_p`-norm by using Equations :math:`\ref{norm4}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_1`-norm of the vector
        """
        return self.to_Lp(1, dimension=dimension)

    def to_L2(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_p`-norm for a given norm bound in :math:`\mathcal{C}_p`-norm by using Equations :math:`\ref{norm4}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_2`-norm of the vector
        """
        return self.to_Lp(1, dimension=dimension)

    def to_Loo(self, dimension=None):
        r"""
        Calculate norm bound in :math:`\ell_p`-norm for a given norm bound in :math:`\mathcal{C}_p`-norm by using Equations :math:`\ref{norm4}`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`\ell_\infty`-norm of the vector
        """
        return self.to_Lp(1, dimension=dimension)

    def to(self, target_norm: BaseNorm):
        """
        Transform norm instance into same norm as ``target_norm``.

        :param target_norm: instance with target norm of norm transformation
        """
        if isinstance(target_norm, Lp):
            return self.to_Lp(target_norm.p, dimension=self.dimension)
        elif isinstance(target_norm, Cp):
            return self.to_Cp(self.dimension)
        else:
            ValueError("target_norm could not be identified (not Lp or Coo).")

    def __add__(self, other):
        r"""Add two norms. Converts ``other`` to :math:`C_\infty`-norm."""
        if not isinstance(other, BaseNorm):
            TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")

        val = other.to_Cp(self.p, self.dimension)
        return Cp(value=self.value + val, p=self.p, dimension=self.dimension)

    def __radd__(self, other):
        return self + other

    def __sub__(self, other):
        return self + other

    def __rsub__(self, other):
        return self + other

    def __mul__(self, other):
        r"""
        Multiply :math:`C_p`-norm with ``other``. ``other`` can be a scalar or an instance of :class:`BaseNorm` as in :func:`~norm.Lp.__mul__`.

        we can multiply two bounds :math:`\|\sigma(f)\|_p, \|\sigma(f)\|_q` in the embedding norm as in :class:`BaseNorm` as in :func:`~norm.Lp.__mul__`. To apply :math:`\ref{norm5}` we have to recursively embedded $\sigma(f)$ and $\sigma(g)$ and obtain
        
        .. math::
            \|\sigma(f) \cdot \sigma(g)\|_\infty & \leq \|\sigma(\sigma(f)\cdot \sigma(g))\|_\infty \leq \|\sigma(\sigma(f)) \|_\infty \cdot \| \sigma(\sigma(g))\|_\infty \\
                                                & \leq  n^{1-\frac{1}{p}}\|\sigma(f) \|_\infty \cdot n^{1-\frac{1}{q}} \|\sigma(f) \|_\infty.
            \\
                                                & \leq  n^{2-\frac{1}{p}-\frac{1}{q}}\|\sigma(f) \|_\infty \cdot \|\sigma(f) \|_\infty.
        """
        if not isinstance(other, BaseNorm):
            try:
                return Cp(value=self.value * other, p=self.p, dimension=self.dimension)
            except:
                raise TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")
        dimension = self.dimension
        if isinstance(other, Cp):
            if self.p == oo and other.p == oo:
                return Cp(
                    value=dimension ** 2 * self.value * other.value,
                    p=oo,
                    dimension=dimension,
                )
            elif (
                (self.p == 1 and other.p == oo)
                or (self.p == oo and other.p == 1)
                or (self.p == 2 and other.p == 2)
            ):
                return Cp(value=self.value * other.value, p=oo, dimension=dimension)

        return Cp(
            value=dimension ** (2 - 1 / self.p - 1 / other.p)
            * self.to_Coo().value
            * other.to_Coo().value,
            p=oo,
            dimension=dimension,
        )

    def __rmul__(self, other):
        return self * other

    def __str__(self) -> str:
        return f"{self.value} (Coo-norm)"


def C1(value, dimension) -> Lp:
    r"""Alias for :math:`\mathcal{C}_p`-norm with ``p=1``. See :class:`Cp`."""
    return Cp(value=value, p=1, dimension=dimension)


def C2(value, dimension) -> Lp:
    r"""Alias for :math:`\mathcal{C}_p`-norm with ``p=2``. See :class:`Cp`."""
    return Cp(value=value, p=2, dimension=dimension)


def Coo(value, dimension) -> Lp:
    r"""Alias for :math:`\mathcal{C}_p`-norm with ``p=oo``. See :class:`Cp`."""
    return Cp(value=value, p=oo, dimension=dimension)
