r"""
Module for norms and norm transformation.

From :cite:`BDLOP18`: Let :math:`\mathcal{R}_q` be a ring as defined in :cite:`BDLOP18` and :math:`f \in \mathcal{R}_q` with :math:`f = \sum_i f_i X^i`. Then the following inequations hold:

.. math::
    \begin{align}
        \| f \|_1 &\leq \sqrt{n} \| f \|_2 \label{norm1} \tag{1}\\
        \| f \|_1 &\leq n \| f \|_\infty \label{norm2} \tag{2}\\
        \| f \|_2 &\leq \sqrt{n} \| f \|_\infty \;\;(\text{since }  \sqrt{n} \| f \|_2 \leq n \| f \|_\infty) \label{norm3} \tag{3}\\
        \| f \|_\infty& \leq \| f \|_1 \label{norm4} \tag{4}
    \end{align}


And from :cite:`DPSZ12`, Theorem 7: Let :math:`\mathcal{O}_K` be the ring of integers of a number field :math:`K=\mathbb{Q}(\theta)`, where :math:`\theta` is an algebraic number and :math:`\sigma` denote the canonical embedding as defined in :cite:`DPSZ12`. Then, for :math:`x, y \in \mathcal{O}_K` it holds the following inequations hold (we assume that :math:`C_m` in :cite:`DPSZ12` is :math:`1`):

.. math::
    \begin{align}
        \| f \|_\infty &\leq \| \sigma(f) \|_\infty \label{norm5} \tag{5}\\
        \| \sigma(f) \|_\infty &\leq \| f \|_1 \label{norm6} \tag{6}
    \end{align}
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
        :param value: value of :math:`L_p`-norm of a vector
        :param p: specifies :math:`L_p`-norm, only values 1, 2, oo are supported
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        self.p = p
        self.value = value
        if dimension is None:
            raise ValueError("Dimension must be specified.")
        self.dimension = dimension

    def to_L1(self, dimension=None):
        r"""
        From :math:`\ref{norm1}`, it follows that :math:`\| f \|_1 \leq \sqrt{n} \| f \|_2` and from :math:`\ref{norm2}`, :math:`\| f \|_1 \leq n \| f \|_\infty`.
            
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_1`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension")

        if self.p == 1:
            return Lp(value=self.value, p=1, dimension=dimension)
        elif self.p == 2:
            return Lp(value=self.value * sqrt(dimension), p=1, dimension=dimension)
        elif self.p == oo:
            return Lp(value=self.value * dimension, p=1, dimension=dimension)
        else:
            raise ValueError(f"L{self.p}-norm not supported")

    def to_L2(self, dimension=None):
        r"""
        From :math:`\ref{norm3}` and :math:`\ref{norm4}`, it follows that :math:`\| f \|_2 \leq \sqrt{n}  \| f \|_1` and from :math:`\ref{norm3}`, :math:`\| f \|_2 \leq \sqrt{n}  \| f \|_\infty`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_2`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")

        if self.p == 1:
            return Lp(value=self.value * sqrt(dimension), p=2, dimension=dimension)
        elif self.p == 2:
            return Lp(value=self.value, p=2, dimension=dimension)
        elif self.p == oo:
            return Lp(value=self.value * sqrt(dimension), p=2, dimension=dimension)
        else:
            raise ValueError(f"L{self.p}-norm not supported")

    def to_Loo(self, dimension=None):
        r"""
        From :math:`\ref{norm4}`, it follows that :math:`\| f \|_\infty \leq  \| f \|_1` and from :math:`\ref{norm1}` and :math:`\ref{norm4}`, :math:`\| f \|_\infty \leq \sqrt{n}  \| f \|_2`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_\infty`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        if self.p == 1:
            return Lp(value=self.value, p=oo, dimension=dimension)
        elif self.p == 2:
            return Lp(value=self.value * sqrt(dimension), p=oo, dimension=dimension)
        elif self.p == oo:
            return Lp(value=self.value, p=oo, dimension=dimension)
        else:
            raise ValueError(f"L_{self.p}-norm not supported")

    def to_Coo(self, dimension=None):
        r"""
        From :math:`\ref{norm6}`, it follows that :math:`\| \sigma(f) \|_\infty \leq  \| f \|_1`, from :math:`\ref{norm1}` and :math:`\ref{norm6}`, :math:`\| \sigma(f) \|_\infty \leq \sqrt{n}  \| f \|_2`, and from :math:`\ref{norm2}` and :math:`\ref{norm6}`, :math:`\| \sigma(f) \|_\infty \leq n  \| f \|_\infty`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`C_\infty`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        if self.p == 1:
            return Coo(value=self.value, dimension=dimension)
        elif self.p == 2:
            return Coo(value=self.value * sqrt(dimension), dimension=dimension)
        elif self.p == oo:
            return Coo(value=self.value * dimension, dimension=dimension)
        else:
            raise ValueError(f"L{self.p}-norm not supported")

    def to(self, target_norm : BaseNorm):
        """ 
        Transform norm instance into same norm as ``target_norm``.
        
        :param target_norm: instance with target norm of norm transformation
        """
        if isinstance(target_norm, Lp):
            if target_norm.p == 1:
                return self.to_L1(self.dimension)
            if target_norm.p == 2:
                return self.to_L2(self.dimension)
            if target_norm.p == oo:
                return self.to_Loo(self.dimension)
        elif isinstance(target_norm, Coo):
            return self.to_Coo(self.dimension)
        else:
            ValueError("target_norm could not be identified (not Lp or Coo).")
    
    def __add__(self, other : BaseNorm):
        """
        Addition of two norm instances by converting ``other`` to norm of ``self``.
        """
        if not isinstance(other, BaseNorm):
            TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")

        if self.p == other.p:
            return Lp(value=self.value + other.value, p=self.p, dimension=self.dimension)
        else:
            if self.p == 1:
                val = other.to_L1().value
            if self.p == 2:
                val = other.to_L2().value
            if self.p == oo:
                val = other.to_Loo().value
            return Lp(value=self.value + val, p=self.p, dimension=self.dimension)

    def __mul__(self, other):
        r""" 
        Multiply :math:`L_p`-norm with ``other``. ``other`` can be a scalar or an instance of :class:`BaseNorm`. 

        From :cite:`BDLOP18`: Let :math:`\mathcal{R}_q` be a ring as defined in :cite:`BDLOP18` and :math:`f, g \in \mathcal{R}_q`

        1. If :math:`\|f\|_\infty \leq \beta, \|g\|_1 \leq \gamma` then :math:`\|f \cdot g\|_\infty \leq \beta \cdot \gamma`.
        2. If :math:`\|f\|_2 \leq \beta, \|g\|_2 \leq \gamma` then :math:`\|f \cdot g\|_\infty \leq \beta \cdot \gamma`.

        And from :cite:`DPSZ12`: Let :math:`\mathcal{O}_K` be the ring of integers of a number field :math:`K=\mathbb{Q}(\theta)`, where :math:`\theta` is an algebraic number. Then, for :math:`x, y \in \mathcal{O}_K` it holds that

        3. :math:`\| x \cdot y \|_\infty \leq C_m \cdot n^2 \cdot \| x \|_\infty \cdot \| y \|_\infty`
            
        We assume that :math:`C_m = 1`.
        """
        if not isinstance(other, BaseNorm):
            try:
                return Lp(value=self.value * other, p=self.p, dimension=self.dimension)
            except:
                raise TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")
        if self.p == oo and other.p == oo:
            return Lp(value=self.dimension * self.value * other.value, p=oo, dimension=self.dimension)
        elif (self.p == 1 and other.p == oo) \
                or (self.p == oo and other.p == 1) \
                or (self.p == 2 and other.p == 2):
            return Lp(value=self.value * other.value, p=oo, dimension=self.dimension)
        else:
            return self.to_Coo() * other.to_Coo()

    def __rmul__(self, other):
        return self * other

    def __str__(self) -> str:
        return f"{self.value} (L{self.p}-norm)"

def L1(value, dimension) -> Lp:
    r"""Alias for Lp-norm with p=1. See :class:`Lp`."""
    return Lp(value=value, p=1, dimension=dimension)

def L2(value, dimension) -> Lp:
    r"""Alias for Lp-norm with p=2. See :class:`Lp`."""
    return Lp(value=value, p=2, dimension=dimension)

def Loo(value, dimension) -> Lp:
    r"""Alias for Lp-norm with p=oo. See :class:`Lp`."""
    return Lp(value=value, p=oo, dimension=dimension)


class Coo(BaseNorm):
    """
    Infinity norm of canonical embedding.
    """
    def __init__(self, value, dimension):
        r"""
        :param value: value of :math:`C_\infty`-norm of a vector
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        """
        if dimension is None:
            raise ValueError("Dimension must be specified.")
        self.value = value
        self.dimension = dimension

    def to_L1(self, dimension):
        r"""
        From :math:`\ref{norm2}` and :math:`\ref{norm5}`, it follows that :math:`\| f \|_1 \leq  n \| \sigma(f) \|_\infty`.
            
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_1`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        return Lp(value=self.value * self.dimension, p=1, dimension=dimension)

    def to_L2(self, dimension):
        r"""
        From :math:`\ref{norm3}` and :math:`\ref{norm5}`, it follows that :math:`\| f \|_2 \leq  \sqrt{n} \| \sigma(f) \|_\infty`.
        
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_2`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        return Lp(value=self.value * sqrt(self.dimension), p=2, dimension=dimension)

    def to_Loo(self, dimension):
        r"""
        From :math:`\ref{norm5}`, it follows that :math:`\| f \|_\infty \leq  \| \sigma(f) \|_\infty`.

        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`L_\infty`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        return Lp(value=self.value, p=oo, dimension=dimension)
    
    def to(self, target_norm : BaseNorm):
        """ 
        Transform norm instance into same norm as ``target_norm``.
        
        :param target_norm: instance with target norm of norm transformation
        """
        if isinstance(target_norm, Lp):
            if target_norm.p == 1:
                return self.to_L1(self.dimension)
            if target_norm.p == 2:
                return self.to_L2(self.dimension)
            if target_norm.p == oo:
                return self.to_Loo(self.dimension)
        elif isinstance(target_norm, Coo):
            return self.to_Coo(self.dimension)
        else:
            ValueError("target_norm could not be identified (not Lp or Coo).")
            

    def to_Coo(self, dimension):
        r"""
        :param dimension: dimension, note that for RLWE and MLWE the dimension has to be multiplied by the degree of the polynomial ``n``
        :returns: upper bound of :math:`C_\infty`-norm of the vector
        """
        return self
    
    def __add__(self, other):
        r"""Add two norms. Converts ``other`` to :math:`C_\infty`-norm."""
        if not isinstance(other, BaseNorm):
            raise TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")
        
        return Lp(value=self.value + other.to_Coo(), dimension=self.dimension)

    def __mul__(self, other):
        r""" 
        Multiply :math:`C_\infty`-norm with ``other``. ``other`` can be a scalar or an instance of :class:`BaseNorm`. In the latter case ``other``is transformed to :math:`C_\infty`-norm.

        From :cite:`DPSZ12`: For :math:`x, y \in \mathcal{O}_K` it holds that

        .. math::
            \| \sigma(x \cdot y) \|_\infty \leq  \| \sigma(x) \|_\infty \cdot \| \sigma(y) \|_\infty.

        """
        if not isinstance(other, BaseNorm):
            try:
                return Coo(value=self.value * other, dimension=self.dimension)
            except:
                TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")
        
        return Coo(value=self.value * other.to_Coo().value, dimension=self.dimension)

    def __rmul__(self, other):
        return self * other

    def __str__(self) -> str:
        return f"{self.value} (Coo-norm)"
