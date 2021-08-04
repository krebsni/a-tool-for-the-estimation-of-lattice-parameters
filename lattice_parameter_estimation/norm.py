r"""
Module for norms and norm transformation.

Let :math:`n` be the dimension of the vector and with a slight abuse of notation :math:`L_i` represent the value of :math:`L_i`-norm of the vector. From section 2.1 in :cite:`BDLOP18` we have:
TODO: change definition to match BDLOP => ring elements as vectors...

#. :math:`\;\;L_1 \leq \sqrt{n} L_2`
#. :math:`\;\;L_1 \leq n L_\infty`
#. :math:`\;\;L_2 \leq \sqrt{n} L_\infty \;\;\;(\text{since }  \sqrt{n} L_2 \leq n L_\infty)`
#. :math:`\;\;L_\infty \leq L_1`


And from Theorem 7 in :cite:`DPSZ12`:

5. :math:`\;\;L_\infty \leq C_\infty`
6. :math:`\;\;C_\infty \leq L_1`

# TODO: norm transformations documentation
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
    # TODO: inform user about how to use norm on vector in ring/module? I.e. multiply dimension with degree
    
    def __init__(self, value, p, dimension):
        """
        :param value: value of :math:`L_p`-norm of a vector
        :param p: specifies :math:`L_p`-norm, only values 1, 2, oo are supported
        :param dimension: dimension of the vector
        """
        self.p = p
        self.value = value
        if dimension is None:
            raise ValueError("Dimension must be specified.")
        self.dimension = dimension

    def to_L1(self, dimension=None):
        r"""
        .. math::
            L_1 &\leq \sqrt{n} L_2  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\; &[1]\\
            L_1 &\leq n L_\infty &[2]
            
        :param dimension: dimension of the vector
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
        .. math::
            L_2 &\leq \sqrt{n} L_1  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\; &[3,4]\\
            L_2 &\leq \sqrt{n} L_\infty &[3]

        :param dimension: dimension of the vector
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
        .. math::
            L_\infty &\leq L_1  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\; &[4]\\
            L_\infty &\leq \sqrt{n} L_2 &[1,4]

        :param dimension: dimension of the vector
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
        .. math::
            C_\infty &\leq L_1  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\; &[6]\\
            C_\infty &\leq \sqrt{n} L_2 &[1,6]\\
            C_\infty &\leq n L_\infty &[2, 6]

        :param dimension: dimension of the vector
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
    
    def __add__(self, other):
        """
        TODO
        """
        if not isinstance(other, BaseNorm):
            TypeError(f"Cannot add {type(self)} to {type(other)}")
        if self.dimension != other.dimension:
            raise ValueError("Vectors must have the same dimension for addition.")

        if self.p == other.p:
            return Lp(value=self.value + other.value, p=self.p, dimension=self.dimension)
        else:
            
            if self.p == 1:
                val = other.to_L1().value # TODO
            if self.p == 2:
                val = other.to_L2().value # TODO
            if self.p == oo:
                val = other.to_Loo().value # TODO
            return Lp(value=self.value + val, p=self.p, dimension=self.dimension)

    def __mul__(self, other):
        r""" 
        Multiply :math:`L_p`-norm with ``other`` by converting other norm to :math:`C_\infty`-norm or with a scalar.

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
        :param dimension: dimension of the vector
        """
        if dimension is None:
            raise ValueError("Dimension must be specified.")
        self.value = value
        self.dimension = dimension

    def to_L1(self, dimension):
        r"""
        .. math::
            L_1 \leq n C_\infty  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;[2,5]
            
        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_1`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        return Lp(value=self.value * self.dimension, p=1, dimension=dimension)

    def to_L2(self, dimension):
        r"""
        .. math::
            L_2 \leq \sqrt{n} C_\infty  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;[3,5]

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_2`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        return Lp(value=self.value * sqrt(self.dimension), p=2, dimension=dimension)

    def to_Loo(self, dimension):
        r"""
        .. math::
            L_\infty \leq C_\infty  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;[5]

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_\infty`-norm of the vector
        """
        if dimension is None:
            dimension = self.dimension
            if self.dimension is None:
                raise ValueError("Dimension must be specified as the object has not be initialized with a dimension.")
                
        return Lp(value=self.value, p=oo, dimension=dimension)
    
    def to_Coo(self, dimension):
        r"""
        :param dimension: dimension of the vector
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
        Multiply :math:`C_\infty`-norm norm with ``other`` by converting other norm to :math:`C_\infty`-norm or with a scalar.

        From :cite:`DPSZ12`: Let :math:`\mathcal{O}_K` be the ring of integers of a number field :math:`K=\mathbb{Q}(\theta)`, where :math:`\theta` is an algebraic number and :math:`\sigma` denote the canonical embedding as defined in :cite:`DPSZ12`. Then, for :math:`x, y \in \mathcal{O}_K` it holds that

        .. math::
            \| \sigma(x \cdot y) \|_\infty \leq  \| \sigma(x) \|_\infty \cdot \| \sigma(y) \|_\infty

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