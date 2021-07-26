r"""
Module for norms and norm transformation.

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

import sys
import os
from abc import ABC
from abc import abstractmethod
import sage.all
from sage.functions.other import sqrt
import estimate_all_schemes.estimator as est
oo = est.PlusInfinity()


class Base_Norm(ABC):
    """
    Provides norm transformations and property access to value in norm and dimension .
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


class Lp(Base_Norm):
    # TODO: inform user about how to use norm on vector in ring/module? I.e. multiply dimension with degree
    
    def __init__(self, value, p, dimension=None):
        """
        :param value: value of :math:`L_p`-norm of a vector
        :param p: specifies :math:`L_p`-norm, only values 1, 2, oo are supported
        :param dimension: dimension of the vector
        """
        self.p = p
        self.value = value
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
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")

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
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")

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
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
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
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
        if self.p == 1:
            return Coo(value=self.value, dimension=dimension)
        elif self.p == 2:
            return Coo(value=self.value * sqrt(dimension), dimension=dimension)
        elif self.p == oo:
            return Coo(value=self.value * dimension, dimension=dimension)
        else:
            raise ValueError(f"L{self.p}-norm not supported")
        
    def __str__(self) -> str:
        return f"{self.value} (L{self.p}-norm)"


class Coo(Base_Norm):
    """
    Infinity norm of canonical embedding.
    """

    def __init__(self, value, dimension=None):
        r"""
        :param value: value of :math:`C_\infty`-norm of a vector
        :param dimension: dimension of the vector
        """
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
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
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
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
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
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
        return Lp(value=self.value, p=oo, dimension=dimension)
    
    def to_Coo(self, dimension):
        r"""
        :param dimension: dimension of the vector
        :returns: upper bound of :math:`C_\infty`-norm of the vector
        """
        return self
    
    def __str__(self) -> str:
        return f"{self.value} (Coo-norm)"