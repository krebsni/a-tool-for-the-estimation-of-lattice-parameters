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

try: # sage-related imports do not work with sphinx for documentation
    import sys
    import os
    from abc import ABC
    from abc import abstractmethod
    import sage.all
    from sage.functions.other import sqrt
    sys.path.append(os.path.dirname(__file__) + "/estimate_all")
    from estimator import estimator as est
    oo = est.PlusInfinity()
except:
    pass


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
        if not dimension:
            dimension = self.dimension
            if not self.dimension:
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")

        if self.p == 1:
            return Lp(self.value, 1, dimension)
        elif self.p == 2:
            return Lp(self.value * sqrt(dimension), 1, dimension)
        elif self.p == oo:
            return Lp(self.value * dimension, 1, dimension)
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
        if not dimension:
            dimension = self.dimension
            if not self.dimension:
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")

        if self.p == 1:
            return Lp(self.value * sqrt(dimension), 2, dimension)
        elif self.p == 2:
            return Lp(self.value, 2, dimension)
        elif self.p == oo:
            return Lp(self.value * sqrt(dimension), 2, dimension)
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
        if not dimension:
            dimension = self.dimension
            if not self.dimension:
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
        if self.p == 1:
            return Lp(self.value, oo, dimension)
        elif self.p == 2:
            return Lp(self.value * sqrt(dimension), oo, dimension)
        elif self.p == oo:
            return Lp(self.value, oo, dimension)
        else:
            raise ValueError(f"L{self.p}-norm not supported")

    def to_Coo(self, dimension=None):
        r"""
        .. math::
            C_\infty &\leq L_1  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\; &[6]\\
            C_\infty &\leq \sqrt{n} L_2 &[1,6]\\
            C_\infty &\leq n L_\infty &[2, 6]

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`C_\infty`-norm of the vector
        """
        if not dimension:
            dimension = self.dimension
            if not self.dimension:
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
        if self.p == 1:
            return Coo(self.value, dimension)
        elif self.p == 2:
            return Coo(self.value * sqrt(dimension), dimension)
        elif self.p == oo:
            return Coo(self.value * dimension, dimension)
        else:
            raise ValueError(f"L{self.p}-norm not supported")


class Coo(Base_Norm):
    """
    Infinity norm of canonical embedding.
    """

    def __init__(self, value, dimension=None):
        """
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
        if not dimension:
            dimension = self.dimension
            if not self.dimension:
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
        return Lp(self.value * self.dimension, 1, dimension)

    def to_L2(self, dimension):
        r"""
        .. math::
            L_2 \leq \sqrt{n} C_\infty  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;[3,5]

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_2`-norm of the vector
        """
        if not dimension:
            dimension = self.dimension
            if not self.dimension:
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
        return Lp(self.value * sqrt(self.dimension), 2, dimension)

    def to_Loo(self, dimension):
        r"""
        .. math::
            L_\infty \leq C_\infty  \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;[5]

        :param dimension: dimension of the vector
        :returns: upper bound of :math:`L_\infty`-norm of the vector
        """
        if not dimension:
            dimension = self.dimension
            if not self.dimension:
                raise ValueError("dimension must be specified as the object has not be initialized with dimension")
                
        return Lp(self.value, oo, dimension)
    
    def to_Coo(self, dimension):
        """
        :param dimension: dimension of the vector
        :returns: upper bound of :math:`C_\infty`-norm of the vector
        """
        return self