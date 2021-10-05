# A Tool for the Estimation of Lattice Parameters

A library to find secure parameter sets of popular versions of lattice problems (LWE and SIS in their integer, ring, and module versions) given various p-norms. 


# Bugfixes
If the following exception occurs
```
TypeError: type sage.rings.real_mpfr.RealNumber doesn't define __round__ method
```
try to add the line
```
from sage.misc.functional import round
```
at the beggining of estimator.py.