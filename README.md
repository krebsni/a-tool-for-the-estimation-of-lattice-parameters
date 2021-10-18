# A Tool for the Estimation of Lattice Parameters

A library to find secure parameter sets of popular versions of lattice problems (LWE and SIS in their integer, ring, and module versions) given various :math:`\ell_p`-norms. 

# Basic Usage

The main functionality of the library is encapsulated in the module :py:mod:`lattice_parameter_estimation.param_search` which contains a generic search to find secure parameters for a given set of problems. In addition, the library includes moduls for distributions and :math:`\ell_p`-norms and norm inequations that help to specify error and secret distributions and bounds. Classes for LWE and SIS and their variants can be found in  :py:mod:`lattice_parameter_estimation.problem`. The estimation can be configured in the class :py:class`lattice_parameter_estimation.algorithms.Configuration`. 

To start a parameter search simply import :py:mod:`lattice_parameter_estimation.param_search` and call the function :py:func:`lattice_parameter_estimation.param_search.generic_search` with customized parameters. The library can also be installed as a python package by running the setup script. 

In Linux, you can run the script with the command 

.. code-block::

    sage <my_script>.py

Note that a current version of ``sagemath`` must be installed. 

Examples of what can be done with the module can be found in the script `usage_examples.py <https://github.com/krebsni/a-tool-for-the-estimation-of-lattice-parameters/blob/main/usage_example.py>`_. 