#!/usr/bin sage
r"""
A library to find secure parameter sets of popular versions of lattice problems (LWE and SIS in their integer, ring, and module versions) given various p-norms.
This script assumes that the estiamte-all-the-lwe-ntru-schemes commit 2bf02cc is present in a subdirectory `estimate_all` and within that subdirectory the LWE estimator commit 9302d42 in a subdirectory `estimator`.

NOTATION:
    LWE
    n       lwe secret dimension
    k       mlwe rank
    q       lwe modulo
    sigma   standard deviation :math:`\sigma` (if secret is normal form, also the secret standard devation)
    s       Gaussian width parameter, :math:`s = \sigma \cdot \sqrt{2\pi}`
    m       number of lwe samples

AUTHOR:
    Nicolai Krebs - 2021

"""

from problem import Estimate_Res


try: # sage-related imports do not work with sphinx for documentation
    from typing import Generator, Iterator
    from attacks import Attack_Configuration
    from norm import Base_Norm
    from problem import Base_Problem
    import norm
    import attacks
    import problem
    import distributions
    import os
    import sys
    import traceback
    from attr.validators import instance_of
    import fire
    import sympy
    import random
    import time
    from datetime import timedelta
    import bisect
    from collections import deque
    import multiprocessing
    from collections import OrderedDict
    from functools import partial
    from scipy.optimize import newton
    from abc import ABC, abstractmethod
    import sage.all 
    from sage.functions.log import exp, log
    from sage.functions.other import ceil, sqrt, floor, binomial
    from sage.rings.all import QQ, RR, ZZ, RealField, PowerSeriesRing, RDF
    from sage.symbolic.all import pi, e
    from sage.arith.all import random_prime as make_prime
    sys.path.append(os.path.dirname(__file__) + "/estimate_all")
    from estimator import estimator as est
    import cost_asymptotics
    import logging

    oo = est.PlusInfinity()
except:
    raise

## Logging ##
logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.DEBUG) # set to INFO to hide exceptions
# TODO: put in config file or so? param_search needs to be imported for logging level to be set (?)

# Security parameter
SECURITY = 128

# Utility # perhaps export if more is added in the future
def number_of_bits(v):
    if v == oo or v == -oo:
        return oo
    else:
        return ceil(log(abs(v), 2).n())


def unit_cost():
    """
    Unit cost for given parameter set
    """
    return 0 # ensure that new ones are added at the end
    # TODO: perhaps another generic search without unit cost


class Parameter_Set():
    """
    Helper class to order parameter sets in list 
    """

    parameter_cost = unit_cost
    def __init__(self, parameters):
        self.parameters = parameters
    
    def __lt__(self, other):
        # reversed sorting to pop from sorted list
        return self.parameter_cost(*self.parameters) > other.parameter_cost(*self.parameters) # TODO check


# is_secure and estimate functions are not really needed anymore... Functionality is provided by problem.estimate_cost
def is_secure(parameter_problem : Iterator[Base_Problem], sec, attack_configuration : Attack_Configuration):
    i = 0; secure = True
    # TODO: possibly  run parallel
    best_res = Estimate_Res(is_secure=False, results={"rop": oo}) # result with lowest sec
    for problem_instance in parameter_problem: 
        i += 1
        logger.info("Estimating cost of: " + str(problem_instance) + "...")
        res = problem_instance.estimate_cost(sec=sec, attack_configuration=attack_configuration)
        if "error" in res.results:
            print(res.results["error"]) # TODO error handling
        elif best_res.results["rop"] > res.results["rop"]:
            best_res = res
        if not res.is_secure:
            break
    
    if i == 0:
        raise ValueError("Empty Problem")
    return best_res
    
    # beliebig viele problem instances als parameter + sec ... => kein extra loop in generic_search notwendig


def estimate(parameter_problem : Iterator[Base_Problem], attack_configuration : Attack_Configuration):
    # TODO: run parallel
    best_result = {"rop": oo} # result with lowest sec
    for problem_instance in parameter_problem: 
        logger.info("Estimating cost of: " + str(problem_instance))
        res = problem_instance.estimate_cost(attack_configuration=attack_configuration)
        if "error" in res.results:
            print(res.results["error"]) # TODO error handling
        elif best_result["rop"] > res.results["rop"]:
            best_result = res.results    
    return best_result


def generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem, 
        attack_configuration : Attack_Configuration):
    """TODO: summary

    :param sec: required security level in bits
    :param initial_parameters: initial parameter set of search
    :param next_parameters: function yielding possibly multiple new parameter sets with previous parameter set as input
    :param parameter_cost: cost function of a parameter set used in the scheme to determine to order currently queued parameter sets. Use lib.unit_cost if sequence does not matter
    :param parameter_problem: function yielding possibly multiple problem instances with a paramter set as input

    :returns: parameter set fulfulling security condition
    """
    # TODO: check validity of parameters
    # TODO: test
    # TODO: LWE: search vs decision?

    # set parameter cost function for list sorting
    Parameter_Set.parameter_cost = parameter_cost

    problem.statistical_sec = sec # TODO add to other places, too, does that work?
    current_parameter_sets = [Parameter_Set(initial_parameters)]
    while current_parameter_sets:

        current_parameter_set = current_parameter_sets.pop().parameters # remove last
        i = 0; secure = True
        # TODO: possible to run parallel
        for problem_instance in parameter_problem(*current_parameter_set): 

            # TODO: logging?
            res = problem_instance.estimate_cost(sec=sec, attack_configuration=attack_configuration)
            if not res.is_secure:
                secure = False; break

        if secure and i > 0:
            # Only if all problem instances of a parameter set pass
            # TODO: logging?
            return (current_parameter_set, res) 
            
        # TODO: check if correct
        for parameter_set in next_parameters(*current_parameter_set):
            bisect.insort_left(current_parameter_sets, Parameter_Set(parameter_set))


if __name__ == "__main__":
    class Commandline:
        def doc(self):
            # requires sphinx (e.g. "pip install sphinx")
            os.system("sphinx-apidoc -o doc . usage_example.py") # EXCLUDE usage_example for now as it does not "compile" at all
            os.system("sphinx-build doc doc/html")

    fire.Fire(Commandline)