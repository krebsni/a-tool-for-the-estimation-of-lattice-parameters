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



from queue import Empty
from . import problem
from . import algorithms_and_config
from . import problem
import logging
from typing import Generator, Iterator
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
from estimate_all_schemes import cost_asymptotics
from estimate_all_schemes import estimator as est

oo = est.PlusInfinity()

## Logging ##
logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.DEBUG) # set to INFO to hide exceptions
# TODO: put in config file or so? param_search needs to be imported for logging level to be set (?)

# Utility # perhaps export if more is added in the future
def number_of_bits(v):
    if v == oo or v == -oo:
        return oo
    else:
        return ceil(log(abs(v), 2))


def unit_cost():
    """
    Unit cost for given parameter set
    """
    return 0 # ensure that new ones are added at the end
    # TODO: perhaps another generic search without unit cost


class ParameterSet():
    """
    Helper class to order parameter sets in list 
    """

    parameter_cost = unit_cost
    def __init__(self, parameters):
        self.parameters = parameters
    
    def __lt__(self, other):
        return ParameterSet.parameter_cost(*self.parameters) < ParameterSet.parameter_cost(*other.parameters) # TODO check


# is_secure and estimate functions are not really needed anymore... Functionality is provided by problem.estimate_cost
# TODO write new
def is_secure(parameter_problems : Iterator[problem.BaseProblem], sec, config : algorithms_and_config.EstimationConfiguration):
    return problem.estimate(parameter_problems=parameter_problems, config=config, sec=sec)

def generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem, 
        config : algorithms_and_config.EstimationConfiguration):
    """TODO: summary

    :param sec: required security level in bits
    :param initial_parameters: initial parameter set of search
    :param next_parameters: function yielding possibly multiple new parameter sets with previous parameter set as input
    :param parameter_cost: cost function of a parameter set used in the scheme to determine to order currently queued parameter sets. Use lib.unit_cost if sequence does not matter
    :param parameter_problem: function yielding possibly multiple problem instances with a paramter set as input

    :returns: parameter set fulfulling security condition
    """
    # TODO: check validity of parameters, or that if not proper exceptions are thrown 
    # TODO: test
    # TODO: LWE: search vs decision?

    # set parameter cost function for list sorting
    ParameterSet.parameter_cost = parameter_cost
    current_parameter_sets = [ParameterSet(initial_parameters)]
    while current_parameter_sets:
        current_parameter_set = current_parameter_sets.pop(0).parameters
        logger.info("----------------------------------------------------------------------------")
        logger.info(f"Checking next parameter set: {current_parameter_set}") # TODO: print nicely
        try:
            res = problem.estimate(parameter_problems=parameter_problem(*current_parameter_set), config=config, sec=sec)
            if res.is_secure:
                return {"parameters": current_parameter_set, "result": res}
        except problem.EmptyProblem:
            pass
        
        # check if correct
        for parameter_set in next_parameters(*current_parameter_set):
            bisect.insort_left(current_parameter_sets, ParameterSet(parameter_set))