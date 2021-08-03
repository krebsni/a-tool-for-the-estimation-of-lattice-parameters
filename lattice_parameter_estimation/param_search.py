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
from . import algorithms
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
import psutil
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
from estimator import oo

## Logging ##
logger = logging.getLogger(__name__)

# Utility # perhaps export if more is added in the future
def number_of_bits(v):
    if v == oo or v == -oo:
        return oo
    else:
        return ceil(log(abs(v), 2))


def unit_cost(*argv, **args):
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
def is_secure(parameter_problems : Iterator[problem.BaseProblem], sec, config : algorithms.Configuration):
    return problem.estimate(parameter_problems=parameter_problems, config=config, sec=sec)

def generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem, 
        config : algorithms.Configuration, scalar_parameters=False):
    """TODO: summary
    The search terminates after the best cost (``log(rop, 2)``) of some parameter set exceeds ``sec``. TODO: if (*parameter_set) > parameter_cost(next(next_parameters(*parameter_set))) not satisfied the solution may not be ideal...

    :param sec: required security level in bits
    :param initial_parameters: initial parameter set of search. Must be tuple or scalar. If it is a scalar, set ``scalar_parameters`` to ``True``. 
    :param next_parameters: generator function yielding (possibly multiple) new parameter sets with previous parameter set as input. Note that duplicate detection does not work if paramter_cost(*parameter_set) > parameter_cost(next(next_parameters(*parameter_set))). It is recommended to yield parameter sets in some ascending order. The function must yield a tuple or a scalar. If a scalar is yielded, set ``scalar_parameters`` to ``True``. 
    :param parameter_cost: cost function of a parameter set used in the scheme to determine to order currently queued parameter sets. Use lib.unit_cost if sequence does not matter
    :param parameter_problem: function yielding possibly multiple problem instances with a paramter set as input
    :scalar_parameters: True if parameter sets are scalars, else parameter sets must be tuples. 

    :returns: parameter set fulfulling security condition
    """
    # TODO: LWE: search vs decision?
    start = time.time()
    parameters = [initial_parameters]
    if scalar_parameters:
        costs = [parameter_cost(initial_parameters)]
    else:
        costs = [parameter_cost(*initial_parameters)]

    def insort(parameter_set):
        if scalar_parameters:
            cost = parameter_cost(parameter_set)
        else:
            cost = parameter_cost(*parameter_set)

        i = bisect.bisect_right(costs, cost)

        # only insert if not duplicate
        j = i - 1
        while j >= 0 and costs[j] == cost:
            if parameters[j] == parameter_set:
                return # duplicate
            j -= 1

        costs.insert(i, cost)
        parameters.insert(i, parameter_set)


    while parameters:
        current_parameter_set = parameters.pop(0)
        costs.pop(0)

        logger.info("----------------------------------------------------------------------------")
        logger.info(f"Checking next parameter set: {current_parameter_set}") # TODO: print nicely
        
        try:
            if scalar_parameters:
                res = problem.estimate(parameter_problems=parameter_problem(current_parameter_set), config=config, sec=sec)
            else:
                res = problem.estimate(parameter_problems=parameter_problem(*current_parameter_set), config=config, sec=sec)
            if res.is_secure:
                try:
                    log_rop = floor(float(log(res.cost["rop"], 2)))
                    if log_rop < 0:
                        log_rop = 0
                except:
                    logger.warning(f"Exception in calculating log_rop = float(log({res.cost['rop']}), 2). Assume that log_rop = oo.")
                    logger.debug(traceback.format_exc())
                    log_rop = oo
                duration = time.time() - start 
                logger.info("----------------------------------------------------------------------------")
                logger.info(f"Generic search successful (took {duration}s). Estimated security level is > {log_rop}.") # TODO: print more info?
                return {"parameters": current_parameter_set, "result": res}
        except problem.EmptyProblem:
            pass    
        
        if scalar_parameters:
            for parameter_set in next_parameters(current_parameter_set):
                insort(parameter_set)
        else:
            for parameter_set in next_parameters(*current_parameter_set):
                insort(parameter_set)
        
        # Check RAM
        perc_RAM = psutil.virtual_memory()[2]
        if perc_RAM > 95:
            logger.critical(f"RAM almost full {perc_RAM}. Terminating...")
            break
        else:
            logger.debug(f"{perc_RAM} % of RAM used.")