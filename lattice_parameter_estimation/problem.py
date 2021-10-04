r""" 
TODO: documentation
"""

from numpy.core.fromnumeric import var
from . import distributions
from . import algorithms
from . import norm
from abc import ABC, abstractmethod
from collections import OrderedDict
from typing import Generator, Iterable, List
import time
import sys
import os
import logging
import traceback
import multiprocessing as mp
from concurrent.futures import ThreadPoolExecutor
from queue import Empty
from functools import partial
import json
import sage.all 
from sage.functions.log import exp, log
from sage.functions.other import ceil, sqrt, floor, binomial
from sage.rings.all import QQ, RR
from sage.symbolic.all import pi, e
from sage.misc.functional import round
import estimator as est
oo = est.PlusInfinity()


## Logging ##
logger = logging.getLogger(__name__)
# info about running algorithms and results
alg_logger = logging.getLogger(logger.name + ".estimation_logging")
# exceptions from estimator
alg_exception_logger = logging.getLogger(logger.name + ".estimation_exception_logging")

## Configuration ##
ERROR_HANDLING_ON = True # if True try to deal with errors and not raise exceptions
REDUCE_PROBLEMS = True

## Helper Classes ##
class EmptyProblem(Exception):
    pass

class AllFailedError(Exception):
    pass

class BaseProblem():
    pass

## Helper class
class AlgorithmResult():
    """
    Encapsulates algorithm estimates.
    """
    def __init__(self, runtime, problem_instance, params, alg_name, c_name="", cost=est.Cost([("rop", oo)]), is_successful=True, error=None, is_insecure=False):
        """ 
        :param runtime: runtime [s]
        :param problem_instance: label of problem instance
        :param params: list of input parameters for algorithm
        :param alg_name: name of algorithm
        :param c_name: name of cost model
        :param cost: cost dict (:py:mod:`lattice_parameter_estimation.estimator.estimator.Cost` from lwe-estimator)
        :param is_successful: ``True`` if algorithm was successful
        :param error: string with error description
        :param is_insecure: must be ``True`` if found cost estimate violates security requirement
        """
        self.runtime = runtime
        self.problem_instance = problem_instance
        self.params = params
        self.alg_name = alg_name
        self.c_name = c_name
        self.cost = cost
        self.is_successful = is_successful
        self.error = error
        self.is_insecure = is_insecure
    
    def to_dict(self):
        """ 
        :returns: JSON-serializable dict
        """
        return {
            "inst": self.problem_instance,
            "alg_name": self.alg_name,
            "cost_model": self.c_name,
            "params": self.params,
            "sec": max(0, float(log(abs(self.cost["rop"]), 2).n())),
            "cost": str(self.cost),
            "runtime": self.runtime,
            "is_successful": self.is_successful,
            "is_insecure": self.is_insecure,
            "error": self.error
        }

    def __bool__(self):
        return self.is_secure

    def __str__(self) -> str:
        ret = self.str_no_err()
        if self.error is not None:
            ret += f"\nError: {self.error}"
        return ret
    
    def str_no_err(self) -> str:
        """ 
        :returns: string without error message.
        """
        if not self.is_successful:
            detail = f"insuccessful (took {str(self.runtime)}s) \n\tparams: {str(self.params)}"
        else:
            sec = max(0, float(log(abs(self.cost["rop"]), 2).n()))
            detail = f'{["secure", "insecure"][self.is_insecure]} (took {self.runtime:.1f}s): \n\tsec: {str(sec)}\n\tparams: {str(self.params)}'
        return f'\n\tEstimate for "{self.alg_name}"{["", " " + self.c_name][self.c_name != ""]} - {self.problem_instance} ' + detail


class AggregateEstimationResult():
    """
    Encapsulates aggregation of estimate results and automates is_secure check according to specified security strategy in config.
    
    TODO: Type of return value needed for overloaded lt-operator :class:`BaseProblem` instances.
    """
    def __init__(self, config : algorithms.Configuration, error="all_failed", runtime=0, problem_instances : List[BaseProblem] = []):
        """
        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`
        :param error: set to ``"all_failed"`` if no algorithm passes, can also be ``"timeout"`` and ``"early_termination"``
        :param runtime: list of runtime of algorithms run during estimation     
        :param problem_instances: pre-defined list of all problem instances (e.g. instance of :class:`MLWE`) for which estimates are run (used to check if result is secure, if not specified the list is dynamically created when results are added)

        :ivar error: error message
        :ivar is_insecure: ``True`` if aggregate result is insecure
        :ivar lowest_sec: lowest found security estimate
        :ivar runtime: total runtime
        """
        self.error = error
        self.is_insecure = False
        self.lowest_sec = oo
        self.alg_res_dict = {}
        for inst in problem_instances:
            self.alg_res_dict[inst] = []
        self.runtime = runtime
        self.config = config
        self._contains_res = False

    def add_algorithm_result(self, algorithm_result : AlgorithmResult):
        """ 
        Adds algorithm result and automatically updates ``is_insecure``, ``error``, and ``cost`` instance variables. 

        :param algorithm_result: instance of :class:`AlgorithmResult`
        """
        self._contains_res = True
        if algorithm_result.is_insecure:
            self.is_insecure = True
            self.error = algorithm_result.error # "early_termination" or "timeout"
        if algorithm_result.is_successful:
            self.error = None

        if algorithm_result.cost is not None:
            new_sec = max(0, log(abs(algorithm_result.cost["rop"]), 2).n()) # make sure this does not raise an exception
            if new_sec <= self.lowest_sec:
                self.lowest_sec = new_sec
        if not algorithm_result.problem_instance in self.alg_res_dict:
            self.alg_res_dict[algorithm_result.problem_instance] = []
        self.alg_res_dict[algorithm_result.problem_instance].append(algorithm_result)
    
    def add_aggragate_result(self, aggregate_result):
        """ 
        Adds aggregate result and automatically updates ``is_insecure``, ``error``, and ``cost`` instance variables. 

        :param algorithm_result: instance of :class:`AggregateEstimationResult`
        """
        if not aggregate_result.is_secure():
            self.is_insecure = True
        if aggregate_result.error != "all_failed": # => error is "early_termination" or "timeout"
            self.error = aggregate_result.error

        if aggregate_result.lowest_sec < self.lowest_sec:
            self.lowest_sec = aggregate_result.lowest_sec

        for inst in aggregate_result.alg_res_dict:
            if not inst in self.alg_res_dict:
                self.alg_res_dict[inst] = []
            self.alg_res_dict[inst].extend(aggregate_result.alg_res_dict[inst])

    def get_algorithm_result_dict(self, sort_by_rop=False, only_best_per_algorithm=False, only_successful=False):
        """
        Returns dict of that for each problem instance contains a list of estimation results corresponding to an algorithm and (not in all cases) a cost model. 

        :param sort_by_rop: if ``True`` list is sorted in ascending order by rop
        :param only_best_per_algorithm: if ``True`` only the best algorithm for each cost model is returned
        :param only_successful: only return estimate results for successful algorithms
        """
        if not self._contains_res:
            return self.alg_res_dict

        result_dict = {}
        for inst in self.alg_res_dict:
            result_dict[inst] = self.alg_res_dict[inst]

            if only_successful:
                result_dict[inst] = [x for x in result_dict[inst] if x.is_successful]

            if only_best_per_algorithm:
                alg_names = set()
                for alg_res in result_dict[inst]:
                    alg_names.add(alg_res.alg_name)
                best_results = {}
                for alg_name in alg_names:
                    best_results[alg_name] = min([x for x in result_dict[inst] if x.alg_name == alg_name], key=lambda x: x.cost["rop"])
                result_dict[inst] = list(best_results.values())

            if sort_by_rop:
                result_dict[inst] = sorted(result_dict[inst], key=lambda x: x.cost["rop"])

        return result_dict

    def is_secure(self):
        """
        Returns if secure according to security strategy in config
        """
        if self.is_insecure:
            return False
        
        for inst in self.alg_res_dict:
            if not self.alg_res_dict[inst]:
                return False

            if self.config.security_strategy == algorithms.ALL_SECURE:
                # TODO: x.is_insecure should not be necessary
                if not all([x.is_successful for x in self.alg_res_dict[inst]]):
                    return False

            elif self.config.security_strategy == algorithms.SOME_SECURE:
                if not any([x.is_successful for x in self.alg_res_dict[inst]]):
                    return False
                    
            elif not self.config.security_strategy == algorithms.NOT_INSECURE:
                raise ValueError("Security strategy in config improperly configured.")
        return True

    def to_dict(self, sort_by_rop=False, only_best_per_algorithm=False, only_successful=False):
        """ 
        Returns results in JSON-serializable dict.
        
        :param sort_by_rop: if ``True`` list is sorted in ascending order by rop
        :param only_best_per_algorithm: if ``True`` only the best algorithm for each cost model is returned
        :param only_successful: only return estimate results for successful algorithms
        """
        alg_result_dict = {}
        former_dict = self.get_algorithm_result_dict(sort_by_rop=sort_by_rop,   
            only_best_per_algorithm=only_best_per_algorithm, only_successful=only_successful)
        for inst in former_dict:
            alg_result_dict[inst] = [x.to_dict() for x in former_dict[inst]]
        res = {
            "alg_results": alg_result_dict,
            "error": self.error,
            "is_insecure": self.is_insecure,
            "lowest_sec": max(0, float(self.lowest_sec)),
            "runtime": self.runtime,
        }
        return res
    
    def save_as_JSON(self, filename, sort_by_rop=False, only_best_per_algorithm=False, only_successful=False):
        """ 
        Save results in file.
        
        :param filename: filename
        :param sort_by_rop: if ``True`` list is sorted in ascending order by rop
        :param only_best_per_algorithm: if ``True`` only the best algorithm for each cost model is returned
        :param only_successful: only return estimate results for successful algorithms
        """
        with open(filename + ".json", 'w') as fout:
            json.dump(self.to_dict(sort_by_rop=sort_by_rop, only_best_per_algorithm=only_best_per_algorithm, 
                        only_successful=only_successful), fout, indent=4)

    def __bool__(self):
        """ 
        Calls :meth:`is_secure`.
        """
        return self.is_secure()

    def __str__(self) -> str:
        error = ", Error: " + self.error if self.error is not None else ""
        return f'Estimates successful and {["insecure", "secure"][self.is_secure()]}' \
            + f' (took {self.runtime:.1f}s):' \
            + f' best sec={str(self.lowest_sec)}' + error


class BaseProblem(ABC):
    @abstractmethod
    def __init__(self):
        pass

    @abstractmethod
    def get_estimate_algorithms(self, config=None):
        pass

    # TODO: check, perhaps add other operators
    def __ge__(self, sec) -> AggregateEstimationResult:
        config = algorithms.Configuration() # use default config
        return estimate(parameter_problem=[self], config=config, sec=sec)

    def __gt__(self, sec) -> AggregateEstimationResult:
        config = algorithms.Configuration() # use default config
        return estimate(parameter_problem=[self], config=config, sec=sec + 1)

    def __lt__(self, sec) -> AggregateEstimationResult:
        return not self.__ge__(sec)

    def __le__(self, sec) -> AggregateEstimationResult:
        return not self.__gt__(sec)

    @abstractmethod
    def __str__(self):
        pass


def reduce_parameter_problems(parameter_problems : Iterable[BaseProblem], config : algorithms.Configuration) -> List[BaseProblem]:
        """ 
        Reduce iterable of parameter problems to easiest versions of SIS and LWE respectively according to the following hardness rules:

        For LWE, 
        * the larger n, the harder 
        * the larger q, the easier
        * the larger alpha, the harder 
        * the larger m, the easier (more samples)

        For SIS, 
        * the larger n, the harder
        * the larger q, the harder
        * the larger bound, the easier
        * the larger m, the easier

        Two problem instances might not be comparable with the above rules, hence the reduction is incomplete.

        :param parameter_problems: iterable over instances of :class:`BaseProblem`
        """
        parameter_problems = list(parameter_problems)
        if not REDUCE_PROBLEMS:
            return parameter_problems
        lwe_problems = [prob.to_LWE() for prob in parameter_problems if isinstance(prob, LWE)]
        sis_problems = [prob.to_SIS() for prob in parameter_problems if isinstance(prob, SIS)]

        def _easier_lwe(a : LWE, b : LWE) -> bool:
            if a.n <= b.n and a.q >= b.q \
                and a.error_distribution.get_alpha(q=a.q, n=a.n) <= b.error_distribution.get_alpha(q=b.q, n=b.n) \
                and a.m >= b.m:
                return True
            return False # does not mean that it is harder, maybe instances cannot be compared

        def _easier_sis(a : SIS, b : SIS) -> bool:
            # compare norms needed for algorithms
            test_L2 = algorithms.REDUCTION or algorithms.REDUCTION_RS in config.algorithms
            test_Loo = algorithms.COMBINATORIAL in config.algorithms
            if test_L2:
                is_larger_bound = a.bound.to_L2(a.n).value >= b.bound.to_L2(b.n).value
            if test_Loo:
                is_larger_bound_Loo = a.bound.to_Loo(a.n).value >= b.bound.to_Loo(b.n).value
                if test_L2:
                    is_larger_bound = is_larger_bound and is_larger_bound_Loo
                else:
                    is_larger_bound = is_larger_bound_Loo
            
            if a.n <= b.n and a.q <= b.q \
                and is_larger_bound \
                and a.m >= b.m:
                return True
            return False # does not mean that it is harder, maybe instances cannot be compared

        lwe_set = set()
        for prob in lwe_problems:
            # determine easiest problem relative to prob (there may be different problems that can't be compared)
            easiest_prob = prob 
            for cmp_prob in lwe_problems:
                if _easier_lwe(cmp_prob, easiest_prob):
                    easiest_prob = cmp_prob
            lwe_set.add(easiest_prob)
        sis_set = set()
        for prob in sis_problems:
            # determine easiest problem relative to prob (there may be different problems that can't be compared)
            easiest_prob = prob 
            for cmp_prob in sis_problems:
                if _easier_sis(cmp_prob, easiest_prob):
                    easiest_prob = cmp_prob
            sis_set.add(easiest_prob)
        return list(lwe_set | sis_set)


## Estmation ##
def algorithms_executor(algs, config : algorithms.Configuration, sec=None, res_queue=None):
    """Executes list of estimate algorithms in ``algs``. Results are written in ``res_queue`` as instances of :class:`AlgorithmResult` if set (in parallel execution).

    :param algs: list of tuples as ``[(problem_instance, alg)]``, where alg is dict as ``{"algname": "a1", "cname": "c1", "algf": f, "prio": 0, "cprio": 0, "inst": "LWE"}`` (item in list returned from :meth:`BaseProblem.get_estimate_algorithms`)
    :param sec: bit security parameter
    :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`
    :param res_queue: for multiprocessing support, instance of :py:mod:`multiprocessing.Queue`

    :returns: ``None`` if res_queue is set, else an instance of :class:`AggregateEstimationResult`
    """
    start = time.time()
    results = AggregateEstimationResult(config=config)
    results = []
    early_termination = False
    timeout = False
    for alg_tuple in algs:
        # for not parallel TODO
        if time.time() - start > config.timeout: # won't prevent algorithm from looping infinitively
            timeout = True
            break 

        # alg_tuple is tuple (problem_instance, alg)
        inst = alg_tuple[0]
        alg = alg_tuple[1]
        algf = alg["algf"]
        def conversion(k, v):
            if k in ["alpha"]:
                return k, float(v)
            else:
                return k, v
        params = dict([conversion(k, algf.keywords[k]) for k in ["secret_distribution", "n", "m", "q", "alpha", "bound"] if k in set(algf.keywords)])
        cname = f'({alg["cname"]})' if alg["cname"] != "" else ""
        alg_logger.info(str(os.getpid()) + f' Running algorithm {alg["algname"]} {cname}... Parameters: {str(params)}')

        start_alg = time.time()
        cost = est.Cost([("rop", oo)]) # else finding best doesn't work
        error = None
        # TODO: could be encapsulated in AlgorithmResult
        is_insecure = False
        is_successful = False
        try:
            cost = algf()
            if cost == None:
                cost = est.Cost([("rop", oo)])
                raise RuntimeError("Bug in estimator (returned None). No solution found.")
            if sec and cost["rop"] < 2**sec:
                is_insecure = True
            is_successful = True
        except algorithms.IntractableSolution:
            # from SIS algorithms
            cost = est.Cost([("rop", oo)])
            is_successful = True
            if sec and cost["rop"] < 2**sec:
                is_insecure = True
            error = "intractable"
            
        except algorithms.TrivialSolution:
            # from SIS algorithms
            cost = est.Cost([("rop", RR(1))])
            if sec and sec > 0:
                is_insecure = True
            is_successful = True
            error = "trivial"
        except:
            # something went wrong
            error = traceback.format_exc()

        runtime = time.time() - start_alg
        alg_res = AlgorithmResult(
            runtime=runtime,
            problem_instance=inst,
            params=params,
            alg_name=alg["algname"],
            c_name= alg["cname"],
            cost=cost,
            is_successful=is_successful,
            error=error,
            is_insecure=is_insecure
        )

        if not is_successful:
            alg_logger.error(str(alg_res))
        else:
            alg_logger.info(str(alg_res))

        if res_queue is None: 
            results.append(alg_res)
        else:
            res_queue.put(alg_res)
        if is_insecure or (config.security_strategy == algorithms.ALL_SECURE \
                and is_successful == False): 
            # early termination
            break

        
    if res_queue is None:
        # no multiprocessing
        total_runtime = time.time() - start
        agg_result = AggregateEstimationResult(config=config)
        agg_result.runtime = total_runtime
        for alg_res in results:
            agg_result.add_algorithm_result(alg_res)
        if early_termination: # if all_failed no early termination
            agg_result.error = "early_termination"
        if timeout:
            agg_result.error = "timeout"
        return agg_result

    return True # TODO try without


def estimate(
        parameter_problems : Iterable[BaseProblem], 
        config : algorithms.Configuration, sec=None
    ) -> AggregateEstimationResult:
    """ 
    Runs estiamtes for problem instances in ``parameter_problems``.

    First, the list of problem instances is reduced to the simplest version of LWE and SIS respectively. Then, a list algorithm instances are created and executed sequentially or concurrently by :meth:`algorithms_executor` according to the configuration in ``config``. 

    Estimate logging can be configured in in :py:mod:`lattice_parameter_estimation.Logging`.

    :param parameter_problems: iterable over instances of :class:`BaseProblem`. If empty or no algorithms can be created :class:`EmptyProblem` is raised.
    :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`
    :param sec: optional bit security parameter. If set, early termination is supported once insecure estimate is found. 

    :returns: instance of :class:`AggregateEstimationResult`
    """
    # Create algorithm list of tuples (problem_instance, alg)
    algs = [] 
    parameter_problems = reduce_parameter_problems(parameter_problems, config)
    
    for problem_instance in parameter_problems:
        try:
            inst_algs = problem_instance.get_estimate_algorithms(config=config)
        except NotImplementedError as e:
            if ERROR_HANDLING_ON: # TODO
                logger.error(e)
            else:
                raise e
        if not inst_algs:
            raise EmptyProblem(f"No algorithm for instance {str(problem_instance)}. Perhaps algorithm in Configuration was not set properly.")
        for alg in inst_algs:
            algs.append((problem_instance.label, alg)) # TODO maybe find better description for inst or change __str__
    if not algs: # no instance
        raise EmptyProblem("Could not find any algorithms for given input parameters.")

    # sort first by algorithm priority, then by cost model priority
    algs = sorted(algs, key=lambda a: (a[1]["prio"], a[1]["cprio"])) 

    start = time.time()
    if not config.parallel:
        num_procs = 1 # needed to terminate infinite loops
    elif config.num_cpus is None:
        num_procs = min(mp.cpu_count(), len(algs))
    else:
        num_procs = config.num_cpus

    # evenly distribute algorithms according to sorting among #NUM_CPUS lists
    split_list = num_procs * [None]
    for j in range(num_procs):
        split_list[j] = []
    for i in range(len(algs)):
        split_list[i % num_procs].append(algs[i])

    alg_logger.debug(f"Starting {num_procs} processes for {len(algs)} algorithms...")
    alg_logger.debug("Running estimates " + ["without", "with"][bool(sec)] + " early termination...") # TODO
    p = [None]*len(split_list)
    results = AggregateEstimationResult(config=config, 
                                        problem_instances=[x.label for x in parameter_problems])
    result_queue = mp.Queue()
    async_res = []
    for i in range(len(split_list)):
        # TODO NEW VERSION - not working
        # pool = mp.Pool(processes=len(split_list)) # TODO outsource in global var
        # async_res.append(
        #     pool.apply_async(
        #         func=algorithms_executor, 
        #         args=(split_list[i], config, sec, result_queue)
        #     )
        # )
        # map_async could also work

        # TODO OLD VERSION
        p[i] = mp.Process(target=algorithms_executor, args=(split_list[i], config, sec, result_queue))
        p[i].start()
        alg_logger.debug(str(p[i].pid) + " started...")
    
    terminated = False
    while not terminated:
        try:
            # Check if all processes finished their calculation
            
            # TODO OLD VERSION
            all_done = True
            for i in range(len(split_list)):
                if p[i].is_alive():
                    all_done = False
                    break
            if all_done:
                terminated = True
                for i in range(len(split_list)):
                    p[i].join()
                    result_queue.close()
                    terminated = True
                break

            # Try to get result
            alg_res = result_queue.get(block=True, timeout=0.5) # timeout necessary as process that wrote result in queue may still be alive in the above check 
            results.add_algorithm_result(alg_res)

            if sec and results.is_insecure: # is_secure may not be right as tests not complete
                alg_logger.debug("Received insecure result. Terminate all other processes.")
                # insecure result obtained => terminate all other processes
                results.error = "early_termination"
                for i in range(len(split_list)):
                    p[i].terminate()
                    p[i].join()
                    # data put into queue during terminate may become corrupted => just close it
                    result_queue.close()
                    terminated = True
        except Empty: # result not yet available
            if time.time() - start > config.timeout:
                # Computation too long, result not expected anymore
                for i in range(len(split_list)):
                    p[i].terminate() 
                    p[i].join()
                    result_queue.close()
                terminated = True
                
                if sec and results.is_secure():
                    if config.security_strategy == algorithms.ALL_SECURE:
                        # since at least one is not successful => All_SECURE = FALSE 
                        results.is_insecure = True
                    
                results.error = "timeout"
                message = f"Timeout during estimation after {config.timeout}s. Try to specify longer timeout in config. If no result is obtained, one of the algorithms might not terminate for the given parameter set."
                if not results.is_secure():
                    raise TimeoutError(message)
                        
    if results.error == "all_failed": # TODO: don't raise exception 
        raise AllFailedError("All estimate algorithms failed")

    runtime = time.time() - start
    results.runtime = runtime
    alg_logger.info(str(results)) 
    return results


## LWE and its variants ##
class LWE(BaseProblem):
    """ 
    Learning with Errors (LWE) problem class used to create a list of algorithms from lwe-estimator :cite:`APS15` for cost estimation.
    """
    _counter = 1

    def __init__(self, n, q, m, secret_distribution : distributions.Distribution, error_distribution : distributions.Distribution, variant="LWE", label=None): 
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :py:mod:`lattice_parameter_estimation.distributions.Gaussian` or :py:mod:`lattice_parameter_estimation.distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :py:mod:`lattice_parameter_estimation.distributions.Gaussian` or :py:mod:`lattice_parameter_estimation.distributions.Uniform`)
        :param variant: for internal use to distinguish variants
        :param label: short string to refer to describe the problem name, e.g. ``"LWE-Regev"``
        """
        # check soundness of parameters
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")

        if label is None:
            label = variant + str(self._counter)
            self._counter += 1
        self.label = label
        self.variant = variant
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def get_estimate_algorithms(self, config : algorithms.Configuration):
        r"""
        Compute list of estimate functions from the lwe-estimator :cite:`APS15` on the LWE instance according to the attack configuration.

        The priorities are assigned as follows:

        .. list-table:: Algorithm Priorities
            :header-rows: 1

            * - Algorithm
              - Priority
              - Comment
            * - mitm
              - 5
              - fastest, high cost estimate, as prefilter
            * - primal-usvp
              - 10
              - fast, low cost estimates
            * - dual
              - 20
              - fast, estimates may be slightly higher than primal-usvp
            * - dual-no-lll
              - 30
              - fast, estimates may be slightly higher than dual
            * - bkw-coded
              - 90
              - slow, somtimes very low cost estimate (for small stddev), does not always yield results
            * - primal-decode
              - 100
              - slow, estimates often higher than faster algorithms
            * - arora-gb
              - 200
              - extremely slow, often higher estimates, does not always yield results

        .. figure:: ../tests_for_optimization/algorithm_runtime_cost/LWE_stddev=0,125_plots_200s.png
            :align: center
            :figclass: align-center

            LWE instance with :math:`\sigma=0.125,\; m=\infty, \; 2^{n} < q < 2^{n+1}`

        .. figure:: ../tests_for_optimization/algorithm_runtime_cost/LWE_stddev=2,828_plots_200s.png
            :align: center
            :figclass: align-center

            LWE instance with :math:`\sigma=2.828,\; m=\infty, \; 2^{n} < q < 2^{n+1}`

        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`

        :returns: list of algorithms, e.g. ``[{"algname": "a1", "cname": "c1", "algf": f, "prio": 0, "cprio": 0, "inst": "LWE"}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime) and "cprio" of the cost model with lower expected cost estimate for lower priorities
        """         
        secret_distribution = self.secret_distribution._convert_for_lwe_estimator() 
        alpha = RR(self.error_distribution.get_alpha(q=self.q, n=self.n))
        # TODO: if secret is normal, but doesn't follow noise distribution, not supported by estimator => convert to uniform?
        if secret_distribution == "normal" and self.secret_distribution.get_alpha(q=self.q, n=self.n) != alpha:
            raise NotImplementedError("If secret distribution is Gaussian it must follow the error distribution. Differing Gaussians not supported by lwe-estimator at the moment.") # TODO: perhaps change

        cost_models = config.reduction_cost_models()

        algs = []
        # Choose algorithms. Similar to estimate_lwe function in estimator.py
        for reduction_cost_model in cost_models:
            cost_model = reduction_cost_model["cost_model"]
            success_probability = reduction_cost_model["success_probability"]
            cname = reduction_cost_model["name"]
            cprio = reduction_cost_model["prio"]

            if "usvp" in config.algorithms:
                if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                    # Try guessing secret entries via drop_and_solve
                    algs.append({"algname": "primal-usvp-drop", 
                                    "cname": cname, 
                                    "algf": partial(est.drop_and_solve, est.primal_usvp, 
                                                    postprocess=False, decision=False, rotations=False, 
                                                    reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 10,
                                    "cprio": cprio,
                                    "inst": self.variant})
                else: # TODO: can drop and solve yield worse results than standard decode?
                     algs.append({"algname": "primal-usvp", 
                                    "cname": cname, 
                                    "algf": partial(est.primal_usvp, 
                                                    reduction_cost_model=cost_model, n=self.n, 
                                                    alpha=alpha, q=self.q, m=self.m,
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 10,
                                    "cprio": cprio,
                                    "inst": self.variant})
            
            if "dual" in config.algorithms:
                if est.SDis.is_ternary(secret_distribution): # TODO can drop and solve yield worse results than standard?
                    # Try guessing secret entries via drop_and_solve
                    algs.append({"algname": "dual-scale-drop", 
                                    "cname": cname, 
                                    "algf": partial(est.drop_and_solve, est.dual_scale, 
                                                    postprocess=True, rotations=False, use_lll=True, 
                                                    reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 20,
                                    "cprio": cprio,
                                    "inst": self.variant})
                elif est.SDis.is_small(secret_distribution):
                    algs.append({"algname": "dual-scale", 
                                    "cname": cname, 
                                    "algf": partial(est.dual_scale, 
                                                    use_lll=True, reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 20,
                                    "cprio": cprio,
                                    "inst": self.variant})                                                               
                else:
                    algs.append({"algname": "dual", 
                                    "cname": cname, 
                                    "algf": partial(est.dual, reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 20,
                                    "cprio": cprio,
                                    "inst": self.variant})

            if "dual-without-lll" in config.algorithms:
                if est.SDis.is_ternary(secret_distribution): # TODO can drop and solve yield worse results than standard?
                    # Try guessing secret entries via drop_and_solve
                    algs.append({"algname": "dual-scale-drop-without-lll", 
                                    "cname": cname, 
                                    "algf": partial(est.drop_and_solve, est.dual_scale, 
                                                    postprocess=True, rotations=False, use_lll=False, 
                                                    reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 30,
                                    "cprio": cprio,
                                    "inst": self.variant})
                elif est.SDis.is_small(secret_distribution):
                    algs.append({"algname": "dual-scale-without-lll", 
                                    "cname": cname, 
                                    "algf": partial(est.dual_scale, 
                                                    use_lll=False, reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 30,
                                    "cprio": cprio,
                                    "inst": self.variant})                                                                
                elif "dual" not in config.algorithms: # else this algorithm will be run twice
                    algs.append({"algname": "dual-without-lll", 
                                    "cname": cname, 
                                    "algf": partial(est.dual, reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 30,
                                    "cprio": cprio,
                                    "inst": self.variant})

            if "decode" in config.algorithms:
                # TODO: Runtime much worse than primal-usvp, may yield better values for small n (Regev scheme n < 256?)
                # TODO: Could be used when early termination is on perhaps, then it would only be called when all other tests succeed?
                if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                    algs.append({"algname": "primal-decode-drop", 
                                    "cname": cname, 
                                    "algf": partial(est.drop_and_solve, est.primal_decode, 
                                                    postprocess=False, decision=False, rotations=False, 
                                                    reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 100,
                                    "cprio": cprio,
                                    "inst": self.variant})
                else: # TODO: can drop and solve yield worse results than standard decode?
                    algs.append({"algname": "primal-decode", 
                                    "cname": cname, 
                                    "algf": partial(est.primal_decode, reduction_cost_model=cost_model, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 100,
                                    "cprio": cprio,
                                    "inst": self.variant})

        # attacks without reduction cost model
        if "mitm" in config.algorithms: # estimates are very bad but very fast, so no need to exclude 
            algs.append({"algname": "mitm", 
                            "cname": "", 
                            "algf": partial(est.mitm, n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                            secret_distribution=secret_distribution, 
                                            success_probability=success_probability),
                            "prio": 5,
                            "cprio": 5,
                            "inst": self.variant})
            
        if "coded-bkw" in config.algorithms: # sometimes slow but may yield good results
            algs.append({"algname": "coded-bkw", 
                            "cname": "", 
                            "algf": partial(est.bkw_coded, n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                            secret_distribution=secret_distribution, 
                                            success_probability=success_probability),
                            "prio": 90, 
                            "cprio": 0,
                            "inst": self.variant})

        if "arora-gb" in config.algorithms: # slow and bad results
            if est.SDis.is_sparse(secret_distribution) and est.SDis.is_small(secret_distribution):
                algs.append({"algname": "arora-gb-drop", 
                                "cname": "", 
                                "algf": partial(est.drop_and_solve, est.arora_gb, rotations=False, 
                                                n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                secret_distribution=secret_distribution, 
                                                success_probability=success_probability),
                                "prio": 200, 
                                "cprio": 0, 
                                "inst": self.variant})
            elif secret_distribution != "normal" and est.SDis.is_small(secret_distribution): # switch_modulus does not work for normal sec_dis
                algs.append({"algname": "arora-gb-switch-modulus", 
                                "cname": "", 
                                "algf": partial(est.switch_modulus, est.arora_gb,
                                                n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                secret_distribution=secret_distribution, 
                                                success_probability=success_probability),
                                "prio": 200, 
                                "cprio": 0,
                                "inst": self.variant})
            else:
                algs.append({"algname": "arora-gb", 
                                "cname": "", 
                                "algf": partial(est.arora_gb,
                                                n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                secret_distribution=secret_distribution, 
                                                success_probability=success_probability),
                                "prio": 200, 
                                "cprio": 0,
                                "inst": self.variant})
        return algs

    def to_LWE(self):
        return self

    def __str__(self):
        # TODO
        return f"LWE [n={str(self.n)}, q={str(self.q)}, m={str(self.m)}, sec_dis={str(self.secret_distribution._convert_for_lwe_estimator())}, err_dis={str(float(self.error_distribution.get_alpha(q=self.q, n=self.n)))}]"


class MLWE(LWE):
    """ 
    Module Learning with Errors (MLWE) problem class used to create a list of algorithms from lwe-estimator :cite:`APS15` for cost estimation.
    """
    _counter = 1
    
    def __init__(self, n, d, q, m, secret_distribution : distributions.Distribution, error_distribution : distributions.Distribution, label=None, variant="MLWE"):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :py:mod:`lattice_parameter_estimation.distributions.Gaussian` or :py:mod:`lattice_parameter_estimation.distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :py:mod:`lattice_parameter_estimation.distributions.Gaussian` or :py:mod:`lattice_parameter_estimation.distributions.Uniform`)
        :param variant: for internal use to distinguish variants
        :param label: short string to refer to describe the problem name, e.g. ``"LWE-Regev"``
        """
        # check soundness of parameters
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        
        if label is None:
            label = variant + str(self._counter)
            self._counter += 1
        self.label = label
        self.variant = variant
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def get_estimate_algorithms(self, config : algorithms.Configuration, use_reduction=False):
        r"""
        Compute list of estimate functions on the MLWE instance according to the attack configuration.

        If use_reduction is `False`, the cost is estimated for an LWE instance with dimension :math:`n=n \cdot d`. Else, the MLWE instance will be reduced to RLWE according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 1, note: :cite:`KNK20b` contains error in exponent of q):

        If we take :math:`k = d`, then there exists an efficient reduction from :math:`\textit{M-SLWE}_{m,q, \Psi \leq \alpha}^{R^d}\left(\chi^d\right)` to :math:`\textit{R-SLWE}_{m,q^d, \Psi \leq \alpha\cdot n^2\cdot\sqrt{d}}^{R}\left(U(R_q^\vee)\right)` with controlled error rate :math:`\alpha`.

        Note that the reduction only works for Search-MLWE TODO: find reduction for decision-MLWE?

        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`
        :param use_reduction: specify if reduction to RLWE is used

        :returns: list of algorithms, e.g. ``[{"algname": "a1", "cname": "c1", "algf": f, "prio": 0, "cprio": 0, "inst": "MLWE"}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        # TODO: check if correct
        use_reduction = False
        if use_reduction:
            raise NotImplementedError()
            alpha_MLWE = self.error_distribution.get_alpha()
            alpha_RLWE = RR(alpha_MLWE * self.n**2 * sqrt(self.d))
            q_RLWE = self.q**self.d
            secret_distribution_RLWE = distributions.Uniform(0, self.q) # TODO: is this correct?
            error_distribution_RLWE = distributions.Gaussian_alpha(alpha_RLWE, q_RLWE) # TODO: componentwise or L2?
            # TODO how to do RLWE?
            rlwe = RLWE(n=self.n, q=q_RLWE, m=self.m, secret_distribution=secret_distribution_RLWE, 
                                error_distribution=error_distribution_RLWE)

            return rlwe.get_estimate_algorithms(config=config,       
                                        use_reduction=use_reduction)
            
        else:
            lwe = LWE(n=self.n*self.d, q=self.q, m=self.m*self.n, secret_distribution=self.secret_distribution,    
                        error_distribution=self.error_distribution, variant="MLWE", label=self.label)
            return lwe.get_estimate_algorithms(config=config)

    def to_LWE(self):
        """
        :returns: LWE instance with parameters :math:`n=n \cdot d` and :math:`m=m \cdot n`
        """
        return LWE(n=self.n*self.d, q=self.q, m=self.m*self.n, secret_distribution=self.secret_distribution,    
                    error_distribution=self.error_distribution, variant="MLWE", label=self.label)

    def __str__(self):
        # TODO
        return "MLWE instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution._convert_for_lwe_estimator())  \
            + ", error_distribution=" + str(self.error_distribution._convert_for_lwe_estimator()) + ")"


class RLWE(LWE):
    """ 
    Ring Learning with Errors (RLWE) problem class used to create a list of algorithms from lwe-estimator :cite:`APS15` for cost estimation.
    """
    _counter = 1

    def __init__(self, n, q, m, secret_distribution : distributions.Distribution, error_distribution : distributions.Distribution, variant="RLWE", label=None):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (subclass of :py:mod:`lattice_parameter_estimation.distributions.Gaussian` or :py:mod:`lattice_parameter_estimation.distributions.Uniform`)
        :param error_distribution: secret distribution (subclass of :py:mod:`lattice_parameter_estimation.distributions.Gaussian` or :py:mod:`lattice_parameter_estimation.distributions.Uniform`)
        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`
        :param variant: for internal use to distinguish variants
        :param label: short string to refer to describe the problem name, e.g. ``"LWE-Regev"``
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")

        if label is None:
            label = variant + str(self._counter)
            self._counter += 1
        self.label = label
        self.variant = variant
        ## interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6] TODO: check 
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def get_estimate_algorithms(self, config : algorithms.Configuration):
        r"""
        Compute list of estimate functions on the RLWE instance according to the attack configuration by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6. 

        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`
        :param use_reduction: specify if reduction to RLWE is used

        :returns: list of algorithms, e.g. ``[{"algname": "a1", "cname": "c1", "algf": f, "prio": 0, "cprio": 0, "inst": "RLWE"}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        lwe = LWE(n=self.n, q=self.q, m=self.m*self.n, secret_distribution=self.secret_distribution,    
                    error_distribution=self.error_distribution, variant="RLWE", label=self.label)
        return lwe.get_estimate_algorithms(config=config)

    def to_LWE(self):
        """
        :returns: LWE instance with parameters :math:`n=n` and :math:`m=m \cdot n`
        """
        return LWE(n=self.n, q=self.q, m=self.m*self.n, secret_distribution=self.secret_distribution,    
                    error_distribution=self.error_distribution, variant="RLWE", label=self.label)

    def __str__(self):
        # TODO
        return "RLWE instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution._convert_for_lwe_estimator())  \
            + ", error_distribution=" + str(self.error_distribution._convert_for_lwe_estimator()) + ")"


class StatisticalGaussianMLWE():
    r"""
    Statistically secure MLWE over Gaussian distribution according to :cite:`LPR13`.
    
    Mapping of parameters in paper to use here:
    
    ============================= =========== ========================================
    Parameters in :cite:`LPR13`   Use Here    Represents
    ============================= =========== ========================================
    :math:`q`                     :math:`q`   modulus
    :math:`l`                     :math:`m+d` width of matrix :math:`\mathbf{A}`
    :math:`k`                     :math:`m`   height of matrix :math:`\mathbf{A}`
    :math:`n`                     :math:`n`   degree of polynomial
    ============================= =========== ========================================

    Then Corollary 7.5 combined with Theorem 7.4 in :cite:`LPR13` reads as follows:
    Let :math:`\mathcal{R}` be the ring of integers in the :math:`m'`th cyclotomic number field :math:`K` of degree :math:`n`, and :math:`q \geq 2` an integer. 
    For positive integers :math:`m \leq m + d \leq \text{poly}(n)`, let :math:`\mathbf{A} = [ \mathbf{I}_{[m]} \mid \bar{\mathbf{A}}] \in (\mathcal{R}_q)^{[m] \times [m+d]}`, where :math:`\mathbf{I}_{[m]} \in (\mathcal{R}_q)^{[m] \times [m]}` is the identity matrix and :math:`\bar{\mathbf{A}} \in (\mathcal{R}_q)^{[m] \times [d]}` is uniformly random. 
    Then with probability :math:`1 - 2^{-\Omega(n)}` over the choice of :math:`\bar{\mathbf{A}}`, the distribution of :math:`\mathbf{A}\mathbf{x} \in (\mathcal{R}_q)^{[m]}` where each coordinate of :math:`\mathbf{x} \in (\mathcal{R}_q)^{[m+d]}` is chosen from a discrete Gaussian distribution of paramete :math:`r > 2n \cdot q^{m / (m+d) + 2/(n (m+d))}` over :math:`\mathcal{R}`, satisfies that the probability of each of the :math:`q^{n m}` possible outcomes is in the interval :math:`(1 \pm 2^{-\Omega(n)}) q^{-n }` (and in particular is within statistical distance :math:`2^{-\Omega(n)}` of the uniform distribution over :math:`(\mathcal{R}_q)^{[m]}`). 
    
    :ivar min_sigma: minimum :math:`\sigma` (standard deviation) required for statistically secure MLWE
    :ivar sec: set to parameter sec if sec is specified in constructor, else set to n
    """

    def __init__(self, n, d, q, m, sec=None):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        # TODO check parameters
        if sec and sec > n:
            raise ValueError("sec parameter must be greater than degree of polynomial n. Given parameters are not statistically secure.")

        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.sec = sec
        min_s = RR(2 * n * q**(m / (m + d) + 2 / (n * (m + d))))
        self.min_sigma = est.stddevf(min_s)
        
        if self.sec:
            self.sec = sec # we choose sec, not n as we possibly need it for Gaussian to bound conversion
        else:
            self.sec = n
        
    def get_secret_distribution_min_width(self):
        # TODO: auch bei StatisticalMSIS
        return distributions.GaussianSigma(self.min_sigma, q=self.q, componentwise=True, sec=self.sec) 


class StatisticalGaussianMatrixMLWE(StatisticalGaussianMLWE):
    r"""
    Statistically secure MLWE over Gaussian distribution according to :cite:`LPR13`.

    For more details, see :class:`StatisticalGaussianMLWE`.

    :ivar min_sigma: minimum :math:`\sigma` (standard deviation) required for statistically secure MLWE
    :ivar sec: set to parameter sec if sec is specified in constructor, else set to n
    """

    def __init__(self, n, q, width, height, sec=None):
        r"""
        :param n: degree of polynomial
        :param q: modulus
        :param width: width of matrix :math:`\mathbf{A}`
        :param height: height of matrix :math:`\mathbf{A}`
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, q=q, d=width-height, m=height, sec=sec)


class StatisticalGaussianRLWE(StatisticalGaussianMLWE):
    r"""
    Statistically secure RLWE over Gaussian distribution with invertible elements :cite:`LPR13`. 
    
    For details, see :class:`StatisticalGaussianMLWE` with module dimension :math:`d=1`.

    :ivar min_sigma: minimum :math:`\sigma` (standard deviation) required for statistically secure MLWE
    :ivar sec: set to parameter sec if sec is specified in constructor, else set to n
    """
    def __init__(self, n, q, m, sec=None):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, d=1, q=q, m=m, sec=sec)


class StatisticalUniformMLWE():
    r"""
    Statistically secure MLWE over Uniform distribution with invertible elements :cite:`BDLOP18`.

    MLWE problem instance where samples :math:`(\mathbf{A}', h_{\mathbf{A}'}(y))` are within statistical distance :math:`2^{-sec}` of :math:`(\mathbf{A}', \mathbf{u})` for uniform :math:`\mathbf{u}`.

    Mapping of parameters in paper to use here:

    ============================= =========== ============================================================
    Parameters in :cite:`BDLOP18` Use Here    Represents
    ============================= =========== ============================================================
    :math:`q`                     :math:`q`   modulus
    :math:`k`                     :math:`m+d` width of matrix :math:`[ \mathbf{I}_n \; \mathbf{A}' ]` 
    :math:`n`                     :math:`m`   height of matrix :math:`[ \mathbf{I}_n \; \mathbf{A}' ]` 
    :math:`d`                     :math:`d_2` variable
    :math:`N`                     :math:`n`   degree of polynomial
    ============================= =========== ============================================================

    Lemma (:cite:`BDLOP18` Lemma 4): Let :math:`1 < d_2 < n` be a power of 2. If :math:`q` is a prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)` and 

    .. math::

        q^{m/(m+d)} \cdot 2^{2 sec/((m+d)\cdot n)} \leq 2 \beta < \frac{1}{\sqrt{d_2}} \cdot q^{1/d_2}

    then any (all-powerful) algorithm :math:`\mathcal{A}` has advantage at most :math:`2^{-sec}` in solving :math:`\text{DKS}_{m,m+d,\beta}^\infty`, where :math:`\text{DKS}^\infty` is the decisional knapsack problem in :math:`L_\infty`-norm. 

    Hence, we have: 

    .. math::

        \beta_{min} = \frac{q^{m/(m+d)} \cdot 2^{2 sec/((m+d)\cdot n)}}{2}

        \beta_{max} = \frac{1}{2\sqrt{d_2}} \cdot q^{1/d_2} - 1

    TODO: explain ho to arrive at 2*sec instead of 256 

    :ivar min_beta: :math:`\beta_{min}`
    :ivar max_beta: :math:`\beta_{max}`
    """
    def __init__(self, sec, n, d, q, m, d_2=None):
        r"""
        :param sec: required bit security of MLWE instance
        :param n: degree of polynomial
        :param d: rank of module (width of matrix :math:`\mathbf{A}'` in :cite:`BDLOP18`)
        :param q: modulus, must be prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)`
        :param m: number of samples (height of matrix :math:`\mathbf{A}'` in :cite:`BDLOP18`)
        :param d_2: :math:`1 < d_2 < N` and :math:`d_2` is a power of 2
        """
        if d_2 is None:
            d_2 = StatisticalUniformMLWE.find_d(q, n)

        # TODO: check prerequisites?
        self.n = n
        self.q = q
        self.m = m
        self.d = d
        self.d_2 = d_2
        min_beta = RR(q**(m / (m + d)) * 2**(2 * sec / ((m + d) * n)) / 2)
        max_beta = RR(1 / (2 * sqrt(d_2)) * q**(1 / d_2)) - 1

        if min_beta >= max_beta:
            logger.warning("Could not find (min_beta, max_beta) such that min_beta < max_beta.")

        self.min_beta = norm.Lp(min_beta, oo, n * d)
        self.max_beta = norm.Lp(max_beta, oo, n * d)

    def get_beta_bounds(self):
        """
        :returns: tuple (min_beta, max_beta), betas are instances of :py:mod:`lattice_parameter_estimation.norm.Lp`
        """
        return (self.min_beta, self.max_beta)

    def find_d(q, n):
        r"""
        Find :math:`d` that is a power of 2 and satisfies :math:`1 < d < n`  such that the prime :math:`q` is congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)`  
        
        :param q: prime
        :param n: upper bound of d (degree of polynomial)
        """
        d = 2
        while d < n:
            if (q % (4 * d)) == (2 * d + 1):
                return d
            else:
                d *= 2
        raise ValueError("Could not find d such that 1 < d < n power of 2 and q congruent to 2d + 1 (mod 4d). q=" + str(q) + ", n=" + str(n) + ". Try again or call constructor with d_2.")   


class StatisticalUniformMatrixMLWE(StatisticalUniformMLWE):
    r"""
    Statistically secure MLWE over Uniform distribution with invertible elements :cite:`BDLOP18`.

    For more details, see :class:`StatisticalUniformMLWE`.

    :ivar min_beta: :math:`\beta_{min}`
    :ivar max_beta: :math:`\beta_{max}`
    """
    def __init__(self, sec, n, q, width, height, d_2=None):
        r"""
        :param n: degree of polynomial
        :param q: modulus
        :param width: width of matrix :math:`\mathbf{A}`
        :param height: height of matrix :math:`\mathbf{A}`
        :param d_2: :math:`1 < d_2 < N` and :math:`d_2` is a power of 2
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, sec=sec, q=q, d=width-height, m=height, d_2=d_2) 


class StatisticalUniformRLWE(StatisticalUniformMLWE):
    r"""
    Statistically secure RLWE over Uniform distribution with invertible elements :cite:`BDLOP18`. 
    
    For details, see :class:`StatisticalUniformMLWE` with module dimension :math:`d=1`.

    :ivar min_beta: :math:`\beta_{min}`
    :ivar max_beta: :math:`\beta_{max}`
    """
    def __init__(self, sec, n, q, m, d_2=None):
        r"""
        :param sec: required bit security of MLWE instance
        :param n: degree of polynomial
        :param q: modulus, must be prime congruent to :math:`2d_2 + 1 \;(\text{mod } 4d_2)`
        :param m: number of samples (height of matrix :math:`\mathbf{A}'` in :cite:`BDLOP18`)
        :param d_2: :math:`1 < d_2 < N` and :math:`d_2` is a power of 2
        """
        super().__init__(sec=sec, n=n, d=1, q=q, m=m, d_2=d_2)


## SIS and its variants ##
class SIS(BaseProblem):
    """ 
    Short Integer Solution (SIS) problem class used to create a list of algorithms from for cost estimation.
    """
    _counter = 1

    def __init__(self, n, q, m, bound : norm.BaseNorm, variant="SIS", label=None):
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param bound: upper bound on norm of secret distribution, must be instance of subclass of :py:mod:`lattice_parameter_estimation.norm.BaseNorm`. TODO
        :param variant: for internal use to distinguish variants
        :param label: short string to refer to describe the problem name, e.g. ``"LWE-Regev"``
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")

        if label is None:
            label = variant + str(self._counter)
            self._counter += 1
        self.label = label
        self.variant = variant
        self.q = q
        self.n = n
        self.m = m
        self.bound = bound
    
    def get_estimate_algorithms(self, config : algorithms.Configuration):
        r"""
        Compute list of estimate functions on the SIS instance according to the attack configuration.
        
        The priorities are assigned as follows:

        .. list-table:: Algorithm Priorities TODO
            :header-rows: 1

            * - Algorithm
              - Priority
              - Comment
            * - lattice-reduction
              - 5
              - fastest, low cost estimates
            * - lattice-reduction-rs
              - 7
              - same results as lattice-reduction, does not always work
            * - combinatorial
              - 10
              - fast, often slightly higher cost results

        .. figure:: ../tests_for_optimization/algorithm_runtime_cost/SIS_stddev=2,828_plots_1s.png
            :align: center
            :figclass: align-center

            SIS instance with :math:`\sigma=2.828,\; m=n^2, \; 2^{2n} < q < 2^{2n+1}`

        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`

        :returns: list of algorithms, e.g. ``[{"algname": "a1", "cname": "c1", "algf": f, "prio": 0, "cprio": 0, "inst": "SIS"}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        cost_models = config.reduction_cost_models() 
        algs = []
        for reduction_cost_model in cost_models:
            cost_model = reduction_cost_model["cost_model"]
            cname = reduction_cost_model["name"]

            # if "reduction-rs" in config.algorithms:
            #     algs.append({"algname": "lattice-reduction", 
            #                             "cname": cname, 
            #                             "algf": partial(algorithms.SIS.lattice_reduction, 
            #                                             self.n, self.bound.to_L2(self.n).value, 
            #                                             self.q,reduction_cost_model["success_probability"],  
            #                                             self.m, reduction_cost_model=cost_model),
            #                             "prio": 1,
            #                             "cprio": reduction_cost_model["prio"],
            #                             "inst": self.variant})
            if "reduction-rs" in config.algorithms:
                # TODO: implement drop_and_solve and scale variants
                algs.append({"algname": "lattice-reduction-rs", 
                                        "cname": cname, 
                                        "algf": partial(algorithms.SIS._lattice_reduction_rs, 
                                                        n=self.n, beta=self.bound.to_L2(self.n).value, q=self.q, success_probability=reduction_cost_model["success_probability"], 
                                                        m=self.m, reduction_cost_model=cost_model),
                                        "prio": 1,
                                        "cprio": reduction_cost_model["prio"],
                                        "inst": self.variant})
                # algs.append({"algname": "lattice-reduction-rs-rinse", 
                #                         "cname": cname, 
                #                         "algf": partial(algorithms.SIS.lattice_reduction_rs,
                #                                         self.n, self.bound.to_L2(self.n).value, self.q, reduction_cost_model["success_probability"], 
                #                                         self.m, reduction_cost_model=cost_model),
                #                         "prio": 1,
                #                         "cprio": reduction_cost_model["prio"],
                #                         "inst": self.variant})
            if "reduction" in config.algorithms:
                algs.append({"algname": "lattice-reduction", 
                                        "cname": cname, 
                                        "algf": partial(algorithms.SIS._lattice_reduction, 
                                                        n=self.n, beta=self.bound.to_L2(self.n).value, q=self.q, success_probability=reduction_cost_model["success_probability"], 
                                                        m=self.m, reduction_cost_model=cost_model),
                                        "prio": 2,
                                        "cprio": reduction_cost_model["prio"],
                                        "inst": self.variant})
                # algs.append({"algname": "lattice-reduction-rinse", 
                #                         "cname": cname, 
                #                         "algf": partial(algorithms.SIS.lattice_reduction,
                #                                         self.n, self.bound.to_L2(self.n).value, self.q,
                #                                         reduction_cost_model["success_probability"], 
                #                                         self.m, reduction_cost_model=cost_model),
                #                         "prio": 2,
                #                         "cprio": reduction_cost_model["prio"],
                #                         "inst": self.variant})
                # TODO: can drop_and_solve or scale be used here?

        if "combinatorial" in config.algorithms:
            algs.append({"algname": "combinatorial", 
                                        "cname": "",
                                        "algf": partial(algorithms.SIS.combinatorial, 
                                                        n=self.n, q=self.q, m=self.m, bound=self.bound.to_Loo(self.n).value),
                                        "prio": 0,
                                        "cprio": 0,
                                        "inst": self.variant})
        # TODO: add more algorithms?
        return algs

    def to_SIS(self):
        return self
        
    def __str__(self):
        return f"SIS [n={str(self.n)}, q={str(self.q)}, m={str(self.m)}, bound ({type(self.bound).__name__})={str(float(self.bound.value))}]"


class MSIS(SIS):
    """ 
    Module Short Integer Solution (MSIS) problem class used to create a list of algorithms from for cost estimation.
    """
    _counter = 1

    def __init__(self, n, d, q, m, bound : norm.BaseNorm, variant="MSIS", label=None):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :py:mod:`lattice_parameter_estimation.norm.BaseNorm`
        :param variant: for internal use to distinguish variants
        :param label: short string to refer to describe the problem name, e.g. ``"LWE-Regev"``
        """
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")

        if label is None:
            label = variant + str(self._counter)
            self._counter += 1
        self.label = label
        self.variant = variant
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.bound = bound
    
    def get_estimate_algorithms(self, config : algorithms.Configuration, use_reduction=False):
        r"""
        Compute list of estimate functions on the MSIS instance according to the attack configuration.

        TODO: If use_reduction is `False`, the algorithms take an SIS instance with dimension :math:`n=n \cdot d` and :math:`m=m \cdot n` as input. Else, the MSIS instance will be reduced to RSIS according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 2):

        Let :math:`k = 2` and :math:`q` be a prime. Let a positive real number :math:`\beta` be an upper bound on the :math:`L_2`-norm of the solution of :math:`\text{R-SIS}_{q,m,\beta}` and :math:`d \in \mathbb{N}` be a module rank such that

        .. math:: \sqrt{n m} \cdot q^{1/m} \leq \beta < \sqrt[2d-1]{q / (\sqrt{m}^{d-1})}.
        
        Then there exists a reduction from :math:`\text{M-SIS}_{q^k,m^k,\beta'}` to :math:`\text{R-SIS}_{q,m,\beta}` with :math:`\beta' = m^{k(d-1)/2} \cdot \beta^{k(2d-1)}`.

        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`
        :param use_reduction: specify if reduction to RSIS is used

        :returns: list of algorithms, e.g. ``[{"algname": "a1", "cname": "c1", "algf": f, "prio": 0, "cprio": 0, "inst": "MSIS"}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        # TODO
        if use_reduction:
            raise NotImplementedError()
            # transform to L2-norm
            self.beta = self.bound.to_L2(self.n * self.d).value # TODO: check dimension

            # TODO: check preconditions
            k = 2
            lower = RR(sqrt(self.n * self.m) * self.q**(1 / self.m))
            upper = RR((self.q / sqrt(self.m)**(self.d-1))**(1 / (2 * self.d - 1)))
            if lower <= self.beta and self.beta < upper:
                q_RSIS = RR(round(self.q**(1/k)))
                m_RSIS = RR(round(self.m**(1/k)))
                beta_RSIS = RR((self.beta / (self.m**((self.d - 1) / 2)))**(1 / (k * (2 * self.d - 1))))
                bound = norm.Lp(beta_RSIS, self.n, 2) # new dimension of input vector (instead of n * d in M-SIS)

            rsis = RSIS(n=self.n, q=q_RSIS, bound=bound, m=m_RSIS)
            return rsis.get_estimate_algorithms(config=config,     
                                        use_reduction=use_reduction) # TODO: use_reduction makes sense?

        else:
            sis = SIS(n=self.n*self.d, q=self.q, m=self.m*self.n, bound=self.bound, variant="MSIS", label=self.label)
            return sis.get_estimate_algorithms(config=config)
    
    def to_SIS(self):
        """
        :returns: SIS instance with dimension :math:`n=n \cdot d` and :math:`m=m \cdot n`
        """
        return SIS(n=self.n*self.d, q=self.q, m=self.m*self.n, bound=self.bound, variant="MSIS", label=self.label)

    def __str__(self):
        return f"MSIS [n={str(self.n)}, d={str(self.d)}, q={str(self.q)}, m={str(self.m)}, bound ({type(self.bound).__name__})={str(float(self.bound.value))}]"


class RSIS(SIS):
    """ 
    Ring Short Integer Solution (RSIS) problem class used to create a list of algorithms from for cost estimation.
    """
    _counter = 1

    def __init__(self, n, q, m, bound : norm.BaseNorm, variant="RSIS", label=None):
        """
        :param q: modulus
        :param n: degree of polynomial
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :py:mod:`lattice_parameter_estimation.norm.BaseNorm`
        :param variant: for internal use to distinguish variants
        :param label: short string to refer to describe the problem name, e.g. ``"LWE-Regev"``
        """
        ## We interpret the coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        
        if label is None:
            label = variant + str(self._counter)
            self._counter += 1
        self.label = label
        self.variant = variant
        self.n = n
        self.q = q
        self.m = m
        self.bound = bound

    def get_estimate_algorithms(self, config : algorithms.Configuration):
        r"""
        Compute list of estimate functions on a corresponding SIS instance according to the attack configuration by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6.

        :param config: instance of :py:mod:`lattice_parameter_estimation.algorithms.Configuration`

        :returns: list of algorithms, e.g. ``[{"algname": "a1", "cname": "c1", "algf": f, "prio": 0, "cprio": 0, "inst": "RSIS"}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        sis = SIS(n=self.n, q=self.q, m=self.m*self.n, bound=self.bound, variant="RSIS", label=self.label)
        return sis.get_estimate_algorithms(config=config)
    
    def to_SIS(self):
        """
        :returns: SIS instance with dimension :math:`n=n \cdot d` and :math:`m=m \cdot n`
        """
        return SIS(n=self.n, q=self.q, m=self.m*self.n, bound=self.bound, variant="RSIS", label=self.label)

    def __str__(self):
        return f"RSIS [n={str(self.n)}, q={str(self.q)}, m={str(self.m)}, bound ({type(self.bound).__name__})={str(float(self.bound.value))}]"


class StatisticalMSIS():
    r"""
    Statistically secure MSIS according to :cite:`DOTT21`, section 4.1.

    MLWE problem instance where the probability that non zero elements :math:`\mathbf{r}` in the Euclidean ball :math:`B_{m}(0, 2B)` satisfy :math:`\hat{\mathbf{A}}_1 \cdot \mathbf{r} = \mathbf{0}` is smaller than :math:`2^{-sec}`.

    Mapping of parameters in :cite:`DOTT21` to use here:
    
    ============================ ============= ============================================
    Parameters in :cite:`DOTT21` Use Here      Represents
    ============================ ============= ============================================
    :math:`m'`                   :math:`m+d`   width of matrix :math:`\hat{\mathbf{A}}_1`
    :math:`m`                    :math:`m`     height of matrix :math:`\hat{\mathbf{A}}_1`
    :math:`B`                    :math:`B`     norm-bound of secret
    :math:`s`                    :math:`s`     Gaussian width (not stddev)
    :math:`N`                    :math:`n`     degree of polynomial
    ============================ ============= ============================================

    The number of elements in :math:`B_{m+d}(0, 2B)` can be estimated from above as :math:`|B_{m+d}(0, 2B)| \ll (2 \pi e /((m+d) n))^{(m+d) n/2} \cdot (2 B)^{(m+d) n}`. The scheme is statistically binding if the probability that non zero elements in :math:`B_{m+d}(0, 2B)` of radius :math:`2B` in :math:`\mathcal{R}_q^{m+d}` map to :math:`\mathbf{0}` in :math:`\mathcal{R}_q^{m}` is negligible. Hence, it must hold that :math:`|B_{m+d}(0, 2B)|/q^{m n} \leq 2^{-sec}` and we get:
    
    TODO: look for bound of ball without o(...)
        
    .. math::
        \left(\sqrt{\frac{2 \pi e}{(m+d) \cdot n}} \cdot 2 B\right)^{(m+d) \cdot n} &\leq 2^{-sec} \cdot q^{m\cdot n} \\
        B &\leq 2^{\frac{-sec}{(m+d)\cdot n} - 1} \cdot q^\frac{m}{m+d} \cdot \sqrt{\frac{(m+d)\cdot n}{2 \pi e}}\\
    
    We convert the bound :math:`B` to a Gaussian over :math:`L_2`-norm by following the procedure described in :ref:`to_Lp <to_Lp>`:

    .. math::
        s  \approx x \sqrt{\frac{\pi}{(sec + 1) \ln(2)}}

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """

    def __init__(self, sec, n, d, q, m):
        """
        :param sec: required bit security of MSIS instance
        :param n: degree of polynomial
        :param d: rank of module (or height of matrix)
        :param q: modulus
        :param m: number of samples (or width of matrix)
        """
        # TODO: check paramters
        max_beta = RR(2**(-sec / ((m + d) * n)  - 1) * q**(m / (m + d)) * sqrt((m + d) * n / (2 * pi * e)))
        # convert beta bound to Gaussian width parameter
        self.max_s = max_beta * sqrt(pi / ((sec + 1) * log(2.0)))
        
        self.max_sigma =  est.stddevf(self.max_s)
        self.max_beta = norm.Lp(max_beta, 2, n * d) # TODO: is the dimension correct?
        self.sec = sec
        self.n = n
        self.d = d
        self.q = q
        self.m = m
    
    def get_secret_distribution_max_width(self):
        return distributions.GaussianSigma(sigma=self.max_sigma, q=self.q, componentwise=False, sec=self.sec) # TODO check, specify dimensions? or not needed?


class StatisticalMatrixMSIS(StatisticalMSIS):
    r"""
    Statistically secure MSIS according to :cite:`DOTT21`, section 4.1.

    For more details, see :class:`StatisticalMSIS`.

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """
    def __init__(self, n, q, width, height, sec=None):
        r"""
        :param n: degree of polynomial
        :param q: modulus
        :param width: width of matrix :math:`\mathbf{A}`
        :param height: height of matrix :math:`\mathbf{A}`
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, q=q, d=width-height, m=height, sec=sec)
        


class StatisticalRSIS(StatisticalMSIS):
    r"""
    Statistically secure RSIS according to :cite:`DOTT21`, section 4.1.
    
    For details, see :class:`StatisticalMSIS` with module dimension :math:`d=1`.

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """
    def __init__(self, sec, n, q, m):
        """
        :param sec: required bit security of MSIS instance
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples (or width of matrix)
        """
        super().__init__(sec=sec, n=n, d=1, q=q, m=m) # TODO: check Gaussian

class StatisticalSIS(StatisticalMSIS):
    r"""
    Statistically secure RSIS according to :cite:`DOTT21`, section 4.1.
    
    For details, see :class:`StatisticalMSIS` with degree of polynomial dimension :math:`n=1`, height of matrix becomes rank of modulus (i.e. :math:`d=n`). TODO clarify

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """
    def __init__(self, sec, n, q, m):
        """
        :param sec: required bit security of MSIS instance
        :param n: secret dimension
        :param q: modulus
        :param m: number of samples (or width of matrix)
        """
        super().__init__(sec=sec, n=1, d=n, q=q, m=m)