r""" 
TODO: documentation
"""

from numpy.core.fromnumeric import var
from . import distributions
from . import attacks
from . import norm
from abc import ABC, abstractmethod
from collections import OrderedDict
from typing import Generator, Iterator
import time
import sys
import os
import logging
import traceback
import multiprocessing as mp
from concurrent.futures import ThreadPoolExecutor
from queue import Empty
from functools import partial
import sage.all 
from sage.functions.log import exp, log
from sage.functions.other import ceil, sqrt, floor, binomial
from sage.rings.all import QQ, RR
from sage.symbolic.all import pi, e
from sage.misc.functional import round
import estimate_all_schemes.estimator as est
oo = est.PlusInfinity()


## Logging ##
logger = logging.getLogger(__name__)

## Configuration ##
STATISTICAL_SEC = 128 #: for statistical security # TODO
RUNTIME_ANALYSIS = True
TIMEOUT = 600
ERROR_HANDLING_ON = True # if True try to deal with errors and not raise exceptions

## Helper class
class Estimate_Res():
    """
    Type of return value needed for overloaded lt-operator :class:`Problem` instances.

    :param is_secure: true if Problem instance satisfies security requirment
    :param info: attack, cost_model, inst
    :param error: string with error description
    :param runtime: list of runtime of algorithms run during estimation
    """
    def __init__(self, is_secure=True, info={}, cost=est.Cost([("rop", oo)]), error=None, runtime=None):
        self.is_secure = is_secure
        self.info = info
        self.cost = cost
        self.error = error
        self.runtime = runtime

    def __bool__(self):
        return self.is_secure

    def __str__(self) -> str:
        return 'Cost: ' + str(self.cost) + '\nInfo: ' + str(self.info) + ["", f"\nError: {self.error}"][self.error != None]

class EmptyProblem(Exception):
    pass

class Base_Problem(ABC):
    @abstractmethod
    def __init__(self):
        pass

    @abstractmethod
    def get_estimate_algorithms(self, attack_configuration=None):
        pass

    # TODO: check, perhaps add other operators
    def __ge__(self, sec) -> Estimate_Res:
        attack_configuration = attacks.Attack_Configuration() # use default config
        return estimate(parameter_problem=[self], attack_configuration=attack_configuration, sec=sec)

    def __gt__(self, sec) -> Estimate_Res:
        attack_configuration = attacks.Attack_Configuration() # use default config
        return estimate(parameter_problem=[self], attack_configuration=attack_configuration, sec=sec + 1)

    def __lt__(self, sec) -> Estimate_Res:
        return not self.__ge__(sec)

    def __le__(self, sec) -> Estimate_Res:
        return not self.__gt__(sec)

    @abstractmethod
    def __str__(self):
        pass


## Estmation ##
def algorithms_executor(algorithms, sec, res_queue=None):
    """TODO

    Args:
        cname: Cost model name
        algorithms: Dict like {"name_alg": algname, ...}
        sec ([type]): [description]
        problem_instance ([type]): [description]
        res_queue ([type]): [description]
    """
    if RUNTIME_ANALYSIS:
        runtime = []
    
    best_res = Estimate_Res()
    all_failed = True
    for alg in algorithms:
        algf = alg["algf"]
        logger.debug(str(os.getpid()) + f' Running algorithm {alg["algname"]}... Parameters: {str(dict([(k, algf.keywords[k]) for k in ["secret_distribution"] if k in set(algf.keywords)] +[(k, int(algf.keywords[k])) for k in ["n", "q", "m"] if k in set(algf.keywords)] + [(k, float(algf.keywords[k])) for k in ["alpha"] if k in set(algf.keywords)] + [(k, algf.keywords[k].value) for k in ["bound"] if k in set(algf.keywords)]))}')
        start = time.time()
        try:
            cost = algf() # TODO: handle intractable/trivial error from attacks.py? 
            duration = time.time() - start           
            logger.info(f'Estimate for "{alg["algname"]}" successful: result=[{str(cost)}], cost_model={alg["cname"]}, problem={alg["inst"]},  (took {duration:.3f} s)') 
            if cost["rop"] <= best_res.cost["rop"]:
                all_failed = False
                best_res.cost = cost
                best_res.info = {"attack": alg["algname"], "cost_model": alg["cname"], "inst": alg["inst"]}
                if sec and log(cost["rop"], 2) < sec:
                    best_res.is_secure = False; break
            if RUNTIME_ANALYSIS:
                if "beta" in cost:
                    beta = int(cost["beta"])
                else:
                    beta = None
                if "d" in cost:
                    d = int(cost["d"])
                else:
                    d = None
                runtime.append({
                    "algname": alg["algname"], 
                    "cname": alg["cname"], 
                    "runtime": duration, 
                    "log_rop": float(log(cost["rop"], 2)),
                    "beta": beta,
                    "d": d,
                    "parameters": dict([(k, algf.keywords[k]) for k in ["secret_distribution"] if k in set(algf.keywords)] +[(k, int(algf.keywords[k])) for k in ["n", "q", "m"] if k in set(algf.keywords)] + [(k, float(algf.keywords[k])) for k in ["alpha"] if k in set(algf.keywords)] + [(k, algf.keywords[k].value) for k in ["bound"] if k in set(algf.keywords)])
                })
        except Exception:
            # TODO: what to do with the exception??? => extra exception logger for estimator computions?
            # TODO: add error parameter to best_res
            duration = time.time() - start
            logger.debug(str(os.getpid()) + f' Exception during {alg["algname"]}... Parameters: {str(dict([(k, algf.keywords[k]) for k in ["secret_distribution"] if k in set(algf.keywords)] +[(k, int(algf.keywords[k])) for k in ["n", "q", "m"] if k in set(algf.keywords)] + [(k, float(algf.keywords[k])) for k in ["alpha"] if k in set(algf.keywords)] + [(k, algf.keywords[k].value) for k in ["bound"] if k in set(algf.keywords)]))}')
            logger.debug(traceback.format_exc())
    
    if RUNTIME_ANALYSIS:
        best_res.runtime = runtime # runtime of all algorithms (not just the one for best result)
    if all_failed:
        best_res.error = "all_failed"

    if res_queue is None:
        # no multiprocessing
        return best_res
    else:
        res_queue.put(best_res)
        

def estimate(parameter_problems : Iterator[Base_Problem], 
                attack_configuration : attacks.Attack_Configuration, 
                sec=None):
    algorithms = []
    for problem_instance in parameter_problems: 
        algorithms.extend( # TODO what if get_estimate_algorithms returns empty list... raise exception from problem
            problem_instance.get_estimate_algorithms(attack_configuration=attack_configuration))
    if not algorithms: # no instance
        raise EmptyProblem("Could not find any algorithms for given input parameters.")
    start = time.time()

    # TODO: two variants possible: one is to split by cost model, the other to split by algorithm
    # in case early termination is applicable, split by algorithm would probably be better
    # else split by cost model has better load balancing
    # how consistent are the runtimes of the various algorithms? If the order is always same, easy to just sort according to runtime...
    algorithms = sorted(algorithms, key=lambda a: (a["prio"], a["cprio"])) # various sortings possible, here sorted by runtime prio
    # TODO: test cost_model priority
    
    if RUNTIME_ANALYSIS:
        runtime = []

    if attack_configuration.parallel:
        if attack_configuration.num_cpus is None:
            num_procs = min(mp.cpu_count(), len(algorithms))
        else:
            num_procs = attack_configuration.num_cpus

        tp = ThreadPoolExecutor(num_procs)

        # evenly distribute algorithms according to sorting among #NUM_CPUS lists
        split_list = num_procs * [None]
        for j in range(num_procs):
            split_list[j] = []
        for i in range(len(algorithms)):
            split_list[i % num_procs].append(algorithms[i])

        logger.debug(f"Starting {num_procs} processes for {len(algorithms)} algorithms...")
        logger.debug("Running estimates " + ["without", "with"][bool(sec)] + " early termination...") # TODO
        p = [None]*len(split_list)
        best_res = Estimate_Res()
        result_queue = mp.Queue()
        for i in range(len(split_list)):
            p[i] = mp.Process(target=algorithms_executor, args=(split_list[i], sec, result_queue))
            p[i].start()
            logger.debug(str(p[i].pid) + " started...") # TODO: perhaps add debug logging in algorithm_executor
        
        terminated = False
        all_failed = True
        while not terminated:
            try:
                # Check if all processes finished their calculation
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
                res = result_queue.get(block=True, timeout=0.5) # timeout necessary as process that wrote result in queue may still be alive in the above check 
                # TODO perhaps fine tune, check that wait here is not busy waiting... check if all cores are 100% or not...
                
                if RUNTIME_ANALYSIS:
                    runtime.extend(res.runtime)
                
                if res.cost["rop"] <= best_res.cost["rop"]:
                    if res.error is not None and res.error == "all_failed":
                        # all algorithms failed
                        pass
                    else:
                        all_failed = False
                        best_res = res
                        if sec and not res.is_secure: # early termination only if sec parameter is specified
                            logger.debug("Received insecure result. Terminate all other processes.")
                            # insecure result obtained => terminate all other processes
                            for i in range(len(split_list)):
                                p[i].terminate() # TODO: could it happen that exception is cast when a process is already terminated
                                p[i].join()
                                # data put into queue during terminate may become corrupted => just close it
                                result_queue.close()
                                terminated = True
            except Empty: # result not yet available
                if time.time() - start > TIMEOUT:
                    # Computation too long, result not expected anymore
                    for i in range(len(split_list)):
                        p[i].terminate() 
                        p[i].join()
                        result_queue.close()
                        terminated = True
                    message = f"Cost estimation not terminating after {TIMEOUT}s. Forcefully end all computations."
                    if ERROR_HANDLING_ON:
                        logger.error(message)
                    else:
                        raise RuntimeError(message)
        if RUNTIME_ANALYSIS:
            best_res.runtime = runtime

    else: # not parallel
        best_res = algorithms_executor(algorithms, sec) 
    
    if all_failed:
        raise RuntimeError("All estimate algorithms failed")
    
    duration = time.time() - start
    message = f"Estimate successful (took {duration:.3f} s). Lowest computed security: {str(float(log(best_res.cost['rop'], 2)))}. "
    if sec is not None:
        message += f"Result is {['insecure', 'secure'][log(best_res.cost['rop'], 2) > sec]} (sec={sec})."
    logger.info(message) 
    return best_res


## LWE and its variants ##
class LWE(Base_Problem):
    # TODO: docstring (also other variants)

    def __init__(self, n, q, m, secret_distribution : distributions.Distribution, error_distribution : distributions.Distribution, variant = "LWE"): 
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        """
        # check soundness of parameters
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution
        self.variant = variant

    def get_estimate_algorithms(self, attack_configuration):
        """
        Compute list of estimate functions on the LWE instance according to the attack configuration.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`

        :returns: list of algorithms, e.g. ``[{"algname": "algorithm1", "cname": "costmodelname1", "algf": f, "prio": 0, "cprio": 0, "inst": self.variant}}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime) and "cprio" of the cost model with lower expected cost estimate for lower priorities
        """ 
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")
        
        secret_distribution = self.secret_distribution._convert_for_lwe_estimator() 
        alpha = RR(self.error_distribution.get_alpha())
        # TODO: if secret is normal, but doesn't follow noise distribution, not supported by estimator => convert to uniform?
        if secret_distribution == "normal" and self.secret_distribution.get_alpha() != alpha:
            ValueError("If secret distribution is Gaussian it must follow the error distribution. Different Gaussians not supported by lwe-estimator.") # TODO: perhaps change

        cost_models = attack_configuration.reduction_cost_models()
        
        # TODO: coded-bkw: find a case that is working?
        # TODO: arora-gb seems to be not working for sec_dis = "normal" => perhaps change test before adding arora-gb to alg list?

        # TODO: find meaningful prio values
        # algname is algorithm name, cname name of cost model, algf function, 
        algorithms = []
        # Choose attacks. Similar to estimate_lwe function in estimator.py
        for reduction_cost_model in cost_models:
            cost_model = reduction_cost_model["reduction_cost_model"]
            success_probability = reduction_cost_model["success_probability"]
            cname = reduction_cost_model["name"]
            cprio = reduction_cost_model["prio"]

            if "usvp" in attack_configuration.algorithms:
                if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                    # Try guessing secret entries via drop_and_solve
                    algorithms.append({"algname": "primal-usvp-drop", 
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
                     algorithms.append({"algname": "primal-usvp", 
                                        "cname": cname, 
                                        "algf": partial(est.primal_usvp, 
                                                        reduction_cost_model=cost_model, n=self.n, 
                                                        alpha=alpha, q=self.q, m=self.m,
                                                        secret_distribution=secret_distribution, 
                                                        success_probability=success_probability),
                                        "prio": 10,
                                        "cprio": cprio,
                                        "inst": self.variant})
            
            if "dual" in attack_configuration.algorithms:
                if est.SDis.is_ternary(secret_distribution): # TODO can drop and solve yield worse results than standard?
                    # Try guessing secret entries via drop_and_solve
                    algorithms.append({"algname": "dual-scale-drop", 
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
                    algorithms.append({"algname": "dual-scale", 
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
                    algorithms.append({"algname": "dual", 
                                        "cname": cname, 
                                        "algf": partial(est.dual, reduction_cost_model=cost_model, 
                                                        n=self.n, alpha=alpha, q=self.q, m=self.m,
                                                        secret_distribution=secret_distribution, 
                                                        success_probability=success_probability),
                                        "prio": 20,
                                        "cprio": cprio,
                                        "inst": self.variant})

            if "dual-without-lll" in attack_configuration.algorithms:
                if est.SDis.is_ternary(secret_distribution): # TODO can drop and solve yield worse results than standard?
                    # Try guessing secret entries via drop_and_solve
                    algorithms.append({"algname": "dual-scale-drop-without-lll", 
                                        "cname": cname, 
                                        "algf": partial(est.drop_and_solve, est.dual_scale, 
                                                        postprocess=True, rotations=False, use_lll=False, 
                                                        reduction_cost_model=cost_model, 
                                                        n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                        secret_distribution=secret_distribution, 
                                                        success_probability=success_probability),
                                        "prio": 20,
                                        "cprio": cprio,
                                        "inst": self.variant})
                elif est.SDis.is_small(secret_distribution):
                    algorithms.append({"algname": "dual-scale-without-lll", 
                                        "cname": cname, 
                                        "algf": partial(est.dual_scale, 
                                                        use_lll=False, reduction_cost_model=cost_model, 
                                                        n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                        secret_distribution=secret_distribution, 
                                                        success_probability=success_probability),
                                        "prio": 20,
                                        "cprio": cprio,
                                        "inst": self.variant})                                                                
                elif "dual" in attack_configuration.algorithms: # else this algorithm will be run twice
                    algorithms.append({"algname": "dual-without-lll", 
                                        "cname": cname, 
                                        "algf": partial(est.dual, reduction_cost_model=cost_model, 
                                                        n=self.n, alpha=alpha, q=self.q, m=self.m,
                                                        secret_distribution=secret_distribution, 
                                                        success_probability=success_probability),
                                        "prio": 20,
                                        "cprio": cprio,
                                        "inst": self.variant})

            if "decode" in attack_configuration.algorithms:
                # TODO: Runtime much worse than primal-usvp, may yield better values for small n (Regev scheme n < 256?)
                # TODO: Could be used when early termination is on perhaps, then it would only be called when all other tests succeed?
                if est.SDis.is_sparse(secret_distribution) and est.SDis.is_ternary(secret_distribution):
                    algorithms.append({"algname": "primal-decode-drop", 
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
                    algorithms.append({"algname": "primal-decode", 
                                        "cname": cname, 
                                        "algf": partial(est.primal_decode, reduction_cost_model=cost_model, 
                                                        n=self.n, alpha=alpha, q=self.q, m=self.m,
                                                        secret_distribution=secret_distribution, 
                                                        success_probability=success_probability),
                                        "prio": 100,
                                        "cprio": cprio,
                                        "inst": self.variant})

        # attacks without reduction cost model
        if "mitm" in attack_configuration.algorithms: # estimates are very bad but very fast, so no need to exclude 
            algorithms.append({"algname": "mitm", 
                                "cname": "-", 
                                "algf": partial(est.mitm, n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                secret_distribution=secret_distribution, 
                                                success_probability=success_probability),
                                "prio": 0,
                                "cprio": 0,
                                "inst": self.variant})
            
        if "coded-bkw" in attack_configuration.algorithms:
            algorithms.append({"algname": "coded-bkw", 
                                "cname": "-", 
                                "algf": partial(est.bkw_coded, n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                secret_distribution=secret_distribution, 
                                                success_probability=success_probability),
                                "prio": 0, # TODO
                                "cprio": 0,
                                "inst": self.variant})

        if "arora-gb" in attack_configuration.algorithms:
            if est.SDis.is_sparse(secret_distribution) and est.SDis.is_small(secret_distribution):
                algorithms.append({"algname": "arora-gb-drop", 
                                    "cname": "-", 
                                    "algf": partial(est.drop_and_solve, est.arora_gb, rotations=False, 
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 200, # TODO: no results obtained yet
                                    "cprio": 0, 
                                    "inst": self.variant})
            elif secret_distribution != "normal" and est.SDis.is_small(secret_distribution): # switch_modulus does not work for normal sec_dis
                algorithms.append({"algname": "arora-gb-switch-modulus", 
                                    "cname": "-", 
                                    "algf": partial(est.switch_modulus, est.arora_gb,
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 200, 
                                    "cprio": 0,
                                    "inst": self.variant})
            else:
                algorithms.append({"algname": "arora-gb", 
                                    "cname": "-", 
                                    "algf": partial(est.arora_gb,
                                                    n=self.n, alpha=alpha, q=self.q, m=self.m,  
                                                    secret_distribution=secret_distribution, 
                                                    success_probability=success_probability),
                                    "prio": 200, 
                                    "cprio": 0,
                                    "inst": self.variant})
        # TODO: if empty raise exception, also for SIS
        return algorithms

    def __str__(self):
        # TODO
        return "LWE [n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m) + \
            ", sec_dis=" + str(self.secret_distribution._convert_for_lwe_estimator())  + ", err_dis=" + str(self.error_distribution._convert_for_lwe_estimator()) + "]"


class MLWE(Base_Problem):

    def __init__(self, n, d, q, m, secret_distribution, error_distribution):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (instance of subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        """
        # check soundness of parameters
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def get_estimate_algorithms(self, attack_configuration, use_reduction=False):
        r"""
        Compute list of estimate functions on the MLWE instance according to the attack configuration.

        If use_reduction is `False`, the cost is estimated for an LWE instance with dimension :math:`n=n \cdot d`. Else, the MLWE instance will be reduced to RLWE according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 1, note: :cite:`KNK20b` contains error in exponent of q):

        If we take :math:`k = d`, then there exists an efficient reduction from :math:`\textit{M-SLWE}_{m,q, \Psi \leq \alpha}^{R^d}\left(\chi^d\right)` to :math:`\textit{R-SLWE}_{m,q^d, \Psi \leq \alpha\cdot n^2\cdot\sqrt{d}}^{R}\left(U(R_q^\vee)\right)` with controlled error rate :math:`\alpha`.

        Note that the reduction only works for Search-MLWE TODO: find reduction for decision-MLWE?

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param use_reduction: specify if reduction to RLWE is used

        :returns: list of algorithms, e.g. ``[{"algname": "algorithm1", "cname": "costmodelname1", "algf": f, "prio": 0, "inst": self}}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        # TODO: check if correct
        use_reduction = False
        if use_reduction:
            alpha_MLWE = self.error_distribution.get_alpha()
            alpha_RLWE = RR(alpha_MLWE * self.n**2 * sqrt(self.d))
            q_RLWE = self.q**self.d
            secret_distribution_RLWE = distributions.Uniform(0, self.q) # TODO: is this correct?
            error_distribution_RLWE = distributions.Gaussian_alpha(alpha_RLWE, q_RLWE) # TODO: componentwise or L2?
            # TODO how to do RLWE?
            rlwe = RLWE(n=self.n, q=q_RLWE, m=self.m, secret_distribution=secret_distribution_RLWE, 
                                error_distribution=error_distribution_RLWE)

            return rlwe.get_estimate_algorithms(attack_configuration=attack_configuration,       
                                        use_reduction=use_reduction)
            
        else:
            lwe = LWE(n=self.n*self.d, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                        error_distribution=self.error_distributionm, variant="MLWE")
            return lwe.get_estimate_algorithms(attack_configuration=attack_configuration)

    def __str__(self):
        # TODO
        return "MLWE instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution._convert_for_lwe_estimator())  \
            + ", error_distribution=" + str(self.error_distribution._convert_for_lwe_estimator()) + ")"


class RLWE(Base_Problem):

    def __init__(self, n, q, m, secret_distribution, error_distribution):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param m: number of samples
        :param secret_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param error_distribution: secret distribution (subclass of :class:`Distributions.Gaussian` or :class:`Distributions.Uniform`)
        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(secret_distribution, distributions.Gaussian) and not isinstance(secret_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")
        if not isinstance(error_distribution, distributions.Gaussian) and not isinstance(error_distribution, distributions.Uniform):
            raise ValueError("secret_distribution must be subclass of Distributions.Gaussian or Distributions.Uniform.")

        ## interpret coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6] TODO: check 
        self.n = n
        self.q = q
        self.m = m
        self.secret_distribution = secret_distribution
        self.error_distribution = error_distribution

    def get_estimate_algorithms(self, attack_configuration, use_reduction=False):
        r"""
        Compute list of estimate functions on the RLWE instance according to the attack configuration by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6. 

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param use_reduction: specify if reduction to RLWE is used

        :returns: list of algorithms, e.g. ``[{"algname": "algorithm1", "cname": "costmodelname1", "algf": f, "prio": 0, "inst": self}}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        lwe = LWE(n=self.n, q=self.q, m=self.m, secret_distribution=self.secret_distribution,    
                    error_distribution=self.error_distribution, variant="RLWE")
        return lwe.get_estimate_algorithms(attack_configuration=attack_configuration)

    def __str__(self):
        # TODO
        return "RLWE instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) \
            + ", m=" + str(self.m) + ", secret_distribution=" + str(self.secret_distribution._convert_for_lwe_estimator())  \
            + ", error_distribution=" + str(self.error_distribution._convert_for_lwe_estimator()) + ")"


class Statistical_Gaussian_MLWE():
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
        # TODO: auch bei Statistical_MSIS
        return distributions.Gaussian_sigma(self.min_sigma, q=self.q, componentwise=True, sec=self.sec) 


class Statistical_Gaussian_MatrixMLWE(Statistical_Gaussian_MLWE):
    r"""
    Statistically secure MLWE over Gaussian distribution according to :cite:`LPR13`.

    For more details, see :class:`Statistical_Gaussian_MLWE`.

    :ivar min_sigma: minimum :math:`\sigma` (standard deviation) required for statistically secure MLWE
    :ivar sec: set to parameter sec if sec is specified in constructor, else set to n
    """

    def __init__(self, n, q, width, height, sec=None):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param width: width of matrix :math:`\mathbf{A}`
        :param height: height of matrix :math:`\mathbf{A}`
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, q=q, d=width-height, m=height, sec=sec)


class Statistical_Gaussian_RLWE(Statistical_Gaussian_MLWE):
    r"""
    Statistically secure RLWE over Gaussian distribution with invertible elements :cite:`LPR13`. 
    
    For details, see :class:`Statistical_Gaussian_MLWE` with module dimension :math:`d=1`.

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


class Statistical_Uniform_MLWE():
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
            d_2 = Statistical_Uniform_MLWE.find_d(q, n)

        # TODO: check prerequisites?
        self.n = n
        self.q = q
        self.m = m
        self.d = d
        self.d_2 = d_2
        logger.debug("d: " + str(d_2))
        min_beta = RR(q**(m / (m + d)) * 2**(2 * sec / ((m + d) * n)) / 2)
        logger.debug("min_beta: " + str(min_beta))
        max_beta = RR(1 / (2 * sqrt(d_2)) * q**(1 / d_2)) - 1
        logger.debug("max_beta: " + str(max_beta))

        if min_beta > max_beta:
            raise ValueError("Could not find (min_beta, max_beta). Lemma 4 in BDLOP18 does not apply for the given input parameters.")

        self.min_beta = norm.Lp(min_beta, oo, n * d)
        self.max_beta = norm.Lp(max_beta, oo, n * d)

    def get_beta_bounds(self):
        """
        :returns: tuple (min_beta, max_beta), betas are instances of :class:`norm.Lp`
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
        raise ValueError("Could not find d such that 1 < d < n power of 2 and q congruent to 2d + 1 (mod 4d). q=" + str(q) + ", n=" + str(n))   


class Statistical_Uniform_MatrixMLWE(Statistical_Uniform_MLWE):
    r"""
    Statistically secure MLWE over Uniform distribution with invertible elements :cite:`BDLOP18`.

    For more details, see :class:`Statistical_Uniform_MLWE`.

    :ivar min_beta: :math:`\beta_{min}`
    :ivar max_beta: :math:`\beta_{max}`
    """
    def __init__(self, sec, n, q, width, height, d_2=None):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param width: width of matrix :math:`\mathbf{A}`
        :param height: height of matrix :math:`\mathbf{A}`
        :param d_2: :math:`1 < d_2 < N` and :math:`d_2` is a power of 2
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, sec=sec, q=q, d=width-height, m=height, d_2=d_2) 


class Statistical_Uniform_RLWE(Statistical_Uniform_MLWE):
    r"""
    Statistically secure RLWE over Uniform distribution with invertible elements :cite:`BDLOP18`. 
    
    For details, see :class:`Statistical_Uniform_MLWE` with module dimension :math:`d=1`.

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
class SIS(Base_Problem):
        
    def __init__(self, n, q, m, bound, variant="SIS"):
        """
        :param q: modulus
        :param n: secret dimension
        :param m: number of samples
        :param bound: upper bound on norm of secret distribution, must be instance of subclass of :class:`Norm.Base_Norm`. TODO
        """
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        self.q = q
        self.n = n
        self.m = m
        self.bound = bound
        self.variant = variant
    
    def get_estimate_algorithms(self, attack_configuration):
        """
        Compute list of estimate functions on the SIS instance according to the attack configuration.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`

        :returns: list of algorithms, e.g. ``[{"algname": "algorithm1", "cname": "costmodelname1", "algf": f, "prio": 0, "inst": self.variant}}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        if not isinstance(attack_configuration, attacks.Attack_Configuration):
            raise ValueError("attack_configuration must be instance of Attack_Configuration")

        cost_models = attack_configuration.reduction_cost_models() # TODO

        # attack_name = ""
        # is_secure = True  
        # best_cost = {"rop": oo, "error": "All estimates failed"}

        algorithms = []
        for reduction_cost_model in cost_models:
            cost_model = reduction_cost_model["reduction_cost_model"]
            cname = reduction_cost_model["name"]

            if "lattice-reduction" in attack_configuration.algorithms:
                algorithms.append({"algname": "lattice-reduction", 
                                        "cname": cname, 
                                        "algf": partial(attacks.SIS.lattice_reduction, 
                                                        n=self.n, q=self.q, m=self.m, bound=self.bound, 
                                                        reduction_cost_model=cost_model),
                                        "prio": 1,
                                        "cprio": reduction_cost_model["prio"],
                                        "inst": self.variant})

        if "combinatorial" in attack_configuration.algorithms:
            algorithms.append({"algname": "combinatorial", 
                                        "cname": "-",
                                        "algf": partial(attacks.SIS.combinatorial, 
                                                        n=self.n, q=self.q, m=self.m, bound=self.bound),
                                        "prio": 0,
                                        "cprio": 0,
                                        "inst": self.variant})
        # TODO: add more algorithms?
        return algorithms
        
    def __str__(self):
        return "SIS instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m) + ", bound=" + str(self.bound.value)  + ")"


class MSIS(Base_Problem):

    def __init__(self, n, d, q, m, bound):
        """
        :param n: degree of polynomial
        :param d: rank of module
        :param q: modulus
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :class:`Norm.Base_Norm`
        """
        if not n or not d or not q or not m or n<0 or d<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        self.n = n
        self.d = d
        self.q = q
        self.m = m
        self.bound = bound
    
    def get_estimate_algorithms(self, attack_configuration, use_reduction=False):
        r"""
        Compute list of estimate functions on the MSIS instance according to the attack configuration.

        TODO: If use_reduction is `False`, the algorithms take an SIS instance with dimension :math:`n=n \cdot d` as input. Else, the MSIS instance will be reduced to RSIS according to :cite:`KNK20b` as follows:

        Corollary (:cite:`KNK20b` Corollary 2):

        Let :math:`k = 2` and :math:`q` be a prime. Let a positive real number :math:`\beta` be an upper bound on the :math:`L_2`-norm of the solution of :math:`\text{R-SIS}_{q,m,\beta}` and :math:`d \in \mathbb{N}` be a module rank such that

        .. math:: \sqrt{n m} \cdot q^{1/m} \leq \beta < \sqrt[2d-1]{q / (\sqrt{m}^{d-1})}.
        
        Then there exists a reduction from :math:`\text{M-SIS}_{q^k,m^k,\beta'}` to :math:`\text{R-SIS}_{q,m,\beta}` with :math:`\beta' = m^{k(d-1)/2} \cdot \beta^{k(2d-1)}`.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        :param use_reduction: specify if reduction to RSIS is used

        :returns: list of algorithms, e.g. ``[{"algname": "algorithm1", "cname": "costmodelname1", "algf": f, "prio": 0, "inst": self}}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        # TODO
        if use_reduction:
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
            return rsis.get_estimate_algorithms(attack_configuration=attack_configuration,     
                                        use_reduction=use_reduction) # TODO: use_reduction makes sense?

        else:
            sis = SIS(n=self.n*self.d, q=self.q, m=self.m, bound=self.bound, variant="MSIS")
            return sis.get_estimate_algorithms(attack_configuration=attack_configuration)

    def __str__(self):
        return "MSIS instance with parameters (n=" + str(self.n) + ", d=" + str(self.d) + ", q=" + str(self.q) + ", m=" + str(self.m) + ", bound=" + str(self.bound.value)  + ")"


class RSIS(Base_Problem):

    def __init__(self, n, q, m, bound):
        """
        :param q: modulus
        :param n: degree of polynomial
        :param m: number of samples
        :param bound: upper bound on norm of solution, must be subclass of :class:`Norm.Base_Norm`
        """
        ## We interpret the coefficients of elements of R_q as vectors in Z_q^n [ACD+18, p. 6]
        if not n or not q or not m or n<0 or q<0 or m<0:
            raise ValueError("Parameters not specified correctly")
        if not isinstance(bound, norm.Base_Norm):
            raise ValueError("Norm must be subclass of Base_Norm.")
        self.n = n
        self.q = q
        self.m = m
        self.bound = bound

    def get_estimate_algorithms(self, attack_configuration):
        """
        Compute list of estimate functions on a corresponding SIS instance according to the attack configuration by interpreting the coefficients of elements of :math:`\mathcal{R}_q` as vectors in :math:`\mathbb{Z}_q^n` as in :cite:`ACDDPPVW18`, p. 6.

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`

        :returns: list of algorithms, e.g. ``[{"algname": "algorithm1", "cname": "costmodelname1", "algf": f, "prio": 0, "inst": self}}]`` where "prio" is the priority value of the algorithm (lower values have shorted estimated runtime)
        """ 
        sis = SIS(n=self.n, q=self.q, m=self.m, bound=self.bound, variant="RSIS")
        return sis.get_estimate_algorithms(attack_configuration=attack_configuration)

    def __str__(self):
        # TODO
        return "RSIS instance with parameters (n=" + str(self.n) + ", q=" + str(self.q) + ", m=" + str(self.m.n()) + ", bound=" + str(self.bound.value)  + ")"


class Statistical_MSIS():
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
        return distributions.Gaussian_sigma(sigma=self.max_sigma, q=self.q, componentwise=False, sec=self.sec) # TODO check, specify dimensions? or not needed?


class Statistical_MatrixMSIS(Statistical_MSIS):
    r"""
    Statistically secure MSIS according to :cite:`DOTT21`, section 4.1.

    For more details, see :class:`Statistical_MSIS`.

    :ivar max_sigma: standard deviation :math:`\sigma`
    :ivar max_beta: max bound :math:`\beta` in :math:`L_2`-norm
    """
    def __init__(self, n, q, width, height, sec=None):
        """
        :param n: degree of polynomial
        :param q: modulus
        :param width: width of matrix :math:`\mathbf{A}`
        :param height: height of matrix :math:`\mathbf{A}`
        :param sec: optional security parameter to ensure that n >= sec and for Gaussian conversion
        """
        super().__init__(n=n, q=q, d=width-height, m=height, sec=sec)
        


class Statistical_RSIS(Statistical_MSIS):
    r"""
    Statistically secure RSIS according to :cite:`DOTT21`, section 4.1.
    
    For details, see :class:`Statistical_MSIS` with module dimension :math:`d=1`.

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

class Statistical_SIS(Statistical_MSIS):
    r"""
    Statistically secure RSIS according to :cite:`DOTT21`, section 4.1.
    
    For details, see :class:`Statistical_MSIS` with degree of polynomial dimension :math:`n=1`, height of matrix becomes rank of modulus (i.e. :math:`d=n`). TODO clarify

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