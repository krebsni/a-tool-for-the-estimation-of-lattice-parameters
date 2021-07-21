#!/usr/bin/env sage
import fire
import sys
import os
import logging
from lattice_parameter_estimation import attacks
from lattice_parameter_estimation import param_search
from lattice_parameter_estimation import distributions
from lattice_parameter_estimation import norm
from lattice_parameter_estimation import problem
import lattice_parameter_estimation.estimate_all_schemes.estimator as est
import sage.all 
from sage.rings.all import QQ, RR
from sage.symbolic.all import pi, e
from sage.functions.log import exp, log
from sage.functions.other import ceil, sqrt, floor, binomial
from lattice_parameter_estimation.estimate_all_schemes.estimator.estimator import Param

from lattice_parameter_estimation.estimate_all_schemes.schemes import LWE_SCHEMES

logger = logging.getLogger(__name__)
sec = param_search.SECURITY # can be any value, also used in Gaussian to bound trafo and statistically secure variants

def runtime_analysis():
    # TODO: coded-bkw: find a case that is working?
    # TODO: arora-gb did not yield any results yet (tested for normal sec_dis)
    #   arora-gb so far either returns infinity or segmentation fault after long runtime even for small n (at least for a few minutes)...
    config = attacks.Attack_Configuration(algorithms=["usvp", "dual", "dual-without-lll", "mitm", "coded-bkw"], multiprocessing=True)

    # problem_instances = []
    # for i in range(5,6):
    #     n, alpha, q = Param.Regev(2**i)
    #     m = n**2
    #     err_dis = distributions.Gaussian_alpha(alpha=alpha, q=q)
    #     sec_dis = err_dis
    #     problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis))
    # problem.RUNTIME_ANALYSIS = True
    # result = problem.estimate(parameter_problem=problem_instances, attack_configuration=config)
    # runtime = result.info["runtime"]
    # import json
    # with open('runtime.json', 'w') as fout:
    #     json.dump(runtime, fout)
    # return

    schemes = [s for s in LWE_SCHEMES if s["name"] == "Lizard"]
    scheme = schemes[0]
    runtime = []
    problem_instances = []
    logger.info("Scheme: " + scheme["name"])
    
    scheme_params = []
    if isinstance(scheme["params"][0], list):
        for param_sets in scheme["params"]:
            scheme_params.extend([x for x in param_sets])
    else:
        scheme_params = scheme["params"]
    for params in [scheme_params[0]]:
        n = params["n"]
        q = params["q"]
        sigma = params["sd"] #standard deviation
        err_dis = distributions.Gaussian_sigma(sigma=sigma, q=q)
        if not "m" in params:
            m = 2*n
        else:
            m = params["m"]
        if params["secret_distribution"] == "normal":
            sec_dis = err_dis
        else: 
            try:
                (a, b), h = params["secret_distribution"]
                sec_dis = distributions.Uniform(a=a, b=b, h=h)
            except (TypeError, ValueError):
                (a, b) = params["secret_distribution"]
                sec_dis = distributions.Uniform(a=a, b=b)
        problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis))

    result = problem.estimate(parameter_problem=problem_instances, attack_configuration=config)
    runtime = result.info["runtime"]
    runtime = sorted(runtime, key=lambda r: r["log_rop"])
    import json
    with open('runtime_Lizard.json', 'w') as fout:
        json.dump(runtime, fout)

def estimation_example():
    sec = 350
    # Example: KCL‑RLWE
    problem.statistical_sec = sec
    n = 2**10; q = 12289; m = 2*1024; stddev = sqrt(8) # TODO
    err_dis = distributions.Gaussian_sigma(sigma=stddev, q=q, componentwise=True, sec=sec)
    sec_dis = err_dis # "normal"
    config = attacks.Attack_Configuration(quantum=False, enumeration=False, algorithms=["mitm"], multiprocessing=True) # decode and dual take too long for testing purposes...
    lwe = problem.RLWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis)
    
    # estimates
    print("-----------------------------")
    print("LWE Estimates")
    result = problem.estimate(parameter_problem=[lwe], attack_configuration=config, sec=250)
    print("Result: is_secure=" + str(result.is_secure) + ", cost=" + str(result.cost) + ", info=" + str(result.info))
    # result = param_search.is_secure(parameter_problem=[lwe], sec=350, attack_configuration=config)
    # print(["Insecure. ", "Secure! "][result.is_secure] + "Result: " + str(result.results))
    print()
    print()
    print()
    print()
    print()

    # # Example: SIS
    print("-----------------------------")
    print("SIS Estimates")
    q = param_search.make_prime(2**(2*10+1), lbound=2**(2*10))
    m = (n * log(q, 2)).round()
    beta = err_dis.to_Loo(dimension=n) # componentwise beta bound (convert from Gaussian)
    sis = problem.RSIS(n=n, q=q, m=m, bound=beta)
    # estimates
    result = problem.estimate(parameter_problem=[sis], attack_configuration=config)
    print("Result: is_secure=" + str(result.is_secure) + ", cost=" + str(result.cost) + ", info=" + str(result.info))
    # result = param_search.is_secure(parameter_problem=[sis], sec=350, attack_configuration=config)
    # print(["Insecure. ", "Secure! "][result.is_secure] + "Result: " + str(result.results))


def BGV_example():
    attack_configuration = attacks.Attack_Configuration()
    def next_parameters(N, p, q):
        N = 2 * N
        p = 1 # find p depending on new N
        q = 1 # find q depending on new N and p
        yield N, p, q

    def parameter_problem(N, p, q):
        yield problem.RLWE(N, q) # keys are secure
        yield problem.RLWE(N, q) # encryption is secure

    N, p, q, security = param_search.generic_search(sec, (2**10, None, None), next_parameters, param_search.unit_cost, parameter_problem, attack_configuration)

def two_problem_search_example():
    # k: width (over R_q) of commitment matrices
    # n: height (over R_q) of commitment matrices
    # l: dimension (over R_q) of message space
    # beta: norm bound for honest prover's randomness in Loo-norm
    # kappa: maximum L1-norm of any element in challenge space
    # sigma: stddev used in zero-knowledge proof => sigma = 11*kappa*beta*sqrt(k*N)
    # m: width of commitment matrix A_2' => m = k - n - l
    N = 2**15
    p = param_search.make_prime(2**32)
    q = p
    n, m, l = 1, 1, 1
    initial_parameters = N, p, q, n, m, l
    attack_configuration = attacks.Attack_Configuration()

    def next_parameters(N, p, q, n, m, l):
        if m == 1:
            yield N, p, q * 2, n, m, l
        yield N, p, q, n, m + 1, l

    def parameter_cost(N, p, q, n, m, l):
        message = param_search.number_of_bits(p) * N * l
        rndness = param_search.number_of_bits(q) * N * (n + m + l)
        cmmtmnt = param_search.number_of_bits(q) * N * n + message
        cost = cmmtmnt + rndness
        return cost

    def parameter_problem(N, p, q, n, m, l):
        lwe : problem.Statistical_Uniform_MLWE = problem.Statistical_Uniform_MLWE(sec=sec, n=N, q=q, d=n + l, m=n + m + l)

        # TODO: Question: what was the though with the sigmas here?
        # sigma = lwe.sigma
        # min_sigma, max_sigma = lwe.get_sigma_bounds()
        
        # if min_sigma <= sigma <= max_sigma:
        #     yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, sigma=sigma)
        #     yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, sigma=max_sigma)
            # TODO: is the above correct (i.e. value for d)? Why sigma? SIS requires beta (norm bound of solution)
            # TODO: how to transform norm bound in BDLOP16 into stddev?

        min_beta, max_beta = lwe.get_beta_bounds()
        yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, bound=min_beta)
        yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, bound=max_beta)
        

    n, p, q, n, m, l = param_search.generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem, attack_configuration)

if __name__ == "__main__":
    runtime_analysis()
