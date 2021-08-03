#!/usr/bin/env sage
from bisect import bisect
from multiprocessing import Value
import fire
import sys
import os
import logging
from lattice_parameter_estimation import algorithms_and_config
from lattice_parameter_estimation import param_search
from lattice_parameter_estimation import distributions
from lattice_parameter_estimation import norm
from lattice_parameter_estimation import problem
import lattice_parameter_estimation
import lattice_parameter_estimation.estimator as est
import sage.all 
from sage.rings.all import QQ, RR, ZZ
from sage.symbolic.all import pi, e
from sage.functions.log import exp, log
from sage.functions.other import ceil, sqrt, floor, binomial
from lattice_parameter_estimation.estimator.estimator import Param, arora_gb, bkw_coded

from lattice_parameter_estimation.estimate_all_schemes.schemes import LWE_SCHEMES

logging.basicConfig(level=logging.DEBUG) # set to INFO to hide exceptions
logger = logging.getLogger(__name__)

lattice_parameter_estimation.Logging.set_level(logging.INFO)
lattice_parameter_estimation.Logging.disable_estimation_exception_logging_level()

# TODO: put in config file or so? param_search needs to be imported for logging level to be set (?)

def plot_runtime(title, file_name, runtime):
    import matplotlib.pyplot as plt
    logging.getLogger("matplotlib").setLevel(logging.INFO)
    algs = {algn for algn in (x["algname"] for x in runtime)}
    algs_res = {}
    for algn in algs:
        cmodels = {x["cname"] for x in runtime if x["algname"] == algn}
        algs_res[algn] = {}
        for cname in cmodels:
            algs_res[algn][cname] = sorted([x for x in runtime if (x["algname"] == algn and x["cname"] == cname)], key=lambda k : k["parameters"]["n"])

    fig1, ax1 = plt.subplots(1,1)
    colors = ['b', 'g', 'r', 'c', 'm', 'y', 'k']
    styles = ['-', '--', '-.', ':', '.', ',', 'o', 'v', '^', '<', '>', 's', 'p', '*']    
    i = 0
    # TODO: do mean from cost models?
    for algn in algs_res:
        j = 0
        for cname in algs_res[algn]:
            label = algn + ["", f" (Cost model: {cname})"][cname != "-"]
            ax1.plot([x["parameters"]["n"] for x in algs_res[algn][cname]], [x["runtime"] for x in algs_res[algn][cname]], colors[i] + styles[j], label=label)
            j += 1
        i += 1
    ax1.set_xlabel(r'Secret dimension $n$')
    ax1.set_ylabel('Runtime [s]')
    ax1.set_title(title)
    ax1.legend()
    plt.grid()
    plt.savefig(file_name)
    plt.show()


    # Mean of different cost models
    algs = {algn for algn in (x["algname"] for x in runtime)}
    algs_res = {}
    for algn in algs:
        cmodels = {x["cname"] for x in runtime if x["algname"] == algn}
        algs_res[algn] = {}
        for cname in cmodels:
            algs_res[algn][cname] = sorted([x for x in runtime if (x["algname"] == algn and x["cname"] == cname)], key=lambda k : k["parameters"]["n"])

    fig1, ax1 = plt.subplots(1,1)
    colors = ['b', 'g', 'r', 'c', 'm', 'y', 'k']
    styles = ['-', '--', '-.', ':', '.', ',', 'o', 'v', '^', '<', '>', 's', 'p', '*']    
    i = 0
    # TODO: do mean from cost models?
    for algn in algs_res:
        j = 0
        for cname in algs_res[algn]:
            label = algn + ["", f" (Cost model: {cname})"][cname != "-"]
            ax1.plot([x["parameters"]["n"] for x in algs_res[algn][cname]], [x["runtime"] for x in algs_res[algn][cname]], colors[i] + styles[j], label=label)
            j += 1
        i += 1
    ax1.set_xlabel(r'Secret dimension $n$')
    ax1.set_ylabel('Runtime [s]')
    ax1.set_title(title)
    ax1.legend()
    plt.grid()
    plt.savefig(file_name)
    plt.show()

def runtime_analysis():
    print("---------------------------------")
    print("Runtime Analysis")
    print("---------------------------------")
    problem.RUNTIME_ANALYSIS = True
    # TODO: coded-bkw: find a case that is working - not even example case in script is working (same with online sage runner... maybe worked for sage 2.x?)
    # TODO: arora-gb did not yield any results yet (tested for normal sec_dis)
    #   arora-gb so far either returns infinity or segmentation fault after long runtime even for small n (at least for a few minutes)...
    config = algorithms_and_config.EstimationConfiguration(algorithms=["usvp", "dual", "dual-without-lll", "arora-gb", "decode", "mitm", "coded-bkw"])

    problem_instances = []
    for i in range(9, 10):
        n, alpha, q = Param.Regev(2**i)
        m = n**2
        err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
        sec_dis = err_dis
        # print(est.bkw_coded(n=n, alpha=alpha, q=q, m=m,  
        #                 secret_distribution=alpha, 
        #                 success_probability=0.99))
        # return
        problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis))
    problem.RUNTIME_ANALYSIS = True
    result = problem.estimate(parameter_problems=problem_instances, config=config)

    print("---------------------------------")
    print("Estimates complete")
    runtime = result.runtime
    # plot_runtime("Regev", "runtime_regev", runtime)
    # import json
    # with open('runtime_Regev.json', 'w') as fout:
    #     json.dump(runtime, fout)

    return

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
    for params in scheme_params:
        n = params["n"]
        q = params["q"]
        sigma = params["sd"] #standard deviation
        err_dis = distributions.GaussianSigma(sigma=sigma, q=q)
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

    result = problem.estimate(parameter_problem=problem_instances, config=config)
    runtime = result.runtime
    runtime = sorted(runtime, key=lambda r: r["log_rop"])
    import json
    with open('runtime_Lizard.json', 'w') as fout:
        json.dump(runtime, fout)

def estimation_example():
    sec = 350
    # Example: KCL‑RLWE
    problem.STATISTICAL_SEC = sec
    n = 2**10; q = 12289; m = 2*1024; stddev = sqrt(8) # TODO
    err_dis = distributions.GaussianSigma(sigma=stddev, q=q, componentwise=True, sec=sec)
    sec_dis = err_dis # "normal"
    config = algorithms_and_config.EstimationConfiguration(algorithms=["mitm"])
    lwe = problem.RLWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis)
    
    # estimates
    print("---------------------------------")
    print("LWE Estimates")
    print("---------------------------------")
    result = problem.estimate(parameter_problem=[lwe], config=config, sec=250)
    print("Result: is_secure=" + str(result.is_secure) + ", cost=" + str(result.cost) + ", info=" + str(result.info))
    # result = param_search.is_secure(parameter_problem=[lwe], sec=350, config=config)
    # print(["Insecure. ", "Secure! "][result.is_secure] + "Result: " + str(result.results))
    print()
    print()
    print()
    print()
    print()

    # # Example: SIS
    print("---------------------------------")
    print("SIS Estimates")
    print("---------------------------------")
    q = param_search.make_prime(2**(2*10+1), lbound=2**(2*10))
    m = (n * log(q, 2)).round()
    beta = err_dis.to_Loo(dimension=n) # componentwise beta bound (convert from Gaussian)
    sis = problem.RSIS(n=n, q=q, m=m, bound=beta)
    # estimates
    result = problem.estimate(parameter_problem=[sis], config=config)
    print("Result: is_secure=" + str(result.is_secure) + ", cost=" + str(result.cost) + ", info=" + str(result.info))
    # result = param_search.is_secure(parameter_problem=[sis], sec=350, config=config)
    # print(["Insecure. ", "Secure! "][result.is_secure] + "Result: " + str(result.results))


def Regev_example():
    config = algorithms_and_config.EstimationConfiguration()
    sec = 128
    def next_parameters(n, q=None, m=None, alpha=None):
        n, alpha, q = Param.Regev(n*2)
        m = n**2
        yield n, q, m, alpha
    
    def parameter_problem(n, q, m, alpha):
        distribution = distributions.GaussianAlpha(alpha=alpha, q=q)
        yield problem.LWE(n=n, q=q, m=m, secret_distribution=distribution, error_distribution=distribution)
    
    res = param_search.generic_search(sec, next(next_parameters(2**5)), next_parameters, param_search.unit_cost, parameter_problem, config)

    print("---------------------------------")
    print("Search successful")
    print(f"Parameters: {res['parameters']}")
    print(f"Estimate results: {str(res['result'])}")


def SIS_example():
    print("---------------------------------")
    print("SIS")
    print("---------------------------------")
    config = algorithms_and_config.EstimationConfiguration(algorithms=["combinatorial", "lattice-reduction"])
    sec = 128
    def next_parameters(n, q=None, m=None, beta=None):
        n, alpha, q = Param.Regev(n*2)
        beta = distributions.GaussianAlpha(alpha=alpha, q=q).to_Lp(sec=sec, dimension=n)
        m = n**2
        yield n, q, m, beta
    
    def parameter_problem(n, q, m, beta):
        yield problem.SIS(n=n, q=q, m=m, bound=beta)
    
    res = param_search.generic_search(sec, next(next_parameters(2**5)), next_parameters, param_search.unit_cost, parameter_problem, config)

    print("---------------------------------")
    print("Search successful")
    print(f"Parameters: {res['parameters']}")
    print(f"Estimate results: {str(res['result'])}")


def BGV_example():
    print("---------------------------------")
    print("BGV")
    print("---------------------------------")
    sec = 128
    config = algorithms_and_config.EstimationConfiguration()
    def next_parameters(N, p, q):
        N = 2 * N
        p = 1 # find p depending on new N
        q = 1 # find q depending on new N and p
        yield N, p, q

    def parameter_problem(N, p, q):
        yield problem.RLWE(N, q) # keys are secure
        yield problem.RLWE(N, q) # encryption is secure

    N, p, q, security = param_search.generic_search(sec, (2**10, None, None), next_parameters, param_search.unit_cost, parameter_problem, config)

def two_problem_search_example():
    print("---------------------------------")
    print("Two Problem Search Problem")
    print("---------------------------------")
    # k: width (over R_q) of commitment matrices
    # n: height (over R_q) of commitment matrices
    # l: dimension (over R_q) of message space
    # beta: norm bound for honest prover's randomness in Loo-norm
    # kappa: maximum L1-norm of any element in challenge space
    # sigma: stddev used in zero-knowledge proof => sigma = 11*kappa*beta*sqrt(k*N)
    # m: width of commitment matrix A_2' => m = k - n - l
    
    sec = 128
    sigma = 1
    N = 2**15
    p = 2**32
    q = p
    l = 1
    d1 = 1
    d2 = 1
    h = 2**56
    kappa = 11
    config = algorithms_and_config.EstimationConfiguration(algorithms=["usvp", "lattice-reduction"])
    
    def rejection_sample(dimension, modulus, bound, rho=100/99):
        assert dimension >= sec
        sigma = 12 / log(rho) * bound.to_L2().value
        gausssian = distributions.GaussianSigma(sigma, modulus, componentwise=False, sec=sec)
        return gausssian

    def amortized_rejection_sample(dimension, modulus, bound, rho=100/99):
        V = 2 * sec - 1
        response = rejection_sample(V * dimension, modulus, norm.Lp(sec * bound.value, bound.p, bound.dimension), rho)
        assert sec % 2 == 0
        amortization_slack = 2**(sec // 2)
        return norm.Lp(2 * amortization_slack * response.to_Loo(dimension=N).value, norm.oo, dimension=N)

    def next_parameters(q, d1, d2):
        yield 2 * q, d1, d2
        if q == p and d1 == 1:
            d2 = d2 + 1
            k = d2 + d1 + l
            for d1 in range(1, k - l):
                assert d1 + l < k
                yield q, d1, d2
        
    def parameter_cost(q, d1, d2):
        log_q = param_search.number_of_bits(q)
        log_p = param_search.number_of_bits(p)
        m = log_p * N * l
        r = log_q * N * (d2 + d1 + l)
        c = log_q * N * d1 + m
        return m + r + c

    def parameter_problem(q, d1, d2):
        gaussian = distributions.GaussianSigma(sigma, q, componentwise=False, sec=sec)
        normal_randomness = gaussian.to_Loo(dimension=N)
        normal_response = norm.Lp(normal_randomness.value * kappa, norm.oo, dimension=N) # left : Loo * right : L1 = Loo(left.value * right.value)
        normal_response_distribution = rejection_sample((d2 + d1 + l) * N, q, normal_response)
        amortized_response_distribution = amortized_rejection_sample((d2 + d1 + l), q, normal_randomness)

        def hiding(distribution):
            return problem.MLWE(N, d1 + l, q, d2 + d1 + l, distribution, distribution)

        def binding(norm):
            return problem.MSIS(N, d1, q, d2 + d1 + l, norm)

        yield hiding(gaussian)
        yield binding(normal_response_distribution.to_Loo(dimension=N))
        yield binding(norm.Lp(h * normal_response_distribution.to_Loo(dimension=N).value, norm.oo, dimension=N))
        yield binding(amortized_response_distribution.to_Loo(dimension=N))


    res = param_search.generic_search(sec, (q, d1, d2), next_parameters, parameter_cost, parameter_problem, config)

    print("---------------------------------")
    print("Search successful")
    print(f"Parameters: {res['parameters']}")
    print(f"Estimate results: {str(res['result'])}")

if __name__ == "__main__":
    # SIS_example()
    # Regev_example()
    # two_problem_search_example()
    two_problem_search_example()
    # import sage.misc.trace
    # sage.misc.trace.trace("runtime_analysis()")