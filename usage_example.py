#!/usr/bin/env sage
from bisect import bisect
from multiprocessing import Value
import fire
import sys
import os
import logging

from matplotlib.pyplot import ylabel
from lattice_parameter_estimation import algorithms
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

lattice_parameter_estimation.Logging.set_level(logging.DEBUG)

# TODO: put in config file or so? param_search needs to be imported for logging level to be set (?)

RUNTIME = "Runtime [s]"
COST = r"Bit security [$\log_2($rop$)$]"
def alg_results_plotter(title, alg_results : problem.AggregateEstimationResult):

    logging.getLogger("matplotlib").setLevel(logging.INFO)
    import matplotlib.pyplot as plt
    import math

    res_dict = alg_results.get_algorithm_result_dict()
    n = 2 * len(res_dict)
    cols = 2
    rows = int(math.ceil(n / cols))
    fig, axs = plt.subplots(rows, cols, sharex=True, sharey=False)
    try:
        axs = axs.flatten()
    except:
        pass

    i = 0 # position in plot
    for inst in res_dict:
        # plot for each instance
        res_list = sorted(res_dict[inst], key=lambda x: x.params["n"])
        algn_list = sorted(list({algn for algn in (x.alg_name for x in res_list)}))      
        algn_color = {}
        colors = ['b', 'g', 'r', 'c', 'm', 'y', 'k']
        j = 0
        for algn in algn_list:
            algn_color[algn] = colors[j]
            j += 1

        # styles = ['-', '--', '-.', ':', '.', ',', 'o', 'v', '^', '<', '>', 's', 'p', '*']    
        for algn in algn_color:
            label = algn # + ["", f" (Cost model: {cname})"][cname != "-"]
            color = algn_color[algn]
            x = sorted(list(set([x.params["n"] for x in res_list if x.alg_name == algn])))
            y = []
            z = []
   
            for n in x:
                y.append(min([r.runtime for r in res_list 
                            if r.alg_name == algn and r.params["n"] == n]))
                z.append(min([log(abs(r.cost["rop"]),2).n() for r in res_list 
                            if r.alg_name == algn and r.params["n"] == n]))
            style = '-.' if algn == "lattice-reduction-rs" else '-'
            axs[i].plot(x, y, color + style, label=label)
            axs[i+1].plot(x, z, color + style, label=label)
        axs[i].set(ylabel=RUNTIME)
        axs[i+1].set(ylabel=COST)
        i += 2
    
    for ax in axs.flat:
        ax.legend()
        ax.grid()
        ax.set(xlabel=r'Dimension $n$')
    
    plt.tight_layout()
    plt.savefig(title)
    plt.show()


    # # Mean of different cost models
    # from statistics import mean
    # algs = set([algn for algn in (x["algname"] for x in runtime)])
    # n_set = sorted(set([x["parameters"]["n"] for x in runtime]))
    # algs_res = {}
    # for algn in algs:
    #     cmodels = {x["cname"] for x in runtime if x["algname"] == algn}
    #     algs_res[algn] = {}
        
    #     mean_runtime = []
    #     for n in n_set:
    #         mean_runtime.append(mean([x for x in runtime if (x["algname"] == algn and x["parameters"]["n"] == n)]))
    #     mean_runtime = sorted(mean_runtime, key=lambda k : k["parameters"]["n"])

    # fig1, ax1 = plt.subplots(1,1)
    # colors = ['b', 'g', 'r', 'c', 'm', 'y', 'k']
    # i = 0
    # for algn in algs_res:
    #     label = algn + ["", f" (Cost model: {cname})"][cname != "-"]
    #     ax1.plot([x["parameters"]["n"] for x in algs_res[algn][cname]], [x["runtime"] for x in algs_res[algn][cname]], colors[i] + '-', label=label)
    #     i += 1
    # ax1.set_xlabel(r'Secret dimension $n$')
    # ax1.set_ylabel('Runtime [s]')
    # ax1.set_title(title)
    # ax1.legend()
    # plt.grid()
    # plt.savefig(output_file_name + "_mean")
    # plt.show()

def alg_runtime_analysis():
    # TODO also write tests for parallel on/off
    pass

def alg_cost_analysis():
    # TODO perhaps combine with alg_runtime_analysis
    pass

def compare_to_literature_examples():
    pass

def runtime_and_cost_analysis():
    LWE = False
    SIS = True
    import time
    if LWE:
        print("---------------------------------")
        print("Runtime Analysis LWE")
        print("---------------------------------")
        std_dev = sqrt(8**(-2))
        problem_instances = []
        for i in range(7, 14):
            n = 2**i
            q = param_search.make_prime(2**(i+1), lbound=2**i)
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = est.PlusInfinity()
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis, label="Regev-LWE"))

        start = time.time()
        config = algorithms.Configuration(conservative=True, parallel=True, algorithms=algorithms.ALL, timeout=200)
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(title=(f"LWE_stddev={std_dev:.3f}_plots_{total_runtime}s").replace('.', ','), alg_results=result)
        result.save_as_JSON((f"LWE_stddev={std_dev:.3f}_results_{total_runtime}s").replace('.', ','))

        print()
        print()
        print()
    
    if SIS:
        print("---------------------------------")
        print("Runtime Analysis SIS")
        print("---------------------------------")
        import time
        std_dev = sqrt(8)
        problem_instances = []
        for i in range(7, 14):
            n = 2**i
            q = param_search.make_prime(2**(2*i + 1), lbound=2**(2*i))
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = n**2
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, sec=128, dimension=n)
            beta = err_dis.to_Loo() # componentwise beta bound (convert from Gaussian)
            problem_instances.append(problem.SIS(n=n, q=q, m=m, bound=beta, label="SIS"))

        start = time.time()
        config = algorithms.Configuration(conservative=True, parallel=True, algorithms=algorithms.ALL, timeout=200)
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(title=(f"SIS_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace('.', ','), alg_results=result)
        result.save_as_JSON((f"SIS_stddev={float(std_dev):.3f}_results_{total_runtime}s").replace('.', ','))
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
    n = 2**15; q = 12289; m = 2*1024; stddev = sqrt(8**(-3)) # TODO
    err_dis = distributions.GaussianSigma(sigma=stddev, q=q, componentwise=True, sec=sec)
    sec_dis = err_dis # "normal"
    config = algorithms.Configuration(algorithms=[algorithms.MITM, algorithms.LATTICE_REDUCTION])
    lwe = problem.RLWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis)
    
    # estimates
    print("---------------------------------")
    print("LWE Estimates")
    print("---------------------------------")
    result = problem.estimate(parameter_problems=[lwe], config=config, sec=250)
    import json
    print("Result: " + str(result))
    print(json.dumps(result.to_dict(), indent=4))
    # result = param_search.is_secure(parameter_problem=[lwe], sec=350, config=config)
    # print(["Insecure. ", "Secure! "][result.is_secure] + "Result: " + str(result.results))


    # # Example: SIS
    print("---------------------------------")
    print("SIS Estimates")
    print("---------------------------------")
    q = param_search.make_prime(2**(2*10+1), lbound=2**(2*10))
    m = (n * log(q, 2)).round()
    beta = err_dis.to_Loo(dimension=n) # componentwise beta bound (convert from Gaussian)
    sis = problem.RSIS(n=n, q=q, m=m, bound=beta)
    # estimates
    result = problem.estimate(parameter_problems=[sis], config=config)
    print("Result: " + json.dumps(result, indent=4))
    # result = param_search.is_secure(parameter_problem=[sis], sec=350, config=config)
    # print(["Insecure. ", "Secure! "][result.is_secure] + "Result: " + str(result.results))


def Regev_example():
    config = algorithms.Configuration(algorithms=[algorithms.DUAL])
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
    config = algorithms.Configuration(algorithms=[algorithms.COMBINATORIAL, algorithms.LATTICE_REDUCTION], parallel=False)
    sec = 128
    def next_parameters(n, q=None, m=None, beta=None):
        n, alpha, q = Param.Regev(n*2)
        beta = distributions.GaussianAlpha(alpha=alpha, q=q).to_Lp(sec=sec, dimension=n)
        m = n**2
        yield n, q, m, beta
    
    def parameter_problem(n, q, m, beta):
        yield problem.SIS(n=n, q=q, m=m, bound=beta, label="SIS-Regev")
    
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
    config = algorithms.Configuration()
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
    problem.RUNTIME_ANALYSIS = False
    sec = 128
    sigma = 1
    N = 2**15
    # p = 205688069665150755269371147819668813122841983204197482918576128
    p = 2**128
    # TODO: try coded-bkw and mitm for the parameters
    q = p
    l = 1
    d1 = 1
    d2 = 1
    h = 2**155
    kappa = 10
    lattice_parameter_estimation.Logging.set_estimation_debug_logging_level(logging.INFO)
    config = algorithms.Configuration(conservative=True, algorithms=algorithms.ALL, parallel=True, security_strategy=algorithms.SOME_SECURE)
    
    def rejection_sample(dimension, modulus, bound, rho=100/99):
        assert dimension >= sec
        sigma = 12 / log(rho) * bound.to_L2().value
        gausssian = distributions.GaussianSigma(sigma, modulus, componentwise=False, sec=sec, dimension=N)
        return gausssian

    def amortized_rejection_sample(dimension, modulus, bound, rho=100/99):
        V = 2 * sec - 1
        response = rejection_sample(V * dimension, modulus, norm.Lp(sec * bound.value, bound.p, bound.dimension), rho)
        assert sec % 2 == 0
        amortization_slack = 2**(sec // 2)
        return norm.Lp(2 * amortization_slack * response.to_Loo().value, norm.oo, dimension=N)

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
        gaussian = distributions.GaussianSigma(sigma, q, componentwise=False, sec=sec, dimension=N)
        normal_randomness = gaussian.to_Loo()
        normal_response = norm.Lp(normal_randomness.value * kappa, norm.oo, dimension=N) # left : Loo * right : L1 = Loo(left.value * right.value)
        normal_response_distribution = rejection_sample((d2 + d1 + l) * N, q, normal_response)
        amortized_response_distribution = amortized_rejection_sample((d2 + d1 + l), q, normal_randomness)

        def hiding(distribution):
            return problem.MLWE(N, d1 + l, q, d2 + d1 + l, distribution, distribution)

        def binding(norm):
            return problem.MSIS(N, d1, q, d2 + d1 + l, norm)

        yield hiding(gaussian)
        yield binding(normal_response_distribution.to_Loo())
        yield binding(norm.Lp(h * normal_response_distribution.to_Loo().value, norm.oo, dimension=N))
        yield binding(amortized_response_distribution.to_Loo())


    res = param_search.generic_search(sec, (q, d1, d2), next_parameters, parameter_cost, parameter_problem, config)

    res_params = res.parameters
    res_alg_results : problem.AggregateEstimationResult = res.results
    print(res_alg_results.get_algorithm_result_dict(sort_by_rop=True))


    print(algorithms.SEPARATOR)
    print("Search successful")


if __name__ == "__main__":
    # SIS_example()
    # Regev_example()
    # two_problem_search_example()
    # runtime_and_cost_analysis()
    # import sage.misc.trace
    # sage.misc.trace.trace("runtime_analysis()")
    fire.Fire()