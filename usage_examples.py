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
COST = r"Bit security $\log_2($rop$)$"
def alg_results_plotter(title, alg_results : problem.AggregateEstimationResult, runtime=True):

    logging.getLogger("matplotlib").setLevel(logging.INFO)
    import matplotlib.pyplot as plt
    import math

    res_dict = alg_results.get_algorithm_result_dict()
    n = 2 * len(res_dict)
    cols = 2 if runtime else 1

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
            if runtime:
                axs[i].plot(x, y, color + style, label=label)
                axs[i+1].plot(x, z, color + style, label=label)
            else:
                try:
                    ax = axs[i]
                except:
                    ax = axs
                ax.plot(x, z, color + style, label=label)

        if runtime:
            axs[i].set(ylabel=RUNTIME)
            axs[i+1].set(ylabel=COST)
        else:
            try:
                ax = axs[i]
            except:
                ax = axs
            ax.plot(x, z, color + style, label=label)
        i += 2
    
    try:
        for ax in axs.flat:
            ax.legend()
            ax.grid()
            ax.set(xlabel=r'Dimension $n$')
    except:
        axs.legend()
        axs.grid()
        axs.set(xlabel=r'Dimension $n$')
    plt.tight_layout()
    plt.savefig(title)
    plt.show()


def alg_tests(test_lwe = True, test_sis = True):
    problem.REDUCE_PROBLEMS = False
    import time
    config = algorithms.Configuration(conservative=True, parallel=True, algorithms=algorithms.ALL, timeout=200)

    if test_lwe:
        print("---------------------------------")
        print("Runtime Analysis LWE")
        print("---------------------------------")
        problem_instances = []
        std_dev = sqrt(8)
        for i in range(7, 14):
            n = 2**i
            q = param_search.make_prime(2**(i+1), lbound=2**i)
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = est.PlusInfinity()
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis, label="Regev-LWE"))

        start = time.time()
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(title=(f"LWE_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace('.', ','), alg_results=result)
        result.save_as_JSON((f"LWE_stddev={float(std_dev):.3f}_results_{total_runtime}s").replace('.', ','))

        print()
        print()
        print()

    if test_sis:
        print("---------------------------------")
        print("Runtime Analysis SIS")
        print("---------------------------------")
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
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(title=(f"SIS_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace('.', ','), alg_results=result)
        result.save_as_JSON((f"SIS_stddev={float(std_dev):.3f}_results_{total_runtime}s").replace('.', ','))

        print()
        print()
        print()

def hardness_tests():
    HARDNESS_LWE = False
    HARDNESS_SIS = True
    import time    

    if HARDNESS_LWE:
        # parameter q
        print("---------------------------------")
        print("Hardness Analysis for q in LWE")
        print("---------------------------------")
        problem_instances = []
        config = algorithms.Configuration(conservative=True, parallel=False, algorithms=[algorithms.USVP])
        n = 2**12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(8)
        m = est.PlusInfinity()
        for i in range(20):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis, label="Regev-LWE"))
            lbound *= 2
            q = param_search.make_prime(lbound * 2, lbound=lbound)

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="LWE_hardness_q", alg_results=result, runtime=False)
        result.save_as_JSON("LWE_hardness_q")

        # parameter alpha
        print("---------------------------------")
        print("Hardness Analysis for alpha in LWE")
        print("---------------------------------")
        problem_instances = []
        n = 2**12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(1/16)
        alpha = est.alphaf(est.sigmaf(std_dev), q)
        m = est.PlusInfinity()
        for i in range(30):
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis, label="Regev-LWE"))
            alpha *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="LWE_hardness_std_dev", alg_results=result, runtime=False)
        result.save_as_JSON("LWE_hardness_std_dev")

        # parameter m
        print("---------------------------------")
        print("Hardness Analysis for m in LWE")
        print("---------------------------------")
        problem_instances = []
        n = 2**12
        m = n/2
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(1/16)
        for i in range(30):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis, label="Regev-LWE"))
            m *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="LWE_hardness_m", alg_results=result, runtime=False)
        result.save_as_JSON("LWE_hardness_m")

    if HARDNESS_SIS:
        config = algorithms.Configuration(conservative=True, parallel=False, algorithms=[algorithms.LATTICE_REDUCTION])

        # parameter q
        print("---------------------------------")
        print("Hardness Analysis for q in SIS")
        print("---------------------------------")
        problem_instances = []
        n = 2**12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(8)
        m = est.PlusInfinity()
        for i in range(20):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, dimension=n)
            problem_instances.append(problem.SIS(n=n, q=q, m=m, bound=err_dis.to_Lp(sec=128), label="SIS"))
            lbound *= 2
            q = param_search.make_prime(lbound * 2, lbound=lbound)

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="SIS_hardness_q", alg_results=result, runtime=False)
        result.save_as_JSON("SIS_hardness_q")

        # parameter bound
        print("---------------------------------")
        print("Hardness Analysis for bound in SIS")
        print("---------------------------------")
        problem_instances = []
        n = 2**12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(1/16)
        m = est.PlusInfinity()
        for i in range(30):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, dimension=n)
            problem_instances.append(problem.SIS(n=n, q=q, m=m, bound=err_dis.to_Lp(sec=128), label="SIS"))
            std_dev *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="SIS_hardness_bound", alg_results=result, runtime=False)
        result.save_as_JSON("SIS_hardness_bound")

        # parameter m
        print("---------------------------------")
        print("Hardness Analysis for m in SIS")
        print("---------------------------------")
        problem_instances = []
        n = 2**12
        m = n/2
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(8)
        for i in range(30):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, dimension=n)
            problem_instances.append(problem.SIS(n=n, q=q, m=m, bound=err_dis.to_Lp(sec=128), label="SIS"))
            m *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="SIS_hardness_m", alg_results=result, runtime=False)
        result.save_as_JSON("SIS_hardness_m")


def alg_runtime_analysis():
    # TODO also write tests for parallel on/off
    pass

def alg_cost_analysis():
    # TODO perhaps combine with alg_runtime_analysis
    pass

def compare_to_literature_examples():
    # TODO
    config = algorithms.Configuration()
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


def rejection_sample(staticstical_sec, dimension, bound, out_dimension, rho=100/99):
        assert dimension >= staticstical_sec
        sigma = 12 / log(rho) * bound.to_L2().value
        gausssian = distributions.GaussianSigma(sigma, sec=staticstical_sec, dimension=out_dimension)
        return gausssian

def amortized_rejection_sample(staticstical_sec, dimension, bound, out_norm, out_dimension, rho=100/99):
    V = 2 * staticstical_sec - 1
    response = rejection_sample(staticstical_sec, V * dimension, staticstical_sec * bound, out_dimension, rho)
    assert staticstical_sec % 2 == 0
    amortization_slack = 2**(staticstical_sec // 2)
    if out_norm == 2:
        return 2 * amortization_slack * response.to_L2()
    elif out_norm == norm.oo:
        return 2 * amortization_slack * response.to_Loo()

def BGV_example():
    print("---------------------------------")
    print("BGV")
    print("---------------------------------")

    staticstical_sec = 80
    secret_distribution = distributions.GaussianS(3)
    error_distribution = distributions.GaussianS(3)
    encryption_error_distribution = distributions.GaussianS(3)

    class BgvLheCipher():
        def __init__(self, x, v, e1, e2):
            assert(x.dimension == v.dimension)
            assert(v.dimension == e1.dimension)
            assert(e1.dimension == e2.dimension)
            
            self.dimension = x.dimension
            self.x = x
            self.v = v
            self.e1 = e1
            self.e2 = e2

        @staticmethod
        def encryption_proof(N, p):
            gaussianV = encryption_error_distribution
            gaussianE1 = encryption_error_distribution
            gaussianE2 = encryption_error_distribution

            if p != 0:
                boundP = norm.Coo(N, (p - 1) // 2)
                sampledBoundP = amortized_rejection_sample(staticstical_sec, N, boundP, 2, N)
            else:
                sampledBoundP = norm.L1(N, 0)

            return BgvLheCipher(
                sampledBoundP,
                amortized_rejection_sample(staticstical_sec, N, gaussianV.to_L2(sec=staticstical_sec, dimension=N), 2, N).to_Coo(),
                amortized_rejection_sample(staticstical_sec, N, gaussianE1.to_L2(sec=staticstical_sec, dimension=N), 2, N).to_Coo(),
                amortized_rejection_sample(staticstical_sec, N, gaussianE2.to_L2(sec=staticstical_sec, dimension=N), 2, N).to_Coo()) 

        def bounds(self):
            return (self.x, self.v, self.e1, self.e2)

        def decryption_bound(self, p, s, e):
            bound = self.x + p * (e * self.v + self.e1 - s * self.e2)
            return bound.to_Coo()

        def __mul__(self, other):
            if isinstance(other, BgvLheCipher):
                return BgvSheCipher(
                    self.x * other.x,
                    self.v * other.x + other.v * self.x,
                    self.v * other.e1 + other.v * self.e1,
                    self.v * other.e2 + other.v * self.e2,
                    self.v * other.v,
                    self.e1 * other.x + other.e1 * self.x,
                    self.e2 * other.x + other.e2 * self.x,
                    self.e1 * other.e1,
                    self.e1 * other.e2 + other.e1 * self.e2,
                    self.e2 * other.e2)
            else:
                return BgvLheCipher(
                    other * self.x,
                    other * self.v,
                    other * self.e1,
                    other * self.e2)

        def __rmul__(self, other):
            return self * other

        def __add__(self, other):
            if isinstance(other, BgvLheCipher):
                return BgvLheCipher(
                    self.x + other.x,
                    self.v + other.v,
                    self.e1 + other.e1,
                    self.e2 + other.e2)
            
            if isinstance(other, norm.BaseNorm):
                return BgvLheCipher(
                    self.x + other,
                    self.v,
                    self.e1,
                    self.e2)

            return NotImplemented

        def __radd__(self, other):
            return self + other

        def __sub__(self, other):
            return self + other

        def __rsub__(self, other):
            return self + other

        def __str__(self):
            return f"LHE-BGV cipher (in dimension {self.dimension})"

    class BgvSheCipher():
        def __init__(self, x, ba, bap, baps, bbaa, p, ps, pp, pps, ppss):
            self.dimension = x.dimension
            assert(all(y.dimension == self.dimension for y in [ba, bap, baps, bbaa, p, ps, pp, pps, ppss]))

            self.partX = x
            self.partBA = ba
            self.partBAP = bap
            self.partBAPS = baps
            self.partBBAA = bbaa
            self.partP = p
            self.partPS = ps
            self.partPP = pp
            self.partPPS = pps
            self.partPPSS = ppss

        def decryption_bound(self, p, s, ss, e, ee):
            ba = p * e
            bap = p * ba
            baps = p * ba * s
            bbaa = p * p * ee
            ps = p * s
            pp = p * p
            pps = pp * s
            ppss = pp * ss

            bound = self.partX \
                + ba * self.partBA \
                + bap * self.partBAP \
                - baps * self.partBAPS \
                + bbaa * self.partBBAA \
                + p * self.partP \
                - ps * self.partPS \
                + pp * self.partPP \
                - pps * self.partPPS \
                + ppss * self.partPPSS
            return bound.to_Coo()

        def __mul__(self, other):
            if isinstance(other, (BgvLheCipher, BgvSheCipher)):
                raise TypeError("Cannot multiply BGV ciphertexts if was already multiplied")
        
            return BgvSheCipher(
                other * self.partX, 
                other * self.partBA,
                other * self.partBAP,
                other * self.partBAPS,
                other * self.partBBAA,
                other * self.partP,
                other * self.partPS,
                other * self.partPP,
                other * self.partPPS,
                other * self.partPPSS)

        def __rmul__(self, other):
            return self * other

        def __add__(self, other):
            if isinstance(other, BgvLheCipher):
                return BgvSheCipher(
                    self.partX + other.x, 
                    self.partBA + other.v,
                    self.partBAP,
                    self.partBAPS,
                    self.partBBAA,
                    self.partP + other.e1,
                    self.partPS + other.e2,
                    self.partPP,
                    self.partPPS,
                    self.partPPSS)

            if isinstance(other, BgvSheCipher):
                return BgvSheCipher(
                    self.partX + other.partX, 
                    self.partBA + other.partBA,
                    self.partBAP + other.partBAP,
                    self.partBAPS + other.partBAPS,
                    self.partBBAA + other.partBBAA,
                    self.partP + other.partP,
                    self.partPS + other.partPS,
                    self.partPP + other.partPP,
                    self.partPPS + other.partPPS,
                    self.partPPSS + other.partPPSS)

            if isinstance(other, norm.BaseNorm):
                return BgvSheCipher(
                    self.partX + other, 
                    self.partBA,
                    self.partBAP,
                    self.partBAPS,
                    self.partBBAA,
                    self.partP,
                    self.partPS,
                    self.partPP,
                    self.partPPS,
                    self.partPPSS)

            return NotImplemented

        def __radd__(self, other):
            return self + other

        def __sub__(self, other):
            return self + other

        def __rsub__(self, other):
            return self + other

        def __str__(self):
            return f"SHE-BGV cipher (in dimension {self.dimension})"
    
    computational_sec = 128
    p = 2**64
    n = 2 
    config = algorithms.Configuration()
    def next_parameters(N, q):
        N = 2 * N

        s = secret_distribution.to_L2(sec=staticstical_sec, dimension=N).to_Coo()
        e = error_distribution.to_L2(sec=staticstical_sec, dimension=N).to_Coo()
        ss = s * s
        ee = e * e

        zkp = BgvLheCipher.encryption_proof(N, p)

        def decrypt(cipher):
            return n * amortized_rejection_sample(staticstical_sec, N, (2**staticstical_sec + 1) * cipher.decryption_bound(p, s, ss, e, ee), 2, N).to_Coo()

        a = n * zkp
        b = n * zkp
        c = a * b
        
        r = n * zkp

        bound = decrypt(c + r)
        q = 2 * ceil(bound.value)
        yield N, q

    def parameter_problem(N, q):
        if q is not None:
            yield problem.RLWE(N, q, norm.oo, secret_distribution, error_distribution) # keys are secure
            yield problem.RLWE(N, q, 1, secret_distribution, encryption_error_distribution) # encryption is secure

    res = param_search.generic_search(computational_sec, (2**10, None), next_parameters, param_search.unit_cost, parameter_problem, config)
    res_params = res["parameters"]
    res_alg_results : problem.AggregateEstimationResult = res["result"]

    res_params = res["parameters"]
    res_alg_results : problem.AggregateEstimationResult = res["result"]
    print(res_params)
    for k, v in res_alg_results.get_algorithm_result_dict(sort_by_rop=True).items():
        print(f"{k}:")
        for x in v:
            print(f" - {x}")


    print(algorithms.SEPARATOR)
    print("Search successful")

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
    staticstical_sec = 128
    computational_sec = 80
    sigma = 1
    N = 2**15
    p = 2**64
    # TODO: try coded-bkw and mitm for the parameters
    q = p
    l = 1
    d1 = 1
    d2 = 1
    h = 2**92
    kappa = 6

    lattice_parameter_estimation.Logging.set_estimation_debug_logging_level(logging.INFO)
    config = algorithms.Configuration()

    def next_parameters(q, d1, d2):
        yield 2 * q, d1, d2
        if q == p and d1 == 1:
            k = d2 + d1 + l + 1
            for d1 in range(1, k - l):
                d2 = k - d1 - l
                assert d1 + l < k
                assert d1 + d2 + l == k
                yield q, d1, d2
        
    def parameter_cost(q, d1, d2):
        log_q = param_search.number_of_bits(q)
        log_p = param_search.number_of_bits(p)
        m = log_p * N * l
        r = log_q * N * (d2 + d1 + l)
        c = log_q * N * d1 + m
        return m + r + c

    def parameter_problem(q, d1, d2):
        k = d1 + d2 + l
        challenge_bound = norm.L1(dimension=N, value=kappa)
        approximation_bound = challenge_bound - challenge_bound
        normal_sample = norm.Loo(dimension=N, value=1)
        amortized_zk_response_2 = amortized_rejection_sample(staticstical_sec, k * N, normal_sample, 2, N)
        amortized_zk_response_oo = amortized_rejection_sample(staticstical_sec, k * N, normal_sample, norm.oo, N)

        differenceHom = h * amortized_zk_response_oo - h * normal_sample
        ## should not break binding between a normally obtained commitment and one that we can extract for the adversary
        differenceZKP = h * approximation_bound.to_L2() * amortized_zk_response_2 - 2 * rejection_sample(staticstical_sec, N, challenge_bound * h * normal_sample, N).to_Loo()
        ## should not break binding between what we prove in the final ZKP and a commitment that we can extract for the adversary
        differenceOut = approximation_bound * normal_sample - 2 * rejection_sample(staticstical_sec, N, challenge_bound * normal_sample, N).to_Loo()
        ## should not break binding for what is opened as output
        assert differenceHom.p == norm.oo
        assert differenceZKP.p == norm.oo
        assert differenceOut.p == norm.oo

        def hiding(distribution):
            return problem.MLWE(N, d1 + l, q, k, distribution, distribution)

        def binding(norm):
            return problem.MSIS(N, d1, q, k, norm)

        yield hiding(distributions.Uniform(1))
        yield binding(differenceHom)
        yield binding(differenceZKP)
        yield binding(differenceOut)


    res = param_search.generic_search(computational_sec, (q, d1, d2), next_parameters, parameter_cost, parameter_problem, config)

    res_params = res["parameters"]
    res_alg_results : problem.AggregateEstimationResult = res["result"]
    print(res_params)
    for k, v in res_alg_results.get_algorithm_result_dict(sort_by_rop=True).items():
        print(f"{k}:")
        for x in v:
            print(f" - {x}")


    print(algorithms.SEPARATOR)
    print("Search successful")


def test_reduction():
    pass


if __name__ == "__main__":
    # SIS_example()
    # Regev_example()
    # two_problem_search_example()
    # runtime_and_cost_analysis()
    # import sage.misc.trace
    # sage.misc.trace.trace("runtime_analysis()")
    fire.Fire()