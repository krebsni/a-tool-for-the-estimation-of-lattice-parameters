#!/usr/bin/env sage
from bisect import bisect
from multiprocessing import Value
import fire
import sys
import os
import inspect
import logging

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
parentdir = os.path.dirname(currentdir)
sys.path.insert(0, parentdir)

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

logging.basicConfig(level=logging.DEBUG)  # set to INFO to hide exceptions
logger = logging.getLogger(__name__)

lattice_parameter_estimation.Logging.set_level(logging.DEBUG)


RUNTIME = "Runtime [s]"
COST = r"Bit security $\log_2($rop$)$"


def alg_results_plotter(
    title, alg_results: problem.AggregateEstimationResult, runtime=True
):

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

    i = 0  # position in plot
    for inst in res_dict:
        # plot for each instance
        res_list = sorted(res_dict[inst], key=lambda x: x.params["n"])
        algn_list = sorted(list({algn for algn in (x.alg_name for x in res_list)}))
        algn_color = {}
        colors = ["b", "g", "r", "c", "m", "y", "k"]
        j = 0
        for algn in algn_list:
            algn_color[algn] = colors[j]
            j += 1

        # styles = ['-', '--', '-.', ':', '.', ',', 'o', 'v', '^', '<', '>', 's', 'p', '*']
        for algn in algn_color:
            label = algn  # + ["", f" (Cost model: {cname})"][cname != "-"]
            color = algn_color[algn]
            x = sorted(
                list(set([x.params["n"] for x in res_list if x.alg_name == algn]))
            )
            y = []
            z = []

            for n in x:
                y.append(
                    min(
                        [
                            r.runtime
                            for r in res_list
                            if r.alg_name == algn and r.params["n"] == n
                        ]
                    )
                )
                z.append(
                    min(
                        [
                            log(abs(r.cost["rop"]), 2).n()
                            for r in res_list
                            if r.alg_name == algn and r.params["n"] == n
                        ]
                    )
                )
            style = "-." if algn == "lattice-reduction-rs" else "-"
            if runtime:
                axs[i].plot(x, y, color + style, label=label)
                axs[i + 1].plot(x, z, color + style, label=label)
            else:
                try:
                    ax = axs[i]
                except:
                    ax = axs
                ax.plot(x, z, color + style, label=label)

        if runtime:
            axs[i].set(ylabel=RUNTIME)
            axs[i + 1].set(ylabel=COST)
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
            ax.set(xlabel=r"Dimension $n$")
    except:
        axs.legend()
        axs.grid()
        axs.set(xlabel=r"Dimension $n$")
    plt.tight_layout()
    plt.savefig(title + ".pdf", format="pdf")
    plt.show()


def alg_tests(test_lwe=True, test_sis=True):
    long = False
    problem.REDUCE_PROBLEMS = False
    import time

    config = algorithms.Configuration(
        conservative=True, parallel=True, algorithms=algorithms.ALL, timeout=200
    )

    if test_lwe and long:
        print("---------------------------------")
        print("Runtime Analysis LWE")
        print("---------------------------------")
        problem_instances = []
        std_dev = sqrt(8)
        for i in range(7, 14):
            n = 2 ** i
            q = param_search.make_prime(2 ** (i + 1), lbound=2 ** i)
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = est.PlusInfinity()
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(
                problem.LWE(
                    n=n,
                    q=q,
                    m=m,
                    secret_distribution=sec_dis,
                    error_distribution=err_dis,
                    label="Regev-LWE",
                )
            )

        start = time.time()
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(
            title=(f"LWE_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace(
                ".", ","
            ),
            alg_results=result,
        )
        result.save_as_JSON(
            (f"LWE_stddev={float(std_dev):.3f}_results_{total_runtime}s").replace(
                ".", ","
            )
        )

        print()
        print()
        print()

    if test_lwe and not long:
        print("---------------------------------")
        print("Runtime Analysis LWE short algs")
        print("---------------------------------")
        problem_instances = []
        std_dev = sqrt(8)
        for i in range(7, 14):
            n = 2 ** i
            q = param_search.make_prime(2 ** (i + 1), lbound=2 ** i)
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = est.PlusInfinity()
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(
                problem.LWE(
                    n=n,
                    q=q,
                    m=m,
                    secret_distribution=sec_dis,
                    error_distribution=err_dis,
                    label="Regev-LWE",
                )
            )
        start = time.time()
        result = problem.estimate(
            parameter_problems=problem_instances,
            config=algorithms.Configuration(
                conservative=True,
                parallel=True,
                algorithms=list(
                    set(algorithms.ALL)
                    - set(
                        [algorithms.ARORA_GB, algorithms.CODED_BKW, algorithms.DECODE]
                    )
                ),
                timeout=200,
            ),
        )
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(
            title=(f"LWE_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace(
                ".", ","
            ),
            alg_results=result,
        )
        result.save_as_JSON(
            (
                f"LWE_short_runtime_stddev={float(std_dev):.3f}_results_{total_runtime}s"
            ).replace(".", ",")
        )

        print()
        print()
        print()

    if test_lwe and long:
        print("---------------------------------")
        print("Runtime Analysis LWE")
        print("---------------------------------")
        problem_instances = []
        std_dev = 1 / 8
        for i in range(7, 14):
            n = 2 ** i
            q = param_search.make_prime(2 ** (i + 1), lbound=2 ** i)
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = est.PlusInfinity()
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(
                problem.LWE(
                    n=n,
                    q=q,
                    m=m,
                    secret_distribution=sec_dis,
                    error_distribution=err_dis,
                    label="Regev-LWE",
                )
            )

        start = time.time()
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(
            title=(f"LWE_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace(
                ".", ","
            ),
            alg_results=result,
        )
        result.save_as_JSON(
            (f"LWE_stddev={float(std_dev):.3f}_results_{total_runtime}s").replace(
                ".", ","
            )
        )

        print()
        print()
        print()

    if test_lwe and not long:
        print("---------------------------------")
        print("Runtime Analysis LWE")
        print("---------------------------------")
        problem_instances = []
        std_dev = 1 / 8
        for i in range(7, 14):
            n = 2 ** i
            q = param_search.make_prime(2 ** (i + 1), lbound=2 ** i)
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = est.PlusInfinity()
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(
                problem.LWE(
                    n=n,
                    q=q,
                    m=m,
                    secret_distribution=sec_dis,
                    error_distribution=err_dis,
                    label="Regev-LWE",
                )
            )

        start = time.time()
        result = problem.estimate(
            parameter_problems=problem_instances,
            config=algorithms.Configuration(
                conservative=True,
                parallel=True,
                algorithms=list(
                    set(algorithms.ALL)
                    - set(
                        [algorithms.ARORA_GB, algorithms.CODED_BKW, algorithms.DECODE]
                    )
                ),
                timeout=200,
            ),
        )
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(
            title=(f"LWE_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace(
                ".", ","
            ),
            alg_results=result,
        )
        result.save_as_JSON(
            (f"LWE_stddev={float(std_dev):.3f}_results_{total_runtime}s").replace(
                ".", ","
            )
        )

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
            n = 2 ** i
            q = param_search.make_prime(2 ** (2 * i + 1), lbound=2 ** (2 * i))
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            m = n ** 2
            err_dis = distributions.GaussianAlpha(
                alpha=alpha, q=q, sec=128, dimension=n
            )
            beta = err_dis.to_Loo()  # componentwise beta bound (convert from Gaussian)
            problem_instances.append(
                problem.SIS(n=n, q=q, m=m, bound=beta, label="SIS")
            )

        start = time.time()
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        total_runtime = str(round(time.time() - start))
        print("---------------------------------")
        print(f"Estimates complete (took {total_runtime}s)")
        alg_results_plotter(
            title=(f"SIS_stddev={float(std_dev):.3f}_plots_{total_runtime}s").replace(
                ".", ","
            ),
            alg_results=result,
        )
        result.save_as_JSON(
            (f"SIS_stddev={float(std_dev):.3f}_results_{total_runtime}s").replace(
                ".", ","
            )
        )

        print()
        print()
        print()


def hardness_tests():
    HARDNESS_LWE = True
    HARDNESS_SIS = True
    import time

    if HARDNESS_LWE:
        # parameter q
        print("---------------------------------")
        print("Hardness Analysis for q in LWE")
        print("---------------------------------")
        problem_instances = []
        config = algorithms.Configuration(
            conservative=True, parallel=False, algorithms=[algorithms.USVP]
        )
        n = 2 ** 12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(8)
        m = est.PlusInfinity()
        for i in range(20):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(
                problem.LWE(
                    n=n,
                    q=q,
                    m=m,
                    secret_distribution=sec_dis,
                    error_distribution=err_dis,
                    label="Regev-LWE",
                )
            )
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
        n = 2 ** 12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(1 / 16)
        alpha = est.alphaf(est.sigmaf(std_dev), q)
        m = est.PlusInfinity()
        for i in range(30):
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(
                problem.LWE(
                    n=n,
                    q=q,
                    m=m,
                    secret_distribution=sec_dis,
                    error_distribution=err_dis,
                    label="Regev-LWE",
                )
            )
            alpha *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(
            title="LWE_hardness_std_dev", alg_results=result, runtime=False
        )
        result.save_as_JSON("LWE_hardness_std_dev")

        # parameter m
        print("---------------------------------")
        print("Hardness Analysis for m in LWE")
        print("---------------------------------")
        problem_instances = []
        n = 2 ** 12
        m = n / 2
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(1 / 16)
        for i in range(30):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q)
            sec_dis = err_dis
            problem_instances.append(
                problem.LWE(
                    n=n,
                    q=q,
                    m=m,
                    secret_distribution=sec_dis,
                    error_distribution=err_dis,
                    label="Regev-LWE",
                )
            )
            m *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="LWE_hardness_m", alg_results=result, runtime=False)
        result.save_as_JSON("LWE_hardness_m")

    if HARDNESS_SIS:
        config = algorithms.Configuration(
            conservative=True, parallel=False, algorithms=[algorithms.LATTICE_REDUCTION]
        )

        # parameter q
        print("---------------------------------")
        print("Hardness Analysis for q in SIS")
        print("---------------------------------")
        problem_instances = []
        n = 2 ** 12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(8)
        m = est.PlusInfinity()
        for i in range(20):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, dimension=n)
            problem_instances.append(
                problem.SIS(n=n, q=q, m=m, bound=err_dis.to_Lp(sec=128), label="SIS")
            )
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
        n = 2 ** 12
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(1 / 16)
        m = est.PlusInfinity()
        for i in range(30):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, dimension=n)
            problem_instances.append(
                problem.SIS(n=n, q=q, m=m, bound=err_dis.to_Lp(sec=128), label="SIS")
            )
            std_dev *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(
            title="SIS_hardness_bound", alg_results=result, runtime=False
        )
        result.save_as_JSON("SIS_hardness_bound")

        # parameter m
        print("---------------------------------")
        print("Hardness Analysis for m in SIS")
        print("---------------------------------")
        problem_instances = []
        n = 2 ** 12
        m = n / 2
        lbound = n
        q = param_search.make_prime(lbound * 2, lbound=lbound)
        std_dev = sqrt(8)
        for i in range(30):
            alpha = est.alphaf(est.sigmaf(std_dev), q)
            err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, dimension=n)
            problem_instances.append(
                problem.SIS(n=n, q=q, m=m, bound=err_dis.to_Lp(sec=128), label="SIS")
            )
            m *= 2

        result = problem.estimate(parameter_problems=problem_instances, config=config)
        alg_results_plotter(title="SIS_hardness_m", alg_results=result, runtime=False)
        result.save_as_JSON("SIS_hardness_m")


if __name__ == "__main__":
    alg_tests()
