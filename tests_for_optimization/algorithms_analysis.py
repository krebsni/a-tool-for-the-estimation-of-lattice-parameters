#!/usr/bin/env sage
from bisect import bisect
import math
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
    title: str,
    alg_results: problem.AggregateEstimationResult,
    runtime=True,
    max_y=None,
    height=3.5,
):

    logging.getLogger("matplotlib").setLevel(logging.INFO)
    import matplotlib.pyplot as plt
    import math

    res_dict = alg_results.get_algorithm_result_dict()
    n = 2 * len(res_dict)
    cols = 2 if runtime else 1

    rows = int(math.ceil(n / cols))
    fig, axs = plt.subplots(rows, cols, sharex=True, sharey=False)
    if height:
        fig.set_size_inches(h=height, w=6.4)

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
        if "LWE" in title:
            colors = {
                "arora-gb": "b",
                "coded-bkw": "g",
                "dual-scale": "r",
                "dual-scale-without-lll": "c",
                "mitm": "m",
                "primal-decode": "y",
                "primal-usvp": "k",
            }
        elif "SIS" in title:
            colors = {
                "combinatorial": "b",
                "combinatorial-cons": "g",
                "lattice-reduction": "r",
                "lattice-reduction-rs": "c",
            }
        else:
            colors = ["b", "g", "r", "c", "m", "y", "k"]

        j = 0
        for algn in algn_list:
            if "SIS" in title or "LWE" in title:
                algn_color[algn] = colors[algn]
            else:
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
            if algn == "lattice-reduction-rs" or algn == "combinatorial-cons":
                style = "-."
            else:
                style = "-"
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
            if max_y:
                axs[i + 1].set_ylim([0, max_y])
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


def get_LWE_Regev(n, sec=None):
    # [Reg05]
    n, alpha, q = Param.Regev(n)
    err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, sec=sec)
    sec_dis = err_dis  # "normal"
    return problem.LWE(
        n=n,
        q=q,
        m=est.oo,
        secret_distribution=sec_dis,
        error_distribution=err_dis,
        label="LWE",
    )


def get_LWE_other(n, sec=None):
    m = est.oo
    sigma = sqrt(8)
    q = param_search.make_prime(n ** 2, lbound=n)
    err_dis = distributions.GaussianSigma(sigma=sigma, q=q, sec=sec)
    sec_dis = err_dis  # "normal"
    return problem.LWE(
        n=n,
        q=q,
        m=est.oo,
        secret_distribution=sec_dis,
        error_distribution=err_dis,
        label="LWE",
    )


def get_SIS(n, sec):
    # use [MP12] to get an SIS problem instance
    q = param_search.make_prime(2 * n ** 2, lbound=n ** 2)
    m = 2 * n * log(q, 2)
    s = 2 * sqrt(n * log(q, 2))
    beta = distributions.GaussianS(s, q, 128, n)  # internally converted to bound
    return problem.SIS(n=n, q=q, m=m, bound=beta, label="SIS")


def alg_tests(test_lwe=False, test_sis=True):
    long = False
    problem.REDUCE_PROBLEMS = False
    import time

    config = algorithms.Configuration(
        conservative=True, parallel=True, algorithms=algorithms.ALL, timeout=200
    )

    config_short = algorithms.Configuration(
        conservative=True,
        parallel=True,
        algorithms=list(
            set(algorithms.ALL)
            - set([algorithms.ARORA_GB, algorithms.CODED_BKW, algorithms.DECODE])
        ),
        timeout=200,
    )

    def test_LWE(config, tag, get_LWE, max_y=None, max_i=14, height=None):
        print("---------------------------------")
        print("Runtime Analysis LWE " + tag)
        print("---------------------------------")
        problem_instances = []

        for i in range(7, max_i):
            n = 2 ** i
            problem_instances.append(get_LWE(n))
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        result.save_as_JSON("LWE_" + tag)
        alg_results_plotter(title="LWE_plot_" + tag, alg_results=result, max_y=max_y)

    def test_SIS(config, max_y=None, tag="", max_i=14, height=None):
        print("---------------------------------")
        print("Runtime Analysis SIS")
        print("---------------------------------")
        problem_instances = []
        for i in range(7, max_i):
            n = 2 ** i
            problem_instances.append(get_SIS(n, sec=128))
        result = problem.estimate(parameter_problems=problem_instances, config=config)
        result.save_as_JSON("SIS")
        alg_results_plotter(title="SIS_plot_" + tag, alg_results=result, max_y=max_y)

    # test_LWE(
    #     config, tag="Regev_long", get_LWE=get_LWE_Regev, max_y=10000, max_i=14, height=5
    # )
    # test_LWE(
    #     config,
    #     tag="Regev_long_small",
    #     get_LWE=get_LWE_Regev,
    #     max_y=None,
    #     max_i=11,
    #     height=5,
    # )
    # test_LWE(
    #     config_short, tag="Regev_short", get_LWE=get_LWE_Regev, max_y=None, max_i=14
    # )
    # test_LWE(config, tag="long", get_LWE=get_LWE_other, max_y=5000, max_i=14)
    # test_LWE(config_short, tag="short", get_LWE=get_LWE_other, max_y=5000, max_i=14)
    test_SIS(config_short, tag="", max_y=None, max_i=14)
    # test_SIS(config_short, tag="small", max_y=2000, max_i=11)


if __name__ == "__main__":
    alg_tests()
