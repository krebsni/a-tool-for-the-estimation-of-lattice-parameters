from mpl_toolkits.mplot3d import Axes3D
from cost_models_log import BKZ_COST_MODELS


def runtime_results():
    import json
    import statistics
    import matplotlib.pyplot as plt
    import matplotlib as mpl

    with open("runtime_Regev.json") as json_file:
        runtime = json.load(json_file)

    # data = [x for x in data if x["successful"] == True]
    # algs = {algn for algn in (x["algname"] for x in data)}
    # print(algs)
    # avg_list = [(algn, statistics.mean([x["log_rop"] for x in data if x["algname"] == algn])) for algn in algs]
    # # for algn in algs:
    # #     avg_list.append((algn, [x["runtime"] for x in data if x["algname"] == algn]))

    algs = {algn for algn in (x["algname"] for x in runtime)}
    algs_res = {}
    for algn in algs:
        cmodels = {x["cname"] for x in runtime if x["algname"] == algn}
        algs_res[algn] = {}
        for cname in cmodels:
            algs_res[algn][cname] = sorted(
                [x for x in runtime if (x["algname"] == algn and x["cname"] == cname)],
                key=lambda k: k["parameters"]["n"],
            )

    fig1, ax1 = plt.subplots(1, 1)
    colors = ["b", "g", "r", "c", "m", "y", "k"]
    styles = ["-", "--", "-.", ":", ".", ",", "o", "v", "^", "<", ">", "s", "p", "*"]
    i = 0
    for algn in algs_res:
        j = 0
        for cname in algs_res[algn]:
            label = algn + ["", f" (Cost model: {cname})"][cname != "-"]
            ax1.plot(
                [x["parameters"]["n"] for x in algs_res[algn][cname]],
                [x["runtime"] for x in algs_res[algn][cname]],
                colors[i] + styles[j],
                label=label,
            )
            j += 1
        i += 1
    ax1.set_xlabel(r"Secret dimension $n$")
    ax1.set_ylabel("Runtime [s]")
    ax1.legend()
    plt.grid()
    plt.savefig("algorithms", format="pdf")
    plt.show()


def cost_model_plotter():
    import numpy as np
    import matplotlib.pyplot as plt
    import matplotlib as mpl
    import sage.all
    from sage.all import RR, ZZ, log, gamma, pi

    sieving = True
    enumeration = True
    if sieving and enumeration:
        method = ""
    elif sieving:
        method = "_sieving"
    else:
        method = "_enum"
    beta = np.array([i for i in range(10, 500, 10)])
    ones = np.array([1] * len(beta))
    rop = {}

    # cost models without d
    for cost_model in BKZ_COST_MODELS:
        if sieving and enumeration:
            rop[cost_model["name"]] = np.vectorize(cost_model["cost_model"])(
                beta, ones, ones
            )
        elif sieving and cost_model["method"] == "sieving":
            rop[cost_model["name"]] = np.vectorize(cost_model["cost_model"])(
                beta, ones, ones
            )
        elif enumeration and cost_model["method"] == "enumeration":
            rop[cost_model["name"]] = np.vectorize(cost_model["cost_model"])(
                beta, ones, ones
            )

    fig1, ax1 = plt.subplots(1, 1)
    ax1.set_prop_cycle(
        color=[
            "magenta",
            "indigo",
            "navy",
            "deepskyblue",
            "cyan",
            "darkgreen",
            "lightgreen",
            "yellow",
            "orange",
            "darksalmon",
            "red",
            "brown",
            "lightgrey",
            "dimgrey",
            "black",
            "lightpink",
            "rosybrown",
        ]
    )
    for cname in rop:
        label = cname
        if "8d" in cname:
            label += ", d=1"
        ax1.plot(beta, rop[cname], label=label)
    ax1.set_xlabel(r"Block size $\beta$")
    ax1.set_ylabel("log2 of BKZ reduction cost [rop]")
    ax1.set_ylim([0, 300])
    ax1.legend()
    plt.grid()
    plt.savefig("cost_models" + method + ".pdf", format="pdf")
    plt.show()


def cost_model_d_2d_plotter():
    import numpy as np
    import matplotlib.pyplot as plt
    import matplotlib as mpl
    import sage.all
    from sage.all import RR, ZZ, log, gamma, pi

    betas = [1, 50, 100]
    d = np.array([i for i in range(10, 1000, 10)])
    ones = np.array([1] * len(d))
    rop = {}

    for b in betas:
        beta = np.array([b] * len(d))
        rop[b] = {}
        for cost_model in [
            cm
            for cm in BKZ_COST_MODELS
            if cm["name"]
            in [
                "Q‑8d‑Sieve + O(1)",
                "8d‑Enum (quadratic fit) + O(1)",
                "8d‑Sieve + O(1)",
            ]
        ]:
            rop[b][cost_model["name"]] = np.vectorize(cost_model["cost_model"])(
                beta, d, ones
            )

    fig1, ax1 = plt.subplots(1, 1)
    colors = ["r", "b", "g"]
    styles = ["-", "--", ":"]
    for i in range(len(betas)):
        b = betas[i]

        j = 0
        for cname in rop[b]:
            label = cname + r", $\beta = $" + str(b)
            ax1.plot(d, rop[b][cname], colors[j] + styles[i], label=label)
            j += 1

    ax1.set_xlabel(r"Lattice dimension $d$")
    ax1.set_ylabel("log2 of BKZ reduction cost [rop]")
    ax1.legend()
    plt.grid()
    plt.savefig("cost_models_d_2d", format="pdf")
    plt.show()


def cost_model_d_plotter():
    import numpy as np
    import matplotlib.pyplot as plt
    import matplotlib as mpl
    import sage.all
    from sage.all import RR, ZZ, log, gamma, pi
    from matplotlib import cm
    import matplotlib.ticker as mticker

    # cost models with d
    beta = np.array([i for i in range(10, 1000, 10)])
    d = np.array([i for i in range(10, 1000, 10)])
    zero = np.zeros(len(beta))
    BETA, D = np.meshgrid(beta, d)
    ZERO = np.meshgrid(zero, zero)[0]
    rop_d = {}
    for cost_model in [
        cm
        for cm in BKZ_COST_MODELS
        if cm["name"]
        in ["Q‑8d‑Sieve + O(1)", "8d‑Enum (quadratic fit) + O(1)", "8d‑Sieve + O(1)"]
    ]:
        rop = np.array(
            np.vectorize(cost_model["cost_model"])(
                np.ravel(BETA), np.ravel(D), np.ravel(ZERO)
            )
        )  # already log10 of actual cost
        rop_d[cost_model["name"]] = rop.reshape(BETA.shape)

    fig, ax = plt.subplots(subplot_kw={"projection": "3d"})
    for cname in rop_d:
        surf = ax.plot_surface(
            BETA,
            D,
            rop_d[cname],
            label=cname,
            rstride=5,
            cstride=5,
            alpha=0.9,
            linewidth=0,
            antialiased=True,
            vmin=0,
        )
        surf._facecolors2d = surf._facecolor3d
        surf._edgecolors2d = surf._edgecolor3d

    ax.set_xlabel(r"Block size $\beta$")
    ax.set_ylabel("lattice dimension d")
    ax.set_zlabel("log2 of BKZ reduction cost [rop]")
    ax.legend()
    plt.savefig("cost_models_d", format="pdf")
    plt.show()


if __name__ == "__main__":
    cost_model_plotter()
