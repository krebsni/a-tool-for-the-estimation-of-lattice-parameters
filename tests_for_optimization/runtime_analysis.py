from mpl_toolkits.mplot3d import Axes3D
from cost_asymptotics_new import BKZ_COST_ASYMPTOTICS


def runtime_results():
    import json
    import statistics  
    with open('runtime_CRYSTALS.json') as json_file:
        data = json.load(json_file)

    data = [x for x in data if x["successful"] == True]
    algs = {algn for algn in (x["algname"] for x in data)}
    print(algs)
    avg_list = [(algn, statistics.mean([x["log_rop"] for x in data if x["algname"] == algn])) for algn in algs]
    # for algn in algs:
    #     avg_list.append((algn, [x["runtime"] for x in data if x["algname"] == algn]))
    print(avg_list)

def cost_model_plotter():
    import numpy as np
    import matplotlib.pyplot as plt
    import matplotlib as mpl
    import sage.all 
    from sage.all import RR, ZZ, log, gamma, pi

    beta = np.array([i for i in range(10, 800, 10)])
    zero = np.array([1]*len(beta))
    rop = {}

    # cost models without d
    for cost_model in [cm for cm in BKZ_COST_ASYMPTOTICS if cm["name"] not in ["8d‑Enum (quadratic fit) + O(1)"]]:
        rop[cost_model["name"]] = np.vectorize(cost_model["reduction_cost_model"])(beta, zero, zero)

    fig1, ax1 = plt.subplots(1,1)
    ax1.set_prop_cycle(color=['magenta', 'indigo', 'navy', 'deepskyblue', 'cyan',  'darkgreen',  'lightgreen', 'yellow', 'orange', 'darksalmon','red', 'brown', 'lightgrey', 'dimgrey', 'black'])
    for cname in rop:
        ax1.plot(beta, rop[cname], label=cname)
    ax1.set_xlabel(r'Block size $\beta$')
    ax1.set_ylabel('log10 of BKZ reduction cost [rop]')
    ax1.legend()
    plt.grid()
    plt.savefig('cost_models.png')
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
    beta = np.array([i for i in range(10, 5000, 10)])
    d = np.array([i for i in range(10, 5000, 10)])
    zero = np.zeros(len(beta))
    BETA, D = np.meshgrid(beta, d)
    ZERO = np.meshgrid(zero,zero)[0]
    rop_d = {}
    for cost_model in [cm for cm in BKZ_COST_ASYMPTOTICS  if cm["name"] in ["Q‑8d‑Sieve + O(1)", "8d‑Enum (quadratic fit) + O(1)", "8d‑Sieve + O(1)"]]:
        rop = np.array(np.vectorize(cost_model["reduction_cost_model"])(np.ravel(BETA), np.ravel(D), np.ravel(ZERO))) # already log10 of actual cost
        rop_d[cost_model["name"]] = rop.reshape(BETA.shape)
    
    fig, ax = plt.subplots(subplot_kw={"projection": "3d"})
    for cname in rop_d:
        surf = ax.plot_surface(BETA, D,  rop_d[cname], label=cname,
                        rstride=5, cstride=5,
                        alpha=0.9,
                        linewidth=0,
                        antialiased=True,
                        vmin=0)
        surf._facecolors2d = surf._facecolor3d
        surf._edgecolors2d = surf._edgecolor3d

    def log_tick_formatter(val, pos=None):
        return "{:.0e}".format(10**val)

    ax.zaxis.set_major_formatter(mticker.FuncFormatter(log_tick_formatter))
    ax.set_xlabel(r'Block size $\beta$')
    ax.set_ylabel("lattice dimension d")
    ax.set_zlabel('BKZ reduction cost [rop]')
    ax.legend()
    plt.savefig('cost_models_d.png')
    plt.show()

if __name__ == "__main__":
    runtime_results()