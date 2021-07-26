# -*- coding: utf-8 -*-
"""
BKZ cost asymptotics proposed to NIST as part of the PQC process.

NOTATION:

    BKZ COST
    beta        block size
    d           lattice dimension
    B           bitsize of entries

    LWE
    n       lwe secret dimension  (d*n for module lwe)
    q       lwe modulo
    sd      lwe secret standard deviation (if normal form)
    m       number of lwe samples

AUTHOR of original file:

    Fernando Virdia - 2017, 2018
    Ben Curtis - 2018

AUTHOR of adapted file (additional information and parameters needed for lattice_parameter_estimation):

    Nicolai Krebs - 2021


ADDITIONAL INFORMATION:

.. _cost-models:

The value for key ``prio`` is derived from the folling plots of the various cost models. The scale is ordinal, not cardinal. To compare and assign suitable priority values for custom cost models the function ``cost_model_plotter()`` in ``tests_for_optimization/runtime_analysis.py`` can be used. If your own custom cost model should be evaluated first during the the cost estimation, set `prio`` to `0`.

.. figure:: ../tests_for_optimization/cost_models.png
   :width: 600
   :align: center
   :figclass: align-center

   Cost models without parameter d or d=1



.. figure:: ../tests_for_optimization/cost_models_d.png
   :width: 500
   :align: center
   :figclass: align-center

   Cost models with parameter d
"""



from sage.all import RR, ZZ, log, gamma, pi
from estimate_all_schemes.estimator import BKZ


# List of proposed cost models for BKZ
# Q-Sieving | Sieving | Q-Enum | Enum
# with Rounds = Core  | beta | 8d
BKZ_COST_ASYMPTOTICS = [
    {
        "name": "Q‑Core‑Sieve",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.265*beta),
        "success_probability": 0.99,
        "human_friendly": "2^(0.265 β)",
        "group": "Quantum sieving",
        "prio": 1,
    },
    {
        "name": "Q‑Core‑Sieve + O(1)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.265*beta + 16),
        "success_probability": 0.99,
        "human_friendly": "2^(0.265 β + O(1))",
        "group": "Quantum sieving",
        "prio": 30,
    },
    {
        "name": "Q‑Core‑Sieve (min space)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.2975*beta),
        "success_probability": 0.99,
        "human_friendly": "2^(0.298 β)",
        "group": "Quantum sieving",
        "prio": 20,
    },
    {
        "name": "Q‑β‑Sieve",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.265*beta + log(beta,2)),
        "success_probability": 0.99,
        "human_friendly": "β 2^(0.265 β)",
        "group": "Quantum sieving",
        "prio": 5,
    },
    {
        "name": "Q‑8d‑Sieve + O(1)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.265*beta + 16.4 + log(8*d,2)),
        "success_probability": 0.99,
        "human_friendly": "8d 2^(0.265 β + O(1))",
        "group": "Quantum sieving",
        "prio": 25,
    },
    {
        "name": "Core‑Sieve",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.292*beta),
        "success_probability": 0.99,
        "human_friendly": "2^(0.292 β)",
        "group": "Classical sieving",
        "prio": 10,
    },
    {
        "name": "Core‑Sieve + O(1)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.292*beta + 16),
        "success_probability": 0.99,
        "human_friendly": "2^(292 β + O(1))",
        "group": "Classical sieving",
        "prio": 50,
    },
    {
        "name": "Core‑Sieve (min space)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.368*beta),
        "success_probability": 0.99,
        "human_friendly": "2^(0.368 β)",
        "group": "Classical sieving",
        "prio": 70,
    },
    {
        "name": "β‑Sieve",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.292*beta + log(beta,2)),
        "success_probability": 0.99,
        "human_friendly": "β 2^(0.292 β)",
        "group": "Classical sieving",
        "prio": 40,
    },
    {
        "name": "8d‑Sieve + O(1)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.292*beta + 16.4 + log(8*d,2)),
        "success_probability": 0.99,
        "human_friendly": "8d 2^(0.292 β + O(1))",
        "group": "Classical sieving",
        "prio": 60,
    },
    {
        "name": "Q‑Core‑Enum + O(1)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR((0.18728*beta*log(beta, 2) - 1.0192*beta + 16.1)/2),
        "success_probability": 0.99,
        "human_friendly": "2^((0.18728 β log β - 1.0192 β + O(1))/2)",
        "group": "Quantum enumeration",
        "prio": 5,
    },
    {
        "name": "Lotus",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(-0.7550818937366788*beta + 0.12472525302110621*beta*log(beta,2) + 2.254440896969337),
        "success_probability": 0.99,
        "human_friendly": "2^(0.125 β log β -0.755 β + O(1))",
        "group": "Classical enumeration",
        "prio": 1,
    },
    {
        "name": "Core‑Enum + O(1)",
        "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.18728*beta*log(beta, 2) - 1.0192*beta + 16.1),
        "success_probability": 0.99,
        "human_friendly": "2^(0.18728 β log β - 1.0192 β + O(1))",
        "group": "Classical enumeration",
        "prio": 100,
    },
    # {
    #     "name": "8d‑Enum + O(1)",
    #     "reduction_cost_model": lambda beta, d, B: BKZ.LLL(d, B) +  BKZ.svp_repeat(beta, d) * ZZ(2)**RR(0.270188776350190*beta*log(beta) - 1.0192050451318417*beta + 16.10253135200765),
    #     "success_probability": 0.99,
    #     "human_friendly": "8d 2^(0.270 β ㏑ beta - 1.019 β + O(1))",
    #     "group": "Classical enumeration",
    # },
    {
        "name": "8d‑Enum (quadratic fit) + O(1)",
        "reduction_cost_model": lambda beta, d, B: BKZ.svp_repeat(beta, d) * ZZ(2)**RR(0.000784314*beta**2 + 0.366078*beta - 6.125 + 7),
        "success_probability": 0.99,
        "human_friendly": "8d 2^(0.000784 β² + 0.366 β + O(1))",
        "group": "Classical enumeration",
        "prio": 200,
    },
]

table = ".. list-table:: Reduction Cost Models\n\
   :header-rows: 1\n\
\n\
   * - Name\n\
     - Cost model\n\
     - P(success)\n\
     - Group\n\
     - Priority\n"

for model in BKZ_COST_ASYMPTOTICS:
    table += "   * - " + model["name"] + "\n"
    table += "     - " + model["human_friendly"] + "\n"
    table += "     - " + str(model["success_probability"]) + "\n"
    table += "     - " + model["group"] + "\n"
    table += "     - " + str(model["prio"]) + "\n"

__doc__ += f"{table}"