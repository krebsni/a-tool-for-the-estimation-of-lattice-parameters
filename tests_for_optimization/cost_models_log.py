# -*- coding: utf-8 -*-
"""
BKZ cost models that were part of round 1 submissions to NIST PQC.

This file is based on `cost_asymptotics.py <https://github.com/estimate-all-the-lwe-ntru-schemes/estimate-all-the-lwe-ntru-schemes.github.io/blob/master/cost_asymptotics.py>` authored by Fernando Virdia (2017, 2018) and Ben Curtis (2018).

NOTATION:

    BKZ COST
    beta        block size
    d           lattice dimension
    B           bitsize of entries


"""

from math import log

BKZ_COST_MODELS = [
    # TODO: add worst lower bounds for sieving algorithms (0.2075*beta), :cite:`ADPS16`, Frodo?
    {
        "name": "Q‑Sieve (paranoid lower bound)",
        "reference": ":cite:`ADPS16`",
        "cost_model": lambda beta, d, B: 0.2075 * beta,
        "success_probability": 0.99,
        "human_friendly": "2^(0.2075 β)",
        "latex": r"2^{0.2075 \beta}",
        "quantum": True,
        "method": "sieving",
        "prio": 150,
    },
    {
        "name": "Q‑Sieve",
        "reference": ":cite:`Laa15`, :cite:`ADPS16`, :cite:`AGPS20`",
        "cost_model": lambda beta, d, B: 0.265 * beta,
        "success_probability": 0.99,
        "human_friendly": "2^(0.265 β)",
        "latex": r"2^{0.265 \beta}",
        "quantum": True,
        "method": "sieving",
        "prio": 1,
    },
    {
        "name": "Q‑Sieve + O(1)",
        "reference": ":cite:`SAL+17`",
        "cost_model": lambda beta, d, B: 0.265 * beta + 16,
        "success_probability": 0.99,
        "human_friendly": "2^(0.265 β + 16)",
        "latex": r"2^{0.265 \beta + 16}",
        "quantum": True,
        "method": "sieving",
        "prio": 30,
    },
    {
        "name": "Q‑Sieve (min space)",
        "reference": ":cite:`SHRS17`",
        "cost_model": lambda beta, d, B: 0.2975 * beta,
        "success_probability": 0.99,
        "human_friendly": "2^(0.2975 β)",
        "latex": r"2^{0.2975 \beta}",
        "quantum": True,
        "method": "sieving",
        "prio": 20,
    },
    {
        "name": "Sieve",
        "reference": ":cite:`BDGL16`, :cite:`ADPS16`, :cite:`AGPS20`",
        "cost_model": lambda beta, d, B: 0.292 * beta,
        "success_probability": 0.99,
        "human_friendly": "2^(0.292 β)",
        "latex": r"2^{0.292 \beta}",
        "quantum": False,
        "method": "sieving",
        "prio": 10,
    },
    {
        "name": "Sieve + O(1)",
        "reference": ":cite:`SAL+17`",
        "cost_model": lambda beta, d, B: 0.292 * beta + 16,
        "success_probability": 0.99,
        "human_friendly": "2^(0.292 β + O(1))",
        "latex": r"2^{0.292 \beta + 16}",
        "quantum": False,
        "method": "sieving",
        "prio": 50,
    },
    {
        "name": "Sieve (min space)",
        "reference": ":cite:`SHRS17`",
        "cost_model": lambda beta, d, B: 0.368 * beta,
        "success_probability": 0.99,
        "human_friendly": "2^(0.368 β)",
        "latex": r"2^{0.368 \beta}",
        "quantum": False,
        "method": "sieving",
        "prio": 70,
    },
    {
        "name": "Lotus",
        "reference": ":cite:`PHAM17`, :cite:`ACDDPPVW18`",
        "cost_model": lambda beta, d, B: -0.7550818937366788 * beta
        + 0.12472525302110621 * beta * log(beta, 2)
        + 2.254440896969337,
        "success_probability": 0.99,
        "human_friendly": "2^(0.125 β log β -0.755 β + 2.254)",
        "latex": r"2^{0.125 \beta \log \beta -0.755 \beta + 2.254}",
        "quantum": False,
        "method": "enumeration",
        "prio": 2,
    },
    {
        "name": "Enum + O(1)",
        "reference": ":cite:`SHRS17`, :cite:`Chen13`, :cite:`ACDDPPVW18`",
        "cost_model": lambda beta, d, B: 0.18728 * beta * log(beta, 2)
        - 1.0192 * beta
        + 16.1,
        "success_probability": 0.99,
        "human_friendly": "2^(0.18728 β log β - 1.0192 β + 16.1)",
        "latex": r"2^{0.18728 \beta \log \beta -1.0192 \beta + 16.1}",
        "quantum": False,
        "method": "enumeration",
        "prio": 100,
    },
    {
        "name": "Q‑Enum + O(1)",
        "reference": ":cite:`SHRS17`, :cite:`Chen13`, :cite:`ACDDPPVW18`",
        "cost_model": lambda beta, d, B: (
            0.18728 * beta * log(beta, 2) - 1.0192 * beta + 16.1
        )
        / 2,
        "success_probability": 0.99,
        "human_friendly": "2^((0.18728 β log β - 1.0192 β + 16.1)/2)",
        "latex": r"2^{(0.18728 \beta \log \beta - 1.0192 \beta + 16.1) / 2}",
        "quantum": True,
        "method": "enumeration",
        "prio": 6,
    },
    {
        "name": "BCLV-Enum (quadratic fit) + O(1)",
        "reference": ":cite:`BCLV17`",
        "cost_model": lambda beta, d, B: 0.000784314 * beta ** 2
        + 0.366078 * beta
        - 6.125
        + 7,
        "success_probability": 0.99,
        "human_friendly": "2^(0.000784 β² + 0.366 β + 0.875)",
        "latex": r"2^{0.000784 \beta^2 + 0.366 \beta + 0.875}",
        "quantum": False,
        "method": "enumeration",
        "prio": 200,
    },
    {
        "name": "BKZ2.0-Enum",
        "reference": ":cite:`CN11`, :cite:`Chen13`, :cite:`ABFKSW20`",
        "cost_model": lambda beta, d, B: 0.184 * beta * log(beta, 2)
        - 0.995 * beta
        + 16.25,
        "success_probability": 0.99,
        "human_friendly": "2^(0.184 β log β - 0.995 β + 16.25)",
        "latex": r"2^{0.184 \beta \log \beta - 0.995 \beta + 16.25}",
        "quantum": False,
        "method": "enumeration",
        "prio": 200,
    },
    {
        "name": "ABF-Enum",
        "reference": ":cite:`ABFKSW20`",
        "cost_model": lambda beta, d, B: 0.125 * beta * log(beta, 2),
        "success_probability": 0.99,
        "human_friendly": "2^(0.125 β log β)",
        "latex": r"2^{0.125 \beta \log \beta}",
        "quantum": False,
        "method": "enumeration",
        "prio": 200,
    },
    {
        "name": "ABF-Enum + O(1)",
        "reference": ":cite:`ABFKSW20`",
        "cost_model": lambda beta, d, B: 0.125 * beta * log(beta, 2)
        - 0.547 * beta
        + 10.4,
        "success_probability": 0.99,
        "human_friendly": "2^(0.125 β log β - 0.547β + 10.4)",
        "latex": r"2^{0.125 \beta \log \beta - 0.547 \beta + 10.4}",
        "quantum": False,
        "method": "enumeration",
        "prio": 200,
    },
    {
        "name": "Q-ABF-Enum",
        "reference": ":cite:`ABFKSW20`",
        "cost_model": lambda beta, d, B: 0.0625 * beta * log(beta, 2),
        "success_probability": 0.99,
        "human_friendly": "2^(0.0625 β log β)",
        "latex": r"2^{0.0625 \beta \log \beta}",
        "quantum": True,
        "method": "enumeration",
        "prio": 200,
    },
    {
        "name": "ABLR-Enum + O(1)",
        "reference": ":cite:`ABFKSW20`",
        "cost_model": lambda beta, d, B: 0.125 * beta * log(beta, 2)
        - 0.654 * beta
        + 25.84,
        "success_probability": 0.99,
        "human_friendly": "2^(0.125 β log β - 0.654 β + 25.84)",
        "latex": r"2^{0.125 \beta \log \beta - 0.654 \beta + 25.84}",
        "quantum": False,
        "method": "enumeration",
        "prio": 200,
    },
]
