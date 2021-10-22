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
import multiprocessing as mp
from lattice_parameter_estimation.estimate_all_schemes.schemes import LWE_SCHEMES

logging.basicConfig(level=logging.DEBUG)  # set to INFO to hide exceptions
logger = logging.getLogger(__name__)

lattice_parameter_estimation.Logging.set_level(logging.DEBUG)
SEPARATOR = algorithms.SEPARATOR


def simple_estimation_example():
    """So simple estimation example for LWE and SIS"""

    # Configuration
    config = algorithms.Configuration(
        # Cost models
        conservative=True,
        paranoid=False,
        classical=True,
        quantum=True,
        sieving=True,
        enumeration=True,
        bkz_svp_rounds=algorithms.BKZ_SVP_repeat_core,
        custom_cost_models=[],
        # Algorithms and security criteria of result
        algorithms=algorithms.ALL,
        security_strategy=algorithms.SOME_SECURE,
        # Others
        parallel=True,
        num_cpus=mp.cpu_count(),  # this is the default
        timeout=1000,
    )

    n = 2 ** 9
    sec = 250

    ## LWE Example
    print(SEPARATOR)
    print("LWE Estimates")
    print(SEPARATOR)
    # use [Reg05] to get an LWE problem instance
    n, alpha, q = Param.Regev(n)
    err_dis = distributions.GaussianAlpha(alpha=alpha, q=q, sec=sec)
    sec_dis = err_dis  # "normal"
    lwe = problem.LWE(
        n=n, q=q, m=est.oo, secret_distribution=sec_dis, error_distribution=err_dis
    )
    result = problem.estimate(parameter_problems=[lwe], config=config)
    print(SEPARATOR)
    print("Result: " + str(result))
    result.save_as_JSON(("LWE_Regev_example"))

    # SIS Example
    print(SEPARATOR)
    print("SIS Estimates")
    print(SEPARATOR)
    # use [MP12] to get an SIS problem instance
    q = param_search.make_prime(2 * n ** 2, lbound=n ** 2)
    m = 2 * n * log(q, 2)
    s = 2 * sqrt(n * log(q, 2))
    beta = distributions.GaussianS(s, q, 128, n)  # internally converted to bound
    sis = problem.SIS(n=n, q=q, m=m, bound=beta, label="SIS")
    print(SEPARATOR)
    result = problem.estimate(parameter_problems=[sis], config=config)
    print(SEPARATOR)
    print("Result: " + str(result))
    result.save_as_JSON(("SIS_MP12_example"))


def simple_LWE_parameter_search_example():
    print(SEPARATOR)
    print("LWE Parameter Search (Regev)")
    print(SEPARATOR)
    config = algorithms.Configuration(algorithms=[algorithms.DUAL])
    sec = 128

    def next_parameters(n, q=None, m=None, alpha=None):
        n, alpha, q, m = Param.Regev(n * 2, m=n ** 2)
        yield n, q, m, alpha

    def parameter_problem(n, q, m, alpha):
        distribution = distributions.GaussianAlpha(alpha=alpha, q=q)
        yield problem.LWE(
            n=n,
            q=q,
            m=m,
            secret_distribution=distribution,
            error_distribution=distribution,
        )

    res = param_search.generic_search(
        sec,
        next(next_parameters(2 ** 5)),
        next_parameters,
        param_search.unit_cost,
        parameter_problem,
        config,
    )

    print(SEPARATOR)
    print("Search successful")
    print(f"Parameters: {res['parameters']}")
    print(f"Estimate results: {str(res['result'])}")


def simple_SIS_parameter_search_example():
    print(SEPARATOR)
    print("SIS Parameter Search")
    print(SEPARATOR)
    config = algorithms.Configuration()
    sec = 128

    def next_parameters(n):
        # Parameters as in MP12
        n *= 2
        q = param_search.make_prime(2 * n ** 2, lbound=n ** 2)
        m = 2 * n * log(q, 2)
        s = 2 * sqrt(n * log(q, 2))
        beta = distributions.GaussianS(s, q, 128, n)  # internally converted to bound
        yield n, q, m, beta

    def parameter_problem(n, q, m, beta):
        yield problem.SIS(n=n, q=q, m=m, bound=beta, label="SIS")

    res = param_search.generic_search(
        sec,
        next(next_parameters(2 ** 5)),
        next_parameters,
        param_search.unit_cost,
        parameter_problem,
        config,
    )

    print(SEPARATOR)
    print("Search successful")
    print(f"Parameters: {res['parameters']}")
    print(f"Estimate results: {str(res['result'])}")


def rejection_sample(staticstical_sec, dimension, bound, out_dimension, rho=100 / 99):
    assert dimension >= staticstical_sec
    sigma = 12 / log(rho) * bound.to_L2().value
    gausssian = distributions.GaussianSigma(
        sigma, sec=staticstical_sec, dimension=out_dimension
    )
    return gausssian


def amortized_rejection_sample(
    staticstical_sec, dimension, bound, out_norm, out_dimension, rho=100 / 99
):
    V = 2 * staticstical_sec - 1
    response = rejection_sample(
        staticstical_sec, V * dimension, staticstical_sec * bound, out_dimension, rho
    )
    assert staticstical_sec % 2 == 0
    amortization_slack = 2 ** (staticstical_sec // 2)
    if out_norm == 2:
        return 2 * amortization_slack * response.to_L2()
    elif out_norm == norm.oo:
        return 2 * amortization_slack * response.to_Loo()


def BGV_example():
    """Advanced example of a BGV with accountability based on [BGV11, DPSZ12]"""
    print(SEPARATOR)
    print("BGV Parameter Search")
    print(SEPARATOR)

    staticstical_sec = 80
    secret_distribution = distributions.GaussianS(3)
    error_distribution = distributions.GaussianS(3)
    encryption_error_distribution = distributions.GaussianS(3)

    class BgvLheCipher:
        def __init__(self, x, v, e1, e2):
            assert x.dimension == v.dimension
            assert v.dimension == e1.dimension
            assert e1.dimension == e2.dimension

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
                sampledBoundP = amortized_rejection_sample(
                    staticstical_sec, N, boundP, 2, N
                )
            else:
                sampledBoundP = norm.L1(N, 0)

            return BgvLheCipher(
                sampledBoundP,
                amortized_rejection_sample(
                    staticstical_sec,
                    N,
                    gaussianV.to_L2(sec=staticstical_sec, dimension=N),
                    2,
                    N,
                ).to_Coo(),
                amortized_rejection_sample(
                    staticstical_sec,
                    N,
                    gaussianE1.to_L2(sec=staticstical_sec, dimension=N),
                    2,
                    N,
                ).to_Coo(),
                amortized_rejection_sample(
                    staticstical_sec,
                    N,
                    gaussianE2.to_L2(sec=staticstical_sec, dimension=N),
                    2,
                    N,
                ).to_Coo(),
            )

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
                    self.e2 * other.e2,
                )
            else:
                return BgvLheCipher(
                    other * self.x, other * self.v, other * self.e1, other * self.e2
                )

        def __rmul__(self, other):
            return self * other

        def __add__(self, other):
            if isinstance(other, BgvLheCipher):
                return BgvLheCipher(
                    self.x + other.x,
                    self.v + other.v,
                    self.e1 + other.e1,
                    self.e2 + other.e2,
                )

            if isinstance(other, norm.BaseNorm):
                return BgvLheCipher(self.x + other, self.v, self.e1, self.e2)

            return NotImplemented

        def __radd__(self, other):
            return self + other

        def __sub__(self, other):
            return self + other

        def __rsub__(self, other):
            return self + other

        def __str__(self):
            return f"LHE-BGV cipher (in dimension {self.dimension})"

    class BgvSheCipher:
        def __init__(self, x, ba, bap, baps, bbaa, p, ps, pp, pps, ppss):
            self.dimension = x.dimension
            assert all(
                y.dimension == self.dimension
                for y in [ba, bap, baps, bbaa, p, ps, pp, pps, ppss]
            )

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

            bound = (
                self.partX
                + ba * self.partBA
                + bap * self.partBAP
                - baps * self.partBAPS
                + bbaa * self.partBBAA
                + p * self.partP
                - ps * self.partPS
                + pp * self.partPP
                - pps * self.partPPS
                + ppss * self.partPPSS
            )
            return bound.to_Coo()

        def __mul__(self, other):
            if isinstance(other, (BgvLheCipher, BgvSheCipher)):
                raise TypeError(
                    "Cannot multiply BGV ciphertexts if was already multiplied"
                )

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
                other * self.partPPSS,
            )

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
                    self.partPPSS,
                )

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
                    self.partPPSS + other.partPPSS,
                )

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
                    self.partPPSS,
                )

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
    p = 2 ** 64
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
            return (
                n
                * amortized_rejection_sample(
                    staticstical_sec,
                    N,
                    (2 ** staticstical_sec + 1)
                    * cipher.decryption_bound(p, s, ss, e, ee),
                    2,
                    N,
                ).to_Coo()
            )

        a = n * zkp
        b = n * zkp
        c = a * b

        r = n * zkp

        bound = decrypt(c + r)
        q = 2 * ceil(bound.value)
        yield N, q

    def parameter_problem(N, q):
        if q is not None:
            yield problem.RLWE(
                N, q, norm.oo, secret_distribution, error_distribution
            )  # keys are secure
            yield problem.RLWE(
                N, q, 1, secret_distribution, encryption_error_distribution
            )  # encryption is secure

    res = param_search.generic_search(
        computational_sec,
        (2 ** 10, None),
        next_parameters,
        param_search.unit_cost,
        parameter_problem,
        config,
    )
    res_params = res["parameters"]
    res_alg_results: problem.AggregateEstimationResult = res["result"]

    res_params = res["parameters"]
    res_alg_results: problem.AggregateEstimationResult = res["result"]
    print(res_params)
    for k, v in res_alg_results.get_algorithm_result_dict(sort_by_rop=True).items():
        print(f"{k}:")
        for x in v:
            print(f" - {x}")

    print(algorithms.SEPARATOR)
    print("Search successful")


def two_problem_search_example():
    """Advanced example of a commitment scheme based on [BDLOP18]"""
    print(SEPARATOR)
    print("Two Problem Parameter Search")
    print(SEPARATOR)
    staticstical_sec = 128
    computational_sec = 80
    sigma = 1
    N = 2 ** 15
    p = 2 ** 64
    q = p
    l = 1
    d1 = 1
    d2 = 1
    h = 2 ** 92
    kappa = 6

    lattice_parameter_estimation.Logging.set_estimation_debug_logging_level(
        logging.INFO
    )
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
        amortized_zk_response_2 = amortized_rejection_sample(
            staticstical_sec, k * N, normal_sample, 2, N
        )
        amortized_zk_response_oo = amortized_rejection_sample(
            staticstical_sec, k * N, normal_sample, norm.oo, N
        )

        differenceHom = h * amortized_zk_response_oo - h * normal_sample
        ## should not break binding between a normally obtained commitment and one that we can extract for the adversary
        differenceZKP = (
            h * approximation_bound.to_L2() * amortized_zk_response_2
            - 2
            * rejection_sample(
                staticstical_sec, N, challenge_bound * h * normal_sample, N
            ).to_Loo()
        )
        ## should not break binding between what we prove in the final ZKP and a commitment that we can extract for the adversary
        differenceOut = (
            approximation_bound * normal_sample
            - 2
            * rejection_sample(
                staticstical_sec, N, challenge_bound * normal_sample, N
            ).to_Loo()
        )
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

    res = param_search.generic_search(
        computational_sec,
        (q, d1, d2),
        next_parameters,
        parameter_cost,
        parameter_problem,
        config,
    )

    res_params = res["parameters"]
    res_alg_results: problem.AggregateEstimationResult = res["result"]
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
    fire.Fire()
