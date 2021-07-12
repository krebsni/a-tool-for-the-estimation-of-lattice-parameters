#!/usr/bin/env sage

import sys
import os
from attacks import Attack_Configuration
import param_search, distributions, norm, problem
sys.path.append(os.path.dirname(__file__) + "/estimate_all")
from estimator import estimator as est
import sage.all 
from sage.rings.all import QQ

sec = param_search.SECURITY # can be any value, also used in Gaussian to bound trafo and statistically secure variants
DEBUG = True

def estimation_example():
    problem.statistical_sec = sec
    n = 128
    q = param_search.make_prime(n=2^64, lbound=2^63)
    m = 256
    alpha = est.alphaf(2.0*q, q, sigma_is_stddev=True) # TODO
    sec_dis = distributions.Gaussian_alpha(alpha=alpha, q=q, sec=sec)
    err_dis = sec_dis
    config = Attack_Configuration()
    lwe = problem.LWE(n=n, q=q, m=m, secret_distribution=sec_dis, error_distribution=err_dis)

    if param_search.is_secure(parameter_problem=[lwe], sec=sec, attack_configuration=config, debug=DEBUG):
        pass # do things
    
    # or maybe
    if param_search.estimate(lwe) < sec:
        pass # not secure
    else:
        pass # secure
    
    # same for sis, ring-lwe, ring-sis, module-lwe, module-sis

def BGV_example():
    attack_configuration = Attack_Configuration()
    def next_parameters(N, p, q):
        N = 2 * N
        p = 1 # find p depending on new N
        q = 1 # find q depending on new N and p
        yield N, p, q

    def parameter_problem(N, p, q):
        yield problem.RLWE(N, q) # keys are secure
        yield problem.RLWE(N, q) # encryption is secure

    N, p, q, security = param_search.generic_search(sec, (2**10, None, None), next_parameters, param_search.unit_cost, parameter_problem, attack_configuration)

def two_problem_search_example():
    # k: width (over R_q) of commitment matrices
    # n: height (over R_q) of commitment matrices
    # l: dimension (over R_q) of message space
    # beta: norm bound for honest prover's randomness in Loo-norm
    # kappa: maximum L1-norm of any element in challenge space
    # sigma: stddev used in zero-knowledge proof => sigma = 11*kappa*beta*sqrt(k*N)
    # m: width of commitment matrix A_2' => m = k - n - l
    N = 2**15
    p = param_search.make_prime(2**32)
    q = p
    n, m, l = 1, 1, 1
    initial_parameters = N, p, q, n, m, l
    attack_configuration = Attack_Configuration()

    def next_parameters(N, p, q, n, m, l):
        if m == 1:
            yield N, p, q * 2, n, m, l
        yield N, p, q, n, m + 1, l

    def parameter_cost(N, p, q, n, m, l):
        message = param_search.number_of_bits(p) * N * l
        rndness = param_search.number_of_bits(q) * N * (n + m + l)
        cmmtmnt = param_search.number_of_bits(q) * N * n + message
        cost = cmmtmnt + rndness
        return cost

    def parameter_problem(N, p, q, n, m, l):
        lwe : problem.Statistical_Uniform_MLWE = problem.Statistical_Uniform_MLWE(sec=sec, n=N, q=q, d=n + l, m=n + m + l)

        # TODO: Question: what was the though with the sigmas here?
        # sigma = lwe.sigma
        # min_sigma, max_sigma = lwe.get_sigma_bounds()
        
        # if min_sigma <= sigma <= max_sigma:
        #     yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, sigma=sigma)
        #     yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, sigma=max_sigma)
            # TODO: is the above correct (i.e. value for d)? Why sigma? SIS requires beta (norm bound of solution)
            # TODO: how to transform norm bound in BDLOP16 into stddev?

        min_beta, max_beta = lwe.get_beta_bounds()
        yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, bound=min_beta)
        yield problem.MSIS(N=N, q=q, d=n, m=n + m + l, bound=max_beta)
        

    n, p, q, n, m, l = param_search.generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem, attack_configuration)

if __name__ == "__main__":
    estimation_example()