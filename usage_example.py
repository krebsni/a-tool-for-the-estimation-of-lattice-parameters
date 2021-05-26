from . import lib

sec = lib.Sec(...)

def estimation_example():
    lwe = lib.LWE(...)

    if lib.is_secure(lwe, sec):
        pass # do things
    
    # or maybe
    if lib.estimate(lwe) < sec:
        pass # not secure
    else:
        pass # secure
    
    # same for sis, ring-lwe, ring-sis, module-lwe, module-sis

def BGV_example():
    def next_parameters(N, p, q):
        N = 2 * N
        p = ... # find p depending on new N
        q = ... # find q depending on new N and p
        yield N, p, q

    def parameter_problem(N, p, q):
        yield lib.RLWE(N, q, ...) # keys are secure
        yield lib.RLWE(N, q, ...) # encryption is secure

    N, p, q, security, ... = lib.generic_search(sec, (2**10, None, None), next_parameters, lib.unit_cost, parameter_problem)
    ...

def two_problem_search_example():
    N = 2**15
    p = lib.make_prime(2**32)
    q = p
    n, m, l = 1, 1, 1
    initial_parameters = N, p, q, n, m, l

    def next_parameters(N, p, q, n, m, l):
        if m == 1:
            yield N, p, q * 2, n, m, l
        yield N, p, q, n, m + 1, l

    def parameter_cost(N, p, q, n, m, l):
        message = lib.number_of_bits(p) * N * l
        rndness = lib.number_of_bits(q) * N * (n + m + l)
        cmmtmnt = lib.number_of_bits(q) * N * n + message
        cost = cmmtmnt + rndness
        return cost

    def parameter_problem(N, p, q, n, m, l):
        lwe = lib.statistical_MLWE(sec, N, q, n + l, n + m + l, ...)
        sigma = lwe.sigma
        min_sigma, max_sigma = ... # compute sigmas for application
        
        if min_sigma <= sigma <= max_sigma:
            yield lib.MSIS(N, q, n, n + m + l, sigma, ...)
            yield lib.MSIS(N, q, n, n + m + l, max_sigma, ...)

    N, p, q, n, m, l = lib.generic_search(sec, initial_parameters, next_parameters, parameter_cost, parameter_problem)
        