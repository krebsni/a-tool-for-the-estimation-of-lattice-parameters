r""" 
TODO: documentation
"""

try:
    import sys
    import os
    import logging 
    import sage.all
    from sage.functions.log import log
    from sage.functions.other import ceil, sqrt
    from sage.rings.all import QQ, RR
    from sage.symbolic.all import pi
    from estimator import estimator as est
    sys.path.append(os.path.dirname(__file__) + "/estimate_all")
    from cost_asymptotics import BKZ_COST_ASYMPTOTICS
    oo = est.PlusInfinity()
except:
    pass

## Logging ##
logger = logging.getLogger(__name__)


class Attack_Configuration():
    """
    Configuration of the attack vector (including cost models and algorithms used).
    """

    def __init__(self, classical=True, quantum=True, sieving=True, enumeration=True, skip=["mitm", "arora-gb", "coded-bkw"], dual_use_lll=True, multiprocessing=False):
        """ 
        :param classical: use classical cost_models, `True` by default (at least one of classical/quantum must be `True`)
        :param quantum: use quantum quantum, `True` by default 
        :param sieving: use sieving cost_models, `True` by default (at least one of sieving/enumeration must be `True`)
        :param enumeration: use enumeration cost_models, `True` by default
        :param skip: list containing algorithms to be skipped during cost estimate. For LWE and its variants, the list can contain "mitm", "usvp", "decode", "dual", "coded-bkw", "arora-gb". For SIS and its variants, the list can contain "combinatorial", "lattice-reduction". Note that if all algorithms are in list, no estimate is computed and the return cost will be :math:`\infty`. 
        :param dual_use_lll: optional, if True LLL is used for the dual attack. 
        """
        if not classical and not quantum:
            raise ValueError("At least one of classical or quantum must be True")
        if not sieving and not enumeration:
            raise ValueError("At least one of sieving or enumeration must be True")

        self.classical = classical
        self.quantum = quantum
        self.sieving = sieving
        self.enumeration = enumeration
        self.skip = skip # TODO: check docstring once all attacks have been implemented
        self.dual_use_lll = dual_use_lll
        self.multiprocessing = multiprocessing
        logger.info("Attack configuration:" + str(self))


    def reduction_cost_models(self):
        """
        Returns filtered list of reduction cost models from `cost_asymptotics.py <https://github.com/estimate-all-the-lwe-ntru-schemes/estimate-all-the-lwe-ntru-schemes.github.io/blob/master/cost_asymptotics.py>`__ 

        :param attack_configuration: instance of :class:`Attacks.Attack_Configuration`
        """

        
        bkz_cost_models = BKZ_COST_ASYMPTOTICS
        return [c for c in bkz_cost_models if c["name"] == "Core‑Sieve"] # TODO: remove, just for test purposes
        if self.quantum and not self.classical:
            bkz_cost_models = [c for c in bkz_cost_models if "Quantum" in c["group"]]
        elif self.classical and not self.quantum:
            bkz_cost_models = [c for c in bkz_cost_models if "Classical" in c["group"]]
        if self.sieving and not self.enumeration:
            bkz_cost_models = [c for c in bkz_cost_models if "sieving" in c["group"]]
        elif self.enumeration and not self.sieving:
            bkz_cost_models = [c for c in bkz_cost_models if "enumeration" in c["group"]]
        return bkz_cost_models
        # TODO: other cost models?

    def __str__(self) -> str:
        return "Cost schemes: [" + ["", "classical "][self.classical] + ["", "quantum "][self.quantum] + ["", " sieving"][self.sieving] + ["", "enumeration"][self.enumeration] + "]" + " Skip list: " + str(self.skip)


class SIS:
    """
    Namespace for SIS attacks
    """

    def lattice_reduction(n, q, m, bound, reduction_cost_model):
        r""" 
        Estimate cost of solving SIS by means of lattice reduction according to :cite:p:`RS10`.

        Find optimal lattice subdimension :math:`d` and root-Hermite factor :math:`\delta_0` for lattice reduction.
        To calculate :math:`d`, we use :cite:p:`RS10` Proposition 1 (Normalization of q-ary Lattices):

        Let :math:`n \geq 128, q \geq n^2,` and :math:`\beta < q`. Let :math:`S` be a :math:`\delta`-HSVP solver for variable :math:`\delta`. The optimal dimension for solving SIS(:math:`n, m, q, \beta`) with :math:`S` is :math:`d = \min(x : q^{2n/x} \leq \beta)`.

        .. math::

            q^{2n / d} &\leq \beta \\
            \frac{2n}{d \log(q)} &\leq \beta \\
            d &\geq \frac{2n \log(q)}{\log(\beta)}

        To calculate :math:`\delta_0` we use :cite:p:`RS10` Conjecture 2:

        For every :math:`n \geq 128,` constant :math:`c \geq 2, q \geq n^c, m = \Omega(n \log_2(q)` and :math:`\beta < q`, the best known approach to solve SIS with parameters (:math:`n, m, q, \beta`) involves solving :math:`\delta`-HSVP in dimension :math:`d = \min(x : q^{2n/x} \leq \beta)` with :math:`\delta = \sqrt[d]{\beta / q^{n/d}}`.

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param bound: bound of solution, must be instance of :class:`Norm.Base_norm` 
        """
        beta = bound.to_L2(n).value # we need L2 norm TODO: check
        logger.debug("b: " + str(beta) + ", q: " + str(q))
        if 1 < beta < q: # Condition is not a requirement for [RS10] but we would divide by log(beta) which is <= 0
            # TODO: RS10 assumes delta-SVP solver => ensure that solver used here is indeed delta-HSVP

            # Requirements
            if n < 128 or q < n*n: 
                raise ValueError("Violation of requirements of [RS10, Proposition 1] during SIS lattice reduction.")
            # Calculate optimal dimension for delta-HSVP solver
            d = ceil(2 * n * log(q, 2) / log(beta, 2)) 
            if d > m:
                d = m
            
            ## [RS10, Conjecture 2]
            # Requirements
            if q < n**2 or m <= n * log(log(q, 2), 2): # second condition to ensure that m = Omega(n log q)
                raise ValueError("Violation of requirements of [RS10, Conjecture 2] during SIS lattice reduction.")
            # Calculate approximation factor for delta-HSVP solver
            delta_0 = RR((beta / (q ** (n / d))) ** (1 / d))
            log_delta_0 = log(delta_0, 2)

            if delta_0 < 1: # intractable
                return {"rop": oo, "error": "delta_0 < 1"} # TODO: what to return?

            else: # standard case
                k = est.betaf(2**log_delta_0) # block size k [APS15, lattice rule of thumb and Lemma 5]
                B = log(q, 2)

                # TODO: is that all we need?
                cost = reduction_cost_model(k, d, B) 
                return {"rop": cost, "dim": d, "beta": k} # dim is lattice dimension, beta is block size

        else: # not a hard problem, trivial solution exists
            return {"rop": 1,"error": "trivial"} # TODO
            

    def combinatorial(q, n, m, bound, reduction_cost_model=None):
        r""" 
        Estimate cost of solving SIS by means of the combinatorial method as described in :cite:`MR09`.

        Search for optimal k such that combinatorial method can divide columns of :math:`A` into :math:`2^k` groups as described in :cite:`MR09`, p. 7. :math:`k` is chosen such that :math:`n \approx (k + 1) \log_q (L)`, where :math:`L = (2\beta + 1)^{m/2^k}` describes the number of vectors per list. Equivalently, we have 

        .. math::
            \frac{2^k}{k+1} &\approx \frac{m \log(2\beta + 1)}{n \log(q)}\\
            \text{diff} &= \text{abs}\left(\frac{2^k}{k+1} - \frac{m \log(2\beta + 1)}{n \log(q)}\right)

        To find an optimal :math:`k`, we iterate over :math:`k` starting from :math:`k=1` and calculate the difference :math:`\text{diff}`. When :math:`\text{diff}` does not decrease for 10 iteration steps, we stop and take the current :math:`k`.

        We make a conservative estimate of the cost by estimating the number of operations needed to create the initial lists. Each of the :math:`2^k` lists contains :math:`L` vectors. The cost for any operation on a list element is at least :math:`\log_2(q) * n`. Hence, the total cost is :math:`2^k * L * \log_2(q) * n`.

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param bound: bound of solution, must be instance of :class:`Norm.Base_norm`
        """
        beta = bound.to_Loo(n).value # we need Loo norm
        if beta < q:
            # find optimal k
            k = 1
            difference = oo
            failed, max_failures = 0, 10
            while failed < max_failures:
                left = 2**k / (k + 1)
                right = m / n * log(2 * beta + 1, q)
                new_difference = abs(left - right)
                if new_difference < difference:
                    difference = new_difference
                    closest_k = k
                    failed = 0
                else:
                    failed += 1
                k += 1
            k = closest_k

            # cost of creating initial lists
            L = RR((2 * beta + 1)**(m / 2**k))
            list_element_cost = log(q, 2) * n
            lists = (2 ** k) * L
            cost = lists * list_element_cost

            return {"rop": cost.n(), "k": k} # TODO other information?

        else: # not a hard problem, trivial solution exists
            return {"rop": 1, "error": "trivial"} # TODO