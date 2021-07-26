r""" 
TODO: documentation
"""

import sys
import os
import logging 
import sage.all
from sage.functions.log import log
from sage.functions.other import ceil, sqrt
from sage.rings.all import QQ, RR, ZZ
from sage.symbolic.all import pi
import cost_asymptotics
import estimate_all_schemes.estimator as est
oo = est.PlusInfinity()

## Logging ##
logger = logging.getLogger(__name__)


class Attack_Configuration():
    """
    Configuration of the attack vector (including cost models and algorithms used).
    """
    # TODO: custom reduction_cost_function

    def __init__(self, conservative=True, classical=True, quantum=True, sieving=True, enumeration=True, algorithms=["usvp", "lattice-reduction"], parallel=True, num_cpus=None):
        r""" 
        Configure cost estimation. 
        
        .. list-table:: List of cost models included for `conservative=True`
            :header-rows: 1
            
            * - Selection
              - Cost models
            * - default
              - "Q‑Core‑Sieve", "Lotus"
            * - `classical=False`
              - "Q‑Core‑Sieve", "Q‑Core‑Enum + O(1)"
            * - `quantum=False`
              - "Core‑Sieve", "Lotus"
        
        If `sieving=False` or `enumeration=False`, the cost models in the respective groups are removed from the list. For more details, see :ref:`cost_asymptotics <cost-models>`.
        
        :param conservative: use conservative estimates
        :param classical: use classical cost_models, `True` by default (at least one of classical/quantum must be `True`)
        :param quantum: use quantum quantum, `True` by default 
        :param sieving: use sieving cost_models, `True` by default (at least one of sieving/enumeration must be `True`)
        :param enumeration: use enumeration cost_models, `True` by default
        :param algorithms: list containing algorithms for cost estimate. For LWE and its variants, the list can contain "usvp", "dual", "dual-without-lll", "arora-gb", "decode", "mitm", "coded-bkw". For SIS and its variants, the list can contain "combinatorial", "lattice-reduction". Note that if all algorithms are in list, no estimate is computed and the return cost will be :math:`\infty`. 
        :param parallel: multiprocessing support, active by default
        :param num_cpus: optional parameter to specify number of cpus used during estimation
        """
        if not classical and not quantum:
            raise ValueError("At least one of classical or quantum must be True")
        if not sieving and not enumeration:
            raise ValueError("At least one of sieving or enumeration must be True")

        self.classical = classical
        self.quantum = quantum
        self.sieving = sieving
        self.enumeration = enumeration
        self.algorithms = algorithms # TODO: check docstring once all attacks have been implemented
        self.parallel = parallel
        self.num_cpus = num_cpus

        # TODO: change way of specifying cost models?
        if conservative:
            if self.quantum and self.classical and self.sieving and self.enumeration:
                bkz_cost_models = [c for c in cost_asymptotics.BKZ_COST_ASYMPTOTICS if c["name"] in ["Q‑Core‑Sieve", "Lotus"]]
            else:
                if self.quantum and not self.classical:
                    bkz_cost_models = [c for c in cost_asymptotics.BKZ_COST_ASYMPTOTICS if c["name"] in ["Q‑Core‑Sieve", "Q‑Core‑Enum + O(1)"]]
                elif self.classical and not self.quantum:
                    bkz_cost_models = [c for c in cost_asymptotics.BKZ_COST_ASYMPTOTICS if c["name"] in ["Core‑Sieve", "Lotus"]]
                if self.sieving and not self.enumeration:
                    bkz_cost_models = [c for c in bkz_cost_models if "sieving" in c["group"]]
                elif self.enumeration and not self.sieving:
                    bkz_cost_models = [c for c in bkz_cost_models if "enumeration" in c["group"]]
            self.cost_models = bkz_cost_models
        else:
            # TODO take all from each category, add priority for cost
            self.cost_models = cost_asymptotics.BKZ_COST_ASYMPTOTICS # TODO manually annotate priority
        
        logger.debug("Attack configuration:" + str(self))
    
    def add_reduction_cost_models(self, cost_models, replace_default=False):
        """
        Add custom reduction_cost_model. 

        Set "prio" to 0 in order to prioritize custom cost models.

        Example::

            cost_models = [
                {
                    "name": "Q-Enum",
                    "reduction_cost_model": lambda beta, d, B: ZZ(2)**RR(0.5*beta),
                    "success_probability": 0.99,
                    "human_friendly": "2<sup>0.5 β</sup>",
                    "group": "Quantum enumeration",
                    "prio": 0,
                },
            ]
        
        :param cost_model: list of reduction cost models (dict with keys "name", "reduction_cost_model" and "success_probability", optionally "human_friendly" and "group")
        :param replace_default: overwrite default cost model list
        """
        if replace_default:
            self.cost_models = cost_models
        else:
            self.cost_models = self.cost_models.extend(cost_models)

    def reduction_cost_models(self):
        """
        Returns list of reduction cost models.
        """
        return self.cost_models

    def __str__(self) -> str:
        return "Cost schemes: [" + ["", "classical "][self.classical] + ["", "quantum "][self.quantum] + ["", " sieving"][self.sieving] + ["", " enumeration"][self.enumeration] + "], " + "Algorithms: " + str(self.algorithms)


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
        
        If :math:`d > m`, take :math:`d = m`. 

        To calculate :math:`\delta_0` we use :cite:p:`RS10` Conjecture 2:

        For every :math:`n \geq 128,` constant :math:`c \geq 2, q \geq n^c, m = \Omega(n \log_2(q))` and :math:`\beta < q`, the best known approach to solve SIS with parameters (:math:`n, m, q, \beta`) involves solving :math:`\delta`-HSVP in dimension :math:`d = \min(x : q^{2n/x} \leq \beta)` with :math:`\delta_0 = \sqrt[d]{\beta / q^{n/d}}`.

        :math:`\delta_0` must be larger than 1 for the reduction to be tractable. From :math:`\delta_0 = \sqrt[d]{\beta / q^{n/d}} \geq 1` it follows that :math:`d \geq n \log_2(q) / \log_2(\beta)`. If :math:`m \leq n \log_2(q) / \log_2(\beta)` a :class:`ValueError` is raised. 

        
        Another approach is found in section 3.3 of :cite:`APS15`:
        
        .. math::

            \beta = \|x\|_2 = \delta_0 ^ m  \text{vol}(L) ^ {\frac{1}{m}} 

        If :math:`\text{vol}(L)=q^n`, then :math:`\beta = \delta_0 ^ m  q ^ {\frac{n}{m}}` and hence,

        .. math::
            \log \delta_0 = \frac{\log \beta}{m}  - \frac{n \log q}{m^2} \;\;\;\;\text{(I.)}

        The optimal dimension for the lattice reduction is :math:`m = \sqrt{\frac{n \log q}{\log \delta_0}}  \;\;\;\;\text{(II.)}`
        
        Combining II. with I. yields:

        .. math::

            \log \delta_0 &= \frac{\log \beta}{ \sqrt{n \log q / \log \delta_0}} - \frac{n \log q }{n \log q / \log \delta_0} \\
            \log \delta_0 &= \frac{\log \beta}{ \sqrt{n \log q / \log \delta_0}} - \log \delta_0 \\
            2\log \delta_0 &= \frac{\log \beta}{\sqrt{n \log q / \log \delta_0}} \\ 
            \sqrt{\log \delta_0} &= \frac{\log \beta}{ 2 \sqrt{n \log q}} \\ 
            \log \delta_0 &= \frac{\log^2 \beta}{ 4n \log q}

        In case both approaches succeed, the results of the approach that yields a lower :math:`\log \delta_0` are chosen to compute the block size :math:`k` to apply the reduction cost model.

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param bound: bound of solution, must be instance of :class:`Norm.Base_norm` 
        """
        # TODO check if use of n and m are correct
        # TODO: is it possible to use code from lwe-estimator, if yes, does it render better results? If not can we improve the model here to get a more practical result by including an estimate for number calls to the SVP oracle?

        beta = RR(bound.to_L2(n).value) # we need L2 norm TODO: check
        if beta <= 1:
            raise ValueError("beta < 1")
        if beta < q:
            rs10_failed = False
            try:
                # TODO: RS10 assumes delta-SVP solver => ensure that solver used here is indeed delta-HSVP
                # Requirements
                if n < 128 or q < n*n: 
                    raise ValueError("Violation of requirements of [RS10, Proposition 1] during SIS lattice reduction: n < 128 or q < n^2")
                if m < n * log(q, 2) / log(beta, 2):
                    raise ValueError("m must be > n * log_2(q)/log_2(beta). Else delta_0 < 1.")
                
                n = ZZ(n)
                q = ZZ(q)
                # Calculate optimal dimension for delta-HSVP solver
                d = ceil(2 * n * log(q, 2) / log(beta, 2)) 
                if d > m:
                    d = m            

                # Calculate approximation factor for delta-HSVP solver
                delta_0 = RR((beta / (q ** (n / d))) ** (1 / d))
                log_delta_0 = log(delta_0, 2)
            
            except ValueError:
                rs10_failed = True
                
            # [APS15]
            log_delta_0_APS15 = log(beta, 2) ** 2  / (4  * n * log(q, 2))
            d_APS15 = sqrt(n * log(q, 2) / log_delta_0_APS15)
            if d_APS15 > m:
                d_APS15 = m
                log_delta_0_APS15 = log(beta, 2) / m - n * log(q, 2) / (m ** 2)

            # take best value
            if rs10_failed or log_delta_0_APS15 < log_delta_0: 
                log_delta_0 = log_delta_0_APS15
                d = d_APS15

            if log_delta_0 < 0: # intractable
                    raise ValueError("Intractable: delta_0 < 1")

            else: # standard case
                k = est.betaf(2**log_delta_0) # block size k [APS15, lattice rule of thumb and Lemma 5]
                B = log(q, 2)

                # TODO: is that all we need?
                cost = reduction_cost_model(k, d, B) 
                return est.Cost([("rop", cost), ("d", d), ("beta", k)]) # d is lattice dimension, beta is block size

        else: # not a hard problem, trivial solution exists
            raise  ValueError("Trivial. beta > q")
            

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
        if beta <= 1:
            raise ValueError("beta < 1")
        elif beta < q:
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
            L = RR((2 * beta + 1)**(RR(m) / 2**k))
            list_element_cost = log(q, 2) * n
            lists = (2 ** k) * L
            cost = lists * list_element_cost

            return est.Cost([("rop", cost), ("k", RR(2**k))]) # TODO other information?, return k just as k?

        else: # not a hard problem, trivial solution exists
            raise  ValueError("Trivial. beta > q")