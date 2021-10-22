r"""Module for estimation algorithms. Includes a configuration class and several estimation algorithms for SIS."""

from multiprocessing import Value
import logging
import norm
import sage.all
from sage.functions.log import log
from sage.functions.other import ceil, sqrt
from sage.rings.all import QQ, RR, ZZ, RealField
from sage.symbolic.all import pi
import reduction_cost_models
import estimator as est
from sage.misc.functional import round

oo = est.PlusInfinity()

## Logging ##
logger = logging.getLogger(__name__)
SEPARATOR = (
    "\n----------------------------------------------------------------------------"
)

## Exception class ##
class TrivialSolution(Exception):
    pass


class IntractableSolution(Exception):
    pass


## Algorithms ##
# LWE
USVP = "usvp"
PRIMAL_USVP = "usvp"
PRIMAL_DECODE = "decode"
DECODE = "decode"
DUAL = "dual"
DUAL_NO_LLL = "dual-without-lll"
ARORA_GB = "arora-gb"
MITM = "mitm"
CODED_BKW = "coded-bkw"
BKW = "coded-bkw"

# SIS
LATTICE_REDUCTION = "reduction"
LATTICE_REDUCTION_RS = "reduction-rs"
REDUCTION = "reduction"
REDUCTION_RS = "reduction-rs"
COMBINATORIAL = "combinatorial"
COMBINATORIAL_CONSERVATIVE = "combinatorial_conservative"

# All
ALL = [
    "usvp",
    "decode",
    "dual",
    "dual-without-lll",
    "arora-gb",
    "mitm",
    "coded-bkw",
    "reduction",
    "reduction-rs",
    "combinatorial",
    "combinatorial_conservative",
]


## Solution passing strategy ##
class SecurityStrategy:
    """
    Strategy for a secure solution
    """

    pass


class ALL_SECURE(SecurityStrategy):
    """
    All algorithms must yield results that satisfy the security parameter.
    """

    pass


class SOME_SECURE(SecurityStrategy):
    """
    At least one algorithm must yield results that satisfy the security parameter. Other algorithms may fail in case of timeout or exception, but no insecure result is allowed.
    """

    pass


class NOT_INSECURE(SecurityStrategy):
    """
    Algorithms may fail in case of a timeout or an exception, but no insecure result is allowed.
    """

    pass


## BKZ SVP rounds ##
class BKZ_SVP_repeat_core:
    """Core-SVP model (only one BKZ round) :cite:p:`ADPS16`."""


class BKZ_SVP_repeat_8d:
    """SVP model with ``8n`` BKZ rounds :cite:p:`APS15`."""


class Configuration:
    def __init__(
        self,
        conservative=True,
        paranoid=False,
        classical=True,
        quantum=True,
        sieving=True,
        enumeration=True,
        bkz_svp_rounds=BKZ_SVP_repeat_core,
        custom_cost_models=[],
        algorithms=[USVP, REDUCTION],
        security_strategy: SecurityStrategy = SOME_SECURE,
        parallel=True,
        num_cpus=None,
        timeout=1000,
    ):
        r"""
        Configuration of the cost estimation parameters (including cost models and used algorithm).

        .. list-table:: List of cost models included for ``conservative=True``
            :header-rows: 1

            * - Selection
              - Cost models
            * - default
              - "Q‑Sieve", "Lotus"
            * - `classical=False`
              - "Q‑Sieve", "Q‑Enum + O(1)"
            * - `quantum=False`
              - "Sieve", "Lotus"

        If ``sieving=False`` or ``enumeration=False``, the cost models in the respective groups are removed from the list. For more details, see :ref:`cost_models <cost-models>`.

        To add custom cost models parameter ``custom_cost_models`` must be a list of dicts as in the following example::

            cost_models = [
                {
                    "name": "Q-Enum",
                    "cost_model": lambda beta, d, B: ZZ(2)**RR(0.5*beta),
                    "success_probability": 0.99,
                    "human_friendly": "2<sup>0.5 β</sup>",
                    "group": "Quantum enumeration",
                    "prio": 0,
                },
            ]


        Set ``prio`` to 0 in order to prioritize custom cost models. If you only want to use ``custom_cost_models`` for the estimate, set ``classical = quantum = sieving = enumeration = False``. Note that the filters will not apply to the list of custom_cost_models.

        :param conservative: use conservative estimates, ``True`` by default
        :param paranoid: set to include paranoid lower bound for quantum sieving, ``False`` by default
        :param classical: use classical cost_models, ``True`` by default
        :param quantum: use quantum quantum, ``True`` by default
        :param sieving: use sieving cost_models, ``True`` by default
        :param enumeration: use enumeration cost_models, ``True`` by default
        :param bkz_svp_rounds: ``BKZ_SVP_repeat_core`` for the Core-SVP model, can also be``BKZ_SVP_repeat_8d`` for ``8n`` BKZ rounds
        :param algorithms: list containing algorithms for cost estimate. For LWE and its variants, the list can contain the constants ``USVP`` (or ``PRIMAL_USVP``), ``PRIMAL_DECODE`` (or ``DECODE``), ``DUAL``, ``DUAL_NO_LLL``, ``ARORA_GB``, ``MITM``, ``CODED_BKW`` (or ``BKW``). For SIS and its variants, the list can contain ``LATTICE_REDUCTION`` (or ``REDUCTION``), ``LATTICE_REDUCTION_RS`` (or ``REDUCTION_RS``), ``COMBINATORIAL`` and ``COMBINATORIAL_CONSERVATIVE``. Instead of a list, the parameter can be set to ``ALL`` to run all algorithms. The constants are included in :py:mod:`lattice_parameter_estimation.algorithms`. Default is ``[USVP, REDUCTION]``. For more details see :py:mod:`lattice_parameter_estimation.problem.LWE.get_estimate_algorithms` and :py:mod:`lattice_parameter_estimation.problem.SIS.get_estimate_algorithms`
        :param custom_cost_models: list of reduction cost models (see above)
        :param parallel: multiprocessing support, active by default
        :param num_cpus: optional parameter to specify number of cpus used during estimation
        :param timeout: timeout of cost estimation for one parameter set
        """
        if not algorithms:
            ValueError(
                "algorithms empty. Please choose algorithms to run the estimates."
            )
        if not all(x in ALL for x in algorithms):
            ValueError(
                "algorithms not specified correctly. Please use the constants specified in the documentation."
            )

        self.security_strategy = security_strategy
        self.classical = classical
        self.quantum = quantum
        self.sieving = sieving
        self.enumeration = enumeration
        self.bkz_svp_rounds = bkz_svp_rounds
        sis_algs = [REDUCTION, COMBINATORIAL, REDUCTION_RS, COMBINATORIAL_CONSERVATIVE]
        lwe_algs = [
            "usvp",
            "decode",
            "dual",
            "dual-without-lll",
            "arora-gb",
            "mitm",
            "coded-bkw",
        ]
        if not set(sis_algs) & set(algorithms):
            print(SEPARATOR)
            input(
                "No algorithm for SIS specified. Press Enter to ignore and continue..."
            )
        if not set(lwe_algs) & set(algorithms):
            print(SEPARATOR)
            input(
                "No algorithm for LWE specified. Press Enter to ignore and continue..."
            )
        self.algorithms = (
            algorithms  # TODO: check docstring once all attacks have been implemented
        )
        self.parallel = parallel
        self.num_cpus = num_cpus
        self.timeout = timeout

        if (not classical and not quantum) or (not sieving and not enumeration):
            if not custom_cost_models:
                raise ValueError(
                    "At least one of classical or quantum/sieving and enumeration must be True or custom_cost_models must be specified"
                )
            self.cost_models = custom_cost_models
        else:
            if bkz_svp_rounds == BKZ_SVP_repeat_core:
                unfiltered_cost_models = reduction_cost_models.BKZ_COST_MODELS
            else:
                unfiltered_cost_models = reduction_cost_models.BKZ_COST_MODELS_8d
            bkz_cost_models = []
            if not paranoid:
                unfiltered_cost_models = [
                    c for c in unfiltered_cost_models if "paranoid" not in c["name"]
                ]
            if conservative:
                if (
                    self.quantum
                    and self.classical
                    and self.sieving
                    and self.enumeration
                ):
                    if paranoid:
                        bkz_cost_models = [
                            c
                            for c in unfiltered_cost_models
                            if c["name"] in ["Lotus"] or "paranoid" in c["name"]
                        ]
                    else:
                        bkz_cost_models = [
                            c
                            for c in unfiltered_cost_models
                            if c["name"] in ["Q‑Sieve", "Lotus"]
                        ]
                else:
                    if self.quantum and not self.classical:
                        if paranoid:
                            bkz_cost_models = [
                                c
                                for c in unfiltered_cost_models
                                if c["name"] in ["Q‑Enum + O(1)"]
                                or "paranoid" in c["name"]
                            ]
                        else:
                            bkz_cost_models = [
                                c
                                for c in unfiltered_cost_models
                                if c["name"] in ["Q‑Sieve", "Q‑Enum + O(1)"]
                            ]
                    elif self.classical and not self.quantum:
                        bkz_cost_models = [
                            c
                            for c in unfiltered_cost_models
                            if c["name"] in ["Sieve", "Lotus"]
                        ]
                    if self.sieving and not self.enumeration:
                        bkz_cost_models = [
                            c for c in bkz_cost_models if "sieving" in c["method"]
                        ]
                    elif self.enumeration and not self.sieving:
                        bkz_cost_models = [
                            c for c in bkz_cost_models if "enumeration" in c["method"]
                        ]
                self.cost_models = bkz_cost_models + custom_cost_models
            else:
                bkz_cost_models = [
                    c
                    for c in unfiltered_cost_models
                    if c["quantum"] in {quantum, not enumeration}
                    and c["method"]
                    in ["", "enumeration"][enumeration] + ["", "sieving"][sieving]
                ]
                self.cost_models = bkz_cost_models + custom_cost_models

        logger.debug("Attack configuration:" + str(self))

    def reduction_cost_models(self):
        """
        Returns list of reduction cost models.
        """
        return self.cost_models

    def __str__(self) -> str:
        return (
            "Cost schemes: ["
            + ["", "classical "][self.classical]
            + ["", "quantum "][self.quantum]
            + ["", " sieving"][self.sieving]
            + ["", " enumeration"][self.enumeration]
            + "], "
            + "Algorithms: "
            + str(self.algorithms)
        )


class SIS:
    """
    Namespace for SIS algorithms
    """

    def lattice_reduction_rs(
        n, beta, q, success_probability=None, m=oo, reduction_cost_model=None
    ):
        r""" 
        Estimate cost of solving SIS by means of lattice reduction according to :cite:p:`RS10`. Part of this method is based on :py:mod:`lattice_parameter_estimation.estimator.estimator._dual`.

        Find optimal lattice subdimension :math:`d` and root-Hermite factor :math:`\delta_0` for lattice reduction.
        To calculate :math:`d`, we use :cite:p:`RS10` Proposition 1 (Normalization of q-ary Lattices):

        Let :math:`n \geq 128, q \geq n^2,` and :math:`\beta < q`. Let :math:`S` be a :math:`\delta`-HSVP solver for variable :math:`\delta`. The optimal dimension for solving SIS(:math:`n, m, q, \beta`) with :math:`S` is :math:`d = \min(x : q^{2n/x} \leq \beta)`.

        .. math::

            q^{2n / d} &\leq \beta \\
            \frac{2n}{d \log(q)} &\leq \beta \\
            d &\geq \frac{2n \log(q)}{\log(\beta)}
        
        If :math:`d > m`, take :math:`d = m`. 

        To calculate :math:`\delta_0` we use :cite:p:`RS10` Conjecture 2:

        For every :math:`n \geq 128,` constant :math:`c \geq 2, q \geq n^c, m = \Omega(n \log_2(q))` and :math:`\beta < q`, the best known approach to solve SIS with parameters (:math:`n, m, q, \beta`) involves solving :math:`\delta`-HSVP in dimension :math:`d = \min(x : q^{2n/x} \leq \beta)` with :math:`\delta_0 = \sqrt{d}{\beta / q^{n/d}}`.

        :math:`\delta_0` must be larger than 1 for the reduction to be tractable. From :math:`\delta_0 = \sqrt{d}{\beta / q^{n/d}} \geq 1` it follows that :math:`d \geq n \log_2(q) / \log_2(\beta)`. If :math:`d \leq n \log_2(q) / \log_2(\beta)` a :class:`ValueError` is raised. 

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param beta: bound in :math:`L_2`-norm (value not class)
        """
        # TODO check if use of n and m are correct
        # TODO: is it possible to use code from lwe-estimator, if yes, does it render better results? If not can we improve the model here to get a more practical result by including an estimate for number calls to the SVP oracle?
        # TODO: rinse and repeat? adapt to code in estimator?

        try:
            prec = beta.prec()
        except:
            prec = 128
        RR = RealField(prec)
        beta = RR(beta)

        if beta <= 1:
            raise IntractableSolution("beta < 1")
        if beta < norm.Loo(q / 2, n).to_L2().value:
            # TODO: RS10 assumes delta-SVP solver => ensure that solver used here is indeed delta-HSVP
            # Requirements
            # if n < 128 or q < n * n:
            #     raise ValueError(
            #         "Violation of requirements of [RS10, Proposition 1] during SIS lattice reduction: n < 128 or q < n^2"
            #     )
            # if m < n * log(q, 2) / log(beta, 2):
            #     raise ValueError(
            #         "m must be > n * log_2(q)/log_2(beta). Else delta_0 < 1."
            #     )

            n = ZZ(n)
            q = ZZ(q)
            # Calculate optimal dimension for delta-HSVP solver
            m_optimal = ceil(2 * n * log(q, 2) / log(beta, 2))
            if m > m_optimal:
                m = m_optimal

            # Calculate approximation factor for delta-HSVP solver
            delta_0 = RR((beta / (q ** (n / m))) ** (1 / m))

            # check for valid delta
            if delta_0 < 1:
                raise IntractableSolution("delta_0 < 1")
            if delta_0 < est.delta_0f(m_optimal):
                raise est.OutOfBoundsError(
                    "delta_0 = %f < %f" % (delta_0, est.delta_0f(m))
                )

            ret = est.lattice_reduction_cost(
                reduction_cost_model, delta_0, m, B=log(q, 2)
            )
            ret["m"] = m
            ret["d"] = m  # d is lattice dimension, beta is block size
            ret["|v|"] = RR(delta_0 ** m * q ** (n / m))
            return ret.reorder(["rop", "m"])

        else:  # not a hard problem, trivial solution exists
            raise TrivialSolution(
                f"beta > ||(q/2, ..., q/2)|| (beta={beta}, q={q}, ||...||={norm.Loo(q/2, n).to_L2().value})"
            )

    def lattice_reduction(
        n, beta, q, success_probability=None, m=oo, reduction_cost_model=None
    ):
        r""" 
        Estimate cost of solving SIS by means of lattice reduction according to section 3.3 of :cite:`APS15` and :cite:`MR09`. Part of this method is based on :py:mod:`lattice_parameter_estimation.estimator._dual`.

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

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param beta: bound of solution in :math:`L_2`-norm (value not class)
        """
        # TODO check if use of n and m are correct

        try:
            prec = beta.prec()
        except:
            prec = 128
        RR = RealField(prec)
        beta = RR(beta)

        if beta <= 1:
            raise IntractableSolution("beta < 1")
        if beta < norm.Loo(q / 2, n).to_L2().value:

            log_delta_0 = log(beta, 2) ** 2 / (4 * n * log(q, 2))
            delta_0 = min(RR(2) ** log_delta_0, RR(1.02190))  # at most LLL
            m_optimal = est.lattice_reduction_opt_m(n, q, delta_0)

            if m > m_optimal:
                m = m_optimal
            else:
                log_delta_0 = log(beta, 2) / m - RR(n * log(q, 2)) / (m ** 2)
                delta_0 = RR(2 ** log_delta_0)

            # check for valid delta
            if delta_0 < 1:
                raise IntractableSolution("delta_0 < 1")
            if delta_0 < est.delta_0f(m):
                raise IntractableSolution(
                    "delta_0 = %f < %f (best achievable delta_0 with block size k=m)"
                    % (delta_0, est.delta_0f(m))
                )

            ret = est.lattice_reduction_cost(
                reduction_cost_model, delta_0, m, B=log(q, 2)
            )
            ret["m"] = m
            ret["d"] = m  # d is lattice dimension, beta is block size
            ret["|v|"] = RR(delta_0 ** m * q ** (n / m))
            return ret.reorder(["rop", "m"])

        else:  # not a hard problem, trivial solution exists
            raise TrivialSolution(
                f"beta > ||(q/2, ..., q/2)|| (beta={beta}, q={q}, ||...||={norm.Loo(q/2, n).to_L2().value})"
            )

    def _combinatorial(q, n, m, beta):
        r"""
        Subroutine to compute the list size in the combinatorial attack described in :cite:`MR09`.

        For more details, see :py:func:`algorithms.combinatorial`.

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param beta: bound of solution in :math:`L_\infty`-norm (value not class)

        :returns: tuple ``(L, k)`` of list size ``L`` and optimal ``k``such that combinatorial method can divide columns of :math:`A` into :math:`2^k` groups
        """
        # find optimal k
        k = closest_k = 1
        difference = oo
        failed, max_failures = 0, 10
        while failed < max_failures:
            left = 2 ** k / (k + 1)
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
        L = RR((2 * beta + 1) ** (RR(m) / 2 ** k))
        return (L, k)

    def combinatorial(q, n, m, bound, reduction_cost_model=None):
        r""" 
        Estimate cost of solving SIS by means of the combinatorial method as described in :cite:`MR09`.

        Search for optimal k such that combinatorial method can divide columns of :math:`A` into :math:`2^k` groups as described in :cite:`MR09`, p. 7. :math:`k` is chosen such that :math:`n \approx (k + 1) \log_q (L)`, where :math:`L = (2\beta + 1)^{m/2^k}` describes the number of vectors per list. Equivalently, we have 

        .. math::
            \frac{2^k}{k+1} &\approx \frac{m \log(2\beta + 1)}{n \log(q)}\\
            \text{diff} &= \text{abs}\left(\frac{2^k}{k+1} - \frac{m \log(2\beta + 1)}{n \log(q)}\right)

        To find an optimal :math:`k`, we iterate over :math:`k` starting from :math:`k=1` and calculate the difference :math:`\text{diff}`. When :math:`\text{diff}` does not decrease for 10 iteration steps, we stop and take the current :math:`k`.

        We make a conservative estimate of the cost by estimating the number of operations needed to create the initial lists. Each of the :math:`2^k` lists contains :math:`L` vectors. The cost for any operation on a list element is at least :math:`\log_2(q) \cdot n`. Hence, the total cost is :math:`2^k \cdot L \cdot \log_2(q) \cdot n`.

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param bound: bound of solution in :math:`L_\infty`-norm (value not class)
        """
        beta = bound  # we need Loo norm
        if beta <= 1:
            raise IntractableSolution("beta < 1")
        elif beta < norm.Loo(q / 2, n).to_L2().value:
            (L, k) = SIS._combinatorial(q, n, m, beta)
            list_element_cost = log(q, 2) * n
            lists = (2 ** k) * L
            cost = RR(lists * list_element_cost)

            return est.Cost([("rop", cost), ("k", RR(2 ** k))])

        else:  # not a hard problem, trivial solution exists
            raise TrivialSolution(
                f"beta > ||(q/2, ..., q/2)|| (beta={beta}, q={q}, ||...||={norm.Loo(q/2, n).to_L2().value})"
            )

    def combinatorial_conservative(q, n, m, bound, reduction_cost_model=None):
        r"""
        Estimate cost of solving SIS conservatively by means of the combinatorial method as described in :cite:`MR09`.

        The algorithm works as :py:func:`combinatorial` but outputs a more conservative cost. The overall runtime is dominated by the size of the lists. Variants of the algorithm may speed up various steps and hence we neglect the cost of single operations in the algorithm and just set the cost to the list size :math:`L`.

        :param n: height of matrix
        :param m: width of matrix
        :param q: modulus
        :param bound: bound of solution in :math:`L_\infty`-norm (value not class)
        """
        beta = bound  # we need Loo norm
        if beta <= 1:
            raise IntractableSolution("beta < 1")
        elif beta < norm.Loo(q / 2, n).to_L2().value:

            (L, k) = SIS._combinatorial(q, n, m, beta)
            cost = L

            return est.Cost([("rop", cost), ("k", RR(2 ** k))])

        else:  # not a hard problem, trivial solution exists
            raise TrivialSolution(
                f"beta > ||(q/2, ..., q/2)|| (beta={beta}, q={q}, ||...||={norm.Loo(q/2, n).to_L2().value})"
            )
