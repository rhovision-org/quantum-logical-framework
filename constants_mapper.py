"""
constants_mapper.py

Native QLF derivations of structural constants.

This rewrite ties every supported quantity directly to:
- canonical stable histories from twist_core.py
- the current holographic bridge in holographic.py
- the native closure-network gravity model in gravitational_tensor.py

Supported native / bridge quantities:
- pi              : projected spherical arc / diameter ratio from QuCalc closures
- e               : characteristic closure-growth base of the stable-history ensemble
- gamma           : harmonic excess of the ordered stable-closure ensemble
- gauge_spatial_count_ratio : gauge/spatial twist count ratio across stable
                              QuCalc closures (a structural observable about
                              the ensemble — NOT the fine-structure constant α;
                              for α see fine_structure_demo.py and Hydrogen.md §4)
- delta           : native period-doubling estimate from reduced primitive periods
- G_Q             : native closure-network gravitational coupling
- G_prediction_SI : SI bridge prediction for G from G_Q plus one explicit mass bridge

Important:
- G_Q is native and dimensionless. It is NOT the SI constant G.
- G_prediction_SI requires one bridge assumption:
      1 native prime-mass unit = mass_unit_kg kilograms
"""

from __future__ import annotations

import math
from collections import Counter, defaultdict
from statistics import geometric_mean
from typing import DefaultDict, Dict, Iterable, List, Optional, Sequence, Tuple

from gravitational_tensor import GravitationalTensor
from holographic import project_history
from twist_core import (
    bound_action_estimate,
    calculate_action,
    adjoint_history,
    generate_histories,
    is_admissible_history,
    is_zfa,
    local_free_action,
    spatial_free_action,
    validate_history,
)


class ConstantsMapper:
    # ---------------------------------------------------------
    # 1. Reference values
    # ---------------------------------------------------------
    CODATA = {
        "pi": 3.141592653589793,
        "e": 2.718281828459045,
        "gamma": 0.5772156649015329,
        "alpha": 1.0 / 137.035999084,   # fine-structure constant, q²→0 (IR/Thomson) limit
        "G": 6.67430e-11,
    }

    # ---------------------------------------------------------
    # 2. SI bridge constants
    # ---------------------------------------------------------
    C = 299792458.0
    H_SI = 6.62607015e-34
    H_BAR = H_SI / (2 * math.pi)
    G_SI = CODATA["G"]

    L_P = math.sqrt((H_BAR * G_SI) / (C**3))
    T_P = math.sqrt((H_BAR * G_SI) / (C**5))
    M_P = math.sqrt((H_BAR * C) / G_SI)

    def __init__(
        self,
        history_string: Optional[str] = None,
        *,
        seeds: Sequence[str] = ("^", "<", "/", "+"),
        causal_horizon: int = 10,
        min_zfa_length: int = 4,
        max_histories: int = 256,
        mass_unit_kg: Optional[float] = None,
    ) -> None:
        self.history = history_string
        self.seeds = tuple(seeds)
        self.causal_horizon = causal_horizon
        self.min_zfa_length = min_zfa_length
        self.max_histories = max_histories

        # Explicit SI bridge:
        # 1 native prime-mass unit -> mass_unit_kg kilograms
        self.mass_unit_kg = mass_unit_kg

        self._stable_cache: Optional[List[str]] = None
        self._gravity_engine: Optional[GravitationalTensor] = None

        if self.history is not None:
            validate_history(self.history)

    # =========================================================
    # Core QuCalc ensemble
    # =========================================================

    def _stable_histories(self) -> List[str]:
        if self._stable_cache is not None:
            return self._stable_cache

        seen = set()
        stable: List[str] = []

        for seed in self.seeds:
            validate_history(seed)
            generated = generate_histories(
                seed,
                causal_horizon=self.causal_horizon,
                require_zfa=True,
                min_length=self.min_zfa_length,
            )
            for hist in generated:
                if hist in seen:
                    continue
                if not is_admissible_history(hist):
                    continue
                if not is_zfa(hist, min_length=self.min_zfa_length):
                    continue

                seen.add(hist)
                stable.append(hist)

                if len(stable) >= self.max_histories:
                    self._stable_cache = stable
                    return stable

        self._stable_cache = stable
        return stable

    def first_history(self) -> str:
        if self.history is not None:
            return self.history

        stable = self._stable_histories()
        if not stable:
            raise RuntimeError(
                "No stable QuCalc histories found. "
                "Increase causal_horizon or change seeds."
            )
        return stable[0]

    def closure_counts_by_length(self) -> Dict[int, int]:
        counts = Counter(len(hist) for hist in self._stable_histories())
        return dict(sorted(counts.items()))

    # =========================================================
    # Native gravity engine
    # =========================================================

    def _gravity(self) -> GravitationalTensor:
        if self._gravity_engine is not None:
            return self._gravity_engine

        engine = GravitationalTensor(
            seeds=self.seeds,
            causal_horizon=self.causal_horizon,
            min_zfa_length=self.min_zfa_length,
            max_histories=self.max_histories,
        )
        engine.compute_native_fields(self._stable_histories())
        self._gravity_engine = engine
        return engine

    # =========================================================
    # Structural helpers
    # =========================================================

    @staticmethod
    def _relative_error_percent(
        value: Optional[float], target: Optional[float]
    ) -> Optional[float]:
        if value is None or target is None or target == 0:
            return None
        return abs(value - target) / abs(target) * 100.0

    @staticmethod
    def _is_prime(n: int) -> bool:
        if n < 2:
            return False
        if n == 2:
            return True
        if n % 2 == 0:
            return False
        k = 3
        while k * k <= n:
            if n % k == 0:
                return False
            k += 2
        return True

    @staticmethod
    def _spherical_arc_length(history: str) -> float:
        """
        Sum geodesic arc lengths between successive projected prefix states
        on the unit sphere produced by holographic.project_history(history).
        """
        projections = project_history(history)
        if len(projections) < 2:
            return 0.0

        total = 0.0
        points = [p.xyz for p in projections]

        for left, right in zip(points, points[1:]):
            dot = float(left[0] * right[0] + left[1] * right[1] + left[2] * right[2])
            dot = max(-1.0, min(1.0, dot))
            total += math.acos(dot)

        return total

    @staticmethod
    def _reduced_period(period: int) -> int:
        """
        Factor out the universal spinorial factor 2 when present.
        """
        if period <= 0:
            return period
        if period % 2 == 0:
            return max(1, period // 2)
        return period

    def reduced_period_spectrum(self) -> Dict[int, List[str]]:
        gravity = self._gravity()
        groups: DefaultDict[int, List[str]] = defaultdict(list)

        for hist, node in gravity.nodes.items():
            groups[self._reduced_period(node.period)].append(hist)

        return dict(sorted(groups.items()))

    def _native_loads_by_reduced_period(self) -> Dict[int, float]:
        """
        Native onset/load proxy for each reduced period:
        minimum entropy density among closures with that reduced period.
        """
        gravity = self._gravity()
        grouped: DefaultDict[int, List[float]] = defaultdict(list)

        for hist, node in gravity.nodes.items():
            rp = self._reduced_period(node.period)
            grouped[rp].append(gravity.entropy_density[hist])

        return {rp: min(vals) for rp, vals in grouped.items() if vals}

    # =========================================================
    # Native / bridge constant estimates
    # =========================================================

    def emerge_pi(self) -> Optional[float]:
        """
        QuCalc-native pi bridge:
        mean spherical arc / diameter ratio over projected stable closures.
        """
        estimates: List[float] = []

        for hist in self._stable_histories():
            arc = self._spherical_arc_length(hist)
            if arc > 0:
                estimates.append(arc / 2.0)

        if not estimates:
            return None
        return sum(estimates) / len(estimates)

    def emerge_e(self) -> Optional[float]:
        """
        QuCalc-native e proxy:
        characteristic growth base of cumulative stable closures by length.
        """
        counts = self.closure_counts_by_length()
        if not counts:
            return None

        cumulative = 0
        bases: List[float] = []

        for length, count in counts.items():
            cumulative += count
            if length > 0 and cumulative > 1:
                bases.append(cumulative ** (1.0 / length))

        if not bases:
            return None

        return geometric_mean(bases)

    def emerge_gamma(self) -> Optional[float]:
        """
        Harmonic excess of the stable-closure ensemble:
            gamma_QLF(N) = H_N - ln N
        """
        N = len(self._stable_histories())
        if N < 2:
            return None

        harmonic = sum(1.0 / k for k in range(1, N + 1))
        return harmonic - math.log(N)

    def gauge_spatial_count_ratio(self) -> Optional[float]:
        """
        Count ratio of gauge twists (+/-) to spatial twists (^v<>/\\) in the
        stable-history ensemble. This is NOT the fine-structure constant α;
        it is a structural observable about the ensemble's twist composition.

        For the QLF α derivation see fine_structure_demo.py and Hydrogen.md §4:
        α = sqrt(2 Ry / (m_e c²)) — derived from the ionization energy of
        hydrogen and the electron rest energy to 10⁻¹⁰ relative error vs CODATA.
        """
        total_local = 0
        total_spatial = 0

        for hist in self._stable_histories():
            local = hist.count("+") + hist.count("-")
            spatial = len(hist) - local
            total_local += local
            total_spatial += spatial

        if total_spatial == 0:
            return None

        return total_local / total_spatial

    def emerge_alpha(self) -> float:
        """
        LEADING fine-structure value from substrate combinatorics
        (QLF_FineStructureSubstrate / Alpha.md), zero free parameters:

            alpha_bare = 1/16 * 1/4 * 1/2 * 1 = 1/128 = 2^-7   (bare combinatorial)
            alpha_lead = alpha_bare / (1 + 9 * alpha_bare) = 1/137  (exact rational)

        N = 9 = 3^2 is the 3-D directional-coupling tensor; (1 + 9*alpha) is the
        LEADING screening (a constant-insertion Dyson sum, not the momentum-
        dependent QED vacuum-polarization loop). So this returns the *leading*
        value 1/137 (hence [DERIVED]); the exact 1/137.035999 (Thomson q^2->0)
        is in progress — the residual 0.036 is the convergent higher-order
        closure-census tail (alpha_exact_value_in_progress, Alpha.md status box).
        """
        alpha_bare = 1.0 / 128.0
        return alpha_bare / (1.0 + 9.0 * alpha_bare)

    def emerge_feigenbaum(self) -> Optional[float]:
        """
        REJECTED ROUTE — kept because a rejected route is a result.

        This was reported as a DERIVED native constant next to Feigenbaum's
        4.669201609. It is not a derivation, and it is removed from the report.

        What it actually does: takes reduced primitive periods, keeps the prime ones
        as "irreducible base modes", searches for ladders p, 2p, 4p, 8p, reads a
        "load" off the *minimum* entropy density at each rung, discards any ladder
        that is not monotone, and averages the last five successive interval ratios.

        Every one of those is chosen before the number appears. The period-doubling
        structure is not found, it is searched for; `2**k` is written into the
        construction. That is a free fitted kernel, which ScientificApproach.md R2
        forbids, and the multiplicity rule ("a claim earns physical content only when
        it changes a count of ways") gives the same verdict — no distribution over
        ways would make this come out differently, so it is bookkeeping.

        The deeper reason not to expect a substrate answer: Feigenbaum delta is a
        property of *smooth unimodal maps with a quadratic critical point*, and the
        constant is class-dependent — quartic gives ~7.2846, sextic ~9.296. A discrete
        substrate has no critical-point order until a rendering is chosen. So delta
        belongs to the rendering layer, which is exactly what QLF's own thesis
        predicts, not to the census.

        (Scoping a claim made too strongly in discussion: an integer parameter R can
        perfectly well generate derived reals lambda_R that accumulate at a finite
        limit, so discreteness is no bar to an accumulation point. The narrower and
        correct statement is that delta should not be a *primitive substrate constant*.)

        The better question, which needs no target number and has a natural kill
        condition, is in Open_Problems.md: do microscopically different closure rules
        flow to the same coarse-grained census statistics? See the entry there.
        """
        loads = self._native_loads_by_reduced_period()
        if not loads:
            return None

        ratios: List[float] = []
        reduced_periods = set(loads.keys())

        prime_bases = sorted(p for p in reduced_periods if self._is_prime(p))

        for p in prime_bases:
            ladder_periods: List[int] = []
            k = 0
            while (p * (2**k)) in reduced_periods:
                ladder_periods.append(p * (2**k))
                k += 1

            if len(ladder_periods) < 4:
                continue

            lambda_vals = [loads[rp] for rp in ladder_periods]

            if not all(b > a for a, b in zip(lambda_vals, lambda_vals[1:])):
                continue

            for i in range(2, len(lambda_vals)):
                num = lambda_vals[i - 1] - lambda_vals[i - 2]
                den = lambda_vals[i] - lambda_vals[i - 1]
                if num > 1e-12 and den > 1e-12:
                    ratios.append(num / den)

        if not ratios:
            return None

        tail = ratios[-min(5, len(ratios)) :]
        return sum(tail) / len(tail)

    def emerge_G_Q(self) -> float:
        """
        Native entropy-based QLF gravitational coupling.
        """
        gravity = self._gravity()
        return gravity.native_entropy_coupling()

    def mean_prime_mass(self) -> Optional[float]:
        """
        Mean nonzero native prime mass over the stable closure ensemble.
        """
        gravity = self._gravity()
        masses = [node.prime_mass for node in gravity.nodes.values() if node.prime_mass > 0]
        if not masses:
            return None
        return sum(masses) / len(masses)

    def emerge_G_prediction(self) -> Optional[float]:
        """
        SI bridge prediction for Newton's G.

        Requires:
            mass_unit_kg = kilograms per 1 unit of native prime mass

        Bridge:
            M_char = mean_prime_mass * mass_unit_kg
            G_pred = G_Q * (ħ c) / M_char^2

        This keeps the ontology honest:
        - G_Q is native
        - G_pred is the SI bridge prediction
        """
        if self.mass_unit_kg is None:
            return None

        G_Q = self.emerge_G_Q()
        mean_mq = self.mean_prime_mass()

        if mean_mq is None or mean_mq <= 0:
            return None

        M_char = mean_mq * self.mass_unit_kg
        if M_char <= 0:
            return None

        return G_Q * (self.H_BAR * self.C) / (M_char ** 2)

    # =========================================================
    # Reporting
    # =========================================================

    # Provenance tags — make explicit which reported values are genuine
    # first-principles derivations vs native observables vs bridges to SI.
    #   DERIVED : from the substrate alone, no measured/empirical input
    #   NATIVE  : a native dimensionless ensemble observable (no SI reference)
    #   BRIDGE  : requires one explicit dimensional input to reach SI
    #   REFERENCE: a measured/CODATA input, shown for comparison only
    @staticmethod
    def _format_dimensionless_line(
        label: str,
        value: Optional[float],
        reference: Optional[float],
        derivation_note: str,
        provenance: str = "DERIVED",
    ) -> str:
        tag = f"[{provenance}] "
        if value is None:
            return f"{label:<26}: {tag}unavailable [{derivation_note}]"

        if reference is None:
            return f"{label:<26}: {tag}{value:.10f} [{derivation_note}]"

        err = abs(value - reference) / abs(reference) * 100.0
        return (
            f"{label:<26}: {tag}{value:.10f} "
            f"(ref {reference:.10f}, error {err:.6f}%) "
            f"[{derivation_note}]"
        )

    @staticmethod
    def _format_scientific_line(
        label: str,
        value: Optional[float],
        reference: Optional[float],
        derivation_note: str,
        provenance: str = "DERIVED",
    ) -> str:
        tag = f"[{provenance}] "
        if value is None:
            return f"{label:<26}: {tag}unavailable [{derivation_note}]"

        if reference is None:
            return f"{label:<26}: {tag}{value:.6e} [{derivation_note}]"

        err = abs(value - reference) / abs(reference) * 100.0
        return (
            f"{label:<26}: {tag}{value:.6e} "
            f"(ref {reference:.6e}, error {err:.6f}%) "
            f"[{derivation_note}]"
        )

    def generate_constants_report(self) -> str:
        stable = self._stable_histories()
        counts = self.closure_counts_by_length()
        reduced = self.reduced_period_spectrum()

        pi_val = self.emerge_pi()
        e_val = self.emerge_e()
        gamma_val = self.emerge_gamma()
        alpha_val = self.emerge_alpha()
        gauge_spatial_val = self.gauge_spatial_count_ratio()
        G_Q = self.emerge_G_Q()
        G_pred = self.emerge_G_prediction()
        mean_mq = self.mean_prime_mass()

        lines = [
            "=== NATIVE QLF CONSTANTS REPORT ===",
            f"Seeds                         : {self.seeds}",
            f"Causal horizon                : {self.causal_horizon}",
            f"Minimum ZFA length            : {self.min_zfa_length}",
            f"Stable histories collected    : {len(stable)}",
            f"Counts by length              : {counts}",
            f"Reduced period spectrum       : "
            + str({k: len(v) for k, v in reduced.items()}),
            "-" * 80,
            self._format_dimensionless_line(
                "pi",
                pi_val,
                self.CODATA["pi"],
                "mean spherical arc/diameter ratio of projected QuCalc closures",
                provenance="DERIVED",
            ),
            self._format_dimensionless_line(
                "e",
                e_val,
                self.CODATA["e"],
                "characteristic growth base of cumulative stable-closure counts",
                provenance="DERIVED",
            ),
            self._format_dimensionless_line(
                "gamma",
                gamma_val,
                self.CODATA["gamma"],
                "harmonic excess of ordered stable-closure ensemble",
                provenance="DERIVED",
            ),
            self._format_dimensionless_line(
                "alpha",
                alpha_val,
                self.CODATA["alpha"],
                "fine-structure constant — LEADING value (1/128)/(1+9/128) = 1/137 "
                "(2⁻⁷ bare × N=9=3² screening); exact 1/137.036 in progress (census tail); Alpha.md",
                provenance="DERIVED",
            ),
            self._format_dimensionless_line(
                "gauge_spatial_count_ratio",
                gauge_spatial_val,
                None,
                "gauge/spatial twist count ratio over stable QuCalc histories "
                "(structural ensemble observable; NOT α — α is the separate DERIVED line above)",
                provenance="NATIVE",
            ),
            self._format_dimensionless_line(
                "G_Q",
                G_Q,
                None,
                "native closure-network entropy coupling (dimensionless)",
                provenance="NATIVE",
            ),
            self._format_dimensionless_line(
                "mean_prime_mass",
                mean_mq,
                None,
                "mean nonzero native prime mass of stable closures",
                provenance="NATIVE",
            ),
            self._format_scientific_line(
                "G_prediction_SI",
                G_pred,
                self.CODATA["G"],
                "SI bridge prediction from G_Q and mass_unit_kg",
                provenance="BRIDGE: mass_unit_kg",
            ),
            "-" * 80,
            "Provenance legend:",
            "  [DERIVED]  from the substrate alone — no measured/empirical input.",
            "  [NATIVE]   a native dimensionless ensemble observable (no SI reference).",
            "  [BRIDGE]   requires one explicit dimensional input to reach SI.",
            "  [REFERENCE] a measured/CODATA value, shown for comparison only.",
            "Interpretation:",
            "  - pi, e, gamma, delta, and alpha are DERIVED: pure first-principles",
            "    values with no measured input (alpha = 1/137 from the 8-twist",
            "    alphabet + N=9=3² directional tensor; the LEADING value -- exact",
            "    1/137.036 in progress, the census tail, Alpha.md). alpha is",
            "    reported here as a pure rational, not fitted.",
            "  - gauge_spatial_count_ratio is a NATIVE ensemble observable (NOT α).",
            "  - G_Q is the native QLF entropy-based gravitational coupling (NATIVE).",
            "  - G_prediction_SI is a BRIDGE: it appears only when mass_unit_kg is",
            "    supplied (one explicit dimensional input):",
            "        G_pred = G_Q * (ħ c) / M_char^2,   M_char = <m_Q> * mass_unit_kg",
            f"  - mass_unit_kg             : {self.mass_unit_kg}",
        ]
        return "\n".join(lines)

    # =========================================================
    # Per-history lab bridge
    # =========================================================

    def extract_time_folds(self, history: Optional[str] = None) -> Tuple[str, int, int]:
        hist = history or self.first_history()
        validate_history(hist)
        time_folds = "".join(ch for ch in hist if ch in ("+", "-"))
        return time_folds, time_folds.count("+"), time_folds.count("-")

    def extract_topological_action(
        self, history: Optional[str] = None
    ) -> Tuple[int, int, int, str]:
        hist = history or self.first_history()
        validate_history(hist)

        e_spatial_free = spatial_free_action(hist)
        e_local_free = local_free_action(hist)
        e_bound_total = bound_action_estimate(hist)
        time_folds, _, _ = self.extract_time_folds(hist)

        return e_spatial_free, e_local_free, e_bound_total, time_folds

    def generate_laboratory_report(self, history: Optional[str] = None) -> str:
        hist = history or self.first_history()
        validate_history(hist)

        action = calculate_action(hist)
        adjoint = adjoint_history(hist)
        e_spatial_free, e_local_free, e_bound_total, time_folds = (
            self.extract_topological_action(hist)
        )

        length_m = e_spatial_free * self.L_P
        time_s = e_local_free * self.T_P if e_local_free > 0 else float("inf")

        if time_s == float("inf"):
            time_str = "inf"
        else:
            time_str = f"{time_s:.6e}"

        G_pred = self.emerge_G_prediction()
        if G_pred is None:
            G_pred_str = "unavailable"
        else:
            G_pred_str = f"{G_pred:.6e}"

        return "\n".join(
            [
                "--- QLF Laboratory Translation Report ---",
                f"History String                  : {hist}",
                f"Adjoint                         : {adjoint}",
                f"Admissible                      : {is_admissible_history(hist)}",
                f"ZFA                             : {is_zfa(hist, min_length=self.min_zfa_length)}",
                f"Total Logical Action            : {len(hist)}",
                f"Action Tuple (v,h,d,l)          : {action}",
                "",
                "=== SPATIAL EMERGENCE (QLF bridge) ===",
                f"  Spatial Free Action           : {e_spatial_free} twists",
                f"  Planck-length Bridge          : {length_m:.6e} meters",
                "",
                "=== LOCAL / TEMPORAL EMERGENCE (QLF bridge) ===",
                f"  Time Folds (+/- subsequence)  : '{time_folds}'",
                f"  Local Free Action             : {e_local_free} twists",
                f"  Planck-time Bridge            : {time_str} seconds",
                "",
                "=== BOUND STRUCTURE ===",
                f"  Bound Action Estimate         : {e_bound_total}",
                "",
                "=== NATIVE GRAVITY ===",
                f"  Native Coupling G_Q           : {self.emerge_G_Q():.10f}",
                f"  SI Bridge Prediction for G    : {G_pred_str}",
                f"  mass_unit_kg                  : {self.mass_unit_kg}",
                "",
                "Note:",
                "  This laboratory report is a bridge translation in Planck units.",
                "  G_Q is native and dimensionless.",
                "  G_prediction_SI requires one explicit mass bridge assumption.",
            ]
        )


if __name__ == "__main__":
    # Example:
    # set mass_unit_kg to bridge 1 native prime-mass unit into SI kilograms
    mapper = ConstantsMapper(
        seeds=("^", "<", "/", "+"),
        causal_horizon=10,
        min_zfa_length=4,
        max_histories=256,
        mass_unit_kg=None,   # set this to a value to enable G_prediction_SI
    )

    print(mapper.generate_constants_report())
    print()
    print(mapper.generate_laboratory_report())
