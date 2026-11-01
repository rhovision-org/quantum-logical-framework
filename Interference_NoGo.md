# What an interfering event weight must be

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Status: §2 proved (§4); §5 proved (§6).** The statements in §2 were committed before any proof of them was written.
The Lean module that is to prove them is [`lean/QLF_InterferenceNoGo.lean`](lean/QLF_InterferenceNoGo.lean).
Results are recorded in §4 after the proofs land, and nothing in §1–§3 is to be edited afterwards
except to mark each item passed or failed.

## 0. Why this, and why now

[`QLF_KraftMeasure`](lean/QLF_KraftMeasure.lean) proves one special case: the normalized-event weight
`B = (Σa)²/(Σw)` is sub-additive (`merge_le_sum`), so it cannot produce constructive interference
(`no_constructive_interference`). The contextual census measured the same thing
([`contextual_census.py`](contextual_census.py) `--two-path`: matched pair `1.000000`, destructive `0`).
[`Born_Rule.md`](Born_Rule.md) §8 records several candidate weights that failed in this way.

The question here is whether those failures share one cause. If they do, the cause should be a theorem
about **every** weight of a given shape, and it should say what object a Born amplitude has to be. That
is a structural result, not a new candidate weight.

## 1. Setting

* A finite set of **ways** `ι`. An **event** is a finite set of ways `E ⊆ ι`.
* An **event weight** is any function `μ : Finset ι → ℝ`.
* The **interference term** of two disjoint events is `I₂(A, B) = μ(A ∪ B) − μ(A) − μ(B)`.
  Constructive interference is `I₂ > 0`, destructive is `I₂ < 0`.
* A **tally readout** is a weight of the form `μ(E) = Φ(T(E))`, where every way carries a tally
  `v(h)` in a real vector space `V`, the tally is additive, `T(E) = Σ_{h∈E} v(h)`, and `Φ : V → ℝ`.
  This covers the additive measures (Φ linear, `V = ℝ`), the KraftMeasure normalized-event weight
  (`v = (a, w)`, `Φ(a, w) = a²/w`), and the Born weight (`v` = an amplitude, `Φ = |·|²`).
* A **matched pair** is two disjoint events with the same tally, `T(A) = T(B)`. Two coherent paths of
  equal amplitude are a matched pair, and quantum mechanics gives them `μ(A ∪ B) = 2(μ(A) + μ(B))`.

## 2. Pre-registered statements

* **N1 (additive measures do not interfere).** If `μ` is additive on disjoint events, then
  `I₂(A, B) = 0` for every disjoint pair. *This is a restatement of additivity, recorded as the base
  case. It is bookkeeping by method rule 4 and carries no evidential weight.*

* **N2 (the matched-pair factor fixes the degree).** If `Φ` is positively homogeneous of degree `k`,
  `Φ(c·x) = cᵏ Φ(x)` for `c > 0`, then every matched pair satisfies `μ(A ∪ B) = 2ᵏ μ(A)` and
  `μ(A ∪ B) = 2^(k−1) (μ(A) + μ(B))`. Corollaries:
  * **N2a.** A degree-1 readout gives a matched pair **no interference at all**, whether or not `Φ` is
    convex.
  * **N2b.** For `k ∈ ℕ`, `k ≥ 1`, and `μ(A) ≠ 0`, the quantum factor `μ(A ∪ B) = 2(μ(A) + μ(B))`
    holds **iff `k = 2`**.
  * **N2c.** The KraftMeasure normalized-event readout `Φ(a, w) = a²/w` (on `w > 0`) is degree-1,
    so N2a applies to it. This must agree with the existing equality case `merge_eq_sum_iff`
    (a matched pair has `a/p = b/q`).

* **N3 (sublinear readouts forbid constructive interference everywhere).** If `Φ` is convex on a
  convex set `C ⊆ V` that is closed under scaling by `2`, and degree-1 homogeneous on `C`, then
  `Φ(x + y) ≤ Φ(x) + Φ(y)` for all `x, y ∈ C`. Hence every disjoint pair whose tallies lie in `C` has
  `I₂(A, B) ≤ 0`. This generalizes `no_constructive_interference` from one weight to the whole class.

* **N4 (complete cancellation needs signed tallies).** If every tally is non-negative
  (`V = ℝⁿ`, coordinatewise order), `Φ(0) = 0`, and `Φ(x) = 0` only at `x = 0`, then no two disjoint
  events with `μ(A) ≠ 0` can cancel completely: `μ(A ∪ B) ≠ 0`. So a census of unsigned counts, read
  out by any such `Φ`, cannot produce a dark fringe.

* **N5 (the squared signed tally does both, and only at second order).** For complex tallies and
  `Φ = |·|²`: `I₂(A, B) = 2 Re(T(A) · conj T(B))`; a matched pair gives the factor `2`; opposite tallies
  `T(B) = −T(A)` cancel completely. And the third-order term
  `I₃(A,B,C) = μ(A∪B∪C) − μ(A∪B) − μ(A∪C) − μ(B∪C) + μ(A) + μ(B) + μ(C)` vanishes identically
  (Sorkin's hierarchy: quantum interference is pairwise).

Reading, if all five hold: **an event weight that interferes both ways cannot be a classical
(degree-1, unsigned) quantity on closures.** The additive object must scale as the square root of the
weight (N2b) and must carry a sign or phase (N4); the weight is its square (N5). That is the statement
"amplitude exists before squaring", made into a theorem about a class of weights rather than a
judgement about candidates.

## 3. Predictions and kill conditions

* **P1.** All of N1–N5 are proved in Lean with **zero axioms** and no change to
  [`lean/axioms.expected`](lean/axioms.expected).
* **P2.** N2c agrees with `merge_eq_sum_iff` with no extra hypothesis. A disagreement would mean one
  of the two modules has its normalisation wrong, and would be a failure to report.
* **P3.** N3 needs no hypothesis beyond those listed. If it needs more (for example `0 ∈ C`, or
  closure under all positive scalings), the extra hypothesis is recorded here as a failure of the
  statement as registered.
* **What this cannot do.** These are theorems about the *shape* of a weight. They do not identify the
  amplitude with any census quantity, and they do not derive the Born rule. The positive construction
  (what object the amplitude is, from the weight's own interference data) is the next step and will be
  pre-registered separately.

## 4. Results

All five statements were proved as registered, in
[`lean/QLF_InterferenceNoGo.lean`](lean/QLF_InterferenceNoGo.lean), on the first CI run (commit
`b9b410a`, run 1050).

| Item | Verdict | Lean |
|---|---|---|
| N1 | **passed** (bookkeeping, as registered) | `additive_no_interference` |
| N2, N2a, N2b | **passed** | `matched_pair_scale`, `matched_pair_factor`, `degree_one_matched_no_interference`, `quantum_factor_iff_degree_two` |
| N2c | **passed** | `kraftΦ_degree_one` (holds for every `w`, not only `w > 0`), `kraft_matched_no_interference` |
| N3 | **passed** | `sublinear_subadditive`, `sublinear_no_constructive_interference` |
| N4 | **passed** | `unsigned_no_dark_fringe` |
| N5 | **passed** | `born_I₂`, `born_degree_two`, `born_matched_factor`, `born_dark_fringe`, `born_I₃` |

* **P1 passed.** No axiom was added; [`scripts/axiom_audit.sh`](scripts/axiom_audit.sh) reports the
  same 13 declared axioms.
* **P2 passed.** `kraft_matched_agrees` reads the matched-pair case straight off `merge_eq_sum_iff`
  with no extra hypothesis, so the two modules agree.
* **P3 passed.** N3 used only the registered hypotheses, and in a weaker form: homogeneity is needed
  only under doubling (`Φ(2x) = 2Φ(x)`), not for every positive scalar.

What this establishes, and what it does not. It is a theorem about the **shape** of an event weight.
A weight read out from a classical additive tally interferes both ways only if the readout has
degree two and the tallies carry a sign or phase. So every candidate in
[`Born_Rule.md`](Born_Rule.md) §8 that was degree one, or summed unsigned counts, could not have
worked, and no reweighting of the same tallies would have helped. It does not say which census
quantity the amplitude is, and it does not derive the Born rule.

## 5. The Born construction (pre-registered)

**Status: pre-registered**, committed after §4 and before any proof of the statements below.

§2 shows what an interfering weight cannot be. This section goes the other way: from the weight's
own interference data to the amplitude. The route is the classical one, Sorkin's hierarchy (Sorkin,
*Mod. Phys. Lett. A* **9**, 3119 (1994), "Quantum mechanics as quantum measure theory"): a weight
whose third-order interference vanishes is fixed by its pairwise interference, and if that pairwise
data is positive it is a Gram matrix, so the weight is the squared length of a summed vector
amplitude. The aim is to prove this on QLF's finite event sets, so that "amplitude" is an output of
the weight rather than a postulate.

Setting as in §1. For a weight `μ` define the **decoherence matrix**
`D(x, x) = μ({x})` and `D(x, y) = (μ({x, y}) − μ({x}) − μ({y}))/2` for `x ≠ y`.

* **B1 (vanishing `I₃` makes the weight quadratic).** If `μ(∅) = 0` and `I₃(A, B, C) = 0` for every
  pairwise-disjoint triple, then `μ(E) = Σ_{x∈E} Σ_{y∈E} D(x, y)` for every event `E`. The step that
  carries it: `I₃ = 0` is exactly the statement that `I₂` is additive in each argument.
* **B2 (positive pairwise data gives vector amplitudes).** If moreover the matrix `D` is positive
  semidefinite, there are vectors `ψ_x` in a finite-dimensional real inner-product space with
  `μ(E) = ‖Σ_{x∈E} ψ_x‖²` for every `E`.
* **B3 (that is the whole class).** Conversely, every weight `μ(E) = ‖Σ_{x∈E} ψ_x‖²` has `μ(∅) = 0`,
  `I₃ = 0` and a positive semidefinite `D`. So the weights with vanishing third-order interference
  and positive pairwise data are **exactly** the vector-amplitude weights. The complex Born weight
  of N5 is the two-dimensional case (`ℂ ≅ ℝ²`).

Predictions and kill conditions:

* **P4.** B1–B3 are proved in Lean with zero axioms. If the Gram factorization in B2 needs a Mathlib
  result that is not on the pinned revision, that is recorded here, not worked around with an axiom.
* **P5.** B1 needs no hypothesis beyond `μ(∅) = 0` and `I₃ = 0`. In particular, no positivity: B1
  must hold for signed `μ`.
* **What this cannot do.** It does not show that nature's weight has `I₃ = 0`. That is an empirical
  input (the three-slit bound of Sinha et al., *Science* **329**, 418 (2010)), and in QLF it is the
  open bridge: a census weight would have to be shown to satisfy it. It does not show that the
  amplitude space is complex rather than real or higher-dimensional; B2 gives vectors, and fixing the
  dimension needs more. And it does not identify `ψ_x` with any census quantity.

## 6. Results of the Born construction

All three statements were proved as registered, in the same module (CI run 1055, commit `3099542`;
the run before it failed on a notation error, `ᴴ` not being in scope, not on any proof).

| Item | Verdict | Lean |
|---|---|---|
| B1 | **passed** | `I₂_union_right` (the step: `I₃ = 0` ⟺ `I₂` additive), `I₂_singleton_eq_sum`, `quadratic_of_third_order_free` |
| B2 | **passed** | `vector_amplitude_of_psd`: amplitudes `ψ_x ∈ ℝ^ι`, `μ(E) = Σ_k (Σ_{x∈E} ψ_x(k))²` |
| B3 | **passed** | `vecWeight_empty`, `vecWeight_third_order_free`, `vecWeight_decoh` (the decoherence matrix is the Gram matrix), `vecWeight_psd`; together `vector_amplitude_iff`; the complex Born weight is the `ℝ²` case, `born_eq_vecWeight` |

* **P4 passed.** No axiom. The Gram factorization came from Mathlib's
  `CStarAlgebra.nonneg_iff_eq_star_mul_self` on the matrix order, so no Mathlib gap had to be recorded.
* **P5 passed.** `quadratic_of_third_order_free` takes only `μ(∅) = 0` and `I₃ = 0`. It holds for
  signed weights.

What this establishes. On any finite set of ways, **a weight has no third-order interference and
positive pairwise data exactly when it is the squared length of a summed vector amplitude**
(`vector_amplitude_iff`). Together with §4: a weight that interferes in both directions cannot be a
classical tally (§4), and a weight that interferes only pairwise and positively *is* an amplitude
square (§6). The amplitude is read off the weight's own interference data, `ψ` from the decoherence
matrix, so it is an output, not a postulate.

What stays open, as registered. Why nature's weight has `I₃ = 0` (an empirical input; in QLF, the bridge
a census weight would have to cross). Why the amplitude space is two-dimensional, which is what makes
it complex. And which census quantity `ψ_x` is.
