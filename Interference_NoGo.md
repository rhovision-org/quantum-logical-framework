# What an interfering event weight must be

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Status: pre-registered.** The statements below were committed before any proof of them was written.
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

*To be filled in after the proofs land.*
