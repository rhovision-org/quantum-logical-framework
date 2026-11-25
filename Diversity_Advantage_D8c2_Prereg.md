# D8c2 under D3T: matched diversity test on continuation profiles (pre-registration)

Part of [Quantum Logical Framework (QLF)](README.md). Issue
[#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290), after the D3T gate census
([PR #299](https://github.com/rhovision-org/quantum-logical-framework/pull/299),
[`Diversity_Obligation_D3T.md`](https://github.com/rhovision-org/quantum-logical-framework/blob/2b8a047e67f91deb99da49fd6adfb8dd26951d30/Diversity_Obligation_D3T.md)).

**Status:** pre-registration. No D8c2 census code exists and no D8c2 count has been computed when
this file is committed. The census runs in a later commit, after #299 merges, and reports against
this file unchanged.

---

## 1. Why the phase leaves scope (by theorem)

D3T.6 failed: the per-stream boundary record `B(h)` does not determine the closure phase. Jim chose
on 2026-11-22 to settle the phase by theorem rather than by a second census.
[`QLF_DiversityPhase`](lean/QLF_DiversityPhase.lean) (no axioms) proves:

- `twistMatrixFold_append`: the ordered Pauli fold is multiplicative, `fold(a ++ b) = fold(a)·fold(b)`;
- `prefix_fold_determines_phase`: bases with the same **whole-prefix** fold give the same joint phase
  with every extension;
- `stream_folds_miss_interleaving`: the same two streams `^v` and `<>` scheduled `AABB` fold to `+I`
  and scheduled `ABAB` fold to `−I`. The per-stream record discards the interleaving, and the fold
  depends on it. That is exactly the D3T.6 failure.

So a record that keeps the whole-prefix fold determines the phase, and a census retest of that
repair would only confirm the theorem. The phase is **out of scope** for D8c2. D8c2 asks only about
continuation profiles, which D3T.5 found to be determined by `B(a)`.

## 2. What D3T's Pauli clauses actually constrain (by theorem)

`axis_match_of_countBalanced_append` proves that streams with complementary net action have equal
Pauli axes. So D3T's per-stream axis-match clause removes nothing that the net-match clause admits.
With the keystone `count_balanced_pauli_closed`, the closure test `is_zfa(word(a) ++ word(b))` is
also implied by the per-stream net match (the joint word is count-balanced).

Consequence for the design: the **"net-zero, no fold" null model** of
[`Diversity_Interface_D3.md`](Diversity_Interface_D3.md) §4 is **identical to ZFA by theorem** for
these relations. This explains why it matched ZFA exactly on all 37,376 bases in
[#297](https://github.com/rhovision-org/quantum-logical-framework/pull/297) and
[#298](https://github.com/rhovision-org/quantum-logical-framework/pull/298). Running it again would
show nothing, so D8c2 does not use it. The only parts of `R_T` that go beyond per-stream net
bookkeeping are **provenance** (the no-pooling bijection) and the **typed first-closure** condition.
D8c2's two nulls remove each of these in turn (§5).

---

## 3. Frozen relation and panels

The relation is D3T's `R_T` exactly as implemented by `typed_join` in
[`diversity_obligation.py`](https://github.com/rhovision-org/quantum-logical-framework/blob/2b8a047e67f91deb99da49fd6adfb8dd26951d30/diversity_obligation.py) at #299's head (relation code unchanged since
`cdca65e`). The panels are D3T's: two origins; panel A has open base length 3 and extension bound 3;
panel B has open base length 4 and extension bound 2. Enumeration is exhaustive, with no sampling.

The **continuation profile** `C_T(a)` is as in D3T §4: the set of boundary records `B(b)` over
admitted extensions `b`. The **primary measure** is `K(a) = |C_T(a)|`, the number of distinct
continuation boundary records.

## 4. Populations (fixed before any count)

For a base `a` with origins `A`, `B`, let `supp(o)` be the set of axes on which `net(proj(a, o))` is
nonzero.

- **Eligible base:** both streams carry an obligation, `supp(A) ≠ ∅` and `supp(B) ≠ ∅`.
- **Homogeneous:** `supp(A) = supp(B)`. Both streams owe action on the same axes.
- **Heterogeneous (diverse):** `supp(A) ∩ supp(B) = ∅`. The streams owe action on disjoint axes,
  so they are complementary types.
- **Partial overlap:** neither of the above. Reported, but not part of the primary comparison.

**Matching stratum:** (panel, the unordered pair `{|net(A)|₁, |net(B)|₁}`). Comparisons are made
only within a stratum, so the two groups have the same base length, extension bound, origin count
and per-stream obligation size. A stratum is **eligible** if it has at least one homogeneous and at
least one heterogeneous base.

Diversity is defined from the base's obligation support. The measure counts extension boundary
records. Neither is defined from the other.

## 5. Endpoints and nulls

For each eligible stratum `s`, let `Δ_s = mean_het K − mean_hom K`. The weight is
`w_s = min(n_het, n_hom)`, and the weighted difference is `Δ = Σ w_s Δ_s / Σ w_s`.

Two null relations are computed on the same bases, strata and measure:

- **N1, no provenance (pooled):** D3T's aggregate control (`aggregate_join`), which admits an
  extension whenever the pooled net is complementary. If N1 shows the same sign and every stratum
  sign agrees, provenance does no work in the advantage.
- **N2, no first closure:** `obligations_match` plus `is_zfa` of the joint word, without the
  typed first-closure condition. If N2 shows the same sign and every stratum sign agrees, the
  advantage comes from per-stream net combinatorics, which §2 shows is not specific to ZFA.

## 6. Decision rule (fixed now)

| outcome | condition |
|---|---|
| **PASS (D8c2)** | at least two eligible strata across the panels; `Δ > 0`; no eligible stratum with `Δ_s < 0`; **and** at least one of N1, N2 differs from `R_T` in the sign of `Δ` or of some `Δ_s` |
| **PASS, NOT ZFA-SPECIFIC** | the first three conditions hold, but N1 and N2 both reproduce every sign |
| **FAIL** | `Δ ≤ 0` |
| **MIXED** | `Δ > 0` but some eligible stratum has `Δ_s < 0` |
| **INCONCLUSIVE** | fewer than two eligible strata |

All strata are reported, including those that are not eligible and the partial-overlap group. No
stratum, panel, measure or population is added or removed after the run. In line with
[`ScientificApproach.md`](ScientificApproach.md), a FAIL or MIXED result at these lengths records
the test as run at this depth and does not settle behaviour at physical depth.

**What a PASS would be false for.** A PASS is a claim about the distribution of `K` across the two
populations. It fails for any relation under which the number of distinct ways to answer
complementary obligations is the same as, or smaller than, the number of ways to answer the same
obligation twice. #297's conjugate-boundary relation was such a relation (heterogeneous was lower).
So the test can fail, and has failed before on a neighbouring relation.

## 7. Not claimed

No phase claim (§1). No D9 persistence, D10, Penrose, golden-ratio or physical claim. No
extrapolation beyond the two panels. A PASS is a finite structural result about one frozen relation,
not "nature favours diversity".
