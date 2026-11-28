# Does a diverse library of closures assemble more cheaply? (pre-registration)

Part of [Quantum Logical Framework (QLF)](README.md). Issues
[#264](https://github.com/rhovision-org/quantum-logical-framework/issues/264) (assembly index) and
[#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290) (diversity advantage).

**Status:** pre-registration. When this file is committed, no library-census code exists and no
library count has been computed. The census runs in a later commit and reports against this file
unchanged.

---

## 1. The question, and why a lemma cannot answer it

[`QLF_AssemblyIndex`](lean/QLF_AssemblyIndex.lean) defines assembly from a **library** `L` of parts
(`LibPathway`, `libIndex`). Library parts obey the closure rule: a closed part can be reused, and an
open part is used up once. `libIndex_mono` proves that a larger library never costs more. That is
monotonicity, so it holds for every distribution of parts and says nothing about diversity.

The diversity question needs libraries of **equal size**. Compare a library whose parts all act on
one axis with a library of the same size whose parts act on different axes. Which one lowers the
assembly cost of closures more? Either answer is possible before counting:

- Same-axis parts overlap as substrings (`^v^` contains both `^v` and `v^`), so they compete for the
  same positions in a target. That favours the diverse library.
- Same-axis parts compose with each other (`^v` and `v^` build `^vv^` in one join), and one-axis
  runs are common in balanced words. That favours the homogeneous library.

**Prior, stated before counting:** I expect the diverse library to win, mostly because its parts
occur in more targets (coverage). §5 registers a coverage reading so that a coverage-only win is
labelled as one.

## 2. Frozen definitions

Words, closure and the closure-constrained index are those of
[`Assembly_Index_QLF.md`](Assembly_Index_QLF.md) §1 and
[`assembly_index.py`](assembly_index.py) at this commit. Objects are raw words over
`^ v < > / \ + -`, primitives are the eight letters, and a join is concatenation.

- `a_ZFA(w)`: the closure-constrained assembly index (`assembly_index_closed`).
- `a_ZFA(w | L)`: the same index when every part of `L` is available at zero cost from the start.
  All parts used here are closed, so they are reusable. This is `libIndex` of the Lean module.
- **Saving:** `S(w | L) = a_ZFA(w) − a_ZFA(w | L) ≥ 0`.

**Parts.** Every part is a closed word on **one axis** `(t, t̄)`, where `t̄` is the conjugate of `t`.
Each part has a **shape**:

| panel | part length | shapes (each in both orientations, `t ↔ t̄`) |
|---|---|---|
| A | 2 | `D = t t̄` |
| B | 4 | `B = t t t̄ t̄` (block), `A = t t̄ t t̄` (alternating), `N = t t̄ t̄ t` (nested) |

So an axis carries 2 parts in panel A and 6 in panel B.

**Libraries.** A library is a set of `k` distinct parts.

- **Homogeneous:** all `k` parts lie on the same axis.
- **Diverse:** the `k` parts lie on `k` different axes.

Only libraries that are one or the other enter the comparison.

**Strata.** A stratum is `(panel, k, shape multiset, target length n)`. Within a stratum the two
groups have the same number of parts, the same part lengths and the same shapes. They differ only
in how the parts are spread over axes. The registered strata are:

- panel A, `k = 2`, shapes `{D, D}`;
- panel B, `k = 2`, every shape multiset of size 2 (6 strata per `n`);
- panel B, `k = 3`, every shape multiset of size 3 in which no shape occurs more than twice (a
  single axis has only two parts of each shape), which gives 7 strata per `n`;
- target lengths `n ∈ {6, 8}`.

That makes `(1 + 6 + 7) × 2 = 28` strata. Each group's population is **every** library of its kind
in the stratum (all axes, all orientations), with no sampling.

**Targets.** Every count-balanced word of length `n`: 5,120 words at `n = 6`, 190,120 at `n = 8`.

## 3. Primary measure and decision rule

For a stratum and a group `G` (homogeneous or diverse):

$$
\bar S_G = \text{mean over libraries } L \in G \text{ of the mean over targets } w \text{ of } S(w \mid L).
$$

The stratum difference is `Δ_s = S̄_div − S̄_hom`, and its sign is `+`, `0` or `−`. The overall
statistic `Δ` is the **unweighted mean of `Δ_s` over the 28 strata**. All arithmetic is exact
(rationals).

| outcome | rule |
|---|---|
| **FAIL** | `Δ ≤ 0` |
| **MIXED** | `Δ > 0` and some stratum has `Δ_s < 0` |
| **PASS** | `Δ > 0` and no stratum has `Δ_s < 0` |

A PASS is then qualified by the null (§4) and the coverage reading (§5). Neither qualifier can turn
a FAIL or a MIXED into a pass.

## 4. Null: ordinary assembly (no closure rule)

**N1** repeats the whole computation with the ordinary assembly index `a(w)` and `a(w | L)`, where
every built object is reusable whether closed or not. If N1 has `Δ > 0` and the same stratum signs
as the primary, the PASS is labelled **PASS, NOT ZFA-SPECIFIC**: the closure rule would play no part
in the diversity advantage. Otherwise it is **PASS (ZFA)**.

## 5. Coverage reading (a qualifier, registered now)

A part can save joins only in a target that contains it as a substring. For each library, the
**coverage** is the fraction of targets that contain at least one of its parts. The
**per-covered saving** is the mean of `S(w | L)` over covered targets only. `Δ_cov` is built from
it exactly as `Δ` is built from the mean saving.

- If the primary is a PASS and `Δ_cov > 0`, the diverse library also saves more **where it
  applies**, and the advantage is not only coverage.
- If the primary is a PASS and `Δ_cov ≤ 0`, the result is labelled **coverage-only**: diverse parts
  occur in more targets, but they do not help more where they occur.

## 6. Descriptors (reported, not decision inputs)

- **Synergy:** `S(w | L) − Σ_{p ∈ L} S(w | {p})`, averaged as above. It is positive when parts help
  more together than one at a time.
- Coverage itself, for each group and stratum.

## 7. What this can and cannot show

A PASS supports this statement: in these panels, spreading a fixed number of closed parts over
several axes lowers the closure-constrained assembly cost of balanced words more than concentrating
the parts on one axis. The grade is **N** (finite census), for these panels and lengths only. It
would not show that assembly *selects* diverse libraries, and it says nothing about abundance or
copy number ([`Assembly_Index_QLF.md`](Assembly_Index_QLF.md) §2).

A FAIL would mean that, at equal size, axis diversity among closed parts does not lower assembly
cost here, and that `libIndex_mono` (more parts help) is the only library result.

Out of scope: open parts (consumed on use), mixed-axis parts such as `^<v>`, libraries larger than
three parts, and target lengths beyond 8. Each would need its own pre-registration.

The census will be `library_diversity_census.py`, with results in `Library_Diversity_Assembly.md`.
