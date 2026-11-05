# Curve covers and closure covers: the G3 benchmark

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

This page is target **G3** of [issue #207](https://github.com/rhovision-org/quantum-logical-framework/issues/207):
compare the curve covers of Carrôlo and Figueiredo, *How gluon leading singularities discover curves on
surfaces* ([arXiv:2512.17019](https://arxiv.org/abs/2512.17019), JHEP 07 (2026) 101), with QLF closure covers
on small graphs. Script: [`curve_cover_census.py`](curve_cover_census.py).

**§1–§4 are the pre-registration.** They were committed (`b35fe62`) before the curve side was run on any graph
beyond the published 3-point example. The results are in §5, added afterwards: **all four predictions
passed on all 63 graphs**, and §5 says why that confirms a dictionary rather than a derivation.

---

## 1. The curve side, as the paper defines it

The scaffolded `n`-gluon amplitude lives on the `2n`-gon. Its triangulation `T` holds the `n` scaffolding
chords `(2j−1, 2j+1)` and a triangulation of the inner `n`-gon on the odd vertices, so `|T| = 2n − 3`. The
fatgraph is the dual tree. Its edges are the chords of `T`.

The tree leading singularity is (paper eqs. 12–13) the coefficient of `∏_{P∈T} y_P` in

```text
∏_C ( 1 − X_C · y^{core(C)} · (1 − E_a(C)) · (1 − E_b(C)) ),     E = y_{p1} + y_{p1}y_{p2} + … ,
```

where `C = (a, b)` runs over chords not in `T`, `core(C)` is the set of chords of `T` that `C` crosses, and
`E_a`, `E_b` run over the extra chords the laminated curve crosses at each end (its *extensions*), ordered
from the core outward. One term of the expansion that covers every chord exactly once is a
**configuration**. Its sign is `(−1)^{#curves} · (−1)^{#extended ends}`. The lowest degree in `X` is the pure
Yang–Mills part; higher degrees are the `F³` insertions.

`curve_cover_census.py --check3` expands this for 3 points and reproduces paper eq. (16) term for term:

```text
LS₃ = X14 X26 + X24 X36 + X25 X46 − X14 X25 − X14 X36 − X25 X36      (degree 2, YM)
    − X14 X25 X36                                                    (degree 3, F³)
```

That is 7 configurations, one per monomial, covering the 4 ways to split the 3-edge star into paths.

## 2. The QLF side: strands and handedness

A **strand** is a path of fatgraph edges. At each interior vertex it turns left or right, and
[`QLF_Handedness`](lean/QLF_Handedness.lean) takes handedness as the primitive. A **strand cover** is a
partition of the edges into strands. The candidate closure covers:

| | Closure cover | Count at `n = 3` | Published value | Status |
|---|---|---|---|---|
| Q0 | strand covers, unlabelled | 4 | 7 | **rejected** before the blind run |
| Q1 | strands with zero net handedness (`#L = #R`) | 1 | 7 | **rejected** before the blind run |
| Q2 | strand covers, each strand a ket or a bra (`2^{#strands}`) | 20 | 7 | **rejected** before the blind run |
| Q3 | strands read by the handedness rule below | 7 | 7 | **under test** |

Q0–Q2 were the first things tried, and the published 3-point example kills them. They are recorded so that
the look-elsewhere count is honest: four candidates, one survived to the blind test.

**Q3, the handedness rule.** A strand with turn word `w` (length `m − 1` for `m` edges) is read as a core
plus up to two extended ends. An extended end is **one turn of the opposite hand at the core junction,
followed by a run of constant hand** to the strand's end:

```text
w = R^{ka−1} L · (core turns) · R L^{kb−1}       (ka, kb = extension lengths, 0 = not extended)
```

The core sub-path is the core of exactly one curve: join the far vertices of its two end triangles. The
configuration sign is `(−1)^{#strands + #extended ends}`, and a curve may be used once per configuration.
`handedness_polynomial` builds the whole leading-singularity polynomial this way, from strand covers and
turn words, without consulting eq. (13).

Where Q3 comes from: the paper's extension rule is "turn right once, then left continuously" from each end
of the core (§2.1). Read in one fixed direction along the strand, the far end's extension is `R L…L`; the
near end's, read inward, is the mirror `R…R L`. So Q3 is the paper's rule rewritten in turn words, with
the curve recovered from the core alone. **A pass tests the dictionary, not physics.** It would show that
the curve covers are handedness-local strand covers, which is G3b (the bijection), not that closure
*dynamics* produces them.

Q3 is chirality-symmetric: the mirror convention (`L ↔ R`) gives the identical polynomial on every graph
computed (`n ≤ 7`), so no convention choice is hidden in it.

## 3. Predictions

Scope: every scaffolded tree fatgraph for `n = 4, 5, 6, 7` — 2, 5, 14 and 42 graphs, **63 in all**. The
curve side is computed from eq. (13) by `curve_configurations`; the QLF side from turn words by
`handedness_polynomial`. Both are exact integer computations.

| | Prediction | Kill condition |
|---|---|---|
| **H1** (G3 and G3b) | On all 63 graphs the eq. (13) polynomial equals the Q3 polynomial, coefficient by coefficient. | Any graph with any differing coefficient. |
| **H2** | Configuration counts are 44 (`n=4`), 274 (`n=5`), one of {1687, 1700, 1708, 1712} (`n=6`), one of {10474, 10502, 10540, 10596, 10624, 10676} (`n=7`), graph by graph as Q3 gives them. | Any count differs. (Implied by H1.) |
| **H3** | Every strand cover is realized by at least one configuration, so the realized covers number `4^{n−2}`. | A strand cover with no configuration. |
| **H4** | The paper's 4-point claims hold in the `s` channel: `X14 X16 X58` cancels and `X14 X16 X25` never appears (§3, §6 of the paper). | Either fails; this would be a bug in the curve-side code. |

What the QLF side already says, on its own numbers, and which the blind run will confirm or not:

* **Cancellation is not always pairwise.** Q3 gives coefficients of magnitude 2 from `n = 4` and 4 from
  `n = 6`. So "every cancellation is an equal-and-opposite pair, leaving 0 or ±1" — the obvious ZFA
  reading of the paper's V-rule — is **predicted false** by our own candidate. If H1 passes, it is false.
* **Not every multi-edge strand cancels.** The signed sum of a strand's own readings is 0 except for
  words `R^p L^q` (`p, q ≥ 1`), where it is −1: the one shape whose two ends both admit an extension that
  does not fit together. So setting every `X = 1` does not leave only the all-single-edge cover.

## 4. What is not tested here

* **Loops.** The one-loop `n`-gon coefficient `(2 − D)·∏X` and the closed-curve exponents need curves on a
  punctured disk. The possible hook — `D = 4` counts the four twist axes, so `D − 2` would be the axes
  transverse to propagation — stays untested, and would be bookkeeping unless it changes a count. That is
  G4b.
* **Kinematics.** Nothing here derives an `X_C` from closures. The comparison is of the combinatorics only.
* **Dynamics.** Q3 reads handedness off a given fatgraph. Deriving the extension rule from first closure
  would be the step that gives the dictionary physical content.

---

## 5. Results (blind run, after commit `b35fe62`)

`python3 curve_cover_census.py --compare 7` (about 15 s). Every pre-registered prediction passed.

| | Result |
|---|---|
| **H1** | **Pass, 63/63.** The eq. (13) polynomial equals the handedness polynomial coefficient by coefficient on every tree fatgraph for `n = 4…7` (and on the calibration graph at `n = 3`). |
| **H2** | **Pass, 63/63.** Configuration counts 44, 274, 1687–1712, 10474–10676, graph by graph as predicted. Since the map from a configuration to its strand cover and per-strand reading is injective, equal counts make it a **bijection**: curve covers are handedness strand covers. |
| **H3** | **Pass, 63/63.** Every one of the `4^{n−2}` strand covers is realized. |
| **H4** | **Pass.** In the `s` channel `X14 X16 X58` is generated twice and cancels; `X14 X16 X25` is never generated. |

Inventory, all 63 graphs:

| `n` | graphs | configurations | YM monomials | `|coef|` values | `LS(X ≡ 1)` |
|---|---|---|---|---|---|
| 3 | 1 | 7 | 6 | 1 | −1 |
| 4 | 2 | 44 | 27 | 1, 2 | 0 |
| 5 | 5 | 274 | 121 | 1, 2 | 0 |
| 6 | 14 | 1687–1712 | 528 or 544 | 1, 2, 4 | 0 (12 graphs), −1 (2) |
| 7 | 42 | 10474–10676 | 2381 or 2445 | 1, 2, 4 | 0 |

The top degree (`2n − 3`, the pure `Tr F³` leading singularity) is one monomial with coefficient `−1` on
every graph: one single-edge core per edge and no extension, as the paper states (§3.4).

**What this establishes.** Carrôlo and Figueiredo's covering problem is a handedness problem. A leading
singularity configuration is a partition of the fatgraph into strands, each read as a core plus extended
ends, where an extended end is one turn of the opposite hand followed by a constant-hand run, and the
curve is fixed by the core alone. That is G3 (counts match) and the finite form of G3b (an explicit
bijection), checked exhaustively on all tree fatgraphs through seven gluons.

**What it does not establish.** Q3 was built by rewriting the paper's own extension rule in turn words
(§2), so the pass confirms the rewriting, not any QLF dynamics. By rule 4 of
[`ScientificApproach.md`](ScientificApproach.md), it changes no count of ways that the paper did not
already fix. Its value is the vocabulary: the extension, the ingredient that produces every cancellation,
is a *partial circulation* of one face at constant hand, and the closed curve at one loop is the full
circulation. That is where a closure derivation would have to start.

**Two further observations, not pre-registered** (found after the blind run, labelled as such):

1. **Pure Yang–Mills coefficients are all ±1 through `n = 7`.** Every coefficient of magnitude 2 or 4 sits
   in a degree above the YM part, i.e. it needs at least one `F³` insertion. So the reading "every
   cancellation is an equal-and-opposite pair, leaving 0 or ±1" fails for the full polynomial, as §3
   predicted, but holds on the pure-gluon part at every graph computed. Whether it holds for all `n` is open.
2. **`LS(X ≡ 1) = 0` on all but three graphs** (the 3-point graph, and two of the fourteen 6-point
   graphs, where it is −1). No mechanism for this is offered here.

## 6. Next steps

* **Prove H1 for all trees.** The rewriting argument in §2 is short; a Lean statement would need the
  fatgraph, the lamination and the turn word as finite data. Worth doing only if the vocabulary is used.
* **Derive the extension rule.** The step with physical content: obtain "one opposite turn, then constant
  hand" from first closure on the fatgraph, rather than reading it off the paper.
* **One loop (G4b).** Extend the enumerator to the punctured disk and test the closed-curve exponent
  `1 − D` against a pre-registered reading of `D` as the four twist axes.
