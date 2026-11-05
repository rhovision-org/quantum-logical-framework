# Hidden zeros from closure decompositions: the G2c test

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

This is target **G2c** of [issue #207](https://github.com/rhovision-org/quantum-logical-framework/issues/207):
reproduce a hidden zero of Arkani-Hamed, Cao, Dong, Figueiredo and He
([arXiv:2312.16282](https://arxiv.org/abs/2312.16282)) without imposing it. That is the issue's kill condition
2. The four- and five-point zeros are stated exactly in [`QLF_HiddenZeros`](lean/QLF_HiddenZeros.lean).
Script: [`hidden_zero_closures.py`](hidden_zero_closures.py).

**§1–§3 are the pre-registration**, committed before any amplitude was evaluated.

## 1. The construction

An `n`-point process is one closed history of `n` steps: momentum conservation is ZFA count balance. A
contiguous sub-history `i … j−1` is a **sub-closure** candidate, labelled by the chord `(i, j)` of the
`n`-gon, and its kinematic variable is `X_{ij}`.

* **Compatibility.** Two sub-closures can belong to one decomposition only if they nest or are disjoint.
  Crossing sub-histories share steps without either containing the other, so they cannot both close in one
  decomposition into nested closures. A *complete closure decomposition* is a maximal compatible family:
  a triangulation of the `n`-gon, `n − 3` sub-closures.
* **Propagation.** Each sub-closure contributes the resolvent of the renewal `G = 1 + K G` with deficit
  `1 − K = X`, i.e. `1/X`. **This step is inserted, not derived:** QLF does not yet produce `X_{ij}` from
  closures. What is tested is everything else.
* **Weight.** How many times a complete decomposition is counted. Three readings:

| | Weight of a decomposition | QLF reading |
|---|---|---|
| **W0** | 1 | each decomposition is one event (what closes is what happens; "reached first") |
| **W1** | the number of orders in which its sub-closures can close, inner before outer, averaged over the `n` choices of base step | the event's multiplicity over closure orderings |
| **W2** | `∏ C(2L, L)` over its sub-closures, `L` = particles on the shorter side | the event's multiplicity over 1-D closure ways, each particle a Hermitian pair |

`A_n^W = Σ_T W(T) ∏_{(i,j) ∈ T} 1/X_{ij}`. W0 is the `Tr(φ³)` amplitude.

## 2. The zeros

Mesh variables `c_{ab} = X_{ab} + X_{a+1,b+1} − X_{a,b+1} − X_{a+1,b}`, with `X = 0` on the sides of the
`n`-gon. The hidden zero labelled by the chord `(i, j)` is the locus `c_{ab} = 0` for all
`a ∈ [i, j−2]` and `b ∈ [j, i−2]` (cyclic). At five points the chord `(1, 3)` gives `c₁₃ = c₁₄ = 0`,
`QLF_HiddenZeros.A5_zero`. The test: exact rational arithmetic, `n = 4 … 7`, every zero chord, 20
random points on each locus.

## 3. Predictions

| | Prediction | Kill condition |
|---|---|---|
| **Z0** | `A^{W0}` vanishes on every zero locus. This is the known theorem, so it checks the code; it also says that sum over compatible closure decompositions, one event each, produces the zero without its being imposed. | Any nonzero value. |
| **Z1** | `A^{W1}` vanishes on every zero locus. | Any nonzero value. |
| **Z2** | `A^{W2}` vanishes on every zero locus. | Any nonzero value. |

Prior, stated before running: Z1 and Z2 are expected to **fail** from `n = 5` or 6 on, because a zero is a
cancellation between decompositions and any weight that is not constant across them should spoil it.
If so, the zeros select the "one decomposition, one event" reading over the "count every way" reading,
which bears on the priority-versus-multiplicity distinction in
[`MostWays_First.md`](MostWays_First.md). Note that at `n = 4` all three weights are equal (both channels
have one sub-closure of length 2 on its shorter side), so `n = 4` cannot discriminate.

None of this can be physics beyond the Standard Model: W0 is the standard amplitude.

## 4. Results (after commit `3f37672`)

`python3 hidden_zero_closures.py --max-n 7 --points 20` (under a second; seed 207).

| `n` | decompositions | distinct weights W0 / W1 / W2 | points tested | nonzero `A` for W0 / W1 / W2 |
|---|---|---|---|---|
| 4 | 2 | 1 / 1 / 1 | 40 | 0 / 0 / 0 |
| 5 | 5 | 1 / 1 / 1 | 100 | 0 / 0 / 0 |
| 6 | 14 | 1 / 2 / 2 | 180 | 0 / **180** / **180** |
| 7 | 42 | 1 / 2 / 2 | 279 | 0 / **279** / **279** |

(Points where a random draw put some `X` at zero were skipped, which is why `n = 7` has 279, not 280.)

* **Z0: pass.** Summing over complete compatible closure decompositions, one event each, vanishes on
  every hidden-zero locus through seven points. The zero is not imposed anywhere: it comes from the
  compatibility rule (nest or be disjoint) and the sum.
* **Z1, Z2: fail**, at every point once the weights can differ (`n = 6`, 7). At `n = 4, 5` every
  decomposition has the same weight under both, so those rows could not discriminate.

**What this establishes.** Hidden zeros pick a reading. Counting each complete closure decomposition
once (it either happens or it doesn't) gives the zeros; counting its ways — closure orderings, or 1-D
closure multiplicity — destroys them on every locus tested. This matches the repository's existing
distinction between what closes first and what happens most ways
([`MostWays_First.md`](MostWays_First.md)): the amplitude is built from events, and multiplicity is not
a weight inside it.

**What it does not establish.** The propagator `1/X` was inserted (§1), and with unit weights the
construction *is* the `Tr(φ³)` sum over triangulations, so Z0 passing is the known theorem expressed in
closure language. Kill condition 2 is met for the zero itself, which was never inserted; it is not met for
the kinematics. G2c in full needs `X_{ij}` from closures, and that is still the open step. The negative
result (Z1, Z2) is the new information: it rules out the two natural ways of letting closure multiplicity
into the amplitude.

---

## 5. Pre-registration, round 2: kinematics from twists

Committed before the run. Script: [`hidden_zero_kinematics.py`](hidden_zero_kinematics.py).

§4 left `X_{ij}` inserted. This round takes it from closure data instead of choosing it freely.

**Momenta.** Each of the six spatial twists `t = (axis a, sign s)` carries the null momentum
`k(t) = (1, s·e_a)`, twice its realizable projector `(1 + M(t))/2` from
[`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean), read as a Minkowski vector through
[`QLF_Minkowski`](lean/QLF_Minkowski.lean) (`det Form` = interval). Odd steps are kets (incoming,
`η = +1`), even steps are bras (outgoing, `η = −1`): `p_k = η_k k(t_k)`, the scaffold's Hermitian pairing.
Momentum conservation `Σ p_k = 0` is then exactly **ZFA count balance of the history with every bra
conjugated**. `X_{ij} = (p_i + … + p_{j−1})²`. A history is *singular* if some planar `X_{ij}` vanishes; those
are skipped.

**What follows algebraically, before any run.** `p_a · p_b = η_a η_b (1 − s_a s_b δ_{a_a a_b})`, so for
non-adjacent steps `c_{ab} = −2 p_a·p_b` vanishes **exactly when the two twists are identical**. A
hidden-zero locus (all `c_{ab} = 0` on a rectangle of the mesh) is therefore a history in which **one twist
repeats across the whole rectangle**.

| | Prediction | Kill condition |
|---|---|---|
| **K1** | `c_{ab} = −2 p_a·p_b` on every history (code check). | Any mismatch. |
| **K2** | `A^{W0}` vanishes on every non-singular history lying on a hidden-zero locus, i.e. with one twist repeated across a rectangle. | Any nonzero value there. |
| **K3** | **Every** zero of `A^{W0}` on non-singular twist kinematics lies on some hidden-zero locus: the amplitude has no other zeros on the closure lattice. | One zero off every locus. |

Scope: all histories of 6 spatial twists of length `n = 4, 6, 8` satisfying conservation. (`n` must be even,
since kets and bras pair.) K3 is automatic at `n = 4`, where `A₄ = c₁₃/(X₁₃X₂₄)`; it has content from `n = 6`.

## 6. Results, round 2 (after commit `ffacd9f`)

`python3 hidden_zero_kinematics.py --max-n 8` (about 2 s).

| `n` | conserving histories | singular (some `X_{ij} = 0`) | on a hidden-zero locus | of those, non-singular | zeros of `A` |
|---|---|---|---|---|---|
| 4 | 90 | 66 | 6 | 0 | 0 |
| 6 | 1,860 | 1,812 | 96 | 0 | 0 |
| 8 | 44,730 | 44,298 | 246 | 0 | 0 |

* **K1: pass.** `c_{ab} = −2 p_a·p_b` on every history.
* **K2, K3: vacuous.** Every history that lands on a hidden-zero locus is singular: repeating one twist
  across the rectangle also makes some planar sub-sum null, so a propagator vanishes on the same history
  and the amplitude is not defined there. Off the loci the amplitude never vanishes either. Neither
  prediction could fail, so neither is evidence.

**What this settles.** Taking each particle's momentum to be a single twist does not give usable
kinematics: 97–99 % of conserving histories are singular, and the zero loci sit on poles. The six null
directions of one twist are too coarse. This momentum map is recorded as a **rejected route** for deriving
`X_{ij}` from closures. A viable map would give each particle a momentum built from many twists (a long
closed word per particle, with its realizable projection as the momentum), so that generic sub-sums are
not null; that is the next thing to pre-register.

---

## 7. Pre-registration, round 3: momenta from long words

Committed before the run. Script: [`hidden_zero_words.py`](hidden_zero_words.py).

**Momenta.** A particle is a long twist word `w` over the six spatial twists. Its lattice momentum is the
word's net displacement `k(w) = Σ s·e_a ∈ ℤ³` (the walk picture of [`Closure_Walk.md`](Closure_Walk.md)), and
its energy is the on-shell value of the realizable walk, `|k|`: the walk's generator is the Weyl operator
`k·σ` ([`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean), `realWalk_generator`), whose eigenvalues are
`±|k|`. So `p(w) = η·(|k|, k)`, null, with `η = +1` for kets (incoming) and `−1` for bras. A single twist
gives `|k| = 1` and reproduces round 2 exactly. Exact arithmetic needs `|k| ∈ ℤ`; the words used are those
with `|k| ≤ 3` (displacements `(1,0,0)`, `(2,0,0)`, `(3,0,0)`, `(2,2,1)` and their images: 42 directions).

`n = 4`: every conserving quadruple. `n = 6`: every conserving sextuple reachable by choosing four momenta
and splitting the remainder into two null momenta from the same set, capped at 200,000 histories.

| | Prediction | Kill condition |
|---|---|---|
| **K1′** | `c_{ab} = −2 p_a·p_b` (code check). | Any mismatch. |
| **K4** (the route) | Non-singular histories on a hidden-zero locus exist at `n = 4` and `n = 6`. | None at either `n`: the route is rejected like round 2. |
| **K2′** | `A^{W0}` vanishes on every one of them. | Any nonzero value. |
| **K3′** | Every zero of `A^{W0}` on non-singular histories lies on a hidden-zero locus. | One zero off every locus. |

Expected, and stated so it is not mistaken for a finding: for null momenta `p_a·p_b = 0` only when they are
parallel, so the loci are collinear configurations (at four points, forward scattering `p₃ = −p₁`). A pass on
K4 and K2′ means the closure lattice reaches the hidden zeros with finite propagators. It is standard
kinematics on a QLF-generated momentum set, not new physics. K3′ is the part that could surprise: zeros
off the loci would be zeros the continuum theory does not name, special to the lattice.
