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
