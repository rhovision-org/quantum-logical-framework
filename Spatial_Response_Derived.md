# Spatial Response with Both Ledgers Derived (#287, SR3)

Part of the [Quantum Logical Framework (QLF)](README.md). Issue #287 asks whether interactions that
bind contract space: `Δd < 0 ⇒ ΔS < 0`, with `ΔS` and `Δd` defined independently. The first slice
(PR #288) answered no for a toy in which `Δd` came from a separate two-bit automaton, chosen
independently of the twists. This note runs the same gate with **both ledgers derived from the same
twist steps**, so the answer is not fixed by the construction.

## §1 Pre-registration (committed before the companion script was run)

### SR0: definitions

* **Alphabet.** The six spatial twists, read as unit steps `e_t ∈ ℤ³` (`^ v` on `Y`, `< >` on `X`,
  `/ \` on `Z`), as in [`lean/QLF_EdgeSign.lean`](lean/QLF_EdgeSign.lean). The gauge pair is left
  out, since it does not move anything in space.
* **State.** Two bodies, with relative displacement `r = x_A − x_B ∈ ℤ³`. This is the integer
  ledger, which [`Map_Is_Territory.md`](Map_Is_Territory.md) §3b found is the record a return to ZFA
  needs.
* **Event.** `E = (p, q)`: body `A` steps `p` and body `B` steps `q`. There are 36 events.
* **`ΔS(E) = 2 e_p · e_q`.** This is the joint-cost identity of
  [`lean/QLF_MagneticOrientation.lean`](lean/QLF_MagneticOrientation.lean),
  `(A+B)² − (A² + B²) = 2AB`, applied to the two step vectors. Like steps (`p = q`) give `+2`,
  opposite steps (`q = p†`) give `−2`, and orthogonal steps give `0`. It does not depend on `r`.
* **`Δd(E; r) = |r + e_p − e_q|₁ − |r|₁`**, the change in lattice separation. The squared Euclidean
  separation `|r|²` is reported too.

Neither ledger is defined from the other. `ΔS` reads only the pair `(p, q)`, and `Δd` reads `r`.

### Tests

The census is every event at every `r` with `|r|₁ ≤ 4`.

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| R1 | binding contracts: `Δd < 0 ⇒ ΔS < 0` | no event with `Δd < 0` has `ΔS ≥ 0` | **fail**: orthogonal steps (`ΔS = 0`) move `r` diagonally and can bring the bodies closer |
| R2 | contraction binds: `ΔS < 0 ⇒ Δd < 0` | every opposite-step event brings the bodies closer | **fail**: an opposite pair moves `r` by `±2e_p`, toward or away |
| R3 | the mean response | `⟨Δ\|r\|²⟩` over the six `r ↦ −r` symmetric directions equals `2 − ΔS` in each class | pass: the parallelogram law gives `Δ\|r\|² = 2r·(e_p − e_q) + 2 − ΔS` exactly |
| R4 | sign of the mean | opposite steps (`ΔS = −2`) have the largest mean separation growth, `+4`; like steps `0` | pass, from R3 |

**Verdict rule.** If R1 and R2 fail and R3 holds, the orientation ledger does not predict spatial
contraction under the displacement reading. On average, the binding orientation pushes the bodies
apart, and the like orientation holds them fixed. Any contraction would then have to come from
*which* events happen (selection by closure), not from the ledger of each event. That is the next
gate, and it is not run here.

## §2 Results

Run: [`spatial_response_derived.py`](spatial_response_derived.py), exact integers, the 36 events at
all 129 sites with `|r|₁ ≤ 4`. Output: [`data/spatial_response_derived.json`](data/spatial_response_derived.json).
Lean: [`lean/QLF_SpatialResponseDerived.lean`](lean/QLF_SpatialResponseDerived.lean).

| | Outcome | What was found |
|---|---|---|
| R1 | **fail** | 336 events bring the bodies closer with `ΔS = 0`, all of them orthogonal pairs (witness: `orthogonal_brings_closer`) |
| R2 | **fail** | of the 774 opposite-step events, 114 bring the bodies closer, 150 keep the separation and 510 push them apart (witness: `opposite_pushes_apart`). The excess of "farther" is a property of the finite ball, where sites near `r = 0` can only move out. It is not a law |
| R3 | pass | `Δ\|r\|² = 2r·(e_p − e_q) + 2 − ΔS` held at every event and site, and the ball mean equals `2 − ΔS` exactly (`joint_step_identity`, `unit_symmetric_mean`) |
| R4 | pass | mean growth of `\|r\|²`: like `0`, orthogonal `2`, opposite `4`. Like steps never change the separation (774 of 774 "same") |

### Verdict

**Under the displacement reading, the orientation ledger does not predict contraction.** It predicts
the reverse on average. The binding orientation (`ΔS < 0`) is the one that moves the bodies apart
fastest, and the expanding orientation (`ΔS > 0`) holds them at fixed separation. This is the
parallelogram law, not physics. It holds for any steps, so by method rule 4 it is bookkeeping. Its
force is negative: no contraction law can be read off the per-event ledger.

This sharpens the first slice (PR #288). There, the absence of a correlation came from choosing
`Δd` independently. Here both ledgers come from the same steps, and the relation between them is
exact. It is the opposite of the hypothesis.

### What stays open

* **Selection.** Binding could still contract space if the events that *happen* are weighted, for
  example by first closure or by the joint closure of the two bodies, rather than taken uniformly.
  That is the next gate, and the identity above is the baseline it must beat.
* SR4 (aggregation, gravity), SR5 (propagation versus interaction), SR7 (3D relation beyond the
  step ledger) are untouched.
