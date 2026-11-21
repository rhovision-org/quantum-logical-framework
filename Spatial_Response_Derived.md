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

To be filled from `spatial_response_derived.py` after this section is committed.
