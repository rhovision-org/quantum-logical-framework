import QLF_PlaquetteArea
-- Narrow imports, as in QLF_PlaquetteArea: this module stays off `import Mathlib`.

/-!
# QLF_PhaseAction — the closure phase in action form

Issue #303 S4 asks for a map from the discrete phase to a continuum action difference,
`θ(h) ≡ S[Φ(h)]/ħ (mod 2π)`, derived from the phase data rather than assigned. The test is
pre-registered in [`Stationary_Action.md`](../Stationary_Action.md) §5b and run by
[`signed_phase_track.py`](../signed_phase_track.py).

The phase data already fix the form. [`QLF_PlaquetteArea`](QLF_PlaquetteArea.lean) proves that a
balanced history folds to `(−1)^{#neg} · (−1)^{A_XY + A_XZ + A_YZ}`. This module adds the one fact
that turns that into an action form: count balance makes `#neg` half the length.

* **`two_negCount_of_balanced`.** In a count-balanced history, `2 · #neg = L`.
* **`phase_action_form`.** So the phase of a closure of length `L` is
  `(−1)^{L/2} · (−1)^{Φ}` with `Φ = A_XY + A_XZ + A_YZ`. Read as an angle,
  `θ = π·(L/2) + π·Φ` mod `2π`: a fixed phase per step pair and flux `π` through every spatial
  plaquette.
* **`fold_action_form`.** The Pauli fold itself, in the same form.

## R6a

This is a repackaging of `fold_eq_projected_phase`, not new content. Its use is to state the S4
candidate exactly. The run in §5b shows what the candidate does not settle. The stationary-phase
bound holds for every U(1) flux, so the bound cannot identify it (K5). The fold fixes the flux only
as the ℤ₂ class `±π` (K6). Flux `π` per plaquette has no smooth limit at fixed `ħ` (K7).

No axioms.
-/

namespace QLF.PhaseAction

open QLF QLF.PhaseRule QLF.EdgeSign QLF.PlaquetteArea

/-- The total shadow area of a history: the sum of its three projected spatial areas. -/
def shadowSum (ts : List Twist) : ℤ :=
  projArea Axis.X Axis.Y ts + projArea Axis.X Axis.Z ts + projArea Axis.Y Axis.Z ts

theorem negCount_eq_counts (ts : List Twist) :
    negCount ts = ts.count Twist.down + ts.count Twist.left +
      ts.count Twist.backslash + ts.count Twist.minus := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [negCount] at ih ⊢
      simp only [List.countP_cons, List.count_cons, ih]
      cases t <;> simp +decide <;> omega

theorem length_eq_counts (ts : List Twist) :
    ts.length = ts.count Twist.up + ts.count Twist.down + ts.count Twist.left +
      ts.count Twist.right + ts.count Twist.slash + ts.count Twist.backslash +
      ts.count Twist.plus + ts.count Twist.minus := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.length_cons, List.count_cons, ih]
      cases t <;> simp +decide <;> omega

/-- **Count balance makes `#neg` half the length.** -/
theorem two_negCount_of_balanced {ts : List Twist} (h : countBalanced ts) :
    2 * negCount ts = ts.length := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [negCount_eq_counts, length_eq_counts]
  omega

/-- **The phase in action form.** A closure of length `L` has phase `(−1)^{L/2} · (−1)^{Φ}`:
    `θ = π·(L/2) + π·Φ` mod `2π`, with `Φ` the total shadow area. -/
theorem phase_action_form {ts : List Twist} (h : countBalanced ts) :
    connectionPhase ts = (-1 : ℤ) ^ (ts.length / 2) * sgn ((shadowSum ts : ℤ) : ZMod 2) := by
  have hn : negCount ts = ts.length / 2 := by
    have := two_negCount_of_balanced h
    omega
  rw [connectionPhase_eq_projected, hn]
  rfl

/-- **The fold in action form.** -/
theorem fold_action_form {ts : List Twist} (h : countBalanced ts) :
    twistMatrixFold ts
      = ((((-1 : ℤ) ^ (ts.length / 2) * sgn ((shadowSum ts : ℤ) : ZMod 2) : ℤ)) : ℂ) • (1 : M) := by
  rw [fold_eq_connectionPhase h, phase_action_form h]

end QLF.PhaseAction
