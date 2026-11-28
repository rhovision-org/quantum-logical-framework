import QLF_BoostAmplitudes

/-!
# Why the half-step slice is second order: it is its own time reverse

Part of the [Quantum Logical Framework (QLF)](../README.md). Stages 4a and 4b
([`Relativity_Principle.md`](../Relativity_Principle.md) §6b) measured that the Dirac walk's band,
and the tree amplitudes built from it, follow the continuum to `O(κ²)` on the half-step slice
`massStep(m/2) · handed(k) · massStep(m/2)` and only to `O(κ)` on the raw slice. This module proves
the structural fact behind that.

* **`handed_neg`**: the handed step at `−k` is the adjoint of the step at `k`.
* **`massStep_neg`**: the mass step at `−m` is the adjoint of the step at `m`.
* **`halfWalk_reversal`**: so the half-step slice at `(−k, −m)` is the adjoint, that is the
  inverse, of the slice at `(k, m)`. Reversing every momentum and the mass undoes the step.

What follows, and is not proved here. Write `U(p) = exp(−i H(p))` with `p = (k, m)` and the
eigenphases in `(−π, π)`. `halfWalk_reversal` says `U(−p) = U(p)⁻¹`, so the generator is odd,
`H(−p) = −H(p)`, and its Taylor series has no `κ²` term. Its first-order term is the Dirac
operator (`realWalk_generator` for the kinetic part, the mass step for `β m`), so
`H(p) = H_Dirac(p) + O(κ³)`, and a band built from `H` follows the Dirac band to `O(κ²)`. The raw
slice `massStep(m) · handed(k)` is not its own reverse: its adjoint is `handed(−k) · massStep(−m)`,
the factors in the opposite order. The analytic steps, a matrix logarithm and a Taylor bound on
it, are not formalized. No axioms.
-/

namespace QLF.HalfStepReversal

open Matrix Kronecker
open QLF.ClosureChannels QLF.DiracWalk QLF.BoostStates QLF.BoostAmplitudes
open QLF.Tsirelson (Q)

/-- **The handed step at `−k` is the adjoint of the step at `k`.** -/
theorem handed_neg (ky kx kz : ℝ) :
    handed (-ky) (-kx) (-kz) = (handed ky kx kz)ᴴ := by
  have h1 : (realWalk ky kx kz)ᴴ = realWalk (-ky) (-kx) (-kz) := by
    rw [realWalk_neg]; rfl
  have h2 : (realWalk (-ky) (-kx) (-kz))ᴴ = realWalk ky kx kz := by
    rw [realWalk_neg]; exact star_star _
  rw [handed_eq_chiral, handed_eq_chiral, chiral_conjTranspose, h1, h2, neg_neg, neg_neg, neg_neg]

/-- **The mass step at `−m` is the adjoint of the step at `m`.** -/
theorem massStep_neg (m : ℝ) : Mass.massStep (-m) = (Mass.massStep m)ᴴ := by
  have hb : Mass.betaᴴ = Mass.beta := Mass.beta_herm
  have hc : star (Complex.I * ((Real.sin m : ℝ) : ℂ)) = Complex.I * ((-Real.sin m : ℝ) : ℂ) := by
    rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  have hr : star ((Real.cos m : ℝ) : ℂ) = ((Real.cos m : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [Mass.massStep, Mass.massStep, Mass.coin, Mass.coin, conjTranspose_add, conjTranspose_smul,
    conjTranspose_smul, conjTranspose_one, hb, Real.cos_neg, Real.sin_neg, hc, hr]

/-- **The half-step slice is its own time reverse**: at `(−k, −m)` it is the adjoint of the slice
    at `(k, m)`, and so, being unitary, its inverse. -/
theorem halfWalk_reversal (ky kx kz m : ℝ) :
    halfWalk (-ky) (-kx) (-kz) (-m) = (halfWalk ky kx kz m)ᴴ := by
  rw [halfWalk, halfWalk, conjTranspose_mul, conjTranspose_mul, handed_neg, neg_div,
    massStep_neg, mul_assoc]

/-- The inverse form: stepping at `(k, m)` and then at `(−k, −m)` does nothing. -/
theorem halfWalk_reversal_inv (ky kx kz m : ℝ) :
    halfWalk (-ky) (-kx) (-kz) (-m) * halfWalk ky kx kz m = 1 := by
  rw [halfWalk_reversal]
  have hU := halfWalk_unitary ky kx kz m
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  exact hU

end QLF.HalfStepReversal
