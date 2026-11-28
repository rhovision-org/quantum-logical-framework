import QLF_BoostAmplitudes

/-!
# The half-step slice's parameter-reversal identity

Part of the [Quantum Logical Framework (QLF)](../README.md). Stages 4a and 4b
([`Relativity_Principle.md`](../Relativity_Principle.md) §6b) measured, on a finite grid, that the
band projector and the tree vertex proxy built from the half-step slice
`massStep(m/2) · handed(k) · massStep(m/2)` follow the continuum to `O(κ²)`, and those built from the
raw slice only to `O(κ)`. This module proves an exact algebraic identity consistent with that.

* **`handed_neg`**: the handed step at `−k` is the adjoint of the step at `k`.
* **`massStep_neg`**: the mass step at `−m` is the adjoint of the step at `m`.
* **`halfWalk_reversal`**: so the half-step slice at `(−k, −m)` is the adjoint, that is the
  inverse, of the slice at `(k, m)`. Reversing every momentum and the mass together undoes the step.

This is a simultaneous reversal of the parameters `p = (k, m)`, not the antiunitary time reversal
of a fixed-mass Dirac particle.

A structural explanation, not proved here. With the walk's conventions (`diracWalk_generator`,
`massStep m = cos m + i sin m β`, positive eigenphases for the positive band) the generator is
`H(p) = −i Log U(p)`, so `U = exp(i H)`. On the principal branch near the identity,
`halfWalk_reversal` makes `H` odd in `p`, so it has no second-order term, and its first-order term is
the Dirac operator: `H(p) = H_Dirac(p) + O(κ³)`. The raw slice is not reversed this way: its adjoint
is `handed(−k) · massStep(−m)`, the factors in the opposite order. The raw and half-step slices are
unitarily conjugate and have the same dispersion (`halfWalk_dispersion`), so the different measured
orders concern the band-projector comparison and the vertex proxy, not the eigenvalues. Turning the
explanation into the `O(κ²)` bounds needs a matrix logarithm with a cubic Taylor remainder, a
spectral gap that does not close under scaling for the projector, and control of the vertex proxy's
normalization. None of that is formalized; the audited fact is the identity. No axioms.
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

/-- **The half-step slice under parameter reversal**: at `(−k, −m)` it is the adjoint of the slice
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
