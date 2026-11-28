import QLF_HalfStepReversal

/-!
# The walk's π-doubler: a shift of `kz` by `π` negates the step

Part of the [Quantum Logical Framework (QLF)](../README.md), stage 5 of the relativity dependency
chain ([`Relativity_Principle.md`](../Relativity_Principle.md) §6b, "Stage 5 result"). The real walk
takes its `z` step as two adjacent half steps, `realStep slash (kz/2) · realStep slash (kz/2)`.
Shifting `kz` by `π` multiplies each half step's two phases by `i` and `−i`, so the pair picks up
`i² = −1` and nothing else changes.

* **`realStep_sq`**: two equal half steps are `e^{2ik} P + e^{−2ik} P†`, with `P = fix t`.
* **`realWalk_shift_z`**, **`realWalk_shift_z_sub`**: `realWalk ky kx (kz ± π) = −realWalk ky kx kz`.
* **`handed_shift_z`**, **`halfWalk_shift_z`**, **`diracWalk_shift_z`**: so the handed step and both
  slices of the Dirac walk are negated by `kz ↦ kz + π`.
* **`halfWalk_shift_z_eigen`**: an eigenvector of the step at `k` with eigenvalue `λ` is an
  eigenvector at `k + π e_z` with eigenvalue `−λ`: the quasi-energy moves by `π`, and the positive
  and negative bands trade places.

Consequence for stage 5 (computed in [`loop_boost_check.py`](../loop_boost_check.py), not proved
here): a pair of negative-band states at `(p, P − p)` is a pair of positive-band states at
`(p + π e_z, P − p + π e_z)` with total quasi-energy shifted by `2π`, so in the Feynman-ordered loop
`∫ [Λ⁺⊗Λ⁺ R(E − Ω) − Λ⁻⊗Λ⁻ R(E + Ω)]` the two terms are the same integral and cancel. No axioms.
-/

namespace QLF.PiDoubler

open Matrix Kronecker
open QLF.ClosureChannels QLF.DiracWalk QLF.BoostStates
open QLF.Tsirelson (Q)

/-- Two equal half steps: `e^{2ik} P + e^{−2ik} P†`. -/
theorem realStep_sq (t : Twist) (k : ℝ) :
    realStep t k * realStep t k =
      Complex.exp (2 * (k * Complex.I)) • fix t + Complex.exp (-(2 * (k * Complex.I))) • fix t.conj := by
  unfold realStep
  simp only [add_mul, mul_add, smul_mul_smul_comm, fix_idem, fix_mul_conj, fix_conj_mul, smul_zero,
    add_zero, zero_add]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> ring_nf

theorem exp_shift_pos (k : ℝ) :
    Complex.exp (2 * (((k + Real.pi / 2 : ℝ) : ℂ) * Complex.I)) =
      -Complex.exp (2 * ((k : ℂ) * Complex.I)) := by
  push_cast
  rw [show 2 * (((k : ℂ) + Real.pi / 2) * Complex.I) = 2 * ((k : ℂ) * Complex.I) + Real.pi * Complex.I
    by ring, Complex.exp_add, Complex.exp_pi_mul_I]
  ring_nf

theorem exp_shift_pos' (k : ℝ) :
    Complex.exp (-(2 * (((k + Real.pi / 2 : ℝ) : ℂ) * Complex.I))) =
      -Complex.exp (-(2 * ((k : ℂ) * Complex.I))) := by
  rw [Complex.exp_neg, Complex.exp_neg, exp_shift_pos, inv_neg]

theorem exp_shift_neg (k : ℝ) :
    Complex.exp (2 * (((k - Real.pi / 2 : ℝ) : ℂ) * Complex.I)) =
      -Complex.exp (2 * ((k : ℂ) * Complex.I)) := by
  push_cast
  rw [show 2 * (((k : ℂ) - Real.pi / 2) * Complex.I) = 2 * ((k : ℂ) * Complex.I) - Real.pi * Complex.I
    by ring, Complex.exp_sub, Complex.exp_pi_mul_I]
  rw [div_neg, div_one]

theorem exp_shift_neg' (k : ℝ) :
    Complex.exp (-(2 * (((k - Real.pi / 2 : ℝ) : ℂ) * Complex.I))) =
      -Complex.exp (-(2 * ((k : ℂ) * Complex.I))) := by
  rw [Complex.exp_neg, Complex.exp_neg, exp_shift_neg, inv_neg]

theorem realStep_sq_add (t : Twist) (k : ℝ) :
    realStep t (k + Real.pi / 2) * realStep t (k + Real.pi / 2) = -(realStep t k * realStep t k) := by
  rw [realStep_sq, realStep_sq, exp_shift_pos, exp_shift_pos', neg_smul, neg_smul, neg_add]

theorem realStep_sq_sub (t : Twist) (k : ℝ) :
    realStep t (k - Real.pi / 2) * realStep t (k - Real.pi / 2) = -(realStep t k * realStep t k) := by
  rw [realStep_sq, realStep_sq, exp_shift_neg, exp_shift_neg', neg_smul, neg_smul, neg_add]

/-- **Shifting `kz` by `π` negates the real walk.** -/
theorem realWalk_shift_z (ky kx kz : ℝ) : realWalk ky kx (kz + Real.pi) = -realWalk ky kx kz := by
  unfold realWalk
  rw [show (kz + Real.pi) / 2 = kz / 2 + Real.pi / 2 by ring]
  set a := realStep Twist.up (ky / 2)
  set b := realStep Twist.left (kx / 2)
  have key := realStep_sq_add Twist.slash (kz / 2)
  calc a * b * realStep Twist.slash (kz / 2 + Real.pi / 2) * realStep Twist.slash (kz / 2 + Real.pi / 2)
          * b * a
        = a * b * (realStep Twist.slash (kz / 2 + Real.pi / 2) *
            realStep Twist.slash (kz / 2 + Real.pi / 2)) * b * a := by simp only [mul_assoc]
    _ = a * b * (-(realStep Twist.slash (kz / 2) * realStep Twist.slash (kz / 2))) * b * a := by
          rw [key]
    _ = -(a * b * realStep Twist.slash (kz / 2) * realStep Twist.slash (kz / 2) * b * a) := by
          simp only [mul_neg, neg_mul, mul_assoc]

theorem realWalk_shift_z_sub (ky kx kz : ℝ) : realWalk ky kx (kz - Real.pi) = -realWalk ky kx kz := by
  unfold realWalk
  rw [show (kz - Real.pi) / 2 = kz / 2 - Real.pi / 2 by ring]
  set a := realStep Twist.up (ky / 2)
  set b := realStep Twist.left (kx / 2)
  have key := realStep_sq_sub Twist.slash (kz / 2)
  calc a * b * realStep Twist.slash (kz / 2 - Real.pi / 2) * realStep Twist.slash (kz / 2 - Real.pi / 2)
          * b * a
        = a * b * (realStep Twist.slash (kz / 2 - Real.pi / 2) *
            realStep Twist.slash (kz / 2 - Real.pi / 2)) * b * a := by simp only [mul_assoc]
    _ = a * b * (-(realStep Twist.slash (kz / 2) * realStep Twist.slash (kz / 2))) * b * a := by
          rw [key]
    _ = -(a * b * realStep Twist.slash (kz / 2) * realStep Twist.slash (kz / 2) * b * a) := by
          simp only [mul_neg, neg_mul, mul_assoc]

/-- **Shifting `kz` by `π` negates the handed step.** -/
theorem handed_shift_z (ky kx kz : ℝ) : handed ky kx (kz + Real.pi) = -handed ky kx kz := by
  unfold handed
  rw [realWalk_shift_z, show -(kz + Real.pi) = -kz - Real.pi by ring, realWalk_shift_z_sub]
  have hn : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
    intro A B; ext ⟨i, j⟩ ⟨k, l⟩; simp [kroneckerMap_apply]
  rw [hn, hn, neg_add]

/-- **Shifting `kz` by `π` negates the half-step slice.** -/
theorem halfWalk_shift_z (ky kx kz m : ℝ) :
    halfWalk ky kx (kz + Real.pi) m = -halfWalk ky kx kz m := by
  rw [halfWalk, halfWalk, handed_shift_z, mul_neg, neg_mul]

/-- **Shifting `kz` by `π` negates the raw slice.** -/
theorem diracWalk_shift_z (ky kx kz m : ℝ) :
    diracWalk ky kx (kz + Real.pi) m = -diracWalk ky kx kz m := by
  rw [diracWalk, diracWalk, handed_shift_z, mul_neg]

/-- **The quasi-energy moves by `π`.** An eigenvector at `k` with eigenvalue `λ` is an eigenvector at
    `k + π e_z` with eigenvalue `−λ`, so the positive and negative bands trade places. -/
theorem halfWalk_shift_z_eigen (ky kx kz m : ℝ) (v : Fin 2 × Fin 2 → ℂ) (lam : ℂ)
    (h : halfWalk ky kx kz m *ᵥ v = lam • v) :
    halfWalk ky kx (kz + Real.pi) m *ᵥ v = (-lam) • v := by
  rw [halfWalk_shift_z, neg_mulVec, h, neg_smul]

end QLF.PiDoubler
