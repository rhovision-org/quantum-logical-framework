import QLF_LightCone

set_option linter.unusedVariables false

/-!
# QLF_RealizableWalk — **what is realizable is unitary**

Continues [`QLF_LightCone`](QLF_LightCone.lean) (issue #207, gap "unitary evolution"). See
[`Closure_Unitarity.md`](../Closure_Unitarity.md) §12.

## The raw step is not unitary

Give each outward step a momentum phase and sum the three twists. At zero momentum this is the
unitary `coneStep` of `QLF_LightCone`, but not at every momentum:

> **`rawStep_not_unitary`** — with phase `i` on the up step, `(iσ_y − σ_x + σ_z)/√3` is not unitary.

So the coherent census sum is not by itself a time evolution channel by channel.

## The realizable part of a step

A step by twist `t` does zero free action on the spin exactly on the states `t` leaves unchanged,
the `+1` eigenspace of `M(t)`. Its realizable part is the projector onto them:

> `fix t = (1 + M(t))/2`.

Because `M(t̄) = −M(t)` for the conjugate twist, the realizable parts of a twist and its conjugate
are complementary: each is a projector (`fix_idem`), they are orthogonal (`fix_mul_conj`), and they
sum to the identity (`fix_add_conj`). A step that moves along `t` with phase `e^{ik}` and along `t̄`
with `e^{−ik}`, keeping only the realizable parts, is therefore

> **`realStep_unitary`** — unitary at every momentum,

and so is the walk over the three spatial axes (**`realWalk_unitary`**). The realizable step is
exactly the average of the bare displacement and the raw twist step (`realStep_eq_half`). To first
order in `k` the walk's generator is `k_y σ_y − k_x σ_x + k_z σ_z`, the Weyl operator; that expansion
is checked numerically, not proved here.

The walk has the form of the split-step Weyl walk of the quantum-walk literature (Bialynicki-Birula
1994; Arrighi, Nesme and Forets 2014). Here the spin-locking is read off zero free action per step.

No axioms.
-/

namespace QLF.ClosureChannels

open QLF Matrix

-- ==========================================
-- §1  The raw coherent step fails unitarity
-- ==========================================

/-- The raw step with phase `i` on the up twist and `1` on the others, before the `1/√3`. -/
noncomputable def rawPhaseSum : M :=
  Complex.I • Twist.up.toMatrix + Twist.left.toMatrix + Twist.slash.toMatrix

theorem rawPhaseSum_gram : (rawPhaseSum.conjTranspose * rawPhaseSum) 0 0 = 5 := by
  unfold rawPhaseSum
  simp [Twist.toMatrix, σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  norm_num

theorem star_r3_inv : star r3⁻¹ = r3⁻¹ := by
  unfold r3
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

/-- **The raw coherent step is not unitary at every momentum.** -/
theorem rawStep_not_unitary : r3⁻¹ • rawPhaseSum ∉ Matrix.unitaryGroup (Fin 2) ℂ := by
  intro h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    smul_mul_smul_comm, star_r3_inv] at h
  have e := congrFun (congrFun h 0) 0
  rw [Matrix.smul_apply, rawPhaseSum_gram, Matrix.one_apply_eq, smul_eq_mul] at e
  have h3 : r3⁻¹ * r3⁻¹ = 1 / 3 := by
    rw [← mul_inv, r3_sq]; norm_num
  rw [h3] at e
  norm_num at e

-- ==========================================
-- §2  The realizable part of a step
-- ==========================================

/-- The realizable part of a twist step: the projector onto the spin states it leaves unchanged. -/
noncomputable def fix (t : Twist) : M := (1 / 2 : ℂ) • ((1 : M) + t.toMatrix)

theorem fix_herm (t : Twist) : (fix t).conjTranspose = fix t := by
  unfold fix
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    ClosureUnitarity.twist_herm]
  congr 1
  simp

theorem fix_idem (t : Twist) : fix t * fix t = fix t := by
  unfold fix
  rw [smul_mul_smul_comm, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    ClosureUnitarity.twist_sq]
  rw [← sub_eq_zero]
  module

theorem fix_add_conj (t : Twist) : fix t + fix t.conj = 1 := by
  unfold fix
  rw [ClosureUnitarity.conj_toMatrix, ← smul_add]
  rw [← sub_eq_zero]
  module

theorem fix_mul_conj (t : Twist) : fix t * fix t.conj = 0 := by
  unfold fix
  rw [ClosureUnitarity.conj_toMatrix, smul_mul_smul_comm, add_mul, mul_add, mul_add, one_mul,
    mul_one, one_mul, mul_neg, ClosureUnitarity.twist_sq]
  rw [← sub_eq_zero]
  module

theorem fix_conj_mul (t : Twist) : fix t.conj * fix t = 0 := by
  have h := fix_mul_conj t.conj
  rwa [show t.conj.conj = t by cases t <;> rfl] at h

-- ==========================================
-- §3  Realizable steps are unitary
-- ==========================================

/-- One realizable step along the axis of `t` at momentum `k`: phase `e^{ik}` along `t`, `e^{−ik}`
along its conjugate, each on its realizable part. -/
noncomputable def realStep (t : Twist) (k : ℝ) : M :=
  Complex.exp (k * Complex.I) • fix t + Complex.exp (-(k * Complex.I)) • fix t.conj

theorem star_exp_kI (k : ℝ) : star (Complex.exp (k * Complex.I)) = Complex.exp (-(k * Complex.I)) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

theorem exp_kI_mul_neg (k : ℝ) :
    Complex.exp (-(k * Complex.I)) * Complex.exp (k * Complex.I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- **What is realizable is unitary.** A realizable step is unitary at every momentum. -/
theorem realStep_unitary (t : Twist) (k : ℝ) :
    realStep t k ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold realStep
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, fix_herm,
    fix_herm]
  have h2 : star (Complex.exp (-(k * Complex.I))) = Complex.exp (k * Complex.I) := by
    rw [← star_exp_kI, star_star]
  rw [star_exp_kI, h2]
  simp only [add_mul, mul_add, smul_mul_smul_comm, fix_idem, fix_mul_conj, fix_conj_mul,
    smul_zero, add_zero, zero_add]
  have e1 := exp_kI_mul_neg k
  have e2 : Complex.exp (k * Complex.I) * Complex.exp (-(k * Complex.I)) = 1 := by
    rw [mul_comm, e1]
  rw [e1, e2, one_smul, one_smul, fix_add_conj]

/-- **The realizable step is the average of the bare displacement and the raw twist step.** -/
theorem realStep_eq_half (t : Twist) (k : ℝ) :
    realStep t k = (1 / 2 : ℂ) • ((Complex.exp (k * Complex.I) + Complex.exp (-(k * Complex.I))) •
        (1 : M) +
      (Complex.exp (k * Complex.I) • t.toMatrix + Complex.exp (-(k * Complex.I)) •
        t.conj.toMatrix)) := by
  unfold realStep fix
  rw [ClosureUnitarity.conj_toMatrix]
  rw [← sub_eq_zero]
  module

/-- **The three-axis walk of realizable steps.** Up, then left, then slash. -/
noncomputable def realWalk (ky kx kz : ℝ) : M :=
  realStep Twist.up ky * realStep Twist.left kx * realStep Twist.slash kz

/-- **The walk of realizable steps is unitary at every momentum.** -/
theorem realWalk_unitary (ky kx kz : ℝ) :
    realWalk ky kx kz ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (realStep_unitary _ _) (realStep_unitary _ _))
    (realStep_unitary _ _)

/-- At zero momentum the walk is the identity. -/
theorem realWalk_zero : realWalk 0 0 0 = 1 := by
  simp [realWalk, realStep, fix_add_conj]

end QLF.ClosureChannels
