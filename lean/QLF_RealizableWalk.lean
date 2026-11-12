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

/-- **The three-axis walk of realizable steps, time-symmetric within the tick.** A half step up,
left, slash, then a half step slash, left, up. The order is a palindrome, so the tick reads the same
forwards and backwards.

Why the palindrome: with the one-way order up, left, slash the walk's dispersion is
`cos E = Π cos k_i + Π sin k_i` (`oneWayWalk_trace`, §8; the sign of the odd part depends on the
octant), which carries a term linear in energy, `E ≈ k ∓ k_y k_x k_z / k`. At
Planck spacing, and if this walk describes the electron (an extra physical assumption, not proved
here), that is `η` up to `±0.385`, against the Crab synchrotron bound `η > −7 × 10⁻⁸` (Jacobson,
Liberati and Mattingly 2003). The palindrome has `cos E = Π cos k_i`, with no odd term, and leaves
`E = k − k³/18` on the body diagonal. Both trace identities are proved below (`realWalk_trace`,
`oneWayWalk_trace`) and checked numerically (`liv_dispersion.py`). See
`QM_Postulates_QLF.md` §5b. -/
noncomputable def realWalk (ky kx kz : ℝ) : M :=
  realStep Twist.up (ky / 2) * realStep Twist.left (kx / 2) * realStep Twist.slash (kz / 2) *
    realStep Twist.slash (kz / 2) * realStep Twist.left (kx / 2) * realStep Twist.up (ky / 2)

/-- **The walk of realizable steps is unitary at every momentum.** -/
theorem realWalk_unitary (ky kx kz : ℝ) :
    realWalk ky kx kz ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
    (Submonoid.mul_mem _ (realStep_unitary _ _) (realStep_unitary _ _)) (realStep_unitary _ _))
    (realStep_unitary _ _)) (realStep_unitary _ _)) (realStep_unitary _ _)

/-- At zero momentum the walk is the identity. -/
theorem realWalk_zero : realWalk 0 0 0 = 1 := by
  simp [realWalk, realStep, fix_add_conj]

-- ==========================================
-- §5  The palindromic walk's dispersion
-- ==========================================

/-- **A realizable step is a rotation**: `cos k + i sin k · M(t)`. -/
theorem realStep_eq_cos_sin (t : Twist) (k : ℝ) :
    realStep t k = ((Real.cos k : ℝ) : ℂ) • (1 : M) + (((Real.sin k : ℝ) : ℂ) * Complex.I) • t.toMatrix := by
  unfold realStep fix
  rw [ClosureUnitarity.conj_toMatrix]
  have h1 : Complex.exp (↑k * Complex.I) = ((Real.cos k : ℝ) : ℂ) + ((Real.sin k : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h2 : Complex.exp (-(↑k * Complex.I)) =
      ((Real.cos k : ℝ) : ℂ) - ((Real.sin k : ℝ) : ℂ) * Complex.I := by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2]
  module

/-- **The palindromic walk's dispersion: `cos E = cos k_y cos k_x cos k_z`.** The walk is in `SU(2)`,
so its eigenvalues are `e^{±iE}` with `tr = 2 cos E`, and the trace is exactly this product at every
momentum. `cos E` is therefore even in each `k_i`: the dispersion has no odd term, in particular no
term linear in energy, in any direction. (The one-way order `up · left · slash` gives
`Π cos k_i + Π sin k_i` instead, whose odd part is the linear term; see `oneWayWalk_trace`, §8.)
This is the finite-momentum dispersion of the walk; reading it as a particle's physical dispersion is
a separate assumption. -/
theorem realWalk_trace (ky kx kz : ℝ) :
    Matrix.trace (realWalk ky kx kz) =
      2 * ((Real.cos ky * Real.cos kx * Real.cos kz : ℝ) : ℂ) := by
  have hy : ky = 2 * (ky / 2) := by ring
  have hx : kx = 2 * (kx / 2) := by ring
  have hz : kz = 2 * (kz / 2) := by ring
  conv_rhs => rw [hy, hx, hz]
  simp only [realWalk, realStep_eq_cos_sin, Twist.toMatrix, σx, σy, σz, Real.cos_two_mul']
  generalize ky / 2 = a
  generalize kx / 2 = b
  generalize kz / 2 = c
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Fin.isValue, smul_eq_mul]
  push_cast
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, h4, Complex.I_sq, one_mul]
  have h8 : Complex.I ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, h4, one_mul]
  ring_nf
  simp only [h4, h6, h8, Complex.I_sq]
  ring

/-- **No odd term in any direction.** Reversing any one momentum component leaves `tr = 2 cos E`
unchanged, so the dispersion is even in each `k_i` separately. -/
theorem realWalk_trace_even (ky kx kz : ℝ) :
    Matrix.trace (realWalk (-ky) kx kz) = Matrix.trace (realWalk ky kx kz) ∧
    Matrix.trace (realWalk ky (-kx) kz) = Matrix.trace (realWalk ky kx kz) ∧
    Matrix.trace (realWalk ky kx (-kz)) = Matrix.trace (realWalk ky kx kz) := by
  simp only [realWalk_trace, Real.cos_neg, and_self]

/-- **Reversing the momentum is the adjoint**: `realStep t (−k) = realStep t k†`. -/
theorem realStep_neg (t : Twist) (k : ℝ) : realStep t (-k) = star (realStep t k) := by
  have h2 : star (Complex.exp (-(↑k * Complex.I))) = Complex.exp (↑k * Complex.I) := by
    rw [← star_exp_kI k, star_star]
  rw [realStep, realStep, star_add, star_smul, star_smul, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, fix_herm, fix_herm, star_exp_kI, h2]
  push_cast
  rw [neg_mul, neg_neg]

/-- **The palindromic walk at `−k` is its own adjoint at `k`**, because the reversed product of
adjoints is the same palindrome. -/
theorem realWalk_neg (ky kx kz : ℝ) :
    realWalk (-ky) (-kx) (-kz) = star (realWalk ky kx kz) := by
  simp only [realWalk, neg_div, realStep_neg, star_mul, mul_assoc]

/-- **`W(k) + W(k)† = 2 cos k_y cos k_x cos k_z · 1`** at every momentum: both eigenvalues
`e^{±iE}` obey `cos E = Π cos k_i`. -/
theorem realWalk_add_star (ky kx kz : ℝ) :
    realWalk ky kx kz + star (realWalk ky kx kz) =
      (2 * ((Real.cos ky * Real.cos kx * Real.cos kz : ℝ) : ℂ)) • (1 : M) := by
  rw [← realWalk_neg]
  have hy : ky = 2 * (ky / 2) := by ring
  have hx : kx = 2 * (kx / 2) := by ring
  have hz : kz = 2 * (kz / 2) := by ring
  conv_rhs => rw [hy, hx, hz]
  simp only [realWalk, neg_div, realStep_eq_cos_sin, Real.cos_neg, Real.sin_neg, Twist.toMatrix,
    σx, σy, σz, Real.cos_two_mul']
  generalize ky / 2 = a
  generalize kx / 2 = b
  generalize kz / 2 = c
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, h4, Complex.I_sq, one_mul]
  have h8 : Complex.I ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, h4, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Fin.isValue, smul_eq_mul, Fin.zero_eta, Fin.mk_one, ite_true] <;>
  norm_num <;>
  ring_nf <;>
  simp only [h4, h6, h8, Complex.I_sq] <;>
  ring

/-! ## 6. The realizable step is forced

A nearest-neighbour step along one axis moves the spin state one site forward with some matrix `A`
and one site back with some `B`, so at momentum phase `a` (a unit complex number, `a = e^{ik}`) it is
`a • A + a̅ • B`. Unitarity at every phase alone forces it into the realizable form: a fixed unitary
coin `U = A + B` (the step at zero momentum) times `a • P + a̅ • (1 − P)` for an orthogonal projector
`P` (`step_forced`). With no coin (`A + B = 1`) the step is exactly a projector step
(`coinless_step_forced`), and `realStep` is the case `P = fix t`, the states the twist fixes. -/

/-- A nearest-neighbour step at unit phase `a`. -/
def nnStep (A B : M) (a : ℂ) : M := a • A + star a • B

/-- `star (nnStep) * nnStep` at a unit phase. -/
theorem nnStep_gram (A B : M) (a : ℂ) (ha : star a * a = 1) :
    star (nnStep A B a) * nnStep A B a =
      star A * A + star B * B + (star a ^ 2) • (star A * B) + (a ^ 2) • (star B * A) := by
  have ha' : a * star a = 1 := by rw [mul_comm]; exact ha
  simp only [nnStep, star_add, star_smul, star_star, add_mul, mul_add, smul_mul_smul_comm, ha, ha',
    one_smul, sq]
  abel

/-- `nnStep * star (nnStep)` at a unit phase. -/
theorem nnStep_gram' (A B : M) (a : ℂ) (ha : star a * a = 1) :
    nnStep A B a * star (nnStep A B a) =
      A * star A + B * star B + (star a ^ 2) • (B * star A) + (a ^ 2) • (A * star B) := by
  have ha' : a * star a = 1 := by rw [mul_comm]; exact ha
  simp only [nnStep, star_add, star_smul, star_star, add_mul, mul_add, smul_mul_smul_comm, ha, ha',
    one_smul, sq]
  abel

/-- Three unit phases `1, i, (3 + 4i)/5` separate the three terms of `C + w̄ X + w Y = 1`. -/
private theorem separate (C X Y : M)
    (h : ∀ a : ℂ, star a * a = 1 → C + (star a ^ 2) • X + (a ^ 2) • Y = 1) :
    C = 1 ∧ X = 0 ∧ Y = 0 := by
  have h1 := h 1 (by simp)
  have h2 := h Complex.I (by rw [Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg])
  set z : ℂ := ⟨3 / 5, 4 / 5⟩
  have hz : star z * z = 1 := by
    apply Complex.ext <;> simp [z] <;> norm_num
  have h3 := h z hz
  have hzs : star z ^ 2 = ⟨-7 / 25, -24 / 25⟩ := by
    apply Complex.ext <;> simp [z, sq] <;> norm_num
  have hzz : z ^ 2 = ⟨-7 / 25, 24 / 25⟩ := by
    apply Complex.ext <;> simp [z, sq] <;> norm_num
  have hIs : star Complex.I ^ 2 = -1 := by
    rw [Complex.star_def, Complex.conj_I, neg_sq, Complex.I_sq]
  simp only [star_one, one_pow, one_smul] at h1
  rw [hIs, Complex.I_sq, neg_one_smul, neg_one_smul] at h2
  rw [hzs, hzz] at h3
  -- h1: C + X + Y = 1;  h2: C - X - Y = 1
  have hC : C = 1 := by
    have : (2 : ℂ) • C = (2 : ℂ) • 1 := by
      rw [two_smul, two_smul]
      calc C + C = (C + X + Y) + (C + -X + -Y) := by abel
        _ = 1 + 1 := by rw [h1, h2]
    exact smul_right_injective M two_ne_zero this
  have hXY : X + Y = 0 := by
    have := h1; rw [hC] at this
    calc X + Y = (1 + X + Y) - 1 := by abel
      _ = 0 := by rw [this, sub_self]
  have hY : Y = -X := eq_neg_of_add_eq_zero_right hXY
  rw [hC, hY, smul_neg] at h3
  have h4 : ((⟨-7 / 25, -24 / 25⟩ : ℂ) - ⟨-7 / 25, 24 / 25⟩) • X = 0 := by
    rw [sub_smul]
    calc _ = (1 + (⟨-7 / 25, -24 / 25⟩ : ℂ) • X + -((⟨-7 / 25, 24 / 25⟩ : ℂ) • X)) - 1 := by abel
      _ = 0 := by rw [h3, sub_self]
  have hne : ((⟨-7 / 25, -24 / 25⟩ : ℂ) - ⟨-7 / 25, 24 / 25⟩) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    norm_num at this
  have hX : X = 0 := (smul_eq_zero.mp h4).resolve_left hne
  exact ⟨hC, hX, by rw [hY, hX, neg_zero]⟩

/-- **Unitarity forces the realizable form.** If a nearest-neighbour step `a • A + a̅ • B` is
unitary at every unit phase, then `A = U P` and `B = U (1 − P)`, where `U = A + B` is unitary and
`P` is an orthogonal projector. -/
theorem step_forced (A B : M)
    (h : ∀ a : ℂ, star a * a = 1 → nnStep A B a ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ U P : M, U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ star P = P ∧ P * P = P ∧
      A = U * P ∧ B = U * (1 - P) := by
  obtain ⟨hC, hX, hY⟩ := separate (star A * A + star B * B) (star A * B) (star B * A) (fun a ha => by
    rw [← nnStep_gram A B a ha]; exact Matrix.mem_unitaryGroup_iff'.mp (h a ha))
  obtain ⟨hC', hX', hY'⟩ := separate (A * star A + B * star B) (B * star A) (A * star B)
    (fun a ha => by
      rw [← nnStep_gram' A B a ha]; exact Matrix.mem_unitaryGroup_iff.mp (h a ha))
  have hP1 : 1 - star A * A = star B * B := by rw [← hC]; abel
  refine ⟨A + B, star A * A, ?_, ?_, ?_, ?_, ?_⟩
  · have := h 1 (by simp)
    simpa [nnStep] using this
  · rw [star_mul, star_star]
  · calc star A * A * (star A * A) = star A * (A * star A) * A := by noncomm_ring
      _ = star A * (1 - B * star B) * A := by rw [← hC']; abel_nf
      _ = star A * A - (star A * B) * (star B * A) := by noncomm_ring
      _ = star A * A := by rw [hX, zero_mul, sub_zero]
  · calc A = (A * star A + B * star B) * A := by rw [hC', one_mul]
      _ = A * star A * A + B * (star B * A) := by noncomm_ring
      _ = A * star A * A + B * star A * A := by rw [hY, hX', mul_zero, zero_mul]
      _ = (A + B) * (star A * A) := by noncomm_ring
  · rw [hP1]
    calc B = (A * star A + B * star B) * B := by rw [hC', one_mul]
      _ = A * (star A * B) + B * star B * B := by noncomm_ring
      _ = A * star B * B + B * star B * B := by rw [hX, hY', mul_zero, zero_mul]
      _ = (A + B) * (star B * B) := by noncomm_ring

/-- **With no coin the step is a projector step.** If the step at zero momentum is the identity
(`A + B = 1`), unitarity at every phase forces `nnStep A B a = a • P + a̅ • (1 − P)` with `P` an
orthogonal projector. `realStep t` is the case `P = fix t`. -/
theorem coinless_step_forced (A B : M) (hc : A + B = 1)
    (h : ∀ a : ℂ, star a * a = 1 → nnStep A B a ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ P : M, star P = P ∧ P * P = P ∧ ∀ a : ℂ, nnStep A B a = a • P + star a • (1 - P) := by
  obtain ⟨U, P, -, hs, hp, hA, hB⟩ := step_forced A B h
  have hU : U = 1 := by
    have : A + B = U * P + U * (1 - P) := by rw [← hA, ← hB]
    rw [hc, ← mul_add, add_sub_cancel, mul_one] at this
    exact this.symm
  refine ⟨P, hs, hp, fun a => ?_⟩
  rw [nnStep, hA, hB, hU, one_mul, one_mul]

/-- `realStep` is a nearest-neighbour step at the phase `e^{ik}`, with no coin. -/
theorem realStep_eq_nnStep (t : Twist) (k : ℝ) :
    realStep t k = nnStep (fix t) (fix t.conj) (Complex.exp (k * Complex.I)) := by
  rw [realStep, nnStep, star_exp_kI]

theorem realStep_coinless (t : Twist) : fix t + fix t.conj = 1 := fix_add_conj t

/-- A projector step `a • P + a̅ • (1 − P)` has spin generator `2P − 1`; it is the twist exactly
when `P = fix t`. -/
theorem fix_iff_generator (t : Twist) (P : M) : P = fix t ↔ (2 : ℂ) • P - 1 = t.toMatrix := by
  constructor
  · rintro rfl
    unfold fix
    rw [smul_smul]
    norm_num
  · intro h
    have hP : P = (1 / 2 : ℂ) • ((2 : ℂ) • P) := by rw [smul_smul]; norm_num
    rw [hP, fix, ← h]
    congr 1
    abel

/-- **The realizable step is forced.** A coinless nearest-neighbour step that is unitary at every
phase, and whose spin generator is the twist `t`, is `realStep t` at every momentum. -/
theorem coinless_twist_step (t : Twist) (A B : M) (hc : A + B = 1)
    (h : ∀ a : ℂ, star a * a = 1 → nnStep A B a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hgen : (2 : ℂ) • A - 1 = t.toMatrix) :
    ∀ k : ℝ, nnStep A B (Complex.exp (k * Complex.I)) = realStep t k := by
  obtain ⟨P, -, -, hstep⟩ := coinless_step_forced A B hc h
  have hA : A = P := by
    have h2 := hstep Complex.I
    simp only [nnStep, Complex.star_def, Complex.conj_I, neg_smul] at h2
    have hd : Complex.I • (A - B) = Complex.I • (P - (1 - P)) := by
      rw [smul_sub, smul_sub, sub_eq_add_neg, h2, ← sub_eq_add_neg]
    have hd' : A - B = P - (1 - P) := smul_right_injective M Complex.I_ne_zero hd
    have h2A : (2 : ℂ) • A = (2 : ℂ) • P := by
      rw [two_smul, two_smul]
      calc A + A = (A + B) + (A - B) := by abel
        _ = 1 + (P - (1 - P)) := by rw [hc, hd']
        _ = P + P := by abel
    exact smul_right_injective M two_ne_zero h2A
  have hB : B = 1 - P := by rw [← hA, ← hc]; abel
  have hfix : P = fix t := (fix_iff_generator t P).mpr (hA ▸ hgen)
  intro k
  rw [realStep_eq_nnStep, hA, hB, hfix, ← fix_add_conj t, add_sub_cancel_left]

/-! ## 7. The quadratic term, as a theorem (forecast F2)

`realWalk_trace` gives `cos E = cos k_y cos k_x cos k_z` exactly. Here its fourth-order content is
proved with an explicit remainder: `walk_cos_taylor` expands `Π cos k_i` to fourth order with error at
most `(|k_x| + |k_y| + |k_z|)⁶ · 7/4320`, and `walk_dispersion_quadratic` shows that `cos E` agrees
with `cos E_pred`, where `E_pred² = k² − (k_x²k_y² + k_y²k_z² + k_z²k_x²)/3`, to within
`(|k_x| + |k_y| + |k_z|)⁶ / 50`. That is forecast F2 of `QM_Postulates_QLF.md` §5c: subluminal, zero
along the axes, `ξ = 1/9` on the body diagonal. Momenta are in lattice units and need
`|k_x| + |k_y| + |k_z| ≤ 1`. `walk_energy_quadratic` then inverts the cosine: with
`E = arccos (Π cos k_i)`, the branch `0 ≤ E ≤ π`, `E²` agrees with `E_pred²` to within
`(|k_x| + |k_y| + |k_z|)⁶ / 10`. Choosing that branch, and reading `E` as an energy, are not
derived here. -/

section QuadraticTerm

open Complex Finset


/-- Sixth-order Taylor bound for the complex cosine (Mathlib's `Complex.cos_bound`, two orders
further). -/
theorem cos_bound6 {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)‖ ≤ ‖x‖ ^ 6 * (7 / 4320) :=
  calc
    ‖cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)‖ =
        ‖(exp (-x * I) - ∑ m ∈ range 6, (-x * I) ^ m / m.factorial) / 2 +
         (exp (x * I) - ∑ m ∈ range 6, (x * I) ^ m / m.factorial) / 2‖ := by
      simp [cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ ≤ ‖exp (-x * I) - ∑ m ∈ range 6, (-x * I) ^ m / m.factorial‖ / 2 +
        ‖exp (x * I) - ∑ m ∈ range 6, (x * I) ^ m / m.factorial‖ / 2 := by
      grw [norm_add_le]
      simp
    _ ≤ ‖-x * I‖ ^ 6 * (Nat.succ 6 * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 +
        ‖x * I‖ ^ 6 * (Nat.succ 6 * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [exp_bound (by simpa) (by simp), exp_bound (by simpa) (by simp)]
    _ ≤ ‖x‖ ^ 6 * (7 / 4320) := by norm_num [Nat.factorial]

/-- The real form of `cos_bound6`. -/
theorem rcos_bound6 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ |x| ^ 6 * (7 / 4320) := by
  have h := cos_bound6 (x := (x : ℂ)) (by simpa using hx)
  have e : Complex.cos (x : ℂ) - (1 - (x : ℂ) ^ 2 / 2 + (x : ℂ) ^ 4 / 24) =
      ((Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24) : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Product to sum: `cos a cos b cos c` is the average of four cosines. -/
theorem cos_prod_three (a b c : ℝ) :
    Real.cos a * Real.cos b * Real.cos c =
      (Real.cos (a + b + c) + Real.cos (a + b - c) + Real.cos (a - b + c) + Real.cos (-a + b + c)) / 4 := by
  have e1 : -a + b + c = (b + c) - a := by ring
  have e2 : a - b + c = a - (b - c) := by ring
  have e3 : a + b + c = a + (b + c) := by ring
  have e4 : a + b - c = a + (b - c) := by ring
  rw [e1, e2, e3, e4]
  simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
  ring

/-- The walk's `Π cos k_i` to fourth order, with an explicit sixth-order remainder. -/
theorem walk_cos_taylor (a b c : ℝ) (h : |a| + |b| + |c| ≤ 1) :
    |Real.cos a * Real.cos b * Real.cos c -
      (1 - (a ^ 2 + b ^ 2 + c ^ 2) / 2 + (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / 24 +
        (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) / 6)| ≤
      (|a| + |b| + |c|) ^ 6 * (7 / 4320) := by
  set T := |a| + |b| + |c|
  have hT0 : 0 ≤ T := by positivity
  have hs : ∀ s : ℝ, |s| ≤ T → |Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)| ≤ T ^ 6 * (7 / 4320) :=
    fun s hs => (rcos_bound6 (hs.trans h)).trans (by gcongr)
  have h1 := hs (a + b + c) (by
    calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ T := by linarith [abs_add_le a b])
  have h2 := hs (a + b - c) (by
    calc |a + b - c| ≤ |a + b| + |c| := abs_sub _ _
      _ ≤ T := by linarith [abs_add_le a b])
  have h3 := hs (a - b + c) (by
    calc |a - b + c| ≤ |a - b| + |c| := abs_add_le _ _
      _ ≤ T := by linarith [abs_sub a b])
  have h4 := hs (-a + b + c) (by
    calc |-a + b + c| ≤ |-a + b| + |c| := abs_add_le _ _
      _ ≤ |-a| + |b| + |c| := by linarith [abs_add_le (-a) b]
      _ = T := by rw [abs_neg])
  rw [cos_prod_three]
  have key : (Real.cos (a + b + c) + Real.cos (a + b - c) + Real.cos (a - b + c) +
      Real.cos (-a + b + c)) / 4 -
      (1 - (a ^ 2 + b ^ 2 + c ^ 2) / 2 + (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / 24 +
        (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) / 6) =
      ((Real.cos (a + b + c) - (1 - (a + b + c) ^ 2 / 2 + (a + b + c) ^ 4 / 24)) +
       (Real.cos (a + b - c) - (1 - (a + b - c) ^ 2 / 2 + (a + b - c) ^ 4 / 24)) +
       (Real.cos (a - b + c) - (1 - (a - b + c) ^ 2 / 2 + (a - b + c) ^ 4 / 24)) +
       (Real.cos (-a + b + c) - (1 - (-a + b + c) ^ 2 / 2 + (-a + b + c) ^ 4 / 24))) / 4 := by
    ring
  rw [key, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
  have := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)
  linarith

private theorem poly_gap (r S : ℝ) (hS0 : 0 ≤ S) (hSr : 3 * S ≤ r ^ 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ r - S / 3 ∧ r - S / 3 ≤ r ∧
    |(1 - r / 2 + r ^ 2 / 24 + S / 6) - (1 - (r - S / 3) / 2 + (r - S / 3) ^ 2 / 24)| ≤ r ^ 3 / 108 := by
  have hrr : r ^ 2 ≤ r := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  have hd : (1 - r / 2 + r ^ 2 / 24 + S / 6) - (1 - (r - S / 3) / 2 + (r - S / 3) ^ 2 / 24) =
      r * S / 36 - S ^ 2 / 216 := by ring
  rw [hd, abs_le]
  constructor
  · nlinarith [mul_nonneg hr0 hS0]
  · nlinarith [mul_nonneg hr0 hS0, mul_nonneg hr0 hr0]

/-- **F2 as a theorem.** The walk's `cos E = Π cos k_i` agrees with `cos E_pred`, where
`E_pred² = k² − (k_x²k_y² + k_y²k_z² + k_z²k_x²)/3`, up to `(|k_x| + |k_y| + |k_z|)⁶ / 50`. -/
theorem walk_dispersion_quadratic (a b c : ℝ) (h : |a| + |b| + |c| ≤ 1) :
    |Real.cos a * Real.cos b * Real.cos c -
      Real.cos (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) -
        (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) / 3))| ≤
      (|a| + |b| + |c|) ^ 6 / 50 := by
  have hW := walk_cos_taylor a b c h
  have hrT : a ^ 2 + b ^ 2 + c ^ 2 ≤ (|a| + |b| + |c|) ^ 2 := by
    have ha := sq_abs a; have hb := sq_abs b; have hc := sq_abs c
    nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, mul_nonneg (abs_nonneg a) (abs_nonneg b),
      mul_nonneg (abs_nonneg b) (abs_nonneg c), mul_nonneg (abs_nonneg c) (abs_nonneg a)]
  have hT0 : 0 ≤ |a| + |b| + |c| := by positivity
  have hSr : 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
  have hS0 : 0 ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by positivity
  have hr0 : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  generalize |a| + |b| + |c| = T at h hW hrT hT0 ⊢
  generalize a ^ 2 + b ^ 2 + c ^ 2 = r at hW hrT hSr hr0 ⊢
  generalize a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 = S at hW hSr hS0 ⊢
  generalize Real.cos a * Real.cos b * Real.cos c = P at hW ⊢
  have hT1 : T ^ 2 ≤ 1 := by nlinarith
  obtain ⟨hu0, hur, hgap⟩ := poly_gap r S hS0 hSr hr0 (by linarith)
  generalize r - S / 3 = u at hu0 hur hgap ⊢
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0
  have hx : |Real.sqrt u| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg u)]
    calc Real.sqrt u ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hE := rcos_bound6 hx
  have h4 : Real.sqrt u ^ 4 = u ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  have h6 : |Real.sqrt u| ^ 6 = u ^ 3 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg u), show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hsq]
  rw [hsq, h4, h6] at hE
  have hu3 : u ^ 3 ≤ T ^ 6 := by
    calc u ^ 3 ≤ r ^ 3 := by gcongr
      _ ≤ (T ^ 2) ^ 3 := by gcongr
      _ = T ^ 6 := by ring
  have hr3 : r ^ 3 ≤ T ^ 6 := by
    calc r ^ 3 ≤ (T ^ 2) ^ 3 := by gcongr
      _ = T ^ 6 := by ring
  have hsplit : P - Real.cos (Real.sqrt u) =
      (P - (1 - r / 2 + r ^ 2 / 24 + S / 6)) +
      ((1 - r / 2 + r ^ 2 / 24 + S / 6) - (1 - u / 2 + u ^ 2 / 24)) -
      (Real.cos (Real.sqrt u) - (1 - u / 2 + u ^ 2 / 24)) := by ring
  rw [hsplit]
  have htri : ∀ x y z : ℝ, |x + y - z| ≤ |x| + |y| + |z| := fun x y z =>
    (abs_sub _ _).trans (by linarith [abs_add_le x y])
  have := htri (P - (1 - r / 2 + r ^ 2 / 24 + S / 6))
    ((1 - r / 2 + r ^ 2 / 24 + S / 6) - (1 - u / 2 + u ^ 2 / 24))
    (Real.cos (Real.sqrt u) - (1 - u / 2 + u ^ 2 / 24))
  refine this.trans ((add_le_add (add_le_add hW hgap) hE).trans ?_)
  linarith [pow_nonneg hT0 6]

private theorem abs_sin_ge (y : ℝ) (hy : |y| ≤ Real.pi / 2) : 2 * |y| ≤ |Real.sin y| * Real.pi := by
  rcases le_total 0 y with h0 | h0
  · rw [abs_of_nonneg h0] at hy ⊢
    have := Real.mul_le_sin h0 hy
    rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) Real.pi_pos.le)
  · rw [abs_of_nonpos h0] at hy ⊢
    have := Real.mul_le_sin (neg_nonneg.mpr h0) hy
    rw [Real.sin_neg, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at this
    exact this.trans (mul_le_mul_of_nonneg_right (neg_le_abs _) Real.pi_pos.le)

/-- Two angles with close cosines have close squares: for `0 ≤ p ≤ π/2` and `0 ≤ q ≤ 1`,
`|p² − q²| ≤ (π²/2)·|cos p − cos q|`. No division by the angle is needed. -/
private theorem sq_gap_le_cos_gap (p q : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ Real.pi / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) :
    |p ^ 2 - q ^ 2| ≤ Real.pi ^ 2 / 2 * |Real.cos p - Real.cos q| := by
  have hpi := Real.pi_gt_three
  have h1 := abs_sin_ge ((p + q) / 2) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h2 := abs_sin_ge ((p - q) / 2) (by rw [abs_le]; constructor <;> linarith)
  have hc : |Real.cos p - Real.cos q| = 2 * (|Real.sin ((p + q) / 2)| * |Real.sin ((p - q) / 2)|) := by
    rw [Real.cos_sub_cos, abs_mul, abs_mul]; norm_num; ring
  have hprod := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hfac : |p ^ 2 - q ^ 2| = 4 * (|(p + q) / 2| * |(p - q) / 2|) := by
    rw [← abs_mul, show (p + q) / 2 * ((p - q) / 2) = (p ^ 2 - q ^ 2) / 4 by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    ring
  rw [hc, hfac]
  linarith

/-- **F2 at the level of the energy.** With `E = arccos (Π cos k_i)` the walk's quasi-energy on
the branch `0 ≤ E ≤ π`, `E² = k² − (k_x²k_y² + k_y²k_z² + k_z²k_x²)/3` up to
`(|k_x| + |k_y| + |k_z|)⁶ / 10`. -/
theorem walk_energy_quadratic (a b c : ℝ) (h : |a| + |b| + |c| ≤ 1) :
    |Real.arccos (Real.cos a * Real.cos b * Real.cos c) ^ 2 -
      ((a ^ 2 + b ^ 2 + c ^ 2) - (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) / 3)| ≤
      (|a| + |b| + |c|) ^ 6 / 10 := by
  have hD := walk_dispersion_quadratic a b c h
  have hT0 : 0 ≤ |a| + |b| + |c| := by positivity
  have hT6 : (|a| + |b| + |c|) ^ 6 ≤ 1 := pow_le_one₀ hT0 h
  have hrT : a ^ 2 + b ^ 2 + c ^ 2 ≤ (|a| + |b| + |c|) ^ 2 := by
    have ha := sq_abs a; have hb := sq_abs b; have hc := sq_abs c
    nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, mul_nonneg (abs_nonneg a) (abs_nonneg b),
      mul_nonneg (abs_nonneg b) (abs_nonneg c), mul_nonneg (abs_nonneg c) (abs_nonneg a)]
  have hSr : 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
  have hS0 : 0 ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by positivity
  have hr0 : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have hr1 : a ^ 2 + b ^ 2 + c ^ 2 ≤ 1 := by nlinarith
  have hPle : |Real.cos a * Real.cos b * Real.cos c| ≤ 1 := by
    rw [abs_mul, abs_mul]
    have := Real.abs_cos_le_one a; have := Real.abs_cos_le_one b; have := Real.abs_cos_le_one c
    calc |Real.cos a| * |Real.cos b| * |Real.cos c| ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  generalize |a| + |b| + |c| = T at h hD hT0 hT6 hrT ⊢
  generalize a ^ 2 + b ^ 2 + c ^ 2 = r at hD hrT hSr hr0 hr1 ⊢
  generalize a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 = S at hD hSr hS0 ⊢
  generalize Real.cos a * Real.cos b * Real.cos c = P at hD hPle ⊢
  have hu0 : 0 ≤ r - S / 3 := by nlinarith
  have hu1 : r - S / 3 ≤ 1 := by linarith
  generalize r - S / 3 = u at hD hu0 hu1 ⊢
  have hq0 := Real.sqrt_nonneg u
  have hq1 : Real.sqrt u ≤ 1 := by
    calc Real.sqrt u ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hu1
      _ = 1 := Real.sqrt_one
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0
  -- `cos √u ≥ cos 1 ≥ 43/96`, so `P > 0` and the branch `E ≤ π/2` is the one in play.
  have hcos1 : (43 : ℝ) / 96 ≤ Real.cos 1 := by
    have := Real.cos_bound (x := 1) (by norm_num)
    rw [abs_le] at this; norm_num at this; linarith [this.1]
  have hcosq : Real.cos 1 ≤ Real.cos (Real.sqrt u) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hq0 (by linarith [Real.pi_gt_three]) hq1
  have hP0 : 0 ≤ P := by
    have := (abs_le.mp hD).1
    linarith
  obtain ⟨hPm, hP1⟩ := abs_le.mp hPle
  have hE := Real.cos_arccos hPm hP1
  have hgap := sq_gap_le_cos_gap (Real.arccos P) (Real.sqrt u) (Real.arccos_nonneg P)
    (Real.arccos_le_pi_div_two.mpr hP0) hq0 hq1
  rw [hE, hsq] at hgap
  have hpi2 : Real.pi ^ 2 ≤ 10 := by
    have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
  calc |Real.arccos P ^ 2 - u| ≤ Real.pi ^ 2 / 2 * |P - Real.cos (Real.sqrt u)| := hgap
    _ ≤ 10 / 2 * (T ^ 6 / 50) := by gcongr
    _ = T ^ 6 / 10 := by ring

end QuadraticTerm

/-! ## 8. Why the order is a palindrome

The order of the sub-steps is not derived from logic. What is proved here is what the choice turns
on. Every palindromic word of realizable steps has the reversal identity `W(−k) = W(k)†`
(`palindrome_reversal`), and `realWalk` is one (`realWalk_eq_wordWalk`). The one-way order does not
have it: its dispersion is `cos E = Π cos k_i + Π sin k_i` (`oneWayWalk_trace`), odd under reversal
by `−4 Π sin k_i` (`oneWayWalk_trace_odd`, `oneWayWalk_not_reversal`). The sign of the odd term
follows the Lean twists (`left = −σ_x`); `liv_dispersion.py` uses `+σ_x` and so prints the other
sign, which is the same walk at `k_x → −k_x`. Among four-step walks, the dispersion is even only
when the repeated axis is split equally (`splitWalk_trace`, `splitWalk_even_iff`), and that walk is
the five-step palindrome seen in another frame (`splitWalk_conj_palindrome`). So an even dispersion
needs at least a symmetric split. That the dispersion must be even is a premise, not a theorem. -/

section StepOrder

/-- A walk read off a word: one realizable step per letter, each with its own angle. -/
noncomputable def wordWalk (w : List (Twist × ℝ)) : M := (w.map fun p => realStep p.1 p.2).prod

/-- Reversing every momentum is the adjoint of the word read backwards. -/
theorem wordWalk_neg (w : List (Twist × ℝ)) :
    wordWalk (w.map fun p => (p.1, -p.2)) = star (wordWalk w.reverse) := by
  induction w with
  | nil => simp [wordWalk]
  | cons p w ih =>
    have h1 : wordWalk ((p :: w).map fun p => (p.1, -p.2)) =
        realStep p.1 (-p.2) * wordWalk (w.map fun p => (p.1, -p.2)) := by
      simp [wordWalk]
    have h2 : wordWalk (p :: w).reverse = wordWalk w.reverse * realStep p.1 p.2 := by
      simp [wordWalk]
    rw [h1, h2, ih, star_mul, realStep_neg]

/-- **Every palindromic word has the reversal identity** `W(−k) = W(k)†`. -/
theorem palindrome_reversal (w : List (Twist × ℝ)) (hw : w.reverse = w) :
    wordWalk (w.map fun p => (p.1, -p.2)) = star (wordWalk w) := by
  rw [wordWalk_neg, hw]

/-- The one-way order: a full step up, left, slash. -/
noncomputable def oneWayWalk (ky kx kz : ℝ) : M :=
  realStep Twist.up ky * realStep Twist.left kx * realStep Twist.slash kz

/-- **The one-way walk's dispersion: `cos E = Π cos k_i + Π sin k_i`.** -/
theorem oneWayWalk_trace (ky kx kz : ℝ) :
    Matrix.trace (oneWayWalk ky kx kz) =
      2 * ((Real.cos ky * Real.cos kx * Real.cos kz +
        Real.sin ky * Real.sin kx * Real.sin kz : ℝ) : ℂ) := by
  simp only [oneWayWalk, realStep_eq_cos_sin, Twist.toMatrix, σx, σy, σz]
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Fin.isValue, smul_eq_mul]
  push_cast
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  ring_nf
  simp only [h4]
  ring

/-- **The one-way dispersion is odd under reversal by exactly `−4 Π sin k_i`.** -/
theorem oneWayWalk_trace_odd (ky kx kz : ℝ) :
    Matrix.trace (oneWayWalk (-ky) (-kx) (-kz)) - Matrix.trace (oneWayWalk ky kx kz) =
      -(4 * ((Real.sin ky * Real.sin kx * Real.sin kz : ℝ) : ℂ)) := by
  simp only [oneWayWalk_trace, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **The one-way order has no reversal identity.** -/
theorem oneWayWalk_not_reversal :
    ¬ ∀ ky kx kz : ℝ, oneWayWalk (-ky) (-kx) (-kz) = star (oneWayWalk ky kx kz) := by
  intro h
  have h1 := congrArg Matrix.trace (h (Real.pi / 2) (Real.pi / 2) (Real.pi / 2))
  rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, oneWayWalk_trace,
    oneWayWalk_trace] at h1
  simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two] at h1
  norm_num at h1

/-- A four-step walk: the up step split in two around the left step, then slash. -/
noncomputable def splitWalk (a a' b c : ℝ) : M :=
  realStep Twist.up a * realStep Twist.left b * realStep Twist.up a' * realStep Twist.slash c

/-- **The split walk's dispersion**: `cos E = cos (a + a') cos b cos c + sin (a − a') sin b sin c`. -/
theorem splitWalk_trace (a a' b c : ℝ) :
    Matrix.trace (splitWalk a a' b c) =
      2 * ((Real.cos (a + a') * Real.cos b * Real.cos c +
        Real.sin (a - a') * Real.sin b * Real.sin c : ℝ) : ℂ) := by
  rw [Real.cos_add, Real.sin_sub]
  simp only [splitWalk, realStep_eq_cos_sin, Twist.toMatrix, σx, σy, σz]
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Fin.isValue, smul_eq_mul]
  push_cast
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  ring_nf
  simp only [h4]
  ring

/-- **Even exactly when the split is equal** (or a sine vanishes). -/
theorem splitWalk_even_iff (a a' b c : ℝ) :
    Matrix.trace (splitWalk (-a) (-a') (-b) (-c)) = Matrix.trace (splitWalk a a' b c) ↔
      Real.sin (a - a') * Real.sin b * Real.sin c = 0 := by
  rw [splitWalk_trace, splitWalk_trace, show -a + -a' = -(a + a') by ring,
    show -a - -a' = -(a - a') by ring]
  simp only [Real.cos_neg, Real.sin_neg]
  constructor
  · intro h
    have h' := Complex.ofReal_injective (mul_left_cancel₀ (two_ne_zero) h)
    linarith
  · intro h
    congr 2
    linarith

/-- Steps along one twist add their angles. -/
theorem realStep_add (t : Twist) (x y : ℝ) : realStep t x * realStep t y = realStep t (x + y) := by
  simp only [realStep_eq_cos_sin, Real.cos_add, Real.sin_add]
  cases t <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [Twist.toMatrix, σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- **The equal split is the palindrome in another frame.** -/
theorem splitWalk_conj_palindrome (a b c : ℝ) :
    realStep Twist.slash (c / 2) * splitWalk a a b c =
      wordWalk [(Twist.slash, c / 2), (Twist.up, a), (Twist.left, b), (Twist.up, a),
        (Twist.slash, c / 2)] * realStep Twist.slash (c / 2) := by
  have hc : realStep Twist.slash c = realStep Twist.slash (c / 2) * realStep Twist.slash (c / 2) := by
    rw [realStep_add]; congr 1; ring
  simp only [wordWalk, splitWalk, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, hc, mul_assoc]

/-- The Lean walk is a palindromic word. -/
theorem realWalk_eq_wordWalk (ky kx kz : ℝ) :
    realWalk ky kx kz = wordWalk [(Twist.up, ky / 2), (Twist.left, kx / 2), (Twist.slash, kz / 2),
      (Twist.slash, kz / 2), (Twist.left, kx / 2), (Twist.up, ky / 2)] := by
  simp only [wordWalk, realWalk, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc]

end StepOrder

end QLF.ClosureChannels
