import Mathlib

/-!
# QLF_ControlledUnitary — controlled-U from `A·X·B·X·C`

Stage 1 of Barenco et al. (1995), *Elementary gates for quantum computation*, Phys. Rev. A
**52**, 3457, proved here for `2 × 2` matrices.

* `su2_euler`: every `W ∈ SU(2)` is `D(e^{iμ}) · R(θ) · D(e^{iν})`, with `D(w) = diag(w, w̄)`
  and `R(θ)` the real rotation (Barenco Lemma 4.1).
* `abc_decomposition`: every `W ∈ SU(2)` has `A, B, C ∈ SU(2)` with `A·B·C = 1` and
  `A·X·B·X·C = W` (Barenco Lemma 4.3).
* `unitary_eq_phase_smul_su2`: every `U ∈ U(2)` is `e^{iδ} · W` with `W ∈ SU(2)`.
* `controlled_eq_abc`: on two qubits, controlled-`W` is
  `(1 ⊗ A) · CNOT · (1 ⊗ B) · CNOT · (1 ⊗ C)` (Barenco Corollary 5.3), and
  `controlled_unitary_eq` adds the phase `diag(1, e^{iδ})` on the control for any `U ∈ U(2)`
  (Barenco Lemma 5.2).
* `su2_three_commutators`: every `W ∈ SU(2)` is a product of three group commutators
  `V·V'·V†·V'†` of `SU(2)` elements. Stage 3
  ([`QLF_Barenco`](QLF_Barenco.lean)) uses it to add controls without square roots.

No axioms beyond Lean's own. Part of the
[Quantum Logical Framework (QLF)](../README.md); write-up in
[`Barenco_Universality.md`](../Barenco_Universality.md).
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QLF.ControlledUnitary

open Matrix

/-- `2 × 2` complex matrices: one qubit. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- A phase `e^{ix}`. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp (x * Complex.I)

theorem E_add (x y : ℝ) : E (x + y) = E x * E y := by
  simp only [E]; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem E_zero : E 0 = 1 := by simp [E]

theorem E_star (x : ℝ) : star (E x) = E (-x) := by
  simp only [E]
  rw [show (star (Complex.exp (↑x * Complex.I))) = (starRingEnd ℂ) (Complex.exp (↑x * Complex.I))
    from rfl, ← Complex.exp_conj]
  congr 1; simp [Complex.conj_ofReal]

theorem E_mul_star (x : ℝ) : E x * star (E x) = 1 := by
  rw [E_star, ← E_add, add_neg_cancel, E_zero]

theorem star_E_mul (x : ℝ) : star (E x) * E x = 1 := by
  rw [mul_comm, E_mul_star]

theorem E_half_sq (x : ℝ) : E (x / 2) * E (x / 2) = E x := by
  rw [← E_add]; congr 1; ring

theorem polar (a : ℂ) : a = (‖a‖ : ℂ) * E (Complex.arg a) := by
  simp only [E]; exact (Complex.norm_mul_exp_arg_mul_I a).symm

/-- The bit flip `X`. -/
def X : M2 := !![0, 1; 1, 0]

/-- The diagonal gate `D(w) = diag(w, w̄)`. -/
def Dg (w : ℂ) : M2 := !![w, 0; 0, star w]

/-- The real rotation `R(θ)`. -/
noncomputable def Ry (θ : ℝ) : M2 :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- `iX`, used as a commutator partner. -/
def Yx : M2 := !![0, Complex.I; Complex.I, 0]

/-- The group commutator `V·W·V†·W†`. -/
def comm (V W : M2) : M2 := V * W * star V * star W

theorem X_mul_X : X * X = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]

theorem Dg_mul (u w : ℂ) : Dg u * Dg w = Dg (u * w) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dg, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem Dg_one : Dg 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dg]

theorem star_Dg (w : ℂ) : star (Dg w) = Dg (star w) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dg, Matrix.star_apply]

theorem Ry_add (a b : ℝ) : Ry a * Ry b = Ry (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Ry, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem Ry_zero : Ry 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Ry]

theorem star_Ry (a : ℝ) : star (Ry a) = Ry (-a) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Ry, Matrix.star_apply, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal]

theorem X_Ry_X (a : ℝ) : X * Ry a * X = Ry (-a) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, Ry, Matrix.mul_apply, Fin.sum_univ_two]

theorem X_Dg_X (w : ℂ) : X * Dg w * X = Dg (star w) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, Dg, Matrix.mul_apply, Fin.sum_univ_two]

theorem X_conj_mul (P Q : M2) : X * (P * Q) * X = (X * P * X) * (X * Q * X) := by
  have h : X * P * X * (X * Q * X) = X * P * (X * X) * Q * X := by simp only [mul_assoc]
  rw [h, X_mul_X, mul_one]; simp only [mul_assoc]

/-! ## Membership in `SU(2)` -/

theorem Dg_mem (x : ℝ) : Dg (E x) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_Dg, Dg_mul,
    E_mul_star, Dg_one]
  refine ⟨rfl, ?_⟩
  simp only [Dg, Matrix.det_fin_two_of, mul_zero, sub_zero]
  exact E_mul_star x

theorem Dg_I_mem : Dg Complex.I ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have : Dg Complex.I = Dg (E (Real.pi / 2)) := by
    congr 1; simp only [E]; rw [← Complex.cos_add_sin_I]; push_cast
    rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring
  rw [this]; exact Dg_mem _

theorem Ry_mem (a : ℝ) : Ry a ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_Ry, Ry_add,
    add_neg_cancel, Ry_zero]
  refine ⟨rfl, ?_⟩
  simp only [Ry, Matrix.det_fin_two_of]
  have h := Real.cos_sq_add_sin_sq a
  have : ((Real.cos a : ℂ)) * (Real.cos a : ℂ) - -(Real.sin a : ℂ) * (Real.sin a : ℂ)
      = ((Real.cos a ^ 2 + Real.sin a ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, h]; simp

theorem Yx_mem : Yx ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Yx, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [Yx, Matrix.det_fin_two_of]

/-! ## Euler angles (Barenco Lemma 4.1) -/

theorem euler_entries (u w : ℂ) (θ : ℝ) : Dg u * Ry θ * Dg w =
    !![u * w * (Real.cos θ : ℂ), -(u * star w * (Real.sin θ : ℂ));
       star u * w * (Real.sin θ : ℂ), star u * star w * (Real.cos θ : ℂ)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Dg, Ry, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The shape of an `SU(2)` matrix: `[[a, −b̄], [b, ā]]` with `|a|² + |b|² = 1`. -/
theorem su2_shape (U : M2) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U 1 1 = star (U 0 0) ∧ U 0 1 = -star (U 1 0) ∧
      Complex.normSq (U 0 0) + Complex.normSq (U 1 0) = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hU
  obtain ⟨hu, hdet⟩ := hU
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hsU
  have hadj : star U = Matrix.adjugate U := by
    rw [← hinv, Matrix.inv_def, hdet]; simp
  rw [Matrix.adjugate_fin_two] at hadj
  have e00 := congrArg (fun A : M2 => A 0 0) hadj
  have e01 := congrArg (fun A : M2 => A 1 0) hadj
  have n00 := congrArg (fun A : M2 => A 0 0) hsU
  simp [Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 n00
  refine ⟨e00.symm, ?_, ?_⟩
  · have := congrArg star e01; simp at this; rw [this]; simp
  · apply Complex.ofReal_injective
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    exact n00

/-- **Euler angles.** Every `SU(2)` matrix is `D(e^{iμ}) · R(θ) · D(e^{iν})`. -/
theorem su2_euler (W : M2) (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ μ θ ν : ℝ, W = Dg (E μ) * Ry θ * Dg (E ν) := by
  obtain ⟨h11, h01, hn⟩ := su2_shape W hW
  set a := W 0 0 with ha_def
  set b := W 1 0 with hb_def
  have hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; exact hn
  have ha1 : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
  set θ := Real.arccos ‖a‖
  have hc : Real.cos θ = ‖a‖ := Real.cos_arccos (by linarith [norm_nonneg a]) ha1
  have hs : Real.sin θ = ‖b‖ := by
    rw [Real.sin_arccos, show 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg b)
  refine ⟨(Complex.arg a - Complex.arg b) / 2, θ, (Complex.arg a + Complex.arg b) / 2, ?_⟩
  rw [euler_entries, hc, hs, E_star, E_star, ← E_add, ← E_add, ← E_add, ← E_add]
  have e1 : (Complex.arg a - Complex.arg b) / 2 + (Complex.arg a + Complex.arg b) / 2
      = Complex.arg a := by ring
  have e2 : (Complex.arg a - Complex.arg b) / 2 + -((Complex.arg a + Complex.arg b) / 2)
      = -Complex.arg b := by ring
  have e3 : -((Complex.arg a - Complex.arg b) / 2) + (Complex.arg a + Complex.arg b) / 2
      = Complex.arg b := by ring
  have e4 : -((Complex.arg a - Complex.arg b) / 2) + -((Complex.arg a + Complex.arg b) / 2)
      = -Complex.arg a := by ring
  rw [e1, e2, e3, e4, ← E_star, ← E_star]
  have pa := polar a
  have pb := polar b
  have q1 : a = E (Complex.arg a) * ‖a‖ := by rw [mul_comm]; exact pa
  have q3 : b = E (Complex.arg b) * ‖b‖ := by rw [mul_comm]; exact pb
  have q2 : -star b = -(star (E (Complex.arg b)) * ‖b‖) := by
    nth_rewrite 1 [q3]; simp
  have q4 : star a = star (E (Complex.arg a)) * ‖a‖ := by
    nth_rewrite 1 [q1]; simp
  rw [Matrix.eta_fin_two W, h01, h11, ← q1, ← q2, ← q3, ← q4]

/-! ## `A·X·B·X·C` (Barenco Lemma 4.3) -/

/-- **The ABC decomposition.** For every `W ∈ SU(2)` there are `A, B, C ∈ SU(2)` with
`A·B·C = 1` and `A·X·B·X·C = W`. -/
theorem abc_decomposition (W : M2) (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ A B C : M2, A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ C ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      A * B * C = 1 ∧ A * X * B * X * C = W := by
  obtain ⟨μ, θ, ν, rfl⟩ := su2_euler W hW
  refine ⟨Dg (E μ) * Ry (θ / 2), Ry (-(θ / 2)) * Dg (E (-(ν + μ) / 2)), Dg (E ((ν - μ) / 2)),
    Submonoid.mul_mem _ (Dg_mem _) (Ry_mem _), Submonoid.mul_mem _ (Ry_mem _) (Dg_mem _),
    Dg_mem _, ?_, ?_⟩
  · have : Dg (E μ) * Ry (θ / 2) * (Ry (-(θ / 2)) * Dg (E (-(ν + μ) / 2))) * Dg (E ((ν - μ) / 2))
        = Dg (E μ) * (Ry (θ / 2) * Ry (-(θ / 2))) * (Dg (E (-(ν + μ) / 2)) * Dg (E ((ν - μ) / 2))) :=
      by simp only [mul_assoc]
    rw [this, Ry_add, add_neg_cancel, Ry_zero, mul_one, Dg_mul, Dg_mul, ← E_add, ← E_add]
    have : μ + (-(ν + μ) / 2 + (ν - μ) / 2) = 0 := by ring
    rw [this, E_zero, Dg_one]
  · have : Dg (E μ) * Ry (θ / 2) * X * (Ry (-(θ / 2)) * Dg (E (-(ν + μ) / 2))) * X
        * Dg (E ((ν - μ) / 2))
        = Dg (E μ) * Ry (θ / 2) * (X * (Ry (-(θ / 2)) * Dg (E (-(ν + μ) / 2))) * X)
          * Dg (E ((ν - μ) / 2)) := by simp only [mul_assoc]
    rw [this, X_conj_mul, X_Ry_X, X_Dg_X, E_star, neg_neg]
    have : Dg (E μ) * Ry (θ / 2) * (Ry (θ / 2) * Dg (E (-(-(ν + μ) / 2))))
        * Dg (E ((ν - μ) / 2))
        = Dg (E μ) * (Ry (θ / 2) * Ry (θ / 2)) * (Dg (E (-(-(ν + μ) / 2))) * Dg (E ((ν - μ) / 2))) :=
      by simp only [mul_assoc]
    rw [this, Ry_add, Dg_mul, ← E_add, add_halves]
    congr 3; ring

/-! ## Phases: `U(2) = e^{iδ} · SU(2)` -/

theorem unitary_eq_phase_smul_su2 (U : M2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ δ : ℝ, ∃ W : M2, W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ U = E δ • W := by
  set d := U.det
  have hd : ‖d‖ = 1 := by
    have h : d * star d = 1 := (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary hU)).2
    have : (‖d‖ : ℂ) ^ 2 = 1 := by
      rw [← Complex.mul_conj']; exact h
    have h2 : ‖d‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith [norm_nonneg d]
  refine ⟨Complex.arg d / 2, E (-(Complex.arg d / 2)) • U, ?_, ?_⟩
  · rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    have hU' := Matrix.mem_unitaryGroup_iff.mp hU
    constructor
    · rw [star_smul, smul_mul_smul_comm, hU', E_mul_star, one_smul]
    · have h2 : E (-(Complex.arg d / 2)) ^ 2 = E (-Complex.arg d) := by
        rw [pow_two, ← E_add]; congr 1; ring
      rw [Matrix.det_smul, Fintype.card_fin, h2]
      change E (-Complex.arg d) * d = 1
      have hp := polar d
      rw [hd, Complex.ofReal_one, one_mul] at hp
      calc E (-Complex.arg d) * d = E (-Complex.arg d) * E (Complex.arg d) := 
            congrArg (fun w => E (-Complex.arg d) * w) hp
        _ = 1 := by rw [← E_add, neg_add_cancel, E_zero]
  · rw [smul_smul, ← E_add, add_neg_cancel, E_zero, one_smul]

/-! ## Controlled-`U` on two qubits (Barenco Corollary 5.3, Lemma 5.2)

A two-qubit matrix is indexed by `(target, control)`. A gate on the target alone is
block-diagonal with equal blocks; controlled-`V` has blocks `1` (control `0`) and `V`
(control `1`). -/

/-- Two-qubit matrices, indexed by `(target, control)`. -/
abbrev M4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- `1 ⊗ A`: the gate `A` on the target qubit. -/
def onTarget (A : M2) : M4 := Matrix.blockDiagonal fun _ => A

/-- Controlled-`V`: `V` on the target when the control is `1`. `ctrl2 X` is CNOT. -/
def ctrl2 (V : M2) : M4 := Matrix.blockDiagonal fun c => if c = 0 then 1 else V

/-- The phase gate `diag(1, e^{iδ})` on the control qubit. -/
noncomputable def phaseOnControl (δ : ℝ) : M4 :=
  Matrix.blockDiagonal fun c => if c = 0 then 1 else E δ • (1 : M2)

/-- **Controlled-`W` from two CNOTs.** For `W ∈ SU(2)`, controlled-`W` is
`(1⊗A)·CNOT·(1⊗B)·CNOT·(1⊗C)`. -/
theorem controlled_eq_abc (W : M2) (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ A B C : M2, A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ C ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      ctrl2 W = onTarget A * ctrl2 X * onTarget B * ctrl2 X * onTarget C := by
  obtain ⟨A, B, C, hA, hB, hC, h1, h2⟩ := abc_decomposition W hW
  refine ⟨A, B, C, hA, hB, hC, ?_⟩
  simp only [ctrl2, onTarget, ← Matrix.blockDiagonal_mul]
  congr 1; funext c; fin_cases c
  · simp [h1]
  · simp [h2]

/-- **Controlled-`U` for every `U ∈ U(2)`**: a phase on the control, then the ABC network. -/
theorem controlled_unitary_eq (U : M2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ δ : ℝ, ∃ A B C : M2, A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ C ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      ctrl2 U = phaseOnControl δ * onTarget A * ctrl2 X * onTarget B * ctrl2 X * onTarget C := by
  obtain ⟨δ, W, hW, rfl⟩ := unitary_eq_phase_smul_su2 U hU
  obtain ⟨A, B, C, hA, hB, hC, h1, h2⟩ := abc_decomposition W hW
  refine ⟨δ, A, B, C, hA, hB, hC, ?_⟩
  simp only [ctrl2, onTarget, phaseOnControl, ← Matrix.blockDiagonal_mul]
  congr 1; funext c; fin_cases c
  · simp [h1]
  · simp [h2]

/-! ## Commutators

`D(w)` is the commutator of `D(√w)` with `iX`, and `R(θ)` is the commutator of `R(θ/2)` with
`iZ = D(i)`. With the Euler angles this writes every `SU(2)` matrix as three commutators. -/

theorem comm_Dg_Yx (w : ℂ) : comm (Dg w) Yx = Dg (w * w) := by
  rw [comm, star_Dg]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Dg, Yx, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;> ring_nf <;>
    simp [Complex.I_sq]

theorem comm_Ry_DgI (a : ℝ) : comm (Ry a) (Dg Complex.I) = Ry (2 * a) := by
  rw [comm, star_Dg, star_Ry]
  have c2 : Real.cos (2 * a) = Real.cos a ^ 2 - Real.sin a ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']; ring
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Dg, Ry, Matrix.mul_apply, Fin.sum_univ_two, Real.sin_two_mul, c2] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- **Every `SU(2)` matrix is a product of three commutators of `SU(2)` matrices.** -/
theorem su2_three_commutators (W : M2) (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ V₁ V₁' V₂ V₂' V₃ V₃' : M2,
      V₁ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ V₁' ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      V₂ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ V₂' ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      V₃ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ V₃' ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      W = comm V₁ V₁' * comm V₂ V₂' * comm V₃ V₃' := by
  obtain ⟨μ, θ, ν, rfl⟩ := su2_euler W hW
  refine ⟨Dg (E (μ / 2)), Yx, Ry (θ / 2), Dg Complex.I, Dg (E (ν / 2)), Yx,
    Dg_mem _, Yx_mem, Ry_mem _, Dg_I_mem, Dg_mem _, Yx_mem, ?_⟩
  rw [comm_Dg_Yx, comm_Dg_Yx, comm_Ry_DgI, E_half_sq, E_half_sq,
    show 2 * (θ / 2) = θ by ring]

end QLF.ControlledUnitary
