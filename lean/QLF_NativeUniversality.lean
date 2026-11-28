import QLF_NativeBell
import QLF_Barenco

/-!
# QLF_NativeUniversality — **native closure operations are universal on presence strands**

The rest of obligation O1 of [`Framing.md`](../Framing.md) §6. [`QLF_NativeBell`](QLF_NativeBell.lean)
put three native operations on one presence qubit (branching, joint closure, the census phase) and built
the Bell state from them. This module assembles them: on `n + 1` presence strands, every unitary is a
limit of products of native operations, up to a global scalar.

**The native operations on `n` strands** (`nativeBranch`, `nativeJoint`, `nativePhase`,
`nativeMirror`) act on census sums `ψ : St n → ℂ`, a weight on each configuration of which strands
carry a closed pair:

* *branching* strand `t`: sum over the configurations that differ from `x` only on strand `t`, each
  weighted by the joint sign of the old and new strand, read off the folds (`jointSign_eq`);
* *joint closure* of strands `c`, `t`: each configuration picks up its joint sign;
* *census phase* on strand `t`: a present strand is weighted by three alternate histories over their
  mirror, `z = (2+i)/(2−i)` (`censusRatio_eq_z`); *mirror phase*: the same ratio the other way up,
  `z̄` (`censusRatioMirror_eq_zbar`).

They are proved to be the matrices `had2` (`√2·H`), `CZ`, `diag(1, z)` and `diag(1, z̄)` on that
strand (`nativeBranch_eq`, `nativeJoint_eq`, `nativePhase_eq`, `nativeMirror_eq`).

**Results** (no axioms):

* `D_zpow_native` — every diagonal rotation `D(z^k)`, `k ∈ ℤ`, is a scalar times a product of the two
  native phases.
* `native_one_dense` — **one strand**: every `SU(2)` gate is a limit of scalar multiples of products of
  native branching and phases (from `su2_dense`).
* `cnot_native` — CNOT is `½ · had2 · CZ · had2`, exactly native up to the scalar.
* `native_universal` — **`n + 1` strands**: every unitary is a limit of scalar multiples of native
  circuits (Barenco routing, `QLF.Barenco.universality`, over native gates).

The scalar is the normalization `√2` per branching and an unobservable global phase; a census sum is
read up to its overall weight, so this is universality on rays. Approximation is in the matrix topology;
no rate is claimed (no Solovay–Kitaev bound here).
-/

namespace QLF.NativeUniversality

open Matrix QLF QLF.QuantumComputer QLF.NativeBell

/-! ## The mirror phase -/

/-- **The mirror census phase**: the same three alternate histories, the other way up. -/
noncomputable def censusRatioMirror : ℂ :=
  censusSum [[], [], [Twist.left, Twist.up, Twist.slash]] 0 0 /
    censusSum [[], [], [Twist.right, Twist.up, Twist.slash]] 0 0

theorem censusRatioMirror_eq_zbar : censusRatioMirror = zbar := by
  rw [censusRatioMirror, gauss_census, gauss_census_mirror]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have h : (2 + Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [div_eq_iff h]
  apply Complex.ext <;> simp [zbar] <;> norm_num <;> ring

theorem star_z : star z = zbar := by
  apply Complex.ext <;> simp [z, zbar] <;> ring

theorem z_inv : z⁻¹ = zbar := inv_eq_of_mul_eq_one_right z_mul_zbar

/-- The mirror phase gate `diag(1, z̄)`. -/
noncomputable def phaseZbar : M := Matrix.diagonal ![1, zbar]

/-! ## One strand: density of native gates -/

/-- The native one-strand operations: branching and the two census phases. -/
def nativeOne : Submonoid M := Submonoid.closure {had2, phaseZ, phaseZbar}

theorem had2_mem : had2 ∈ nativeOne := Submonoid.subset_closure (by simp)
theorem phaseZ_mem : phaseZ ∈ nativeOne := Submonoid.subset_closure (by simp)
theorem phaseZbar_mem : phaseZbar ∈ nativeOne := Submonoid.subset_closure (by simp)

/-- Scalar multiples of native one-strand circuits. -/
def rays1 : Set M := {X | ∃ c : ℂ, ∃ W ∈ nativeOne, X = c • W}

theorem D_z_nat (k : ℕ) : D (z ^ k) = z ^ k • phaseZbar ^ (2 * k) := by
  rw [D, phaseZbar, Matrix.diagonal_pow, ← Matrix.diagonal_smul]
  congr 1; ext i; fin_cases i
  · simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
      Pi.pow_apply, smul_eq_mul, star_pow, star_z]
    rw [pow_mul, sq, mul_pow, ← mul_assoc, ← mul_pow, z_mul_zbar, one_pow, one_mul]

theorem D_zbar_nat (k : ℕ) : D (zbar ^ k) = zbar ^ k • phaseZ ^ (2 * k) := by
  rw [D, phaseZ, Matrix.diagonal_pow, ← Matrix.diagonal_smul]
  have hs : star zbar = z := by rw [← star_z, star_star]
  congr 1; ext i; fin_cases i
  · simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
      Pi.pow_apply, smul_eq_mul, star_pow, hs]
    rw [pow_mul, sq, mul_pow, ← mul_assoc, ← mul_pow, mul_comm zbar z, z_mul_zbar, one_pow,
      one_mul]

/-- **Every diagonal rotation `D(z^k)` is native**, up to a scalar. -/
theorem D_zpow_native (k : ℤ) : ∃ c : ℂ, ∃ W ∈ nativeOne, D (z ^ k) = c • W := by
  rcases k with m | m
  · refine ⟨z ^ m, phaseZbar ^ (2 * m), pow_mem phaseZbar_mem _, ?_⟩
    rw [Int.ofNat_eq_natCast, zpow_natCast, D_z_nat]
  · refine ⟨zbar ^ (m + 1), phaseZ ^ (2 * (m + 1)), pow_mem phaseZ_mem _, ?_⟩
    rw [zpow_negSucc, ← inv_pow, z_inv, D_zbar_nat]

/-- The Euler products of `su2_dense` are native up to a scalar. -/
theorem euler_native (j k l : ℤ) : euler (z ^ j) (z ^ k) (z ^ l) ∈ rays1 := by
  obtain ⟨c₁, W₁, h₁, e₁⟩ := D_zpow_native j
  obtain ⟨c₂, W₂, h₂, e₂⟩ := D_zpow_native k
  obtain ⟨c₃, W₃, h₃, e₃⟩ := D_zpow_native l
  refine ⟨c₁ * (1 / (Real.sqrt 2 : ℂ)) * c₂ * (1 / (Real.sqrt 2 : ℂ)) * c₃,
    W₁ * had2 * W₂ * had2 * W₃,
    mul_mem (mul_mem (mul_mem (mul_mem h₁ had2_mem) h₂) had2_mem) h₃, ?_⟩
  rw [euler, e₁, e₂, e₃, hadamard_eq_had2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1; ring

/-- **Native density on one strand**: every `SU(2)` gate is a limit of scalar multiples of products
    of native branching and the two census phases. -/
theorem native_one_dense (U : M) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U ∈ closure rays1 := by
  refine closure_mono ?_ (su2_dense U hU)
  rintro _ ⟨⟨j, k, l⟩, rfl⟩
  exact euler_native j k l

/-! ## `n` strands: the native operations -/

open QLF.Barenco in
/-- **Native branching** on strand `t`. -/
noncomputable def nativeBranch {n : ℕ} (t : Fin n) (ψ : QLF.Barenco.St n → ℂ) : QLF.Barenco.St n → ℂ := fun x =>
  ∑ y, (if (∀ i, i ≠ t → x i = y i) then jointSign (decide (y t = 1)) (decide (x t = 1)) else 0)
    * ψ y

open QLF.Barenco in
/-- **Native joint closure** of strands `c` and `t`. -/
noncomputable def nativeJoint {n : ℕ} (c t : Fin n) (ψ : QLF.Barenco.St n → ℂ) : QLF.Barenco.St n → ℂ := fun x =>
  jointSign (decide (x c = 1)) (decide (x t = 1)) * ψ x

open QLF.Barenco in
/-- **Native census phase** on strand `t`. -/
noncomputable def nativePhase {n : ℕ} (t : Fin n) (ψ : QLF.Barenco.St n → ℂ) : QLF.Barenco.St n → ℂ := fun x =>
  (if x t = 1 then censusRatio else 1) * ψ x

open QLF.Barenco in
/-- **Native mirror phase** on strand `t`. -/
noncomputable def nativeMirror {n : ℕ} (t : Fin n) (ψ : QLF.Barenco.St n → ℂ) : QLF.Barenco.St n → ℂ := fun x =>
  (if x t = 1 then censusRatioMirror else 1) * ψ x

theorem had2_eq_jointSign (a b : Fin 2) : had2 a b = jointSign (decide (b = 1)) (decide (a = 1)) := by
  rw [jointSign_eq]; fin_cases a <;> fin_cases b <;> simp [had2]

open QLF.Barenco in
/-- **Native branching is `had2` on the strand.** -/
theorem nativeBranch_eq {n : ℕ} (t : Fin n) (ψ : QLF.Barenco.St n → ℂ) :
    nativeBranch t ψ = onQubit t had2 *ᵥ ψ := by
  funext x
  simp only [nativeBranch, Matrix.mulVec, dotProduct, onQubit_apply]
  congr 1; funext y
  split_ifs <;> simp [had2_eq_jointSign]

open QLF.Barenco in
theorem onQubit_diag {n : ℕ} (t : Fin n) (p q : ℂ) :
    (onQubit t (Matrix.diagonal ![p, q]) : Mat n) =
      Matrix.diagonal fun x => if x t = 1 then q else p := by
  ext x y
  rw [onQubit_apply]
  simp only [Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [ne_eq, implies_true, ↓reduceIte]
    generalize x t = a
    fin_cases a <;> simp
  · simp only [hxy, ↓reduceIte]
    by_cases ha : ∀ i, i ≠ t → x i = y i
    · have hne : x t ≠ y t := fun e => hxy (eq_of_agree ha e)
      simp [ha, hne]
    · simp [ha]

open QLF.Barenco in
/-- **Native census phase is `diag(1, z)` on the strand.** -/
theorem nativePhase_eq {n : ℕ} (t : Fin n) (ψ : QLF.Barenco.St n → ℂ) :
    nativePhase t ψ = onQubit t phaseZ *ᵥ ψ := by
  rw [phaseZ, onQubit_diag]
  funext x; rw [Matrix.mulVec_diagonal]; simp [nativePhase, censusRatio_eq_z]

open QLF.Barenco in
/-- **Native mirror phase is `diag(1, z̄)` on the strand.** -/
theorem nativeMirror_eq {n : ℕ} (t : Fin n) (ψ : QLF.Barenco.St n → ℂ) :
    nativeMirror t ψ = onQubit t phaseZbar *ᵥ ψ := by
  rw [phaseZbar, onQubit_diag]
  funext x; rw [Matrix.mulVec_diagonal]; simp [nativeMirror, censusRatioMirror_eq_zbar]

open QLF.Barenco in
/-- **Native joint closure is controlled-Z.** -/
theorem nativeJoint_eq {n : ℕ} {c t : Fin n} (hct : c ≠ t) (ψ : QLF.Barenco.St n → ℂ) :
    nativeJoint c t ψ = QLF.Barenco.cz c t *ᵥ ψ := by
  rw [cz_eq_diagonal hct]
  funext x
  rw [Matrix.mulVec_diagonal]
  simp only [nativeJoint, jointSign_eq]
  by_cases h1 : x c = 1 <;> by_cases h2 : x t = 1 <;> simp [h1, h2]

/-! ## `n` strands: native circuits are universal -/

open QLF.Barenco

/-- The native gates on `n` strands, as matrices. -/
def nativeGates (n : ℕ) : Set (Mat n) :=
  {X | ∃ t, X = onQubit t had2 ∨ X = onQubit t phaseZ ∨ X = onQubit t phaseZbar} ∪
    {X | ∃ c t, c ≠ t ∧ X = QLF.Barenco.cz c t}

/-- Native circuits: finite products of native gates. -/
def nativeCircuits (n : ℕ) : Submonoid (Mat n) := Submonoid.closure (nativeGates n)

/-- Scalar multiples of native circuits. -/
def rays (n : ℕ) : Submonoid (Mat n) where
  carrier := {X | ∃ c : ℂ, ∃ W ∈ nativeCircuits n, X = c • W}
  one_mem' := ⟨1, 1, one_mem _, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨c, W, hW, rfl⟩ ⟨c', W', hW', rfl⟩
    exact ⟨c * c', W * W', mul_mem hW hW', by rw [smul_mul_smul_comm]⟩

variable {n : ℕ}

theorem onQubit_one (t : Fin n) : (onQubit t 1 : Mat n) = 1 := by
  rw [onQubit, ctrl]; simp only [ite_self]; exact lift_one t

theorem onQubit_mul' (t : Fin n) (A B : M) :
    (onQubit t (A * B) : Mat n) = onQubit t A * onQubit t B := by
  rw [onQubit, onQubit, onQubit, ctrl_mul]

theorem onQubit_smul (t : Fin n) (c : ℂ) (A : M) :
    (onQubit t (c • A) : Mat n) = c • onQubit t A := by
  ext x y
  simp only [onQubit_apply, Matrix.smul_apply]
  split_ifs <;> simp

theorem onQubit_continuous (t : Fin n) : Continuous fun A : M => (onQubit t A : Mat n) := by
  refine continuous_matrix fun x y => ?_
  simp only [onQubit_apply]
  split_ifs
  · exact continuous_id.matrix_elem _ _
  · exact continuous_const

theorem onQubit_nativeOne (t : Fin n) {W : M} (hW : W ∈ nativeOne) :
    onQubit t W ∈ nativeCircuits n := by
  induction hW using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact Submonoid.subset_closure (Or.inl ⟨t, Or.inl rfl⟩)
    · exact Submonoid.subset_closure (Or.inl ⟨t, Or.inr (Or.inl rfl)⟩)
    · exact Submonoid.subset_closure (Or.inl ⟨t, Or.inr (Or.inr rfl)⟩)
  | one => rw [onQubit_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [onQubit_mul']; exact mul_mem hx hy

theorem smul_mem_closure_rays (c : ℂ) {X : Mat n} (hX : X ∈ closure (rays n : Set (Mat n))) :
    c • X ∈ closure (rays n : Set (Mat n)) := by
  refine map_mem_closure (continuous_const_smul c) hX ?_
  rintro _ ⟨c', W, hW, rfl⟩
  exact ⟨c * c', W, hW, by rw [smul_smul]⟩

/-- **CNOT is native**: `CNOT = ½ · had2 · CZ · had2` on the target strand. -/
theorem cnot_native {c t : Fin n} (hct : c ≠ t) : cnot c t ∈ (rays n : Set (Mat n)) := by
  have hH : QLF.Barenco.H = ((Real.sqrt 2 : ℂ)⁻¹) • had2 := rfl
  refine ⟨(Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹,
    onQubit t had2 * QLF.Barenco.cz c t * onQubit t had2,
    mul_mem (mul_mem (Submonoid.subset_closure (Or.inl ⟨t, Or.inl rfl⟩))
      (Submonoid.subset_closure (Or.inr ⟨c, t, hct, rfl⟩)))
      (Submonoid.subset_closure (Or.inl ⟨t, Or.inl rfl⟩)), ?_⟩
  rw [cnot_eq_h_cz_h, hH, onQubit_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Every one-qubit unitary on a strand is a limit of scalar multiples of native circuits. -/
theorem onQubit_native_closure (t : Fin n) {A : M} (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    onQubit t A ∈ closure (rays n : Set (Mat n)) := by
  obtain ⟨δ, W, hW, rfl⟩ := QLF.ControlledUnitary.unitary_eq_phase_smul_su2 A hA
  rw [onQubit_smul]
  refine smul_mem_closure_rays _ ?_
  refine map_mem_closure (onQubit_continuous t) (native_one_dense W hW) ?_
  rintro _ ⟨c, V, hV, rfl⟩
  exact ⟨c, onQubit t V, onQubit_nativeOne t hV, onQubit_smul t c V⟩

/-- **Native universality.** On `n + 1` presence strands every unitary is a limit of scalar
    multiples of products of native branching, census phases and joint closures. -/
theorem native_universal (U : Mat (n + 1))
    (hU : U ∈ Matrix.unitaryGroup (QLF.Barenco.St (n + 1)) ℂ) :
    U ∈ closure (rays (n + 1) : Set (Mat (n + 1))) := by
  have hle : circuits (n + 1) ≤ (rays (n + 1)).topologicalClosure := by
    rw [circuits, Submonoid.closure_le]
    rintro X (⟨t, A, hA, rfl⟩ | ⟨c, t, hct, rfl⟩)
    · exact onQubit_native_closure t hA
    · exact subset_closure (cnot_native hct)
  exact hle (universality U hU)

end QLF.NativeUniversality
