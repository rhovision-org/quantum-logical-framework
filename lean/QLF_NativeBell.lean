import QLF_QuantumComputer

/-!
# QLF_NativeBell — **a Bell state from native closure operations on one presence qubit**

Obligation O1 of [`Framing.md`](../Framing.md) §3: the Hadamard of `QLF_QuantumComputer` acts on the
spinor space that folds live in, while the controlled-Z sign table (`joint_closure_is_cz`) acts on the
*presence* of a closed pair. They did not act on one encoded qubit. This module puts both on the
presence qubit and builds the Bell state from them.

**The encoding.** A qubit is a strand that carries a closed pair or nothing (`presence_bit_is_fold_sign`):
strand A the x-pair `> <`, strand B the y-pair `^ v`. A two-qubit state is a census sum of alternate
configurations, a weight `ψ a b : ℂ` on each pair of strand histories (`QLF_QuantumComputer` §3a:
superposition is alternate histories).

**The one native sign.** `jointSign a b` is read off the folds: the `(0,0)` entry of the interleaved joint
history times that of the separated one. It is *proved*, not defined, to be `(−1)^{ab}`
(`jointSign_eq`), because `σx` and `σy` anticommute.

**The native operations**, each linear on census sums:

* `nativeCZ` — close the two strands jointly (interleaved): each configuration picks up its joint sign.
* `nativeHA`, `nativeHB` — *branch*: a strand is replaced by both of its alternatives (empty, or a
  pair), each weighted by its joint sign with the old strand.

The branching rule is the encoding choice and is stated as one; what is not imported is the sign table,
which comes from the folds, or the gate semantics, which are checked against the standard matrices
afterwards.

**Results** (no axioms):

* `nativeCZ_eq_cz`, `nativeHA_eq`, `nativeHB_eq` — on the standard basis the native operations are
  `CZ`, `had2 ⊗ 1` and `1 ⊗ had2`, where `hadamard = (1/√2) · had2` (`hadamard_eq_had2`):
  `T_U(E ψ) = E(U ψ)` up to the normalization `√2`.
* `native_bell` — the native circuit `H_B · CZ · H_B · H_A` takes `|00⟩` to `2(|00⟩ + |11⟩)`, integer
  weights, relative phase `+1`.
* `native_bell_matches_circuit` — the same vector is the standard circuit `hB · CZ · hB · hA |00⟩`,
  that is `(√2)³` times `CNOT (H ⊗ 1) |00⟩`.
* `native_bell_not_product` — it is entangled: no product of one-strand weights gives it.
* `native_bell_x_correlated` — after the native Hadamard on both strands it is again perfectly
  correlated, `4(|00⟩ + |11⟩)`: correlation in two bases, which no product state has.

**Still open (the rest of O1).** A native non-Clifford phase on the presence qubit. Hadamard and CZ give
only the Clifford group; universality needs, for example, the count-weighted rotation `diag(z, z̄)` or
`T` acting on presence rather than on the spinor.
-/

namespace QLF.NativeBell

open QLF QLF.QuantumComputer Matrix

/-- Weights on the four configurations of two presence strands. -/
abbrev St := Bool → Bool → ℂ

/-- **The joint sign, read off the folds.** -/
noncomputable def jointSign (a b : Bool) : ℂ :=
  twistMatrixFold (interleaved a b) 0 0 * twistMatrixFold (separated a b) 0 0

/-- The joint sign is `(−1)^{ab}`: proved from the folds, not assumed. -/
theorem jointSign_eq (a b : Bool) : jointSign a b = if a && b then -1 else 1 := by
  have h := congrFun (congrFun (joint_closure_is_cz a b) 0) 0
  have hs : twistMatrixFold (separated a b) 0 0 * twistMatrixFold (separated a b) 0 0 = 1 := by
    cases a <;> cases b <;>
      simp [separated, twistMatrixFold, Twist.toMatrix, σx, σy, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [jointSign, h, mul_assoc, hs, mul_one]

/-- Native controlled-Z: close the strands jointly. -/
noncomputable def nativeCZ (ψ : St) : St := fun a b => jointSign a b * ψ a b

/-- Native branching on strand A. -/
noncomputable def nativeHA (ψ : St) : St := fun a' b => ∑ a : Bool, jointSign a a' * ψ a b

/-- Native branching on strand B. -/
noncomputable def nativeHB (ψ : St) : St := fun a b' => ∑ b : Bool, jointSign b b' * ψ a b

/-- The configuration `|ab⟩`. -/
def basis (a b : Bool) : St := fun x y => if x = a ∧ y = b then 1 else 0

/-- The native Bell circuit, `H_B · CZ · H_B · H_A` on `|00⟩`. -/
noncomputable def bellNative : St :=
  nativeHB (nativeCZ (nativeHB (nativeHA (basis false false))))

/-- **The Bell state from native operations**: `2(|00⟩ + |11⟩)`. -/
theorem native_bell : bellNative = fun a b => if a = b then 2 else 0 := by
  funext a b
  cases a <;> cases b <;>
    simp only [bellNative, nativeHB, nativeCZ, nativeHA, Fintype.sum_bool, basis, jointSign_eq] <;>
    norm_num

/-- **Entangled**: no product of one-strand weights equals the native Bell state. -/
theorem native_bell_not_product : ¬ ∃ u v : Bool → ℂ, ∀ a b, bellNative a b = u a * v b := by
  rintro ⟨u, v, h⟩
  have e1 : u false * v false = 2 := by have := h false false; rw [native_bell] at this; simpa using this.symm
  have e2 : u true * v true = 2 := by have := h true true; rw [native_bell] at this; simpa using this.symm
  have e3 : u false * v true = 0 := by have := h false true; rw [native_bell] at this; simpa using this.symm
  have : (u false * v false) * (u true * v true) = (u false * v true) * (u true * v false) := by ring
  rw [e1, e2, e3] at this
  norm_num at this

/-- **Correlated in a second basis**: after native branching on both strands the state is
    `4(|00⟩ + |11⟩)` again. -/
theorem native_bell_x_correlated :
    nativeHA (nativeHB bellNative) = fun a b => if a = b then 4 else 0 := by
  rw [native_bell]
  funext a b
  cases a <;> cases b <;>
    simp only [nativeHA, nativeHB, Fintype.sum_bool, jointSign_eq] <;> norm_num

-- ==========================================
-- Agreement with the standard gate matrices
-- ==========================================

/-- Read a census state as a vector on the basis `|ij⟩`, `i j : Fin 2`. -/
def toVec (ψ : St) : Fin 2 × Fin 2 → ℂ := fun p => ψ (p.1 = 1) (p.2 = 1)

/-- The unnormalized Hadamard `[[1, 1], [1, −1]]`; the standard one is `hadamard = (1/√2) · had2`. -/
def had2 : M := !![1, 1; 1, -1]

theorem hadamard_eq_had2 : hadamard = (1 / (Real.sqrt 2 : ℂ)) • had2 := rfl

/-- `had2 ⊗ 1` and `1 ⊗ had2` on the basis `|ij⟩`. -/
noncomputable def hA : M4 := Matrix.kroneckerMap (· * ·) had2 (1 : M)
noncomputable def hB : M4 := Matrix.kroneckerMap (· * ·) (1 : M) had2

/-- **Native controlled-Z is `CZ`.** -/
theorem nativeCZ_eq_cz (ψ : St) : toVec (nativeCZ ψ) = cz *ᵥ toVec ψ := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [toVec, nativeCZ, jointSign_eq, cz, Matrix.mulVec_diagonal]

/-- **Native branching on A is `H ⊗ 1`**, unnormalized (`√2 (H ⊗ 1)`). -/
theorem nativeHA_eq (ψ : St) : toVec (nativeHA ψ) = hA *ᵥ toVec ψ := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [toVec, nativeHA, jointSign_eq, hA, had2, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply] <;>
    ring

/-- **Native branching on B is `1 ⊗ H`**, unnormalized (`√2 (1 ⊗ H)`). -/
theorem nativeHB_eq (ψ : St) : toVec (nativeHB ψ) = hB *ᵥ toVec ψ := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [toVec, nativeHB, jointSign_eq, hB, had2, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply] <;>
    ring

/-- **The native circuit is the standard one**: the native Bell state is
    `hB · CZ · hB · hA |00⟩` with the unnormalized Hadamard, that is `(√2)³` times
    `CNOT (H ⊗ 1) |00⟩`, since `CNOT = (1 ⊗ H) CZ (1 ⊗ H)` and `hadamard = (1/√2) · had2`. -/
theorem native_bell_matches_circuit :
    toVec bellNative = hB *ᵥ (cz *ᵥ (hB *ᵥ (hA *ᵥ toVec (basis false false)))) := by
  rw [bellNative, nativeHB_eq, nativeCZ_eq_cz, nativeHB_eq, nativeHA_eq]

-- ==========================================
-- A native non-Clifford phase on the presence qubit
-- ==========================================

/-- **The census phase.** Three alternate histories over their mirror (`gauss_census`,
    `gauss_census_mirror`): a count-weighted ratio read off folds, not a chosen number. -/
noncomputable def censusRatio : ℂ :=
  censusSum [[], [], [Twist.right, Twist.up, Twist.slash]] 0 0 /
    censusSum [[], [], [Twist.left, Twist.up, Twist.slash]] 0 0

theorem censusRatio_eq_z : censusRatio = z := by
  rw [censusRatio, gauss_census, gauss_census_mirror, z_eq_ratio]
  simp

/-- Native phase on strand A: a present strand is weighted by the census phase. -/
noncomputable def nativePA (ψ : St) : St := fun a b => (if a then censusRatio else 1) * ψ a b

/-- The phase gate `diag(1, z)`. -/
noncomputable def phaseZ : M := Matrix.diagonal ![1, z]
noncomputable def pA : M4 := Matrix.kroneckerMap (· * ·) phaseZ (1 : M)

/-- **The native phase is `diag(1, z) ⊗ 1`.** -/
theorem nativePA_eq (ψ : St) : toVec (nativePA ψ) = pA *ᵥ toVec ψ := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [toVec, nativePA, censusRatio_eq_z, pA, phaseZ, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.diagonal]

/-- **It is not Clifford**: no positive power of the native phase is the identity. -/
theorem nativePhase_infinite_order (n : ℕ) (hn : 1 ≤ n) : censusRatio ^ n ≠ 1 := by
  rw [censusRatio_eq_z]
  exact z_pow_ne_one n hn

/-- **Even powers are the rotations of `su2_dense`, up to a global phase**:
    `diag(1, z)^{2k} = z^k · diag(z̄^k, z^k)`, the rotation `D(z̄^k)` about the `z` axis. -/
theorem phaseZ_even_power (k : ℕ) :
    phaseZ ^ (2 * k) = z ^ k • Matrix.diagonal ![zbar ^ k, z ^ k] := by
  rw [phaseZ, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, pow_mul]
  · rw [← mul_pow, z_mul_zbar, one_pow]
  · rw [sq, mul_pow]

end QLF.NativeBell
