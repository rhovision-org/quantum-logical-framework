import QLF_DiracWalk
import QLF_LorentzCover

set_option linter.unusedVariables false

/-!
# QLF_BoostStates — **how a boost acts on the walk's states** (stage 4a)

Part of the [Quantum Logical Framework (QLF)](../README.md). See
[`Relativity_Principle.md`](../Relativity_Principle.md) §6b.

The lattice fixes one frame, so no operator on the Dirac walk's states is a boost. Stage 4 of the
relativity chain needs a frame-comparison map, and §6b records the approved one: turn each
eigenmode's spinor with the chiral action of `A ∈ SL(2,ℂ)` and land it in the walk's band at the
boosted momentum. This module proves the algebra the map rests on. No axioms.

* **`chiral R L`** acts by `R` on the right-handed part and `L` on the left-handed part, through
  the walk's own projectors `fix slash`, `fix slash̄`. It is multiplicative (**`chiral_mul`**) and
  the walk's handed step is itself one (**`handed_eq_chiral`**). The mass generator `β` swaps the
  two parts (**`beta_chiral_beta`**).
* **`chiralAct A = chiral A (Aᴴ)⁻¹`** is the spinor action. It is a homomorphism
  (**`chiralAct_mul`**, **`chiralAct_one`**), `−A` acts as `−1` times `A` (**`chiralAct_neg`**,
  the double cover), and it commutes with chirality (**`chiralAct_chirality`**). A unitary `A`
  (a rotation) acts the same way on both parts (**`chiralAct_of_unitary`**); a boost does not.
* **The half-step slice.** `halfWalk = massStep(m/2) · handed · massStep(m/2)` is the Lean walk
  conjugated by a `k`-independent unitary (**`halfWalk_eq_conj`**), so it is unitary
  (**`halfWalk_unitary`**) and has the same dispersion (**`halfWalk_dispersion`**). The
  pre-registered check (`boost_states_check.py`) found that the map is covariant to second order
  on this slice and only to first order on the raw one, so §6b's map is stated on this slice.
* **The continuum anchor.** For a boost along `z`, `S = chiral (boostZ a b) (boostZ b a)` carries
  `(E + H(k, m)) β`, the Dirac form of `p̸ + m`, exactly to the boosted one
  (**`dirac_boostZ_covariant`**). The walk's band reproduces this to `O(κ²)` on the half-step
  slice; that comparison is numerical, not proved here.
-/

namespace QLF.BoostStates

open Matrix Kronecker
open QLF.ClosureChannels QLF.DiracWalk
open QLF.Tsirelson (Q)

/-! ## The chiral action -/

/-- Act by `R` on the right-handed part and by `L` on the left-handed part. -/
noncomputable def chiral (R L : M) : Q := fix Twist.slash ⊗ₖ R + fix Twist.slash.conj ⊗ₖ L

theorem chiral_mul (R L R' L' : M) : chiral R L * chiral R' L' = chiral (R * R') (L * L') := by
  simp only [chiral, add_mul, mul_add, ← mul_kronecker_mul, fix_idem, fix_mul_conj, fix_conj_mul,
    zero_kronecker, add_zero, zero_add]

theorem chiral_one : chiral 1 1 = 1 := by
  rw [chiral, ← add_kronecker, fix_add_conj, one_kronecker_one]

theorem chiral_neg (R L : M) : chiral (-R) (-L) = -chiral R L := by
  rw [chiral, chiral, Mass.kron_neg_right, Mass.kron_neg_right, neg_add]

/-- The walk's handed step is a chiral pair: `W(k)` on the right, `W(−k)` on the left. -/
theorem handed_eq_chiral (ky kx kz : ℝ) :
    handed ky kx kz = chiral (realWalk ky kx kz) (realWalk (-ky) (-kx) (-kz)) := rfl

/-- **The mass generator swaps the handednesses.** -/
theorem beta_chiral_beta (R L : M) : Mass.beta * chiral R L * Mass.beta = chiral L R := by
  rw [chiral, mul_add, add_mul, beta_kron, beta_kron, sigmaX_fix_slash, sigmaX_fix_slash_conj,
    chiral, add_comm]

/-- **The spinor action of `A ∈ SL(2,ℂ)`**: `A` on the right-handed part, `(Aᴴ)⁻¹` on the left. -/
noncomputable def chiralAct (A : M) : Q := chiral A (Aᴴ)⁻¹

theorem chiralAct_one : chiralAct 1 = 1 := by
  rw [chiralAct, conjTranspose_one, inv_one, chiral_one]

/-- **The spinor action is a homomorphism.** -/
theorem chiralAct_mul (A B : M) : chiralAct (A * B) = chiralAct A * chiralAct B := by
  rw [chiralAct, chiralAct, chiralAct, chiral_mul, conjTranspose_mul, Matrix.mul_inv_rev]

theorem inv_neg_two (B : M) : (-B)⁻¹ = -B⁻¹ := by
  by_cases h : IsUnit B.det
  · refine Matrix.inv_eq_left_inv ?_
    rw [neg_mul_neg, Matrix.nonsing_inv_mul B h]
  · have h' : ¬ IsUnit (-B).det := by
      rwa [Matrix.det_neg, Fintype.card_fin, even_two.neg_one_pow, one_mul]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h', Matrix.nonsing_inv_apply_not_isUnit _ h, neg_zero]

/-- **The double cover**: `A` and `−A` act with opposite signs on spinors. -/
theorem chiralAct_neg (A : M) : chiralAct (-A) = -chiralAct A := by
  rw [chiralAct, chiralAct, conjTranspose_neg, inv_neg_two, chiral_neg]

/-- **The spinor action preserves handedness.** -/
theorem chiralAct_chirality (A : M) :
    chiralAct A * Mass.chirality = Mass.chirality * chiralAct A := by
  have hc : Mass.chirality = chiral 1 (-1) := by
    rw [chiral, Mass.kron_neg_right, Mass.chirality, ← fix_sub_conj, sub_eq_add_neg, add_kronecker,
      Mass.kron_neg_left]
  rw [hc, chiralAct, chiral_mul, chiral_mul, mul_one, one_mul, mul_neg_one, neg_one_mul]

/-- **A rotation acts alike on both handednesses**: for unitary `A`, the spinor action is `1 ⊗ A`. -/
theorem chiralAct_of_unitary (A : M) (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    chiralAct A = (1 : M) ⊗ₖ A := by
  have h : Aᴴ * A = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hA
  have hinv : (Aᴴ)⁻¹ = A := Matrix.inv_eq_right_inv h
  rw [chiralAct, hinv, chiral, ← add_kronecker, fix_add_conj]

/-! ## The half-step slice -/

theorem massStep_add (a b : ℝ) : Mass.massStep a * Mass.massStep b = Mass.massStep (a + b) := by
  simp only [Mass.massStep, Mass.coin]
  push_cast
  rw [Complex.cos_add, Complex.sin_add]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, Mass.beta_sq]
  have h1 : Complex.cos ↑b * Complex.cos ↑a + Complex.I * Complex.sin ↑b * (Complex.I * Complex.sin ↑a)
      = Complex.cos ↑a * Complex.cos ↑b - Complex.sin ↑a * Complex.sin ↑b := by
    linear_combination (Complex.sin ↑a * Complex.sin ↑b) * Complex.I_sq
  have h2 : Complex.cos ↑b * (Complex.I * Complex.sin ↑a) + Complex.I * Complex.sin ↑b * Complex.cos ↑a
      = Complex.I * (Complex.sin ↑a * Complex.cos ↑b + Complex.cos ↑a * Complex.sin ↑b) := by ring
  calc _ = (Complex.cos ↑b * Complex.cos ↑a + Complex.I * Complex.sin ↑b * (Complex.I * Complex.sin ↑a))
          • (1 : Q) + (Complex.cos ↑b * (Complex.I * Complex.sin ↑a) +
            Complex.I * Complex.sin ↑b * Complex.cos ↑a) • Mass.beta := by module
    _ = _ := by rw [h1, h2, mul_add]

/-- The walk read at the half-step slice: half the mass step on each side. -/
noncomputable def halfWalk (ky kx kz m : ℝ) : Q :=
  Mass.massStep (m / 2) * handed ky kx kz * Mass.massStep (m / 2)

/-- **The half-step slice is the Lean walk conjugated by a fixed unitary.** -/
theorem halfWalk_eq_conj (ky kx kz m : ℝ) :
    halfWalk ky kx kz m =
      Mass.massStep (-(m / 2)) * diracWalk ky kx kz m * Mass.massStep (m / 2) := by
  rw [halfWalk, diracWalk, ← mul_assoc, massStep_add]
  congr 3; ring

theorem halfWalk_unitary (ky kx kz m : ℝ) :
    halfWalk ky kx kz m ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (Mass.massStep_unitary _) (handed_unitary _ _ _))
    (Mass.massStep_unitary _)

/-- **Same dispersion on the half-step slice**: `cos E = cos m · Π cos k_i`. -/
theorem halfWalk_dispersion (ky kx kz m E : ℝ) (v : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0)
    (h : halfWalk ky kx kz m *ᵥ v = Complex.exp (E * Complex.I) • v) :
    Real.cos E = Real.cos m * (Real.cos ky * Real.cos kx * Real.cos kz) := by
  set w := Mass.massStep (m / 2) *ᵥ v
  have hinv : Mass.massStep (m / 2) * Mass.massStep (-(m / 2)) = 1 := by
    rw [massStep_add, add_neg_cancel]; simp [Mass.massStep, Mass.coin]
  have hw : w ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (Mass.massStep (-(m / 2)) *ᵥ ·) h0
    simp only [w, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
    rwa [massStep_add, neg_add_cancel, show Mass.massStep 0 = 1 by
      simp [Mass.massStep, Mass.coin], Matrix.one_mulVec] at this
  refine diracWalk_dispersion ky kx kz m E w hw ?_
  have h2 := congrArg (Mass.massStep (m / 2) *ᵥ ·) h
  simp only [halfWalk_eq_conj, Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h2
  rw [← mul_assoc, ← mul_assoc, hinv, one_mul] at h2
  simpa [w, Matrix.mulVec_mulVec] using h2

/-! ## The continuum anchor: a boost along `z` is exact on `p̸ + m` -/

/-- **The Dirac form of `p̸ + m` is boost covariant** for a boost along `z`, with
`a = e^{η/2}`, `b = e^{−η/2}`: `cosh η = (a² + b²)/2`, `sinh η = (a² − b²)/2`. -/
theorem dirac_boostZ_covariant (a b E ky kx kz m : ℝ) (hab : a * b = 1) :
    chiral (LorentzCover.boostZ a b) (LorentzCover.boostZ b a) *
        (((E : ℂ) • (1 : Q) + Mass.dirac ky kx kz m) * Mass.beta) *
      chiral (LorentzCover.boostZ b a) (LorentzCover.boostZ a b) =
    ((((a ^ 2 + b ^ 2) * E + (a ^ 2 - b ^ 2) * kz) / 2 : ℝ) • (1 : Q) +
        Mass.dirac ky kx (((a ^ 2 + b ^ 2) * kz + (a ^ 2 - b ^ 2) * E) / 2 : ℝ) m) *
      Mass.beta := by
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  obtain rfl : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
  simp [chiral, Mass.dirac, Mass.alpha, Mass.beta, LorentzCover.boostZ, fix, Twist.toMatrix,
    Twist.conj, σx, σy, σz, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    kroneckerMap_apply, Matrix.one_apply] <;>
  field_simp [haC] <;> ring

end QLF.BoostStates
