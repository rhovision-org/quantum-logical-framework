import QLF_BoostStates

/-!
# Stage 4b: which contact vertices the frame-comparison map preserves

Part of the [Quantum Logical Framework (QLF)](../README.md). Stage 4b of the relativity dependency
chain ([`Relativity_Principle.md`](../Relativity_Principle.md) §6b) compares tree amplitudes of the
two-body contact walk between frames. A tree amplitude of a contact phase `exp(i g Γ)` is the
matrix element of `Γ` between the two particles' spinors, so whether it is frame independent is
first a question about `Γ`: does the spin part of the approved map, `S = chiralAct A`, preserve it?

* **`chiral_conjTranspose`**: the adjoint of `chiral R L` is `chiral Rᴴ Lᴴ`.
* **`scalar_bilinear_invariant`**: for every `A` with invertible determinant,
  `Sᴴ β S = β`. The scalar density `ψ†βψ = ψ̄ψ` is the same in every frame.
* **`scalar_vertex_invariant`**: so the two-body scalar vertex `β ⊗ β` is preserved by
  `S ⊗ S`: the tree amplitude of a `ψ̄ψ ψ̄ψ` contact is frame independent, up to the band's own
  `O(κ²)` defect (stage 4a).
* **`blind_density_not_invariant`**: for a boost along `z` with `a·b = 1` and `a² ≠ 1`,
  `Sᴴ S ≠ 1`. The spin-blind density `ψ†ψ` changes with the frame.
* **`blind_vertex_not_invariant`**: so the spin-blind two-body vertex `1 ⊗ 1`, the scalar phase
  `g(x₁ − x₂)` of `QLF_InteractingKinematics.twoBodyStep`, is not preserved by any such boost.
  This is the continuum fact that `J⁰ J⁰` is not a Lorentz scalar; the lattice plays no part.

The numerical side, the pre-registered `boost_amplitudes_check.py`, measures the full spin-summed
amplitudes on the walk. No axioms.
-/

namespace QLF.BoostAmplitudes

open Matrix Kronecker
open QLF.ClosureChannels QLF.DiracWalk QLF.BoostStates QLF.LorentzCover
open QLF.Tsirelson (Q)

theorem chiral_conjTranspose (R L : M) : (chiral R L)ᴴ = chiral Rᴴ Lᴴ := by
  rw [chiral, chiral, conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker,
    fix_herm, fix_herm]

theorem beta_mul_chiral (R L : M) : Mass.beta * chiral R L = chiral L R * Mass.beta := by
  rw [← beta_chiral_beta R L, mul_assoc _ Mass.beta Mass.beta, Mass.beta_sq, mul_one]

/-- **The scalar density is frame independent**: `Sᴴ β S = β`. -/
theorem scalar_bilinear_invariant (A : M) (hA : IsUnit A.det) :
    (chiralAct A)ᴴ * Mass.beta * chiralAct A = Mass.beta := by
  have hAh : IsUnit (Aᴴ).det := by rw [det_conjTranspose]; exact hA.star
  have h1 : Aᴴ * (Aᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hAh
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  have h3 : ((Aᴴ)⁻¹)ᴴ = A⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_conjTranspose]
  rw [chiralAct, chiral_conjTranspose, h3, mul_assoc, beta_mul_chiral, ← mul_assoc, chiral_mul,
    h1, h2, chiral_one, one_mul]

/-- **The scalar contact vertex `β ⊗ β` is preserved by the two-body spin action.** -/
theorem scalar_vertex_invariant (A : M) (hA : IsUnit A.det) :
    (chiralAct A ⊗ₖ chiralAct A)ᴴ * (Mass.beta ⊗ₖ Mass.beta) * (chiralAct A ⊗ₖ chiralAct A) =
      Mass.beta ⊗ₖ Mass.beta := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
    scalar_bilinear_invariant A hA]

/-- The `z`-boost's spin action, written out. -/
theorem chiralAct_boostZ (a b : ℝ) (hab : a * b = 1) :
    chiralAct (boostZ a b) = chiral (boostZ a b) (boostZ b a) := by
  have h : boostZ a b * boostZ b a = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [boostZ, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.ofReal_mul, hab, mul_comm b a]
  rw [chiralAct, boostZ_self_adj, Matrix.inv_eq_right_inv h]

/-- One entry of `Sᴴ S` for a `z`-boost: the right-handed spin-up component is scaled by `a²`. -/
theorem blind_density_entry (a b : ℝ) (hab : a * b = 1) :
    ((chiralAct (boostZ a b))ᴴ * chiralAct (boostZ a b)) (0, 0) (0, 0) = ((a : ℂ)) ^ 2 := by
  rw [chiralAct_boostZ a b hab, chiral_conjTranspose, boostZ_self_adj, boostZ_self_adj, chiral_mul]
  simp [chiral, fix, Twist.toMatrix, Twist.conj, σz, boostZ, kroneckerMap_apply]
  ring

theorem sq_ne_one_C {a : ℝ} (ha : a ^ 2 ≠ 1) : ((a : ℂ)) ^ 2 ≠ 1 := by
  intro h; apply ha; exact_mod_cast h

/-- **The spin-blind density is frame dependent**: a genuine `z`-boost has `Sᴴ S ≠ 1`. -/
theorem blind_density_not_invariant (a b : ℝ) (hab : a * b = 1) (ha : a ^ 2 ≠ 1) :
    (chiralAct (boostZ a b))ᴴ * chiralAct (boostZ a b) ≠ 1 := by
  intro h
  have h00 := blind_density_entry a b hab
  rw [h, Matrix.one_apply_eq] at h00
  exact sq_ne_one_C ha h00.symm

/-- **The spin-blind contact vertex `1 ⊗ 1` is not preserved by a genuine boost.** -/
theorem blind_vertex_not_invariant (a b : ℝ) (hab : a * b = 1) (ha : a ^ 2 ≠ 1) :
    (chiralAct (boostZ a b) ⊗ₖ chiralAct (boostZ a b))ᴴ * ((1 : Q) ⊗ₖ (1 : Q)) *
        (chiralAct (boostZ a b) ⊗ₖ chiralAct (boostZ a b)) ≠ (1 : Q) ⊗ₖ (1 : Q) := by
  rw [one_kronecker_one, mul_one, conjTranspose_kronecker, ← mul_kronecker_mul]
  intro h
  have h00 := congrFun (congrFun h ((0, 0), (0, 0))) ((0, 0), (0, 0))
  rw [kroneckerMap_apply, Matrix.one_apply_eq, blind_density_entry a b hab] at h00
  have hpos : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  apply ha
  have h4 : (a ^ 2) * (a ^ 2) = (1 : ℝ) := by exact_mod_cast h00
  nlinarith [sq_nonneg (a ^ 2 - 1)]

end QLF.BoostAmplitudes
