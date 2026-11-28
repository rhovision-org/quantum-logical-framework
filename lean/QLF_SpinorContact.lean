import QLF_InteractingKinematics
import QLF_Mass

/-!
# Stage 3 for a contact that carries spinor structure

Part of the [Quantum Logical Framework (QLF)](../README.md). Stage 4b
([`Relativity_Principle.md`](../Relativity_Principle.md) §6b) found that the spin-blind contact of
`twoBodyStep`, a scalar phase `g(x₁ − x₂)`, is a `J⁰ J⁰` coupling whose vertex `1 ⊗ 1` a boost does
not preserve, while the scalar vertex `β ⊗ β` is preserved by the spin action
(`QLF.BoostAmplitudes.scalar_vertex_invariant`). A contact built on that vertex, such as
`exp(i g β ⊗ β)`, is matrix-valued, and the stage-3 conservation theorems were stated for a scalar
one. This module states them for a contact that is any linear map on the joint internal space
depending only on the relative position.

Three facts are kept apart. Vertex invariance (stage 4b) is a congruence of `β ⊗ β` under the spin
action. Coin unitarity (`scalarContact_unitary`, below) says the contact is a legitimate walk step.
Translation conservation (below) says it conserves lattice momentum. None of them is boost
covariance of the interacting step: for a non-unitary boost `T = S ⊗ S`, the congruence
`Tᴴ G T = cos g · Tᴴ T + i sin g · β ⊗ β` differs from `G` in general, so whether the interacting
evolution is covariant under a suitably defined frame map is open.

* **`spinorStep`**: the two-body step with a matrix-valued contact `G (x₁ − x₂)`.
* **`spinorStep_of_scalar`**: the scalar contact of `twoBodyStep` is the special case
  `G r = g r • id`, so nothing proved here is lost for stage 3.
* **`spinorStep_translation_commute`**, **`spinorStep_conserves_momentum`**: the step commutes with
  joint translation, so it conserves total lattice momentum as a character.
* **`spinorStep_lattice_conservation`**: on `ℤ³`, a plane wave goes to a state of total momentum
  `K′` only if `k₁ + k₂ − K′` is a reciprocal vector.
* **`scalarContact_unitary`**: the stage-4b scalar contact `exp(i g β ⊗ β) = cos g + i sin g β ⊗ β`
  is unitary, so it is a legitimate walk step, and an instance of `G` above. This is not a
  statement that the contact is boost covariant.

No axioms. The proof uses only that `G` depends on the relative position, and the linearity of each
`G r`; unitarity is not needed.
-/

namespace QLF.SpinorContact

open QLF.InteractingKinematics

section General

variable {S : Type*} [AddCommGroup S] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ι : Type*} [Fintype ι]

/-- A two-body step whose contact is a linear map `G (x₁ − x₂)` on the joint internal space. -/
def spinorStep (e : ι → S) (C : ι → ι → W →ₗ[ℂ] W) (G : S → W →ₗ[ℂ] W) (ψ : S × S → W) :
    S × S → W :=
  fun x => G (x.1 - x.2) (∑ i, ∑ j, C i j (ψ (x.1 - e i, x.2 - e j)))

/-- **The scalar contact is the special case `G r = g r • id`.** -/
theorem spinorStep_of_scalar (e : ι → S) (C : ι → ι → W →ₗ[ℂ] W) (g : S → ℂ) :
    spinorStep e C (fun r => g r • LinearMap.id) = twoBodyStep e C g := by
  funext ψ x
  simp [spinorStep, twoBodyStep, Finset.smul_sum]

/-- **The matrix-contact step commutes with joint translation.** -/
theorem spinorStep_translation_commute (e : ι → S) (C : ι → ι → W →ₗ[ℂ] W) (G : S → W →ₗ[ℂ] W)
    (a : S) (ψ : S × S → W) :
    jointShift a (spinorStep e C G ψ) = spinorStep e C G (jointShift a ψ) := by
  funext x
  simp only [jointShift, spinorStep]
  have hrel : x.1 - a - (x.2 - a) = x.1 - x.2 := by abel
  rw [hrel]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  abel_nf

/-- **Total lattice momentum is conserved by the matrix-contact step.** -/
theorem spinorStep_conserves_momentum (e : ι → S) (C : ι → ι → W →ₗ[ℂ] W) (G : S → W →ₗ[ℂ] W)
    (χ : S → ℂ) (ψ : S × S → W) (hψ : ∀ a, jointShift a ψ = χ a • ψ) (a : S) :
    jointShift a (spinorStep e C G ψ) = χ a • spinorStep e C G ψ := by
  rw [spinorStep_translation_commute, hψ a]
  funext x
  simp only [spinorStep, Pi.smul_apply, map_smul, ← Finset.smul_sum]

end General

/-- **Lattice momentum conservation for a matrix-valued contact.** -/
theorem spinorStep_lattice_conservation {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ι : Type*} [Fintype ι] (e : ι → Site) (C : ι → ι → W →ₗ[ℂ] W) (G : Site → W →ₗ[ℂ] W)
    (k₁ k₂ K' : Fin 3 → ℝ) (w : W)
    (hne : spinorStep e C G (planeWave k₁ k₂ w) ≠ 0)
    (hout : ∀ a, jointShift a (spinorStep e C G (planeWave k₁ k₂ w)) =
      momChar K' a • spinorStep e C G (planeWave k₁ k₂ w)) (c : Fin 3) :
    ∃ n : ℤ, k₁ c + k₂ c - K' c = 2 * Real.pi * n := by
  have hin := spinorStep_conserves_momentum e C G (momChar (k₁ + k₂)) (planeWave k₁ k₂ w)
    (planeWave_jointShift k₁ k₂ w)
  have := momChar_eq (char_unique hne _ _ hin hout) c
  simpa using this

open Matrix Kronecker in
theorem betaBeta_herm : (QLF.Mass.beta ⊗ₖ QLF.Mass.beta)ᴴ = QLF.Mass.beta ⊗ₖ QLF.Mass.beta := by
  rw [conjTranspose_kronecker, QLF.Mass.beta_herm]

open Matrix Kronecker in
theorem betaBeta_sq :
    (QLF.Mass.beta ⊗ₖ QLF.Mass.beta) * (QLF.Mass.beta ⊗ₖ QLF.Mass.beta) = 1 := by
  rw [← mul_kronecker_mul, QLF.Mass.beta_sq, one_kronecker_one]

/-- The joint spinor space of two walk particles. -/
abbrev Q2 := Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ

open Matrix Kronecker in
/-- A two-body scalar coin `c + i s · β ⊗ β` with real `c, s`. -/
noncomputable def scalarCoin (c s : ℝ) : Q2 :=
  (c : ℂ) • (1 : Q2) + (Complex.I * (s : ℂ)) • (QLF.Mass.beta ⊗ₖ QLF.Mass.beta)

open Matrix Kronecker in
theorem scalarCoin_unitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    scalarCoin c s ∈ Matrix.unitaryGroup ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star (scalarCoin c s) =
      (c : ℂ) • (1 : Q2) - (Complex.I * (s : ℂ)) • (QLF.Mass.beta ⊗ₖ QLF.Mass.beta) := by
    rw [scalarCoin, star_add, star_smul, star_smul, star_one]
    change _ + _ • (QLF.Mass.beta ⊗ₖ QLF.Mass.beta)ᴴ = _
    rw [betaBeta_herm]
    simp [sub_eq_add_neg]
  rw [hs, scalarCoin]
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, betaBeta_sq]
  have h1 : (c : ℂ) * (c : ℂ) - (Complex.I * (s : ℂ)) * (Complex.I * (s : ℂ)) = 1 := by
    have hc : ((c ^ 2 + s ^ 2 : ℝ) : ℂ) = 1 := by rw [h]; simp
    push_cast at hc
    linear_combination hc - (s : ℂ) ^ 2 * Complex.I_sq
  calc _ = ((c : ℂ) * (c : ℂ) - (Complex.I * (s : ℂ)) * (Complex.I * (s : ℂ))) • (1 : Q2) := by
        module
    _ = 1 := by rw [h1, one_smul]

/-- The two-body scalar contact `exp(i g β ⊗ β) = cos g + i sin g · β ⊗ β`. -/
noncomputable def scalarContact (g : ℝ) : Q2 := scalarCoin (Real.cos g) (Real.sin g)

/-- **The scalar contact is unitary.** -/
theorem scalarContact_unitary (g : ℝ) :
    scalarContact g ∈ Matrix.unitaryGroup ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ :=
  scalarCoin_unitary _ _ (Real.cos_sq_add_sin_sq g)

end QLF.SpinorContact
