import QLF_OpticalTheorem

/-!
# QLF_PoleFactorization — poles of the channel resolvent and their factorized residues (PZ2)

Issue #207, target **PZ2**: *for a simple pole of the closure resolvent, the residue factors into
left and right amplitudes through intermediate channels.* The resolvent of a channel matrix `K` is
`G(z) = (1 − zK)⁻¹ = Σ zⁿ Kⁿ`, the generating function of `n`-fold propagation.

**General finite channel space.**

* **`pole_part`.** If `P` is an idempotent with `K P = P K = λ P` (the projector of an eigenvalue),
  then wherever `G(z)` inverts `1 − zK`: `G(z) P = P G(z) = P / (1 − zλ)`. The whole `λ`-pole of the
  resolvent is `P / (1 − zλ)`, and `G = P/(1 − zλ) + (1 − P) G (1 − P)`, the second term the
  resolvent on the complement (`regular_part`).
* **`residue_through_channels`.** The residue matrix factors through intermediate channels:
  `P_if = Σ_c P_ic P_cf`.
* **`rankOne_projector`.** For a simple eigenvalue with right vector `r`, left vector `ℓ`, `ℓ·r = 1`,
  the projector is `P_if = r_i ℓ_f`: the residue is the amplitude into the intermediate state times
  the amplitude out of it.

**Unitary `2 × 2` channel steps** (the realizable walk at each momentum, the light-cone step):

* **`exists_eigs`.** Eigenvalues `μ₁, μ₂` with `μ₁ + μ₂ = tr W`, `μ₁ μ₂ = det W` exist.
* **`resolvent_partial`.** For distinct eigenvalues,
  `(1 − zW)(P₁/(1 − zμ₁) + P₂/(1 − zμ₂)) = 1` exactly, with `Pₖ = (W − μⱼ)/(μₖ − μⱼ)`: the
  resolvent has simple poles at `z = μ₁⁻¹, μ₂⁻¹` and nowhere else.
* **`eig_unit`.** For unitary `W` each eigenvalue has `|μ| = 1`: **the poles lie on the unit
  circle**, `z = e^{−iω}`. A pole is a propagating mode at the step's dispersion relation, which is
  the finite form of a particle going on shell.
* **`proj_idem`, `proj_det`.** Each residue `Pₖ` is idempotent and has determinant `0`, so it is a
  rank-one channel matrix that factors through intermediate channels.

No axioms. The analytic rendering (`z` as `e^{−iω}` with `ω` the energy, and the continuum limit
of the pole into a Feynman propagator) is the open part of PZ2.

**Credit.** The resolvent and spectral projector are standard linear algebra (the Riesz projector
for a simple eigenvalue); pole factorization is the S-matrix programme's (Eden, Landshoff, Olive
and Polkinghorne, *The Analytic S-Matrix*, Cambridge, 1966). Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.PoleFactorization

open Matrix Complex ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The pole part on a finite channel space -/

/-- **The `λ`-pole of the resolvent is `P / (1 − zλ)`.** -/
theorem pole_part (K P G : Matrix ι ι ℂ) (lam z : ℂ) (hKP : K * P = lam • P)
    (hPK : P * K = lam • P) (hG : (1 - z • K) * G = 1) (hG' : G * (1 - z • K) = 1)
    (hz : 1 - z * lam ≠ 0) :
    G * P = (1 - z * lam)⁻¹ • P ∧ P * G = (1 - z * lam)⁻¹ • P := by
  have h1 : (1 - z • K) * P = (1 - z * lam) • P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hKP, smul_smul, sub_smul, one_smul]
  have h2 : P * (1 - z • K) = (1 - z * lam) • P := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hPK, smul_smul, sub_smul, one_smul]
  constructor
  · have : G * ((1 - z • K) * P) = P := by rw [← Matrix.mul_assoc, hG', Matrix.one_mul]
    rw [h1, Matrix.mul_smul] at this
    calc G * P = (1 - z * lam)⁻¹ • ((1 - z * lam) • (G * P)) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = _ := by rw [this]
  · have : (P * (1 - z • K)) * G = P := by rw [Matrix.mul_assoc, hG, Matrix.mul_one]
    rw [h2, Matrix.smul_mul] at this
    calc P * G = (1 - z * lam)⁻¹ • ((1 - z * lam) • (P * G)) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = _ := by rw [this]

/-- **Pole plus regular part**: `G = P/(1 − zλ) + (1 − P) G (1 − P)`, and the second term inverts
    `1 − zK` on the complement of `P`. -/
theorem regular_part (K P G : Matrix ι ι ℂ) (lam z : ℂ) (hP : P * P = P) (hKP : K * P = lam • P)
    (hPK : P * K = lam • P) (hG : (1 - z • K) * G = 1) (hG' : G * (1 - z • K) = 1)
    (hz : 1 - z * lam ≠ 0) :
    G = (1 - z * lam)⁻¹ • P + (1 - P) * G * (1 - P) ∧
      (1 - z • K) * ((1 - P) * G * (1 - P)) = 1 - P := by
  obtain ⟨hGP, hPG⟩ := pole_part K P G lam z hKP hPK hG hG' hz
  have hPGP : P * G * P = (1 - z * lam)⁻¹ • P := by rw [hPG, Matrix.smul_mul, hP]
  have expand : (1 - P) * G * (1 - P) = G - G * P - P * G + P * G * P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  constructor
  · rw [expand, hGP, hPG, Matrix.smul_mul, hP]; abel
  · have hKc : (1 - z • K) * (1 - P) = (1 - P) * (1 - z • K) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, hKP, hPK]
      rw [smul_sub]; abel
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKc, Matrix.mul_assoc (1 - P), hG, Matrix.mul_one,
      Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP, sub_self, sub_zero]

omit [DecidableEq ι] in
/-- **The residue factors through intermediate channels**: `P_if = Σ_c P_ic P_cf`. -/
theorem residue_through_channels (P : Matrix ι ι ℂ) (hP : P * P = P) (i f : ι) :
    P i f = ∑ c, P i c * P c f := by
  rw [← Matrix.mul_apply, hP]

omit [DecidableEq ι] in
/-- **A simple eigenvalue gives a rank-one residue** `P_if = r_i ℓ_f`. -/
theorem rankOne_projector (K : Matrix ι ι ℂ) (r l : ι → ℂ) (lam : ℂ) (hr : K *ᵥ r = lam • r)
    (hl : l ᵥ* K = lam • l) (hn : l ⬝ᵥ r = 1) :
    vecMulVec r l * vecMulVec r l = vecMulVec r l ∧
      K * vecMulVec r l = lam • vecMulVec r l ∧ vecMulVec r l * K = lam • vecMulVec r l := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vecMulVec_mul_vecMulVec, hn, one_smul]
  · rw [mul_vecMulVec, hr, smul_vecMulVec]
  · rw [vecMulVec_mul, hl, vecMulVec_smul]

/-! ## Unitary 2 × 2 channel steps -/

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- **Cayley–Hamilton for `2 × 2`.** -/
lemma cayley (W : M2) : W * W - trace W • W + det W • (1 : M2) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- **The eigenvalues exist.** -/
theorem exists_eigs (W : M2) : ∃ μ₁ μ₂ : ℂ, μ₁ + μ₂ = trace W ∧ μ₁ * μ₂ = det W := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self (trace W ^ 2 - 4 * det W)
  refine ⟨(trace W + d) / 2, (trace W - d) / 2, by ring, ?_⟩
  linear_combination (1 / 4 : ℂ) * hd

lemma factor (W : M2) (μ₁ μ₂ : ℂ) (hs : μ₁ + μ₂ = trace W) (hp : μ₁ * μ₂ = det W) :
    (W - μ₁ • 1) * (W - μ₂ • 1) = 0 ∧ (W - μ₂ • 1) * (W - μ₁ • 1) = 0 := by
  have hc := cayley W
  rw [← hs, ← hp] at hc
  constructor <;>
  · rw [← hc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, add_smul, smul_sub, smul_smul, mul_comm μ₂ μ₁]
    abel

/-- The spectral projector onto the `μ₁` mode. -/
noncomputable def proj (W : M2) (μ₁ μ₂ : ℂ) : M2 := (μ₁ - μ₂)⁻¹ • (W - μ₂ • 1)

theorem proj_eig (W : M2) (μ₁ μ₂ : ℂ) (hs : μ₁ + μ₂ = trace W) (hp : μ₁ * μ₂ = det W) :
    W * proj W μ₁ μ₂ = μ₁ • proj W μ₁ μ₂ ∧ proj W μ₁ μ₂ * W = μ₁ • proj W μ₁ μ₂ := by
  obtain ⟨h1, h2⟩ := factor W μ₁ μ₂ hs hp
  unfold proj
  constructor
  · rw [Matrix.mul_smul, smul_comm]
    congr 1
    have : W * (W - μ₂ • 1) = (W - μ₁ • 1) * (W - μ₂ • 1) + μ₁ • (W - μ₂ • 1) := by
      simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]; abel
    rw [this, h1, zero_add]
  · rw [Matrix.smul_mul, smul_comm]
    congr 1
    have : (W - μ₂ • 1) * W = (W - μ₂ • 1) * (W - μ₁ • 1) + μ₁ • (W - μ₂ • 1) := by
      simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]; abel
    rw [this, h2, zero_add]

theorem proj_add (W : M2) (μ₁ μ₂ : ℂ) (hne : μ₁ ≠ μ₂) :
    proj W μ₁ μ₂ + proj W μ₂ μ₁ = 1 := by
  unfold proj
  have h : μ₂ - μ₁ = -(μ₁ - μ₂) := by ring
  have hne' : μ₁ - μ₂ ≠ 0 := sub_ne_zero.mpr hne
  rw [h, inv_neg, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  rw [show W - μ₂ • (1 : M2) - (W - μ₁ • 1) = (μ₁ - μ₂) • (1 : M2) by
    rw [sub_smul]; abel, smul_smul, inv_mul_cancel₀ hne', one_smul]

/-- **The residues are idempotent.** -/
theorem proj_idem (W : M2) (μ₁ μ₂ : ℂ) (hs : μ₁ + μ₂ = trace W) (hp : μ₁ * μ₂ = det W)
    (hne : μ₁ ≠ μ₂) : proj W μ₁ μ₂ * proj W μ₁ μ₂ = proj W μ₁ μ₂ := by
  have he := (proj_eig W μ₁ μ₂ hs hp).2
  have hne' : μ₁ - μ₂ ≠ 0 := sub_ne_zero.mpr hne
  have hP : proj W μ₁ μ₂ * (W - μ₂ • 1) = (μ₁ - μ₂) • proj W μ₁ μ₂ := by
    rw [Matrix.mul_sub, he, Matrix.mul_smul, Matrix.mul_one, ← sub_smul]
  calc proj W μ₁ μ₂ * proj W μ₁ μ₂ = (μ₁ - μ₂)⁻¹ • (proj W μ₁ μ₂ * (W - μ₂ • 1)) := by
        rw [show proj W μ₁ μ₂ * proj W μ₁ μ₂ =
          proj W μ₁ μ₂ * ((μ₁ - μ₂)⁻¹ • (W - μ₂ • 1)) from rfl, Matrix.mul_smul]
    _ = _ := by rw [hP, smul_smul, inv_mul_cancel₀ hne', one_smul]

/-- **The residues have determinant zero**: rank one. -/
theorem proj_det (W : M2) (μ₁ μ₂ : ℂ) (hs : μ₁ + μ₂ = trace W) (hp : μ₁ * μ₂ = det W)
    (hne : μ₁ ≠ μ₂) : det (proj W μ₁ μ₂) = 0 := by
  by_contra hd
  have hu : IsUnit (proj W μ₁ μ₂) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  have hz : proj W μ₁ μ₂ * (W - μ₁ • 1) = 0 := by
    unfold proj; rw [Matrix.smul_mul, (factor W μ₁ μ₂ hs hp).2, smul_zero]
  have hW : W - μ₁ • (1 : M2) = 0 := hu.mul_right_eq_zero.mp hz
  have hW' : W = μ₁ • (1 : M2) := sub_eq_zero.mp hW
  have ht : trace W = 2 * μ₁ := by rw [hW']; simp; ring
  rw [ht] at hs
  exact hne (by linear_combination -hs)

/-- **Partial fractions: the resolvent's only poles are at `μ₁⁻¹`, `μ₂⁻¹`.** -/
theorem resolvent_partial (W : M2) (μ₁ μ₂ z : ℂ) (hs : μ₁ + μ₂ = trace W)
    (hp : μ₁ * μ₂ = det W) (hne : μ₁ ≠ μ₂) (h1 : 1 - z * μ₁ ≠ 0) (h2 : 1 - z * μ₂ ≠ 0) :
    (1 - z • W) * ((1 - z * μ₁)⁻¹ • proj W μ₁ μ₂ + (1 - z * μ₂)⁻¹ • proj W μ₂ μ₁) = 1 := by
  have e1 := (proj_eig W μ₁ μ₂ hs hp).1
  have e2 := (proj_eig W μ₂ μ₁ (by rw [add_comm]; exact hs) (by rw [mul_comm]; exact hp)).1
  have k1 : (1 - z • W) * proj W μ₁ μ₂ = (1 - z * μ₁) • proj W μ₁ μ₂ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, e1, smul_smul, sub_smul, one_smul]
  have k2 : (1 - z • W) * proj W μ₂ μ₁ = (1 - z * μ₂) • proj W μ₂ μ₁ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, e2, smul_smul, sub_smul, one_smul]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, k1, k2, smul_smul, smul_smul,
    inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, one_smul, one_smul, proj_add W μ₁ μ₂ hne]

/-- **For a unitary step every eigenvalue has modulus one**: the poles lie on the unit circle. -/
theorem eig_unit (W : M2) (hW : W ∈ unitaryGroup (Fin 2) ℂ) (μ₁ μ₂ : ℂ) (hs : μ₁ + μ₂ = trace W)
    (hp : μ₁ * μ₂ = det W) (hne : μ₁ ≠ μ₂) : normSq μ₁ = 1 := by
  set P := proj W μ₁ μ₂
  have he := (proj_eig W μ₁ μ₂ hs hp).1
  have hu : Wᴴ * W = 1 := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose] at hW; exact hW
  have hP0 : P ≠ 0 := by
    intro h0
    have hsum := proj_add W μ₁ μ₂ hne
    have hidem := proj_idem W μ₂ μ₁ (by rw [add_comm]; exact hs) (by rw [mul_comm]; exact hp)
      (Ne.symm hne)
    have hdet := proj_det W μ₂ μ₁ (by rw [add_comm]; exact hs) (by rw [mul_comm]; exact hp)
      (Ne.symm hne)
    rw [show proj W μ₁ μ₂ = P from rfl, h0, zero_add] at hsum
    rw [hsum, det_one] at hdet
    exact one_ne_zero hdet
  have key : Pᴴ * P = (star μ₁ * μ₁) • (Pᴴ * P) := by
    have : (W * P)ᴴ * (W * P) = Pᴴ * P := by
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hu, Matrix.one_mul]
    rw [he, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at this
    exact this.symm
  have hPP : Pᴴ * P ≠ 0 := fun h => hP0 (conjTranspose_mul_self_eq_zero.mp h)
  have h1 : (star μ₁ * μ₁ - 1) • (Pᴴ * P) = 0 := by rw [sub_smul, one_smul, ← key, sub_self]
  rcases smul_eq_zero.mp h1 with h | h
  · have hc : star μ₁ * μ₁ = (normSq μ₁ : ℂ) := by
      rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [hc, sub_eq_zero] at h
    exact_mod_cast h
  · exact absurd h hPP

/-! ## QLF instances -/

open QLF.ClosureChannels in
/-- **The realizable walk's resolvent has its poles on the unit circle**, at every momentum where
    its two eigenvalues differ, with rank-one residues. -/
theorem realWalk_poles (ky kx kz : ℝ) (μ₁ μ₂ : ℂ) (hs : μ₁ + μ₂ = trace (realWalk ky kx kz))
    (hp : μ₁ * μ₂ = det (realWalk ky kx kz)) (hne : μ₁ ≠ μ₂) :
    normSq μ₁ = 1 ∧ normSq μ₂ = 1 ∧ det (proj (realWalk ky kx kz) μ₁ μ₂) = 0 ∧
      proj (realWalk ky kx kz) μ₁ μ₂ * proj (realWalk ky kx kz) μ₁ μ₂ =
        proj (realWalk ky kx kz) μ₁ μ₂ :=
  ⟨eig_unit _ (realWalk_unitary ky kx kz) μ₁ μ₂ hs hp hne,
   eig_unit _ (realWalk_unitary ky kx kz) μ₂ μ₁ (by rw [add_comm]; exact hs)
     (by rw [mul_comm]; exact hp) (Ne.symm hne),
   proj_det _ μ₁ μ₂ hs hp hne, proj_idem _ μ₁ μ₂ hs hp hne⟩

end QLF.PoleFactorization
