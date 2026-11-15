import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedVariables false

/-!
# QLF_ReadoutCriterion — **which readouts carry an amplitude**

The contextual census ([`contextual_census.py`](../contextual_census.py)) reads an outcome's
unnormalized amplitude as `T = Σ_d A(d)·8^{−d/2}`, where `A(d)` is the signed first-closure census at
depth `d`. At fixed capacity the census is a finite signed transfer operator `M`, so
`A(d) = u·Mᵈ·v` for a readout `u` (the apparatus) and a preparation `v`. Whenever `M` acts
diagonalisably on what the readout sees (true of every case surveyed, whose minimal recurrences are
square-free — [`Born_Readout_Criterion.md`](../Born_Readout_Criterion.md)), this is an
**exponential sum** `A(d) = Σ_k c_k λ_kᵈ` over the *distinct* eigenvalues `λ_k`, with `c_k` the
readout's projection onto the `λ_k`-eigenspace.

[`Born_Rule.md`](../Born_Rule.md) §8 read off 90 geometries that the amplitude exists exactly when the
readout misses every mode with `|λ|² ≥ 8`. This module proves that criterion, for every exponential
sum, so the 90-of-90 agreement is a theorem rather than a regularity:

> **`readout_tendsto_iff`** — `A(d)·rᵈ → 0` iff every eigenvalue the readout sees (`c_k ≠ 0`)
> has `|λ_k|·r < 1`.
>
> **`readout_summable_iff`** — `Σ_d |A(d)|·rᵈ` converges iff the same condition holds. So the
> series converges absolutely exactly when its terms go to zero: there is no conditionally
> convergent middle case.
>
> **`amplitude_exists_iff`** — at QLF's forced rate `r = 8^{−1/2}`: the amplitude exists iff every
> eigenvalue in the joint support of readout and preparation has `|λ|² < 8`.

The hard direction is **`terms_tendsto_zero`**: if an exponential sum with distinct ratios tends to
zero, *every term* does. The proof inverts a Vandermonde matrix: the window
`(A(d), A(d+1), …, A(d+n−1))` is `Vᵀ` applied to the vector of terms `c_k λ_kᵈ`, and `Vᵀ` is
invertible because the `λ_k` are distinct, so the terms are a fixed linear (hence continuous) image
of a window tending to zero. Applied after dividing by the largest supported modulus, this shows a
dominant mode in the support can never be cancelled by the others.

What this does **not** settle: *which* readouts are blind to the dominant modes. That is the
combinatorial question about apparatus words, and it is answered for the cases on record by exact
recurrences in [`Born_Readout_Criterion.md`](../Born_Readout_Criterion.md), not here.

No axioms.
-/

open Filter Topology Matrix

namespace QLF.ReadoutCriterion

/-- The readout of a diagonalisable transfer operator: `d ↦ Σ_k c_k λ_kᵈ`. -/
def readout {n : ℕ} (c lam : Fin n → ℂ) (d : ℕ) : ℂ := ∑ k, c k * lam k ^ d

/-- **Vandermonde separation.** If an exponential sum with distinct ratios tends to zero, every one
of its terms does. -/
theorem terms_tendsto_zero {n : ℕ} (a mu : Fin n → ℂ) (hmu : Function.Injective mu)
    (h : Tendsto (fun d => ∑ k, a k * mu k ^ d) atTop (𝓝 0)) (k : Fin n) :
    Tendsto (fun d => a k * mu k ^ d) atTop (𝓝 0) := by
  set V : Matrix (Fin n) (Fin n) ℂ := (vandermonde mu)ᵀ with hV
  have hdet : IsUnit V.det := by
    rw [hV, det_transpose]
    exact (det_vandermonde_ne_zero_iff.mpr hmu).isUnit
  let w : ℕ → Fin n → ℂ := fun d j => ∑ k, a k * mu k ^ (d + (j : ℕ))
  let y : ℕ → Fin n → ℂ := fun d k => a k * mu k ^ d
  have hy : ∀ d, V *ᵥ y d = w d := by
    intro d
    funext j
    simp only [hV, y, w, mulVec, dotProduct, transpose_apply, vandermonde_apply, pow_add]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hrec : ∀ d, y d = V⁻¹ *ᵥ w d := by
    intro d
    rw [← hy d, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have hw : Tendsto w atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro j
    exact (tendsto_add_atTop_iff_nat (f := fun d => ∑ k, a k * mu k ^ d) (j : ℕ)).mpr h
  have hcont : Continuous (fun v : Fin n → ℂ => V⁻¹ *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hlim : Tendsto (fun d => V⁻¹ *ᵥ w d) atTop (𝓝 0) := by
    have := (hcont.tendsto 0).comp hw
    simpa [Function.comp_def, mulVec_zero] using this
  have hy' : Tendsto y atTop (𝓝 0) := by
    refine hlim.congr' (Eventually.of_forall fun d => ?_)
    exact (hrec d).symm
  have := ((continuous_apply k).tendsto (0 : Fin n → ℂ)).comp hy'
  simpa [Function.comp_def, y] using this

/-- **The readout criterion.** `A(d)·rᵈ → 0` iff every eigenvalue the readout sees has
`|λ|·r < 1`. -/
theorem readout_tendsto_iff {n : ℕ} (c lam : Fin n → ℂ) (hlam : Function.Injective lam)
    {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun d => readout c lam d * (r : ℂ) ^ d) atTop (𝓝 0) ↔
      ∀ k, c k ≠ 0 → ‖lam k‖ * r < 1 := by
  have hexp : ∀ d, readout c lam d * (r : ℂ) ^ d = ∑ k, c k * (lam k * r) ^ d := by
    intro d
    simp only [readout, Finset.sum_mul, mul_pow]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  constructor
  · intro h
    by_contra hneg
    push_neg at hneg
    obtain ⟨k0, hk0, hk0r⟩ := hneg
    have hrpos : 0 < r := by
      rcases hr.lt_or_eq with h' | h'
      · exact h'
      · rw [← h', mul_zero] at hk0r
        linarith
    set S : Finset (Fin n) := Finset.univ.filter (fun k => c k ≠ 0) with hS
    have hS0 : k0 ∈ S := by simp [hS, hk0]
    obtain ⟨k1, hk1S, hmax⟩ := S.exists_max_image (fun k => ‖lam k‖) ⟨k0, hS0⟩
    have hk1 : c k1 ≠ 0 := by simpa [hS] using hk1S
    set ρ : ℝ := ‖lam k1‖ * r with hρ
    have hρ1 : 1 ≤ ρ := le_trans hk0r (mul_le_mul_of_nonneg_right (hmax k0 hS0) hr)
    have hρpos : 0 < ρ := lt_of_lt_of_le one_pos hρ1
    set s : ℝ := r / ρ with hs
    have hs0 : (s : ℂ) ≠ 0 := by
      have : s ≠ 0 := div_ne_zero hrpos.ne' hρpos.ne'
      exact_mod_cast this
    let mu : Fin n → ℂ := fun k => lam k * s
    have hmu : Function.Injective mu := by
      intro i j hij
      exact hlam (mul_right_cancel₀ hs0 hij)
    -- the sum, rescaled by ρ⁻ᵈ ≤ 1, still tends to zero
    have hsum : Tendsto (fun d => ∑ k, c k * mu k ^ d) atTop (𝓝 0) := by
      have hid : ∀ d, ∑ k, c k * mu k ^ d =
          (readout c lam d * (r : ℂ) ^ d) * ((ρ⁻¹ : ℝ) : ℂ) ^ d := by
        intro d
        simp only [readout, mu, Finset.sum_mul, mul_pow, hs, div_eq_mul_inv]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        push_cast
        ring
      simp_rw [hid]
      refine squeeze_zero_norm (fun d => ?_) ((tendsto_zero_iff_norm_tendsto_zero).mp h)
      rw [norm_mul, norm_pow]
      have h1 : ‖((ρ⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρpos)]
        exact inv_le_one_of_one_le₀ hρ1
      have h2 : ‖((ρ⁻¹ : ℝ) : ℂ)‖ ^ d ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
      calc ‖readout c lam d * (r : ℂ) ^ d‖ * ‖((ρ⁻¹ : ℝ) : ℂ)‖ ^ d
          ≤ ‖readout c lam d * (r : ℂ) ^ d‖ * 1 :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖readout c lam d * (r : ℂ) ^ d‖ := mul_one _
    have hterm := terms_tendsto_zero c mu hmu hsum k1
    -- but the dominant term has constant norm |c k1|
    have hunit : ‖mu k1‖ = 1 := by
      simp only [mu, norm_mul, Complex.norm_real, Real.norm_eq_abs, hs]
      rw [abs_of_pos (div_pos hrpos hρpos), hρ]
      field_simp
    have hconst : (fun d => ‖c k1 * mu k1 ^ d‖) = fun _ => ‖c k1‖ := by
      funext d
      rw [norm_mul, norm_pow, hunit, one_pow, mul_one]
    have hn := (tendsto_zero_iff_norm_tendsto_zero).mp hterm
    rw [hconst] at hn
    have : ‖c k1‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hn
    exact hk1 (norm_eq_zero.mp this)
  · intro hall
    simp_rw [hexp]
    rw [show (0 : ℂ) = ∑ _k : Fin n, (0 : ℂ) by simp]
    refine tendsto_finset_sum _ (fun k _ => ?_)
    by_cases hc : c k = 0
    · simp [hc]
    · have hlt : ‖lam k * (r : ℂ)‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
        exact hall k hc
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).const_mul (c k)

/-- **Absolute convergence.** `Σ_d |A(d)|·rᵈ` converges iff every eigenvalue the readout sees has
`|λ|·r < 1` — so the series converges absolutely exactly when its terms tend to zero. -/
theorem readout_summable_iff {n : ℕ} (c lam : Fin n → ℂ) (hlam : Function.Injective lam)
    {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun d => ‖readout c lam d‖ * r ^ d) ↔ ∀ k, c k ≠ 0 → ‖lam k‖ * r < 1 := by
  have hnorm : ∀ d, ‖readout c lam d * (r : ℂ) ^ d‖ = ‖readout c lam d‖ * r ^ d := by
    intro d
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  constructor
  · intro hs
    rw [← readout_tendsto_iff c lam hlam hr, tendsto_zero_iff_norm_tendsto_zero]
    simpa [hnorm] using hs.tendsto_atTop_zero
  · intro hall
    have hgeo : Summable (fun d => ∑ k, ‖c k‖ * (‖lam k‖ * r) ^ d) := by
      refine summable_sum (fun k _ => ?_)
      by_cases hc : c k = 0
      · simp [hc]
      · exact (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg _) hr)
          (hall k hc)).mul_left _
    refine Summable.of_nonneg_of_le (fun d => mul_nonneg (norm_nonneg _) (pow_nonneg hr d))
      (fun d => ?_) hgeo
    calc ‖readout c lam d‖ * r ^ d
        ≤ (∑ k, ‖c k * lam k ^ d‖) * r ^ d :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr d)
      _ = ∑ k, ‖c k‖ * (‖lam k‖ * r) ^ d := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [norm_mul, norm_pow, mul_pow]
          ring

/-- **QLF's threshold.** At the forced rate `r = 8^{−1/2}` (one way weighs its own cylinder mass),
the unnormalized amplitude `Σ_d A(d)·8^{−d/2}` converges absolutely iff every eigenvalue in the
joint support of readout and preparation has `|λ|² < 8`. -/
theorem amplitude_exists_iff {n : ℕ} (c lam : Fin n → ℂ) (hlam : Function.Injective lam) :
    Summable (fun d => ‖readout c lam d‖ * (Real.sqrt 8)⁻¹ ^ d) ↔
      ∀ k, c k ≠ 0 → ‖lam k‖ ^ 2 < 8 := by
  have hs8 : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  rw [readout_summable_iff c lam hlam (inv_nonneg.mpr hs8.le)]
  refine forall_congr' (fun k => imp_congr_right (fun _ => ?_))
  rw [← div_eq_mul_inv, div_lt_one hs8]
  constructor
  · intro h
    have h0 := norm_nonneg (lam k)
    have := mul_self_lt_mul_self h0 h
    rw [Real.mul_self_sqrt (by norm_num)] at this
    nlinarith
  · intro h
    have h8 : ‖lam k‖ ^ 2 < Real.sqrt 8 ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]
      exact h
    exact lt_of_pow_lt_pow_left₀ 2 hs8.le h8

end QLF.ReadoutCriterion
