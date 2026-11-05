import QLF_CoupledEvolution

/-!
# QLF_TsirelsonBound — Tsirelson's bound for every pair of two-outcome observables

Issue #207. [`QLF_Tsirelson`](QLF_Tsirelson.lean) settled the maximal case: when each site's two
observables anticommute, the CHSH operator has spectrum `{0, ±2√2}`, and twists attain `2√2` by an
explicit state. It left open the general bound, for observables that need not anticommute. This
module proves it.

* **`chsh_sos`.** In any `ℂ`-algebra, for two-outcome observables (`x² = 1`) with the sites
  commuting and `s² = 2`,
  `(s a₀ − (b₀ + b₁))² + (s a₁ − (b₀ − b₁))² = 8 − 2s · C`.
  A sum of two squares. No anticommutation, no commutation within a site, nothing else.
* **`tsirelson_bound`.** For Hermitian matrices of any size satisfying those relations and every
  state `v`, `Re⟨v, C v⟩ ≤ 2√2 · ⟨v, v⟩`; **`tsirelson_bound_neg`** gives the lower bound
  `−2√2 · ⟨v, v⟩`. So `|⟨C⟩| ≤ 2√2` for every quantum assignment, whatever the observables.

With `QLF_Tsirelson.twistChsh_saturates` the bound is tight, and twists on two spatial axes reach
it. The proof is the standard sum-of-squares certificate (it is how the bound is proved in
self-testing; see e.g. Šupić and Bowles, *Quantum* **4**, 337 (2020)). Tsirelson's original:
Cirel'son, *Lett. Math. Phys.* **4**, 93 (1980). Finite matrices, no operator-norm theory. No axioms.
-/

namespace QLF.TsirelsonBound

open Matrix
open QLF.Tsirelson (chsh BellPair)

section Algebra

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- **The sum-of-squares certificate.** -/
theorem chsh_sos {a0 a1 b0 b1 : R} (h : BellPair a0 a1 b0 b1) (s : ℂ) (hs : s * s = 2) :
    (s • a0 - (b0 + b1)) * (s • a0 - (b0 + b1)) + (s • a1 - (b0 - b1)) * (s • a1 - (b0 - b1)) =
      (8 : R) - (2 * s) • chsh a0 a1 b0 b1 := by
  have hb0 := h.b0_sq; have hb1 := h.b1_sq
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    h.a0_sq, h.a1_sq, ← h.c00, ← h.c01, ← h.c10, ← h.c11, hb0, hb1, chsh]
  rw [show (8 : R) = (8 : ℂ) • (1 : R) by rw [ofNat_smul_eq_nsmul ℂ 8 (1 : R)]; simp]
  have h1 : (s * s) • (1 : R) = (2 : ℂ) • (1 : R) := by rw [hs]
  linear_combination (norm := module) (2 : ℂ) • h1

end Algebra

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `⟨v, X X v⟩ = ‖X v‖²` for Hermitian `X`, and its real part is non-negative. -/
lemma re_expect_sq_nonneg (X : Matrix ι ι ℂ) (hX : Xᴴ = X) (v : ι → ℂ) :
    0 ≤ (star v ⬝ᵥ ((X * X) *ᵥ v)).re := by
  have : star v ⬝ᵥ ((X * X) *ᵥ v) = star (X *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, hX]
  rw [this]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [Complex.star_def, mul_comm, Complex.mul_conj]
  exact_mod_cast Complex.normSq_nonneg _

lemma re_norm_nonneg (v : ι → ℂ) : 0 ≤ (star v ⬝ᵥ v).re := by
  have := re_expect_sq_nonneg (1 : Matrix ι ι ℂ) (by simp) v
  simpa using this

/-- **Tsirelson's bound** for arbitrary Hermitian two-outcome observables:
    `Re⟨v, C v⟩ ≤ 2√2 ⟨v, v⟩`. -/
theorem tsirelson_bound {a0 a1 b0 b1 : Matrix ι ι ℂ} (h : BellPair a0 a1 b0 b1)
    (ha0 : a0ᴴ = a0) (ha1 : a1ᴴ = a1) (hb0 : b0ᴴ = b0) (hb1 : b1ᴴ = b1) (v : ι → ℂ) :
    (star v ⬝ᵥ (chsh a0 a1 b0 b1 *ᵥ v)).re ≤ 2 * Real.sqrt 2 * (star v ⬝ᵥ v).re := by
  set s : ℂ := (Real.sqrt 2 : ℂ)
  have hs : s * s = 2 := by
    simp only [s]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hsr : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set P := s • a0 - (b0 + b1)
  set Q := s • a1 - (b0 - b1)
  have hsstar : star s = s := by simp only [s]; exact Complex.conj_ofReal _
  have hP : Pᴴ = P := by
    simp only [P, conjTranspose_sub, conjTranspose_add, conjTranspose_smul, hsstar, ha0, hb0, hb1]
  have hQ : Qᴴ = Q := by
    simp only [Q, conjTranspose_sub, conjTranspose_smul, hsstar, ha1, hb0, hb1]
  have hid := chsh_sos h s hs
  -- take the expectation of the certificate
  have hexp : (star v ⬝ᵥ ((P * P) *ᵥ v)).re + (star v ⬝ᵥ ((Q * Q) *ᵥ v)).re =
      8 * (star v ⬝ᵥ v).re - 2 * Real.sqrt 2 * (star v ⬝ᵥ (chsh a0 a1 b0 b1 *ᵥ v)).re := by
    rw [← Complex.add_re, ← dotProduct_add, ← Matrix.add_mulVec, hid, Matrix.sub_mulVec,
      Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
    rw [show (8 : Matrix ι ι ℂ) = (8 : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [ofNat_smul_eq_nsmul ℂ 8 (1 : Matrix ι ι ℂ)]; simp]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, s, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  have h1 := re_expect_sq_nonneg P hP v
  have h2 := re_expect_sq_nonneg Q hQ v
  -- 2√2 · ⟨C⟩ ≤ 8 ⟨v,v⟩ = 2√2 · (2√2 ⟨v,v⟩)
  have h8 : 2 * Real.sqrt 2 * (2 * Real.sqrt 2 * (star v ⬝ᵥ v).re) = 8 * (star v ⬝ᵥ v).re := by
    linear_combination (4 * (star v ⬝ᵥ v).re) * hsr
  have key : 2 * Real.sqrt 2 * (star v ⬝ᵥ (chsh a0 a1 b0 b1 *ᵥ v)).re ≤
      2 * Real.sqrt 2 * (2 * Real.sqrt 2 * (star v ⬝ᵥ v).re) := by
    rw [h8]; linarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- **The lower bound**: `−2√2 ⟨v, v⟩ ≤ Re⟨v, C v⟩`. -/
theorem tsirelson_bound_neg {a0 a1 b0 b1 : Matrix ι ι ℂ} (h : BellPair a0 a1 b0 b1)
    (ha0 : a0ᴴ = a0) (ha1 : a1ᴴ = a1) (hb0 : b0ᴴ = b0) (hb1 : b1ᴴ = b1) (v : ι → ℂ) :
    -(2 * Real.sqrt 2 * (star v ⬝ᵥ v).re) ≤ (star v ⬝ᵥ (chsh a0 a1 b0 b1 *ᵥ v)).re := by
  -- apply the upper bound to `−a₀, −a₁`, whose CHSH operator is `−C`
  have h' : BellPair (-a0) (-a1) b0 b1 :=
    ⟨by rw [neg_mul_neg, h.a0_sq], by rw [neg_mul_neg, h.a1_sq], h.b0_sq, h.b1_sq,
      by rw [neg_mul, mul_neg, h.c00], by rw [neg_mul, mul_neg, h.c01],
      by rw [neg_mul, mul_neg, h.c10], by rw [neg_mul, mul_neg, h.c11]⟩
  have := tsirelson_bound h' (by rw [conjTranspose_neg, ha0]) (by rw [conjTranspose_neg, ha1])
    hb0 hb1 v
  have hc : chsh (-a0) (-a1) b0 b1 = -chsh a0 a1 b0 b1 := by
    simp only [chsh]; noncomm_ring
  rw [hc, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] at this
  linarith

end Matrices

end QLF.TsirelsonBound
