import QLF_AlphaBound

/-!
# QLF_ChainTheory — Chain Theory's α(0) placed against QLF's proven bounds

Companion to [`ChainTheory_YangMills_Kakeya_QLF.md`](../ChainTheory_YangMills_Kakeya_QLF.md).

Chain Theory (A. Wissner-Gross, 2026) obtains the fine-structure constant from a qutrit maximally
entangled with a qubit, as a weighted count over 172 measurement records:

  α(0) = (79 + 48√2 + 42√3 + 3√6) / 31104,   α⁻¹ = 137.035999189566…

This module does **not** derive that formula; it is Chain Theory's. It proves where the number sits
relative to what QLF has already machine-checked in [`QLF_AlphaBound`](QLF_AlphaBound.lean):

* `ctAlphaInv_bounds` — `137.03599 < α⁻¹_CT < 137.03601`, from rational bounds on `√2, √3, √6`.
* `ct_above_leading` — it respects QLF's screening inequality `α⁻¹ > 137` (`alpha_inv_gt_137`).
* `ct_in_census_band` — it lies strictly inside QLF's two-sided census band
  `137 + 1/64 < α⁻¹ < (217 + 512√62)/31`. The band is QLF's; Chain Theory's value is compatible with it.
* `equalWeight_closed_form` — QLF's structural `w = ½` prediction (`Alpha_Residual.md` §2a) has the closed
  form `135 + 8√62/31 ≈ 137.032002`.
* `ct_separated_from_equalWeight` — the two programs' numbers differ by more than `0.0038`, so they are
  distinguishable at the precision α is measured to. QLF's own prediction stays 4 decimals short; Chain
  Theory's claims all 10.
* `ct_denominator_factor`, `qlf_leading_factor` — arithmetic only: `31104 = 2⁷·3⁵` and `137 = 2⁷ + 3²`.
  Both programs build α from the primes 2 and 3 (qubit and qutrit; QLF's 8-twist alphabet and its
  3-D screening). This changes no count of ways, so by the method's rule 4 it is **not evidence** for a
  shared mechanism; it is recorded because it suggests where to look.

No axioms.
-/

namespace QLF.ChainTheory

open QLF.AlphaBound

/-- Chain Theory's numerator `79 + 48√2 + 42√3 + 3√6`. -/
noncomputable def ctNumerator : ℝ :=
  79 + 48 * Real.sqrt 2 + 42 * Real.sqrt 3 + 3 * Real.sqrt 6

/-- Chain Theory's inverse coupling `31104 / (79 + 48√2 + 42√3 + 3√6)`. -/
noncomputable def ctAlphaInv : ℝ := 31104 / ctNumerator

/-- The denominator is a qubit power times a qutrit power: `31104 = 2⁷ · 3⁵`. -/
theorem ct_denominator_factor : (31104 : ℕ) = 2 ^ 7 * 3 ^ 5 := by norm_num

/-- QLF's leading value: `137 = 2⁷ + 3²` (bare `1/128`, plus `d² = 9` screening). -/
theorem qlf_leading_factor : (137 : ℕ) = 2 ^ 7 + 3 ^ 2 := by norm_num

private theorem lt_sqrt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : b ^ 2 < a) : b < Real.sqrt a :=
  calc b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb).symm
    _ < Real.sqrt a := Real.sqrt_lt_sqrt (sq_nonneg b) h

private theorem sqrt_lt_of_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a < b ^ 2) :
    Real.sqrt a < b :=
  calc Real.sqrt a < Real.sqrt (b ^ 2) := Real.sqrt_lt_sqrt ha h
    _ = b := Real.sqrt_sq hb

private theorem sqrt2_lo : (14142135 : ℝ) / 10000000 < Real.sqrt 2 :=
  lt_sqrt_of_sq (by norm_num) (by norm_num)
private theorem sqrt2_hi : Real.sqrt 2 < (14142136 : ℝ) / 10000000 :=
  sqrt_lt_of_sq (by norm_num) (by norm_num) (by norm_num)
private theorem sqrt3_lo : (17320508 : ℝ) / 10000000 < Real.sqrt 3 :=
  lt_sqrt_of_sq (by norm_num) (by norm_num)
private theorem sqrt3_hi : Real.sqrt 3 < (17320509 : ℝ) / 10000000 :=
  sqrt_lt_of_sq (by norm_num) (by norm_num) (by norm_num)
private theorem sqrt6_lo : (24494897 : ℝ) / 10000000 < Real.sqrt 6 :=
  lt_sqrt_of_sq (by norm_num) (by norm_num)
private theorem sqrt6_hi : Real.sqrt 6 < (24494898 : ℝ) / 10000000 :=
  sqrt_lt_of_sq (by norm_num) (by norm_num) (by norm_num)

/-- `√62 < 7.87401` (since `7.87401² = 62.0000334…`). -/
theorem sqrt62_lt : Real.sqrt 62 < (787401 : ℝ) / 100000 :=
  sqrt_lt_of_sq (by norm_num) (by norm_num) (by norm_num)

/-- `226.9768507 < 79 + 48√2 + 42√3 + 3√6 < 226.9768600`. -/
theorem ctNumerator_bounds :
    (2269768507 : ℝ) / 10000000 < ctNumerator ∧ ctNumerator < (2269768600 : ℝ) / 10000000 := by
  unfold ctNumerator
  constructor
  · linarith [sqrt2_lo, sqrt3_lo, sqrt6_lo]
  · linarith [sqrt2_hi, sqrt3_hi, sqrt6_hi]

/-- **Chain Theory's value, machine-checked to eight significant figures:**
    `137.03599 < α⁻¹_CT < 137.03601`. -/
theorem ctAlphaInv_bounds :
    (13703599 : ℝ) / 100000 < ctAlphaInv ∧ ctAlphaInv < (13703601 : ℝ) / 100000 := by
  obtain ⟨hlo, hhi⟩ := ctNumerator_bounds
  have hpos : (0 : ℝ) < ctNumerator := by linarith
  unfold ctAlphaInv
  constructor
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-- Chain Theory's value respects QLF's screening inequality `α⁻¹ > 137` (`alpha_inv_gt_137`). -/
theorem ct_above_leading : (137 : ℝ) < ctAlphaInv := by
  linarith [ctAlphaInv_bounds.1]

/-- **Compatibility:** Chain Theory's value lies strictly inside QLF's proven census band
    `137 + 1/64 < α⁻¹ < (217 + 512√62)/31` (`codata_residual_in_census_bracket`, `alphaInvCap_eq`). -/
theorem ct_in_census_band :
    (137 : ℝ) + 1 / 64 < ctAlphaInv ∧ ctAlphaInv < alphaInvCap := by
  obtain ⟨hlo, hhi⟩ := ctAlphaInv_bounds
  have mono : (217 + 512 * ((7874 : ℝ) / 1000)) / 31 ≤ alphaInvCap := by
    unfold alphaInvCap; gcongr; exact sqrt62_gt.le
  have h1 : (13703601 : ℝ) / 100000 < (217 + 512 * ((7874 : ℝ) / 1000)) / 31 := by norm_num
  have h2 : (137 : ℝ) + 1 / 64 < (13703599 : ℝ) / 100000 := by norm_num
  constructor <;> linarith

/-- QLF's structural equal-weight prediction (`w = ½`, `Alpha_Residual.md` §2a): the leading `137`
    plus the mean of the irreducible and total census tails. -/
noncomputable def equalWeightPrediction : ℝ := 137 + (irreducibleTail + censusTail) / 2

/-- Its closed form: `135 + 8√62/31 ≈ 137.032002`. -/
theorem equalWeight_closed_form : equalWeightPrediction = 135 + 8 * Real.sqrt 62 / 31 := by
  unfold equalWeightPrediction
  rw [irreducibleTail_eq, censusTail_eq]
  ring

/-- `137.032 < 135 + 8√62/31 < 137.0321`. -/
theorem equalWeight_bounds :
    (137032 : ℝ) / 1000 < equalWeightPrediction ∧ equalWeightPrediction < (1370321 : ℝ) / 10000 := by
  rw [equalWeight_closed_form]
  constructor
  · linarith [sqrt62_gt]
  · linarith [sqrt62_lt]

/-- **The two programs' numbers are distinguishable:** Chain Theory's `α⁻¹` exceeds QLF's structural
    `w = ½` prediction by more than `0.0038`. -/
theorem ct_separated_from_equalWeight :
    (38 : ℝ) / 10000 < ctAlphaInv - equalWeightPrediction := by
  linarith [ctAlphaInv_bounds.1, equalWeight_bounds.2]

end QLF.ChainTheory
