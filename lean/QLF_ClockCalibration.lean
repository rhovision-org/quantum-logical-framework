import QLF_ClockRedshift

/-!
# QLF_ClockCalibration — what a clock calibration cannot change (#234)

Companion: [`Gupta_ScaleFree.md`](../Gupta_ScaleFree.md), run by
[`gupta_scale_free.py`](../gupta_scale_free.py). A clock calibration multiplies elapsed readings
by a positive scale `s` and rates read on that clock by `1/s`.
[`QLF_ClockRedshift`](QLF_ClockRedshift.lean) proves that a free scale fits any one age
(`free_clock_scale_hits_any_age`). This module proves the other half.

* **`age_ratio_calibration_free`.** Age ratios do not depend on `s`.
* **`age_rate_product_calibration_free`.** Neither does an age times a rate on the same clock.
* **`one_scale_fits_two_ages_iff`.** One scale fits two target ages exactly when the model's age
  ratio equals the targets' ratio. So a free scale fits one age and no more.

Real algebra, not a selected QLF evolution or a physical clock map.

No QLF axioms.
-/

namespace QLF.ClockCalibration

theorem age_ratio_calibration_free (s t₁ t₂ : ℝ) (hs : 0 < s) :
    (s * t₁) / (s * t₂) = t₁ / t₂ := by
  rw [mul_div_mul_left _ _ (ne_of_gt hs)]

theorem age_rate_product_calibration_free (s t H : ℝ) (hs : 0 < s) :
    (s * t) * (H / s) = t * H := by
  field_simp

theorem one_scale_fits_two_ages_iff (t₁ t₂ T₁ T₂ : ℝ) (h₁ : 0 < t₁) (h₂ : 0 < t₂)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) :
    (∃ s : ℝ, 0 < s ∧ t₁ * s = T₁ ∧ t₂ * s = T₂) ↔ t₁ / t₂ = T₁ / T₂ := by
  constructor
  · rintro ⟨s, hs, e₁, e₂⟩
    rw [← e₁, ← e₂, mul_div_mul_right _ _ (ne_of_gt hs)]
  · intro h
    refine ⟨T₁ / t₁, div_pos hT₁ h₁, by field_simp, ?_⟩
    rw [div_eq_div_iff (ne_of_gt h₂) (ne_of_gt hT₂)] at h
    field_simp
    rw [mul_comm t₂ T₁, ← h, mul_comm]

end QLF.ClockCalibration
