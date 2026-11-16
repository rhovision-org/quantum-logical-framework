import Mathlib

/-!
# Internal resonance versus external construction clock

The resonance frequency is the reciprocal of positive structural depth.
The exterior reference frequency is an independent positive parameter.
Consequently the depth alone does not identify a construction duration.
No physical clock law or frequency-selection mechanism is asserted.
-/

namespace QLF.FrequencyBridge

noncomputable def internalFrequency (R : ℝ) : ℝ := 1 / R
noncomputable def constructionDelay (R externalFrequency : ℝ) : ℝ :=
  R / externalFrequency

theorem internal_frequency_pos (R : ℝ) (hR : 0 < R) :
    0 < internalFrequency R := by
  unfold internalFrequency
  exact one_div_pos.mpr hR

theorem construction_delay_pos (R f : ℝ) (hR : 0 < R) (hf : 0 < f) :
    0 < constructionDelay R f := by
  exact div_pos hR hf

/-- At fixed depth, different positive exterior rates yield different delays. -/
theorem delay_strictly_decreases_with_external_rate
    (R f₁ f₂ : ℝ) (hR : 0 < R) (hf₁ : 0 < f₁) (hff : f₁ < f₂) :
    constructionDelay R f₂ < constructionDelay R f₁ := by
  unfold constructionDelay
  exact div_lt_div_of_pos_left hR hf₁ hff

/-- One depth admits two distinct positive construction delays. -/
theorem depth_does_not_determine_delay (R : ℝ) (hR : 0 < R) :
    ∃ f₁ f₂ : ℝ,
      0 < f₁ ∧ 0 < f₂ ∧
      constructionDelay R f₁ ≠ constructionDelay R f₂ := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  have h := delay_strictly_decreases_with_external_rate R 1 2 hR
    (by norm_num) (by norm_num)
  exact ne_of_gt h

/-- Identifying the exterior rate with internal resonance yields R squared. -/
theorem equal_frequency_gives_squared_delay (R : ℝ) (hR : R ≠ 0) :
    constructionDelay R (internalFrequency R) = R * R := by
  unfold constructionDelay internalFrequency
  field_simp
  ring

/-- A unit exterior reference rate gives delay equal to structural depth. -/
theorem unit_external_frequency (R : ℝ) :
    constructionDelay R 1 = R := by
  simp [constructionDelay]

end QLF.FrequencyBridge
