/-!
# Clock ratios and redshift: first algebraic obligations

Companion: Gupta_CCC_TL.md, stages 1–2.

Positive rate ratios compose and are invariant under common unit rescaling.
Multiplicative redshift has a unique residual factor only after one factor is
fixed. An explicit pair of positive decompositions witnesses underdetermination.
A freely chosen clock conversion can realize every positive elapsed reading.

These are real-algebra facts, not a selected QLF evolution, photon transport law,
CCC derivation, or conservative return on closure records. No physical bridge is
assumed or closed. The lapse statement below is an algebraic conversion given
its inputs; no differentiability or metric identification is asserted.
-/
import Mathlib

namespace QLF.ClockRedshift

/-- Endpoint rate ratio; its operational orientation must be fixed separately. -/
noncomputable def rateRatio (emission reception : ℝ) : ℝ := emission / reception

/-- Redshift in the declared frequency-ratio convention. -/
noncomputable def redshift (emission reception : ℝ) : ℝ :=
  rateRatio emission reception - 1

/-- A clock compared with itself has unit ratio. -/
theorem ratio_self (a : ℝ) (ha : 0 < a) : rateRatio a a = 1 := by
  exact div_self (ne_of_gt ha)

/-- Positive endpoint rates yield a positive ratio. -/
theorem ratio_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < rateRatio a b := div_pos ha hb

/-- Ratios telescope through a nonzero intermediate clock. -/
theorem ratio_composition (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    rateRatio a b * rateRatio b c = rateRatio a c := by
  unfold rateRatio
  field_simp [ne_of_gt hb, ne_of_gt hc]
  all_goals ring

/-- This is ratio bookkeeping, independent of any cosmological mechanism. -/
theorem redshift_composition (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (1 + redshift a b) * (1 + redshift b c) = 1 + redshift a c := by
  have hab : 1 + redshift a b = rateRatio a b := by unfold redshift; ring
  have hbc : 1 + redshift b c = rateRatio b c := by unfold redshift; ring
  have hac : 1 + redshift a c = rateRatio a c := by unfold redshift; ring
  rw [hab, hbc, hac]
  exact ratio_composition a b c hb hc

/-- A common positive rate-unit change leaves an endpoint ratio unchanged. -/
theorem common_rescaling (a b scale : ℝ) (hb : 0 < b) (hs : 0 < scale) :
    rateRatio (scale * a) (scale * b) = rateRatio a b := by
  unfold rateRatio
  field_simp [ne_of_gt hb, ne_of_gt hs]
  all_goals ring

/-- Fixing the nonzero expansion factor fixes the residual factor. -/
theorem residual_factor_unique (total expansion x y : ℝ)
    (he : expansion ≠ 0) (hx : total = expansion * x)
    (hy : total = expansion * y) : x = y := by
  apply mul_left_cancel₀ he
  exact hx.symm.trans hy

/-- The total ratio alone does not identify its two positive factors.
    Both decompositions even have factors >= 1 when total >= 2. -/
theorem positive_factorization_not_unique (total : ℝ) (ht : 0 < total) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a * b = total ∧ c * d = total ∧ a ≠ c := by
  refine ⟨1, total, 2, total / 2, by norm_num, ht, by norm_num,
    div_pos ht (by norm_num), ?_, ?_, by norm_num⟩
  · ring
  · ring

/-- Rescaling a free clock conversion can produce any positive reading.
    A matching age with this freedom is representability, not selection. -/
theorem free_clock_scale_hits_any_age (duration target : ℝ)
    (hd : 0 < duration) (ht : 0 < target) :
    ∃ scale : ℝ, 0 < scale ∧ duration * scale = target := by
  refine ⟨target / duration, div_pos ht hd, ?_⟩
  field_simp [ne_of_gt hd]
  all_goals ring

/-- Algebraic lapse conversion; the differential/physical map is separate. -/
noncomputable def metricRate (h alpha lapse : ℝ) : ℝ := (h + alpha) / lapse

/-- An invertible lapse conversion recovers the supplied coordinate rate. -/
theorem lapse_rate_return (h alpha lapse : ℝ) (hl : 0 < lapse) :
    metricRate h alpha lapse * lapse = h + alpha := by
  unfold metricRate
  exact div_mul_cancel₀ _ (ne_of_gt hl)

end QLF.ClockRedshift
