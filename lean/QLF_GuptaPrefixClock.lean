import QLF_ClockRedshift
import Mathlib.Tactic

/-!
A scoped obstruction for a prefix-length clock, not a physical Gupta–QLF map.
If positive periods are nondecreasing along a history and frequency is k/period
with the same positive calibration k, the reception/emission frequency ratio
cannot exceed one. A Gupta past-branch lapse greater than one therefore cannot
be identified with this ratio. This excludes only the declared identification.
-/

namespace QLF.GuptaPrefixClock

/-- Common-scale inverse-period rates give a lapse equal to the period ratio. -/
theorem inverse_period_ratio (emit now k : ℝ)
    (he : 0 < emit) (hn : 0 < now) (hk : 0 < k) :
    (k / now) / (k / emit) = emit / now := by
  field_simp [ne_of_gt he, ne_of_gt hn, ne_of_gt hk]
  <;> ring

/-- The inverse-period endpoint lapse cannot exceed one for an accumulating prefix. -/
theorem prefix_lapse_le_one (emit now k : ℝ)
    (he : 0 < emit) (hn : 0 < now) (hk : 0 < k)
    (hprefix : emit ≤ now) :
    (k / now) / (k / emit) ≤ 1 := by
  rw [inverse_period_ratio emit now k he hn hk]
  exact (div_le_iff₀ hn).2 (by simpa using hprefix)

/-- A strictly greater-than-one past lapse is incompatible with this specific
    prefix-period identification; it says nothing about other clock models. -/
theorem gupta_past_prefix_obstruction (emit now k f : ℝ)
    (he : 0 < emit) (hn : 0 < now) (hk : 0 < k)
    (hprefix : emit ≤ now) (hpast : 1 < f)
    (hident : f = (k / now) / (k / emit)) : False := by
  have hle := prefix_lapse_le_one emit now k he hn hk hprefix
  rw [← hident] at hle
  exact (not_lt_of_ge hle) hpast

end QLF.GuptaPrefixClock
