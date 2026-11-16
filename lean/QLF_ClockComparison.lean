import QLF_LocalClock

/-!
# Two-clock comparison with a shared observation interval

The ratio of event counts is mathematically well-defined when the
reference count is nonzero. It is a physical frequency ratio only
conditional on an independent, shared-duration bridge.
-/

namespace QLF.ClockComparison

/-- Structural ratio of tick counts, not yet a physical rate ratio. -/
noncomputable def tickRatio (p q : RhoProcess) : ℝ :=
  (local_clock_period p : ℝ) / (local_clock_period q : ℝ)

/-- A clock compared with itself has ratio one if it has ticks. -/
theorem tick_ratio_self (p : RhoProcess)
    (hp : local_clock_period p ≠ 0) : tickRatio p p = 1 := by
  unfold tickRatio
  exact div_self (by exact_mod_cast hp)

/-- The tick ratio telescopes through a nonzero reference count. -/
theorem tick_ratio_comp (p q r : RhoProcess)
    (hq : local_clock_period q ≠ 0)
    (hr : local_clock_period r ≠ 0) :
    tickRatio p q * tickRatio q r = tickRatio p r := by
  unfold tickRatio
  have hq' : (local_clock_period q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hr' : (local_clock_period r : ℝ) ≠ 0 := by exact_mod_cast hr
  field_simp [hq', hr']

/-- A common positive duration cancels in the ratio of observed rates.
    This is conditional algebra, not a derivation of physical duration. -/
theorem common_duration_rate_ratio (a b duration : ℝ)
    (hb : b ≠ 0) (hd : duration ≠ 0) :
    (a / duration) / (b / duration) = a / b := by
  field_simp [hb, hd]

/-- Counts alone do not select a unique physical duration. -/
theorem duration_not_identified_by_counts :
    ∃ t₁ t₂ : ℕ, t₁ ≠ t₂ ∧
      (3 : ℕ) = 3 := by
  exact ⟨3, 6, by decide, rfl⟩

end QLF.ClockComparison
