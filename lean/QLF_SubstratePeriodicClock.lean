import QLF_LoopClosure

/-!
# Exact positive return periods in the actual finite QLF phase transition

The existing QLF.LoopClosure.phase k N := k % N is the substrate's
discrete finite-cycle phase. This proves that the FIRST positive return
to its initial phase is at N, not merely that N is *a* return time.

For two such cycles under a common physical tick duration, the
dimensionless period ratio is N/M. The substrate determines this
relative period after N and M are selected; it does not select N or M,
or derive seconds-per-tick.

This periodic return clock is distinct from the first-passage-to-closure
latency of QLF_ZFAFirstPassageClock.
-/

namespace QLF.SubstratePeriodicClock

open QLF.LoopClosure

/-- The primitive positive return period of the actual finite QLF
phase transition is exactly N, for any N>0. -/
theorem exact_first_positive_return (N : ℕ) (hN : 0 < N) :
    phase N N = phase 0 N ∧
    ∀ k : ℕ, 0 < k → k < N → phase k N ≠ phase 0 N := by
  constructor
  · simp [phase]
  · intro k hk hkN hreturn
    have hzero : k = 0 := by
      simpa [phase, Nat.mod_eq_of_lt hkN] using hreturn
    omega

/-- Operational seconds for one full N-tick cycle under a shared
external seconds-per-substrate-tick conversion. -/
noncomputable def cycleDuration (secondsPerTick : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * secondsPerTick

/-- A common tick calibration cancels from the ratio of two periods.
The right side is determined entirely by the two finite cycle sizes. -/
theorem exact_relative_period (N M : ℕ) (hM : 0 < M)
    (secondsPerTick : ℝ) (htick : 0 < secondsPerTick) :
    cycleDuration secondsPerTick N / cycleDuration secondsPerTick M =
      (N : ℝ) / (M : ℝ) := by
  have hm : (M : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hM)
  have ht : secondsPerTick ≠ 0 := ne_of_gt htick
  unfold cycleDuration
  field_simp [hm, ht] <;> ring

/-- A fully explicit example: the three-tick substrate cycle has
exactly 3/2 the period of the two-tick substrate cycle, for any
shared positive seconds-per-tick calibration. -/
theorem two_vs_three (secondsPerTick : ℝ) (htick : 0 < secondsPerTick) :
    cycleDuration secondsPerTick 3 / cycleDuration secondsPerTick 2 =
      (3 : ℝ) / 2 := by
  simpa using exact_relative_period 3 2 (by norm_num) secondsPerTick htick

end QLF.SubstratePeriodicClock
