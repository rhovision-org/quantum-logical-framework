import Mathlib

/-!
# Generator clock calibration: discrete steps versus physical duration

A discrete generator determines transitions indexed by natural numbers.
A physical duration additionally requires a positive time-per-step parameter.
The formal bridge below makes that independent input explicit. It does not
assert that a QLF closure event has a derived duration in SI seconds.
-/

namespace QLF.GeneratorClockBridge

/-- A generator of one-step transitions, with no physical time scale. -/
structure DiscreteGenerator (State : Type*) where
  step : State → State

/-- A physical clock calibration is an independent strictly positive duration per step. -/
structure ClockCalibration where
  secondsPerStep : ℝ
  positive : 0 < secondsPerStep

/-- Duration for a finite number of generator steps under a supplied calibration. -/
noncomputable def elapsed (clock : ClockCalibration) (steps : ℕ) : ℝ :=
  (steps : ℝ) * clock.secondsPerStep

theorem elapsed_zero (clock : ClockCalibration) : elapsed clock 0 = 0 := by
  simp [elapsed]

theorem elapsed_add (clock : ClockCalibration) (m n : ℕ) :
    elapsed clock (m + n) = elapsed clock m + elapsed clock n := by
  simp only [elapsed, Nat.cast_add]
  ring

theorem elapsed_pos (clock : ClockCalibration) (n : ℕ) (hn : 0 < n) :
    0 < elapsed clock n := by
  exact mul_pos (Nat.cast_pos.mpr hn) clock.positive

/-- Any desired positive elapsed duration can be realized at a fixed
positive number of steps by selecting a corresponding clock calibration. -/
theorem any_positive_duration_at_fixed_steps (n : ℕ) (hn : 0 < n)
    (target : ℝ) (ht : 0 < target) :
    ∃ clock : ClockCalibration, elapsed clock n = target := by
  let clock : ClockCalibration :=
    ⟨target / (n : ℝ), div_pos ht (Nat.cast_pos.mpr hn)⟩
  refine ⟨clock, ?_⟩
  change (n : ℝ) * (target / (n : ℝ)) = target
  field_simp

/-- The same discrete generator and step count admit distinct positive
elapsed durations. A generator alone does not select an SI time scale. -/
theorem generator_does_not_select_duration {State : Type*}
    (_generator : DiscreteGenerator State) (n : ℕ) (hn : 0 < n) :
    ∃ c₁ c₂ : ClockCalibration, elapsed c₁ n ≠ elapsed c₂ n := by
  obtain ⟨c₁, hc₁⟩ := any_positive_duration_at_fixed_steps n hn 1 (by norm_num)
  obtain ⟨c₂, hc₂⟩ := any_positive_duration_at_fixed_steps n hn 2 (by norm_num)
  refine ⟨c₁, c₂, ?_⟩
  rw [hc₁, hc₂]
  norm_num

end QLF.GeneratorClockBridge
