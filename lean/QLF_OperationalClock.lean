import Mathlib
import QLF_GeneratorClockBridge

/-!
# Operational clocks from discrete dynamics

A clock tick is a return of the actual iterated state transition to its
reference state. This module gives two explicit finite-state dynamics with
different return periods and proves a calibration-independent ratio.

These are mathematical toy clocks. No claim is made that either transition
is the physical ZFA generator; identifying such a generator is separate work.
-/

namespace QLF.OperationalClock

/-- An operational return after n applications of the transition. -/
def returns {S : Type*} (step : S → S) (origin : S) (n : ℕ) : Prop :=
  (step^[n]) origin = origin

/-- A fixed point is a one-step clock. -/
theorem identity_one_step : returns (fun b : Bool => b) false 1 := by
  decide

/-- The Boolean flip is a two-step clock. -/
theorem flip_two_steps : returns Bool.not false 2 := by
  decide

/-- The Boolean flip does not return after one step. -/
theorem flip_not_one_step : ¬ returns Bool.not false 1 := by
  decide

/-- A positive common physical seconds-per-step scale cancels from
the ratio of two operational periods. -/
theorem calibrated_period_ratio (scale : ℝ) (hs : 0 < scale) :
    (2 * scale) / (1 * scale) = 2 := by
  field_simp [ne_of_gt hs]
  ring

/-- Two explicitly defined dynamical clocks have distinct first return
periods, independent of the unknown common seconds-per-step. -/
theorem two_dynamical_clocks_ratio :
    returns (fun b : Bool => b) false 1 ∧
    returns Bool.not false 2 ∧
    ¬ returns Bool.not false 1 ∧
    ∀ scale : ℝ, 0 < scale → (2 * scale) / (1 * scale) = 2 := by
  exact ⟨identity_one_step, flip_two_steps, flip_not_one_step,
    calibrated_period_ratio⟩

end QLF.OperationalClock
