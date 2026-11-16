import QLF_GeneratorClockBridge
import QLF_FieldEnergy

/-!
# Field evolution stability does not select a physical clock

The existing QLF.FieldEnergy.energy_bounds and free_stable results use
the sufficient stability hypothesis 4 * n * τ² ≤ 1.
Two distinct positive τ values satisfy this hypothesis for n = 1.
Consequently, even when a clock's seconds-per-step is identified with τ,
this stability condition does not uniquely calibrate elapsed time.

This is a conditional identification, not a derivation of SI units or a
Hamiltonian energy-to-frequency law.
-/

namespace QLF.FieldClockStability

open QLF.GeneratorClockBridge

/-- Two distinct positive step sizes satisfy the existing field-energy
stability criterion for a single spatial direction. -/
theorem distinct_stable_step_sizes :
    ∃ τ₁ τ₂ : ℝ,
      0 < τ₁ ∧ 0 < τ₂ ∧
      4 * (1 : ℝ) * τ₁ ^ 2 ≤ 1 ∧
      4 * (1 : ℝ) * τ₂ ^ 2 ≤ 1 ∧
      τ₁ ≠ τ₂ := by
  refine ⟨1 / 4, 1 / 8, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Identifying a stable step size with seconds-per-step still permits
distinct elapsed durations for one generator step. -/
theorem stability_does_not_select_one_step_duration :
    ∃ c₁ c₂ : ClockCalibration,
      4 * (1 : ℝ) * c₁.secondsPerStep ^ 2 ≤ 1 ∧
      4 * (1 : ℝ) * c₂.secondsPerStep ^ 2 ≤ 1 ∧
      elapsed c₁ 1 ≠ elapsed c₂ 1 := by
  let c₁ : ClockCalibration := ⟨1 / 4, by norm_num⟩
  let c₂ : ClockCalibration := ⟨1 / 8, by norm_num⟩
  refine ⟨c₁, c₂, ?_, ?_, ?_⟩
  · norm_num [c₁]
  · norm_num [c₂]
  · norm_num [elapsed, c₁, c₂]

end QLF.FieldClockStability
