import QLF_GeneratorClockBridge

/-!
# Energy-frequency-clock dependency audit

The QLF documentation writes omega = 1 / duration and E = hbar * omega.
This module formalizes their algebraic consequence and the selection gap:
without an independently supplied energy, any positive duration has a
matching positive energy. Conversely, with independently supplied positive
energy and hbar, the duration is uniquely determined.

IMPORTANT: omega here is inverse duration (cycles per time), not angular
frequency. The conventional angular-frequency relation uses omega = 2*pi/T;
therefore the energy formula must match the selected convention. These
theorems are conditional algebra, not a derivation of energy from QLF.
-/

namespace QLF.EnergyFrequencyClock

/-- Energy assigned by the inverse-duration convention. -/
noncomputable def energyFromDuration (hbar duration : ℝ) : ℝ :=
  hbar / duration

/-- Positive energy scale for positive hbar and duration. -/
theorem energy_positive (hbar duration : ℝ)
    (hh : 0 < hbar) (hd : 0 < duration) :
    0 < energyFromDuration hbar duration := by
  exact div_pos hh hd

/-- For any positive duration, a matching positive energy exists. -/
theorem every_positive_duration_has_matching_energy
    (hbar duration : ℝ) (hh : 0 < hbar) (hd : 0 < duration) :
    ∃ energy : ℝ, 0 < energy ∧ energy * duration = hbar := by
  refine ⟨hbar / duration, div_pos hh hd, ?_⟩
  field_simp

/-- Independent positive energy fixes the duration under E*T = hbar. -/
theorem independent_energy_selects_duration
    (hbar energy duration : ℝ) (he : 0 < energy)
    (h : energy * duration = hbar) :
    duration = hbar / energy := by
  apply (mul_left_cancel₀ (ne_of_gt he))
  calc
    energy * duration = hbar := h
    _ = energy * (hbar / energy) := by field_simp

/-- Two different positive durations correspond to different energy
assignments; the energy-frequency equation alone selects neither. -/
theorem two_positive_durations_fit_same_hbar (hbar : ℝ) (hh : 0 < hbar) :
    ∃ e₁ e₂ : ℝ,
      0 < e₁ ∧ 0 < e₂ ∧
      e₁ * (1 : ℝ) = hbar ∧
      e₂ * (2 : ℝ) = hbar ∧
      e₁ ≠ e₂ := by
  refine ⟨hbar, hbar / 2, hh, div_pos hh (by norm_num), ?_, ?_, ?_⟩
  · ring
  · ring
  · intro heq
    have h : hbar = 0 := by
      rw [heq] at *
      linarith
    exact (ne_of_gt hh) h

end QLF.EnergyFrequencyClock
