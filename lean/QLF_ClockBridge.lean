import QLF_LocalClock

/-!
# Clock comparison: structural facts and a countermodel

The event count is a structural clock. Physical elapsed duration is not
determined by that count without a separate duration assignment.
No physical interpretation or conversion to SI seconds is asserted.
-/

namespace QLF.ClockBridge

/-- Sequential process composition adds structural clock ticks. -/
theorem sequence_tick_add (p q : RhoProcess) :
    local_clock_period (.sequence p q) =
      local_clock_period p + local_clock_period q := by
  simp [local_clock_period, events]

/-- Parallel composition also adds event counts in the current encoding.
    This is NOT an assertion that parallel durations add. -/
theorem parallel_event_count_add (p q : RhoProcess) :
    local_clock_period (.parallel p q) =
      local_clock_period p + local_clock_period q := by
  simp [local_clock_period, events]

/-- A toy duration assignment: sum of per-event natural-number durations. -/
def elapsed (durations : List ℕ) : ℕ := durations.sum

/-- Equal tick counts need not imply equal elapsed durations.
    This countermodel is independent of the QLF event dynamics. -/
theorem same_ticks_different_elapsed :
    ∃ a b : List ℕ,
      a.length = b.length ∧ elapsed a ≠ elapsed b := by
  refine ⟨[1, 1, 1], [1, 2, 3], ?_, ?_⟩
  · decide
  · decide

/-- A uniform per-tick duration makes elapsed time proportional to count;
    the duration scale is an additional input, not a QLF derivation. -/
theorem constant_tick_duration (n d : ℕ) :
    elapsed (List.replicate n d) = n * d := by
  simp [elapsed, List.sum_replicate, Nat.mul_comm]

end QLF.ClockBridge
