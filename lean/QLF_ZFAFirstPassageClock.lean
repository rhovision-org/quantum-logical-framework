import QLF_ClosureDepthLaw

/-!
# A genuine QLF first-passage clock: operational time from ZFA pruning

The elementary transition is the repository's existing zeno_prune, not a
synthetic toy-state transition. closedAtHorizon k s means that k pruning
passes have reduced history s to the empty (closed) state.

For gauge-free balanced histories, the first-passage count is precisely
maxExcursion s, by the existing depth theorem. We then construct two
families of histories of equal raw event count: sequentially nested
pairs and adjacent closing pairs. Their first-passage latencies differ
by an arbitrarily large integer factor d, despite equal input length.

Physical seconds are NOT derived here. A shared seconds-per-pass scale
cancels from the latency ratio, making this a scale-free operational
prediction inside the QLF pruning dynamics. This is a completion
latency, not an oscillation frequency or an SI clock.
-/

namespace QLF.ZFAFirstPassageClock

open QLF.HorizonClosure QLF.ClosureDepth QLF.ClosureDepthLaw

/-- The operational first-passage time in elementary pruning passes. -/
def firstPassageTicks (s : TopoString) : ℕ := maxExcursion s

/-- The first-passage clock is exact for gauge-free balanced histories:
it closes at this count and not at any earlier count. -/
theorem first_passage_exact {s : TopoString}
    (hng : NoGauge s) (hbal : level s = 0) :
    closedAtHorizon (firstPassageTicks s) s ∧
    ∀ k : ℕ, k < firstPassageTicks s → ¬ closedAtHorizon k s := by
  simpa only [firstPassageTicks] using
    (closureDepth_eq_maxExcursion hng hbal)

/-- d adjacent positive/negative pairs, each canceled in the same pass. -/
def adjacentHistory (d : ℕ) : TopoString :=
  pairMatching (List.replicate d true)

/-- Same number of primitive phase events, despite different ordering. -/
theorem equal_event_count (d : ℕ) :
    (nested d).length = (adjacentHistory d).length := by
  calc
    (nested d).length = 2 * d := by
      simp [nested, poss, negs]
      omega
    _ = (adjacentHistory d).length := by
      simp [adjacentHistory, pairMatching_length]

/-- The nested family has exactly d pruning passes to closure. -/
theorem nested_first_passage (d : ℕ) :
    firstPassageTicks (nested d) = d := by
  exact maxExcursion_nested d

/-- Nonempty adjacent-pair families close in exactly one pass. -/
theorem adjacent_first_passage (d : ℕ) (hd : 0 < d) :
    firstPassageTicks (adjacentHistory d) = 1 := by
  unfold firstPassageTicks adjacentHistory
  apply maxExcursion_pairMatching
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_replicate, List.length_nil] at hlen
  omega

/-- Conformance to the actual transition: adjacent pairs are erased
by one invocation of zeno_prune, not an assumed clock cycle. -/
theorem adjacent_closes_in_one (d : ℕ) :
    closedAtHorizon 1 (adjacentHistory d) := by
  change zeno_prune (pairMatching (List.replicate d true)) = []
  exact pairMatching_closes _

/-- A nested history closes precisely after d passes: no earlier pass. -/
theorem nested_is_exact (d : ℕ) :
    closedAtHorizon d (nested d) ∧
    ∀ k : ℕ, k < d → ¬ closedAtHorizon k (nested d) := by
  exact ⟨nested_closed_at_d d, fun k hk => nested_not_closed_before d k hk⟩

/-- The same-size, distinct-latency witness disproves any putative
universal first-passage law based only on the number of phase events. -/
theorem event_count_cannot_determine_first_passage :
    ¬ ∃ f : ℕ → ℕ, ∀ s : TopoString,
      firstPassageTicks s = f s.length := by
  rintro ⟨f, hf⟩
  have hn := hf (nested 2)
  have ha := hf (adjacentHistory 2)
  have heq := equal_event_count 2
  rw [heq] at hn
  have hnd : firstPassageTicks (nested 2) = 2 := nested_first_passage 2
  have had : firstPassageTicks (adjacentHistory 2) = 1 :=
    adjacent_first_passage 2 (by omega)
  rw [hnd] at hn
  rw [had] at ha
  omega

/-- Conditional physical duration under a shared positive cost per prune.
No claim of deriving the scale from QLF is made. -/
noncomputable def elapsedClosure (secondsPerPass : ℝ) (s : TopoString) : ℝ :=
  (firstPassageTicks s : ℝ) * secondsPerPass

/-- A nontrivial operational time dilation between equal-event histories:
nested depth d takes d times as long as d adjacent pairs when both use
the same seconds-per-pruning-pass calibration. -/
theorem nested_vs_adjacent_duration (d : ℕ) (hd : 0 < d)
    (secondsPerPass : ℝ) :
    elapsedClosure secondsPerPass (nested d) =
      (d : ℝ) * elapsedClosure secondsPerPass (adjacentHistory d) := by
  simp [elapsedClosure, nested_first_passage, adjacent_first_passage d hd]

/-- The dimensionless latency ratio is exactly d for any positive
common seconds-per-pass calibration: external scale cancels. -/
theorem nested_vs_adjacent_ratio (d : ℕ) (hd : 0 < d)
    (secondsPerPass : ℝ) (hscale : 0 < secondsPerPass) :
    elapsedClosure secondsPerPass (nested d) /
      elapsedClosure secondsPerPass (adjacentHistory d) = (d : ℝ) := by
  simp only [elapsedClosure, nested_first_passage,
    adjacent_first_passage d hd, Nat.cast_one, one_mul]
  field_simp [ne_of_gt hscale] <;> ring

end QLF.ZFAFirstPassageClock
