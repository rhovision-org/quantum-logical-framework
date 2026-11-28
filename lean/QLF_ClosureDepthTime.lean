import QLF_ZFAFirstPassageClock

/-!
# QLF_ClosureDepthTime — closure depth as intrinsic logical time

[`QLF_ZFAFirstPassageClock`](QLF_ZFAFirstPassageClock.lean) *defines* `firstPassageTicks s := maxExcursion s`
and then proves that this number is the first pruning pass at which `s` closes. This module reverses
the dependency and sharpens the message.

1. **The clock is defined by the dynamics.** `FirstPassageAt s k` says only what `zeno_prune` does:
   `k` passes close `s`, and no fewer do. It mentions no walk and no excursion. For every history it
   has at most one solution (`firstPassageAt_unique`), and for a gauge-free balanced history it has
   exactly one, `k = maxExcursion s` (`firstPassageAt_iff_maxExcursion`). So `maxExcursion` is the
   derived closed form of an operationally defined time, not its definition. Both hypotheses are
   needed: `[+, gauge, −]` and `[+]` never close, so they have no first passage at all
   (`no_first_passage_gauge`, `no_first_passage_unbalanced`).

2. **Time is ordering information, not inventory information.** `nested d` and `adjacentHistory d`
   are permutations of each other (`census_perm`), so they carry the same positive and negative
   phases, yet their latencies are `d` and `1` (`same_census_different_latency`). No function of the
   multiset of events determines the latency (`census_cannot_determine_first_passage`), which is
   strictly stronger than the event-count result `event_count_cannot_determine_first_passage`.

3. **The full spectrum at fixed inventory.** Among the rearrangements of `d` positive and `d`
   negative phases, the latencies that occur are exactly `1, …, d` (`latency_spectrum_exact`):
   every value in that range is attained (`latency_spectrum`), and no other value is
   (`latency_range`, from the excursion budget `2·τ ≤ length`, `latency_le_half_length`). How many
   rearrangements attain each value is the census `W(n,d)` of
   [`QLF_ClosureMultiplicity`](QLF_ClosureMultiplicity.lean), already counted there by an exact
   transfer recurrence on the path graph (`W_eq_dp`). Its membership theorem
   `mem_depthWays_iff_first_closes` is `FirstPassageAt` written out, so that census is the latency
   census. (It is not imported here, to keep this module light.)

4. **Capacity and latency are one number.** For *every* history, the least horizon that closes it is
   its first-passage time (`least_capacity_iff_firstPassageAt`, no hypotheses; this part is
   order-theoretic bookkeeping). Under the depth-law hypotheses the depth law then reads
   `closedAtHorizon R s ↔ firstPassageTicks s ≤ R` (`closes_iff_latency_fits`, a restatement of
   `closedAtHorizon_iff_maxExcursion_le` under the clock's name).

5. **Listening has depth; the closure event does not** — the
   [Event_Timing_QLF.md](../Event_Timing_QLF.md) rule ET1, which that document checks on a finite
   Python model, here derived from `zeno_prune` itself. After `k` passes the remaining latency is
   exactly `τ − k` (`listening_countdown`); the state is open at every pass before `τ`
   (`listening_open_before`) and is one pass from closure at `τ − 1` (`listening_trigger`); at `τ` it
   is the empty history, which has latency `0` and which every further pass leaves unchanged
   (`closure_event_atomic`). The theorem is about pass counts. Reading the fixed point as "the event
   takes no time" is the Event_Timing interpretation, not something the theorem adds.

6. **Two delays.** A history's endpoint imbalance `|level s|` (how much action is still unmatched)
   and its closure depth (how deeply its matched action is nested) are different quantities:
   depth bounds the imbalance from above (`relaxation_ge_distance` in
   [`QLF_Mpemba`](QLF_Mpemba.lean)), and `balanced_yet_deep` shows the gap is unbounded — zero
   imbalance with depth `d` for every `d`. The completion distance of
   [`QLF_Manifestation`](QLF_Manifestation.lean) (`distance_eq_delay`) is defined on twist
   histories, not on phase strings. Here, imbalance plays the analogous endpoint role, and the
   two are not identified.

**Scope.** Everything here counts pruning passes. It does not derive seconds, and it does not
identify pass count with GR proper time or with the tick causal order of
[`QLF_LocalityDefinitions`](QLF_LocalityDefinitions.lean) (`tick_causal`, where time is the number of
steps). Those are different clocks: a history's tick count is its length, which
`same_census_different_latency` shows does not fix its pass count. Relating them is open.

No axioms.
-/

namespace QLF.ClosureDepthTime

open QLF.HorizonClosure QLF.ClosureDepth QLF.ClosureDepthLaw QLF.ZFAFirstPassageClock

/-! ### 1. First passage, defined by the dynamics -/

/-- **`k` is the first-passage time of `s`**: `k` pruning passes close `s`, and no fewer do.
    Defined from `closedAtHorizon` (that is, from `zeno_prune`) alone. -/
def FirstPassageAt (s : TopoString) (k : ℕ) : Prop :=
  closedAtHorizon k s ∧ ∀ j : ℕ, j < k → ¬ closedAtHorizon j s

/-- A first passage, when there is one, is unique — for every history, no hypotheses. -/
theorem firstPassageAt_unique {s : TopoString} {k k' : ℕ}
    (h : FirstPassageAt s k) (h' : FirstPassageAt s k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 k hlt)
  · exact heq
  · exact absurd h'.1 (h.2 k' hgt)

/-- **The operational clock has a closed form.** For a gauge-free balanced history, the first
    passage happens at exactly `maxExcursion s` passes. -/
theorem firstPassageAt_iff_maxExcursion {s : TopoString}
    (hng : NoGauge s) (hbal : level s = 0) (k : ℕ) :
    FirstPassageAt s k ↔ k = maxExcursion s := by
  constructor
  · intro h
    exact firstPassageAt_unique h (closureDepth_eq_maxExcursion hng hbal)
  · rintro rfl
    exact closureDepth_eq_maxExcursion hng hbal

/-- The same statement in the vocabulary of `QLF_ZFAFirstPassageClock`. -/
theorem firstPassageAt_iff_ticks {s : TopoString}
    (hng : NoGauge s) (hbal : level s = 0) (k : ℕ) :
    FirstPassageAt s k ↔ k = firstPassageTicks s :=
  firstPassageAt_iff_maxExcursion hng hbal k

/-- Every gauge-free balanced history has exactly one first-passage time. -/
theorem firstPassage_existsUnique {s : TopoString}
    (hng : NoGauge s) (hbal : level s = 0) : ∃! k, FirstPassageAt s k :=
  ⟨maxExcursion s, (firstPassageAt_iff_maxExcursion hng hbal _).mpr rfl,
    fun k hk => (firstPassageAt_iff_maxExcursion hng hbal k).mp hk⟩

/-- A history that one pass leaves unchanged is left unchanged by every number of passes. -/
theorem boundedPrune_of_fixed {s : TopoString} (h : zeno_prune s = s) :
    ∀ k : ℕ, boundedPrune k s = s
  | 0 => rfl
  | k + 1 => by
      show zeno_prune (boundedPrune k s) = s
      rw [boundedPrune_of_fixed h k, h]

/-- The gauge-blocked history `[+, gauge, −]`: count-balanced, but a gauge separates the pair. -/
def gaugeBlocked : TopoString :=
  [TopoElement.phase LogicPhase.pos, TopoElement.gauge, TopoElement.phase LogicPhase.neg]

/-- **Gauge-freeness is needed**: `[+, gauge, −]` never closes, so it has no first passage. -/
theorem no_first_passage_gauge (k : ℕ) : ¬ FirstPassageAt gaugeBlocked k := by
  intro h
  have hfix : zeno_prune gaugeBlocked = gaugeBlocked := by
    simp [gaugeBlocked, zeno_prune]
  have h1 := h.1
  unfold closedAtHorizon at h1
  rw [boundedPrune_of_fixed hfix k] at h1
  simp [gaugeBlocked] at h1

/-- **Balance is needed**: a lone `+` never closes, so it has no first passage. -/
theorem no_first_passage_unbalanced (k : ℕ) :
    ¬ FirstPassageAt [TopoElement.phase LogicPhase.pos] k := by
  intro h
  have hfix : zeno_prune [TopoElement.phase LogicPhase.pos] = [TopoElement.phase LogicPhase.pos] := by
    simp [zeno_prune]
  have h1 := h.1
  unfold closedAtHorizon at h1
  rw [boundedPrune_of_fixed hfix k] at h1
  simp at h1

/-! ### 2. Same census, different latency -/

/-- The level is the sum of the per-element imbalances. -/
theorem level_eq_sum : ∀ s : TopoString, level s = (s.map imb).sum
  | [] => rfl
  | x :: t => by rw [level_cons, level_eq_sum t, List.map_cons, List.sum_cons]

/-- Rearranging a history does not change its level. -/
theorem level_perm {s t : TopoString} (h : s.Perm t) : level s = level t := by
  rw [level_eq_sum, level_eq_sum]
  exact (h.map imb).sum_eq

/-- Rearranging a history does not introduce a gauge. -/
theorem noGauge_perm {s t : TopoString} (h : s.Perm t) (hs : NoGauge s) : NoGauge t :=
  fun hm => hs (h.symm.subset hm)

theorem adjacentHistory_succ (d : ℕ) :
    adjacentHistory (d + 1) =
      TopoElement.phase LogicPhase.pos :: TopoElement.phase LogicPhase.neg :: adjacentHistory d := by
  simp [adjacentHistory, List.replicate_succ, pairMatching, pairOf]

theorem nested_succ (d : ℕ) :
    nested (d + 1) =
      TopoElement.phase LogicPhase.pos :: (poss d ++ TopoElement.phase LogicPhase.neg :: negs d) := by
  simp [nested, poss, negs, List.replicate_succ]

/-- **Same primitive content.** The nested and adjacent histories are rearrangements of each other:
    both are `d` positive and `d` negative phases. -/
theorem census_perm : ∀ d : ℕ, (nested d).Perm (adjacentHistory d)
  | 0 => by simp [nested, poss, negs, adjacentHistory, pairMatching]
  | d + 1 => by
      rw [nested_succ, adjacentHistory_succ]
      apply List.Perm.cons
      exact List.perm_middle.trans ((census_perm d).cons _)

/-- **Same census, different latency.** For `d ≥ 2`, two histories made of exactly the same events
    close after different numbers of passes, `d` and `1`. Only the order differs. -/
theorem same_census_different_latency (d : ℕ) (hd : 2 ≤ d) :
    (nested d).Perm (adjacentHistory d) ∧
      firstPassageTicks (nested d) ≠ firstPassageTicks (adjacentHistory d) := by
  refine ⟨census_perm d, ?_⟩
  rw [nested_first_passage, adjacent_first_passage d (by omega)]
  omega

/-- **No function of the event multiset determines latency.** This strengthens
    `event_count_cannot_determine_first_passage`: the full inventory, not only its size, is an
    insufficient coarse-graining of the pruning dynamics. -/
theorem census_cannot_determine_first_passage :
    ¬ ∃ f : Multiset TopoElement → ℕ, ∀ s : TopoString,
      firstPassageTicks s = f (s : Multiset TopoElement) := by
  rintro ⟨f, hf⟩
  have hn := hf (nested 2)
  have ha := hf (adjacentHistory 2)
  have hm : ((nested 2 : TopoString) : Multiset TopoElement) = (adjacentHistory 2 : TopoString) :=
    Multiset.coe_eq_coe.mpr (census_perm 2)
  rw [hm, ← ha, nested_first_passage, adjacent_first_passage 2 (by omega)] at hn
  omega

/-! ### 3. The full latency spectrum at fixed inventory -/

/-- A walk's net level is bounded by its length. -/
theorem natAbs_level_le_length : ∀ s : TopoString, (level s).natAbs ≤ s.length
  | [] => by simp
  | x :: t => by
      have ih := natAbs_level_le_length t
      cases x with
      | gauge => simp only [level_cons_gauge, List.length_cons]; omega
      | phase p =>
          cases p
          · simp only [level_cons_pos, List.length_cons]; omega
          · simp only [level_cons_neg, List.length_cons]; omega

/-- The excursion budget on any history (gauges allowed): a walk of length `m` from `c` to `e`
    reaches at most `(|c| + |e| + m) / 2`. Same statement as
    `QLF_ClosureMultiplicity.two_exc_le`, proved here on `TopoString` directly. -/
theorem two_exc_le_length : ∀ (s : TopoString) (c : Int),
    2 * exc c s ≤ c.natAbs + (c + level s).natAbs + s.length
  | [], c => by
      simp only [exc, level_nil, List.length_nil, add_zero]
      omega
  | x :: t, c => by
      have ih := two_exc_le_length t (c + imb x)
      have hl := natAbs_level_le_length t
      have hx : exc c (x :: t) = max c.natAbs (exc (c + imb x) t) := rfl
      rw [hx, level_cons, List.length_cons]
      cases x with
      | gauge => simp only [imb] at ih ⊢; omega
      | phase p => cases p <;> simp only [imb] at ih ⊢ <;> omega

/-- **The excursion budget**: a balanced history's walk never strays more than half its length
    from balance. Gauges allowed; for a gauge-free history this bounds the latency. -/
theorem latency_le_half_length {s : TopoString} (hbal : level s = 0) :
    2 * firstPassageTicks s ≤ s.length := by
  have h := two_exc_le_length s 0
  simp only [zero_add, hbal, Int.natAbs_zero] at h
  unfold firstPassageTicks maxExcursion
  exact h

/-- A non-empty gauge-free history needs at least one pass. -/
theorem latency_pos {s : TopoString} (hng : NoGauge s) (hs : s ≠ []) : 1 ≤ firstPassageTicks s :=
  maxExcursion_pos hng hs

theorem exc_natAbs_le : ∀ (c : Int) (s : TopoString), c.natAbs ≤ exc c s
  | _, [] => le_refl _
  | _, _ :: _ => le_max_left _ _

/-- The walk over a concatenation: the running maximum splits at the junction. -/
theorem exc_append : ∀ (c : Int) (a b : TopoString),
    exc c (a ++ b) = max (exc c a) (exc (c + level a) b)
  | c, [], b => by
      rw [List.nil_append, level_nil, add_zero]
      exact (max_eq_right (exc_natAbs_le c b)).symm
  | c, x :: t, b => by
      show max c.natAbs (exc (c + imb x) (t ++ b)) =
        max (max c.natAbs (exc (c + imb x) t)) (exc (c + level (x :: t)) b)
      rw [exc_append (c + imb x) t b, level_cons, ← add_assoc, max_assoc]

/-- After a balanced prefix the walk is back at `0`, so the maxima simply combine. -/
theorem maxExcursion_append_balanced {a : TopoString} (ha : level a = 0) (b : TopoString) :
    maxExcursion (a ++ b) = max (maxExcursion a) (maxExcursion b) := by
  unfold maxExcursion
  rw [exc_append, ha, add_zero]

theorem pairMatching_append : ∀ a b : List Bool,
    pairMatching (a ++ b) = pairMatching a ++ pairMatching b
  | [], b => rfl
  | x :: t, b => by
      show pairOf x ++ pairMatching (t ++ b) = (pairOf x ++ pairMatching t) ++ pairMatching b
      rw [pairMatching_append t b, List.append_assoc]

theorem adjacentHistory_add (m n : ℕ) :
    adjacentHistory (m + n) = adjacentHistory m ++ adjacentHistory n := by
  unfold adjacentHistory
  rw [List.replicate_add, pairMatching_append]

theorem adjacent_latency_le_one (n : ℕ) : firstPassageTicks (adjacentHistory n) ≤ 1 := by
  cases n with
  | zero => simp [adjacentHistory, pairMatching, firstPassageTicks, maxExcursion, exc]
  | succ n => rw [adjacent_first_passage (n + 1) (by omega)]

/-- The intermediate-latency history: a depth-`r` fold followed by `d − r` adjacent pairs. -/
def spectrumWitness (d r : ℕ) : TopoString := nested r ++ adjacentHistory (d - r)

theorem spectrumWitness_latency (d r : ℕ) (hr : 1 ≤ r) :
    firstPassageTicks (spectrumWitness d r) = r := by
  unfold spectrumWitness
  have h := maxExcursion_append_balanced (level_nested r) (adjacentHistory (d - r))
  have h1 := adjacent_latency_le_one (d - r)
  have h2 := maxExcursion_nested r
  unfold firstPassageTicks at h1 ⊢
  rw [h, h2]
  omega

theorem spectrumWitness_perm (d r : ℕ) (hrd : r ≤ d) :
    (spectrumWitness d r).Perm (nested d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrd
  unfold spectrumWitness
  rw [Nat.add_sub_cancel_left]
  have h1 : (nested r ++ adjacentHistory m).Perm (adjacentHistory r ++ adjacentHistory m) :=
    (census_perm r).append_right _
  rw [← adjacentHistory_add] at h1
  exact h1.trans (census_perm (r + m)).symm

/-- **Every latency from `1` to `d` occurs** among rearrangements of `d` positive and `d` negative
    phases. -/
theorem latency_spectrum (d r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    ∃ s : TopoString, s.Perm (nested d) ∧ firstPassageTicks s = r :=
  ⟨spectrumWitness d r, spectrumWitness_perm d r hrd, spectrumWitness_latency d r hr1⟩

theorem nested_length (d : ℕ) : (nested d).length = 2 * d := by
  simp [nested, poss, negs]; omega

/-- **No other latency occurs.** Every rearrangement of a non-empty inventory closes in at least
    one and at most `d` passes. -/
theorem latency_range (d : ℕ) (hd : 1 ≤ d) {s : TopoString} (hs : s.Perm (nested d)) :
    1 ≤ firstPassageTicks s ∧ firstPassageTicks s ≤ d := by
  have hng : NoGauge s := noGauge_perm hs.symm (noGauge_nested d)
  have hbal : level s = 0 := (level_perm hs).trans (level_nested d)
  have hlen : s.length = 2 * d := hs.length_eq.trans (nested_length d)
  have hne : s ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
    omega
  have hb := latency_le_half_length hbal
  exact ⟨latency_pos hng hne, by omega⟩

/-- **The latency spectrum at fixed inventory is exactly `{1, …, d}`.** The inventory fixes the
    range; the ordering picks the value. -/
theorem latency_spectrum_exact (d : ℕ) (hd : 1 ≤ d) (r : ℕ) :
    (∃ s : TopoString, s.Perm (nested d) ∧ firstPassageTicks s = r) ↔ 1 ≤ r ∧ r ≤ d := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact latency_range d hd hs
  · rintro ⟨h1, h2⟩
    exact latency_spectrum d r h1 h2

/-! ### 4. Capacity and latency -/

/-- **The least capacity that closes a history is its first-passage time** — for every history.
    This is order-theoretic: both sides say "closed at `R`, and at nothing smaller". -/
theorem least_capacity_iff_firstPassageAt (s : TopoString) (R : ℕ) :
    (closedAtHorizon R s ∧ ∀ R' : ℕ, closedAtHorizon R' s → R ≤ R') ↔ FirstPassageAt s R := by
  constructor
  · rintro ⟨hc, hmin⟩
    refine ⟨hc, fun j hj hcj => ?_⟩
    have := hmin j hcj
    omega
  · rintro ⟨hc, hnot⟩
    refine ⟨hc, fun R' hR' => ?_⟩
    by_contra hlt
    exact hnot R' (by omega) hR'

/-- **A horizon closes a history iff its latency fits.** The depth law under the clock's name. -/
theorem closes_iff_latency_fits {s : TopoString}
    (hng : NoGauge s) (hbal : level s = 0) (R : ℕ) :
    closedAtHorizon R s ↔ firstPassageTicks s ≤ R :=
  closedAtHorizon_iff_maxExcursion_le hng hbal R

/-! ### 5. Listening countdown (Event_Timing ET1, derived) -/

/-- **Each pass reduces the remaining latency by exactly one.** -/
theorem listening_countdown {s : TopoString} (hng : NoGauge s) (hbal : level s = 0) (k : ℕ) :
    firstPassageTicks (boundedPrune k s) = firstPassageTicks s - k :=
  maxExcursion_boundedPrune hng hbal k

/-- **The state is open at every pass before the first passage.** -/
theorem listening_open_before {s : TopoString} (hng : NoGauge s) (hbal : level s = 0)
    {k : ℕ} (hk : k < firstPassageTicks s) : boundedPrune k s ≠ [] :=
  (closureDepth_eq_maxExcursion hng hbal).2 k hk

/-- **The trigger**: one pass before closure, the remaining latency is exactly one. -/
theorem listening_trigger {s : TopoString} (hng : NoGauge s) (hbal : level s = 0)
    (hpos : 1 ≤ firstPassageTicks s) :
    firstPassageTicks (boundedPrune (firstPassageTicks s - 1) s) = 1 := by
  rw [listening_countdown hng hbal]
  omega

/-- **The closure event.** At the first passage the state is the empty history, whose latency is
    `0`, and every further pass leaves it unchanged. -/
theorem closure_event_atomic {s : TopoString} (hng : NoGauge s) (hbal : level s = 0) :
    boundedPrune (firstPassageTicks s) s = [] ∧
      firstPassageTicks ([] : TopoString) = 0 ∧
      ∀ m : ℕ, firstPassageTicks s ≤ m → boundedPrune m s = [] := by
  have hc : closedAtHorizon (firstPassageTicks s) s := (closureDepth_eq_maxExcursion hng hbal).1
  exact ⟨hc, rfl, fun m hm => closedAtHorizon_mono hc hm⟩

/-! ### 6. Two delays -/

/-- **Zero imbalance, any depth.** Endpoint imbalance does not bound closure depth: `nested d` has
    nothing unmatched and still needs `d` passes. (The other direction does hold:
    `QLF.Mpemba.relaxation_ge_distance`.) -/
theorem balanced_yet_deep (d : ℕ) :
    level (nested d) = 0 ∧ firstPassageTicks (nested d) = d :=
  ⟨level_nested d, nested_first_passage d⟩

/-- **Summary marker.** Closure depth is an operationally defined time (`FirstPassageAt`) with
    closed form `maxExcursion`; it is ordering information, not inventory information
    (`same_census_different_latency`, `census_cannot_determine_first_passage`); at fixed inventory
    `2d` its spectrum is exactly `{1, …, d}` (`latency_spectrum_exact`); the least closing capacity
    equals it (`least_capacity_iff_firstPassageAt`); and it counts down one per pass to an empty,
    fixed closed state (`listening_countdown`, `closure_event_atomic`). No axioms; no seconds; no
    identification with proper time. -/
theorem closure_depth_time_summary : True := trivial

end QLF.ClosureDepthTime
