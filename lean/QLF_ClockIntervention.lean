import QLF_ClockPairing

/-!
# Interventions on the counterpart, and the age-map interface

Companion: Time_Reversed_Clock_Domains.md (third stage), issue #236.

Two obligations of the clock-domain program are tested on the finite model.

**Causal noninterference.** An intervention replaces the counterpart word `q`
by another admissible `q'`. The record `accessible (p, q) = (p, q.length)` is
tested against two families:

* reorderings of the counterpart are always admissible and never change the
  record;
* inserting a conjugate pair is always admissible and changes the record.

So the record of `QLF_ClockDomains` is **not** a no-signalling interface: the
counterpart can transmit any natural number through its length. The only
length information that cannot signal is the parity, and the parity is already
fixed by the local word. Non-reconstruction (stage one) and no-signalling are
therefore different properties, and this record has the first without the
second.

**Age map.** The interface "a positive tick count on admissible histories" is
bundled and measured: it is satisfied by a constant, and by a map hitting any
prescribed positive value, so it excludes nothing. With word length as the
tick count, "our age is half the total" holds exactly when the two durations
are equal. Closure does not force that: `([up], [down, left, right])` is
admissible with durations 1 and 3.

No physical horizon, no-signalling law or age relation is asserted. No axiom.
-/

namespace QLF.ClockIntervention

open QLF QLF.ClockDomains QLF.ClosureUnitarity QLF.ClockPairing

-- ==========================================
-- §1  Reordering the counterpart is invisible
-- ==========================================

/-- Any reordering of the counterpart of an admissible history is admissible. -/
theorem perm_admissible (p q q' : List Twist) (hperm : q.Perm q')
    (hh : admissible (p, q)) : admissible (p, q') := by
  unfold admissible at hh ⊢
  unfold countBalanced at hh ⊢
  simp only [List.count_append] at hh ⊢
  rw [← hperm.count_eq, ← hperm.count_eq, ← hperm.count_eq, ← hperm.count_eq,
    ← hperm.count_eq, ← hperm.count_eq, ← hperm.count_eq, ← hperm.count_eq]
  exact hh

/-- **Reordering never changes the record.** -/
theorem perm_record (p q q' : List Twist) (hperm : q.Perm q') :
    accessible (p, q) = accessible (p, q') := by
  unfold accessible
  rw [hperm.length_eq]

/-- More generally, the record is blind to every intervention that keeps the
    counterpart's length. This holds by the definition of the record. -/
theorem length_preserving_record (p q q' : List Twist) (hl : q.length = q'.length) :
    accessible (p, q) = accessible (p, q') := by
  unfold accessible
  rw [hl]

/-- The reorder class of a counterpart: its eight twist counts. -/
def countVector (q : List Twist) : List ℕ := allTwists.map (fun t => q.count t)

/-- **The 21 counterparts of the record `([up], 3)` fall into exactly 4 reorder
    classes.** Within a class the record cannot tell members apart and
    reordering moves between them. -/
theorem fiber_up_three_classes :
    ((fiber [Twist.up] 3).map countVector).dedup.length = 4 := by decide

-- ==========================================
-- §2  Pair insertion is visible: the record signals
-- ==========================================

/-- Inserting a conjugate pair anywhere in the counterpart keeps admissibility. -/
theorem insert_pair_admissible (p a b : List Twist) (t : Twist)
    (hh : admissible (p, a ++ b)) : admissible (p, a ++ [t, t.conj] ++ b) := by
  unfold admissible at hh ⊢
  unfold countBalanced at hh ⊢
  simp only [List.count_append] at hh ⊢
  cases t <;>
    simp (config := { decide := true }) only [Twist.conj, List.count_cons, List.count_nil,
      ite_true, ite_false] <;>
    omega

/-- **Inserting a conjugate pair changes the record.** -/
theorem insert_pair_record (p a b : List Twist) (t : Twist) :
    accessible (p, a ++ [t, t.conj] ++ b) ≠ accessible (p, a ++ b) := by
  unfold accessible
  intro h
  have hl := congrArg Prod.snd h
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  omega

/-- So the record is not invariant under admissible interventions: an
    admissible history and an admissible intervention on its counterpart with a
    different record. Non-reconstruction does not give no-signalling. -/
theorem record_signals :
    ∃ p q q' : List Twist, admissible (p, q) ∧ admissible (p, q') ∧
      accessible (p, q) ≠ accessible (p, q') :=
  ⟨[Twist.up], [Twist.down], [Twist.down, Twist.left, Twist.right],
    canonical_admissible, extendedLeft_admissible, records_distinct⟩

/-- **The channel is unbounded.** For every local word and every `k` there is an
    admissible counterpart of length `p.length + 2 * k`, so the counterpart can
    transmit any natural number through the record. -/
theorem channel_unbounded (p : List Twist) (k : ℕ) :
    ∃ q : List Twist, admissible (p, q) ∧ q.length = p.length + 2 * k := by
  induction k with
  | zero => exact ⟨dagger p, countBalanced_append_dagger p, by rw [dagger_length]; rfl⟩
  | succ k ih =>
    obtain ⟨q, hq, hl⟩ := ih
    have hq' : admissible (p, q ++ []) := by rw [List.append_nil]; exact hq
    have hins := insert_pair_admissible p q [] Twist.up hq'
    refine ⟨q ++ [Twist.up, Twist.up.conj] ++ [], hins, ?_⟩
    simp only [List.append_nil, List.length_append, List.length_cons, List.length_nil]
    omega

-- ==========================================
-- §3  What cannot signal: parity
-- ==========================================

/-- A word's length is the sum of its eight twist counts. -/
theorem length_eq_counts (w : List Twist) :
    w.length = w.count Twist.up + w.count Twist.down + w.count Twist.left
      + w.count Twist.right + w.count Twist.slash + w.count Twist.backslash
      + w.count Twist.plus + w.count Twist.minus := by
  induction w with
  | nil => rfl
  | cons t rest ih =>
    cases t <;>
      simp (config := { decide := true }) only [List.length_cons, List.count_cons,
        ite_true, ite_false] <;>
      omega

/-- A count-balanced word has even length. -/
theorem balanced_length_even (w : List Twist) (hw : countBalanced w) : w.length % 2 = 0 := by
  rw [length_eq_counts]
  unfold countBalanced at hw
  omega

/-- **The counterpart's length parity is fixed by the local word.** -/
theorem admissible_parity (h : History) (hh : admissible h) :
    h.2.length % 2 = h.1.length % 2 := by
  have he := balanced_length_even _ hh
  rw [List.length_append] at he
  omega

/-- So a record exposing only the parity of the counterpart's length is
    invariant under every admissible intervention: it carries nothing the local
    word does not already carry. Hiding of this kind is automatic. -/
theorem parity_record_no_signal (p q q' : List Twist)
    (hq : admissible (p, q)) (hq' : admissible (p, q')) :
    (p, q.length % 2) = (p, q'.length % 2) := by
  have h1 := admissible_parity (p, q) hq
  have h2 := admissible_parity (p, q') hq'
  simp only at h1 h2
  rw [h1, h2]

-- ==========================================
-- §4  The age-map interface, measured
-- ==========================================

/-- The bare interface of a tick count: positive on admissible histories. -/
structure AgeMap where
  ticks : History → ℚ
  pos : ∀ h, admissible h → 0 < ticks h

/-- **The bare interface excludes nothing**: a constant satisfies it. -/
theorem ageMap_nonempty : Nonempty AgeMap :=
  ⟨⟨fun _ => 1, fun _ _ => one_pos⟩⟩

/-- …and it fixes no value: any positive number is the age of every history
    under some instance. -/
theorem ageMap_hits_any (c : ℚ) (hc : 0 < c) (h : History) :
    ∃ A : AgeMap, A.ticks h = c :=
  ⟨⟨fun _ => c, fun _ _ => hc⟩, rfl⟩

/-- **With word length as the tick count, "ours is half the total" is exactly
    equality of the two durations.** -/
theorem half_total_iff (h : History) :
    2 * h.1.length = h.1.length + h.2.length ↔ h.1.length = h.2.length := by
  omega

/-- On the strict class (the fixed points of `J`) the half-total relation holds. -/
theorem strict_half_total (h : History) (hs : strict h) :
    2 * h.1.length = h.1.length + h.2.length := by
  have he := J_fixed_lengths h ((J_fixed_iff h).mpr hs)
  omega

/-- **Closure does not force it.** An admissible history with durations 1 and 3. -/
theorem half_total_not_forced :
    ∃ h : History, admissible h ∧ 2 * h.1.length ≠ h.1.length + h.2.length :=
  ⟨extendedLeft, extendedLeft_admissible, by decide⟩

/-- Equal durations do not make a history a fixed point of `J` either: 168
    admissible histories have durations `(2, 2)` and only 64 are fixed. -/
theorem equal_durations_not_fixed :
    ∃ h : History, admissible h ∧ h.1.length = h.2.length ∧ J h ≠ h :=
  ⟨([Twist.up, Twist.left], [Twist.down, Twist.right]), by
    unfold admissible countBalanced; decide, rfl, by decide⟩

end QLF.ClockIntervention
