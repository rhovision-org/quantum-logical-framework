import QLF_SharedReality

/-!
# QLF_SharedEvent — when two perspectives identify the same events

Bridge A of the 2026-11-23 roadmap (issue #296): do compatible perspectives reconstruct the
**same** event invariant from their own records, and when is it uniquely reconstructible?
[`QLF_SharedReality`](QLF_SharedReality.lean) proves that on histories built from shared pairs
`A`'s ZFA verdict is a fact for `B`. This module asks the stronger question about the events
themselves, and finds where the answer stops.

**§1 Words: one event list, read from either side.** On pair-built histories
(`PairBuilt`, a list of shared pairs `(A, t), (B, t.conj)`):

* `pairBuilt_events_unique`: the list of shared events is unique. Two pair decompositions of one
  history are the same list.
* `perspectives_agree_on_events`: `B`'s word, conjugated letter by letter, **is** `A`'s word. The
  two perspectives read the same events in the same order.
* `history_from_A`, `history_from_B`: each body's word alone determines the whole two-body
  history on this domain.

**§2 Territorial records: the same invariant up to a known sign.**
`pair_domain_reconstructs_record`: on the pair-built domain, `B`'s territorial record (fold and
ledger) reconstructs `A`'s whole territorial record, not only its ZFA verdict. The ledger is
conjugated, and the fold carries the sign `(-1)^n` (`pair_phase_transfer`), with `n` read from
`B`'s own ledger.

**§3 What the bodies cannot tell: whether an event was shared.** `jointW` is two shared pairs.
`splitW` has the same tokens on each body, but `A` closes on its own before `B` acts.
`shared_event_not_from_bodies`: the two histories have the **same word on each body**, so the
same territorial records, yet one is pair-built and the other is not.
`pairing_not_reconstructible`: no function of the two body words decides whether the history is
made of shared events. So a shared ledger, or even both full words, does not establish a shared
event. Shared-event identity is a fact about the joint history, which neither perspective holds.

**§4 Relays.** `relay_agree_on_events`: on relay-built histories `C`'s word, conjugated, is
`A`'s word, so `C` identifies `A`'s events in order (the word-level form of
`relay_domain_reconstructs_fold`).

**Reading.** Agreement is real but conditional. Given that the history is made of shared pairs,
each side recovers the same ordered events, and the territorial records agree up to a sign fixed
by the event count. Whether the history *is* made of shared pairs is not visible from the bodies
(§3). That is the precise content of "the existence of a shared ledger does not establish a shared
physical event". The shared-pair posit, its physical birth, and an operational test that
distinguishes `jointW` from `splitW` remain open. No axioms.

Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

noncomputable section

namespace QLF.SharedEvent

open QLF QLF.TensorFromClosure QLF.TensorConservativeReturn QLF.ObservationalEquivalence
open QLF.PerspectiveHolography QLF.TerritoryReturn QLF.SharedReality

/-! ## §1 Words -/

/-- **The shared-event list is unique.** -/
theorem pairBuilt_events_unique {ts ts' : List Twist}
    (h : ts.flatMap sharedPair = ts'.flatMap sharedPair) : ts = ts' := by
  have h' := congrArg projA h
  rwa [projA_pairBuilt, projA_pairBuilt] at h'

lemma map_conj_conj (ts : List Twist) : (ts.map Twist.conj).map Twist.conj = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, conj_conj', ih]

/-- **Both perspectives read the same events, in order.** -/
theorem perspectives_agree_on_events {w : PairHistory} (hw : PairBuilt w) :
    (projB w).map Twist.conj = projA w := by
  obtain ⟨ts, rfl⟩ := hw
  rw [projA_pairBuilt, projB_pairBuilt, map_conj_conj]

/-- `A`'s word alone determines the whole pair-built history. -/
theorem history_from_A {w : PairHistory} (hw : PairBuilt w) :
    w = (projA w).flatMap sharedPair := by
  obtain ⟨ts, rfl⟩ := hw
  rw [projA_pairBuilt]

/-- `B`'s word alone determines the whole pair-built history. -/
theorem history_from_B {w : PairHistory} (hw : PairBuilt w) :
    w = ((projB w).map Twist.conj).flatMap sharedPair := by
  rw [perspectives_agree_on_events hw]
  exact history_from_A hw

/-! ## §2 Territorial records -/

/-- **Phase through a shared pair.** `A`'s fold is `B`'s up to `(-1)^n`. -/
theorem pair_phase_transfer {w : PairHistory} (hw : PairBuilt w) :
    twistMatrixFold (projA w) = (-1 : ℂ) ^ (projB w).length • twistMatrixFold (projB w) := by
  obtain ⟨ts, rfl⟩ := hw
  rw [projA_pairBuilt, projB_pairBuilt, fold_map_conj, smul_smul, List.length_map, ← mul_pow]
  norm_num

/-- **`B`'s territorial record reconstructs `A`'s whole territorial record** on the pair-built
    domain: the ledger (conjugated) and the ordered fold (up to a sign read from `B`'s ledger). -/
theorem pair_domain_reconstructs_record :
    Reconstructs (fun w : {w : PairHistory // PairBuilt w} => recordTB w.1)
      (fun w => recordTA w.1) := by
  rw [reconstructs_iff]
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ he
  have hf : twistMatrixFold (projB w) = twistMatrixFold (projB w') := congrArg Prod.fst he
  have hc : ∀ t, (projB w).count t = (projB w').count t := fun t =>
    congrFun (congrArg Prod.snd he) t
  have hl : (projB w).length = (projB w').length := by
    apply List.Perm.length_eq
    rw [List.perm_iff_count]
    exact hc
  simp only [recordTA]
  refine Prod.ext ?_ ?_
  · simp only
    rw [pair_phase_transfer hw, pair_phase_transfer hw', hf, hl]
  · funext t
    simp only
    rw [pairBuilt_ledger_transfer hw, pairBuilt_ledger_transfer hw', hc]

/-! ## §3 Whether an event was shared is not a fact for the bodies -/

/-- Two shared pairs: `^` then `v` on `A`, each answered on `B`. -/
def jointW : PairHistory :=
  [(false, Twist.up), (true, Twist.down), (false, Twist.down), (true, Twist.up)]

/-- The same tokens on each body, but `A` closes on its own before `B` acts. -/
def splitW : PairHistory :=
  [(false, Twist.up), (false, Twist.down), (true, Twist.down), (true, Twist.up)]

lemma jointW_pairBuilt : PairBuilt jointW := ⟨[Twist.up, Twist.down], rfl⟩

lemma splitW_not_pairBuilt : ¬ PairBuilt splitW := by
  rintro ⟨ts, h⟩
  have hts : ts = [Twist.up, Twist.down] := by
    rw [← projA_pairBuilt ts, ← h]
    rfl
  subst hts
  exact absurd h (by decide)

/-- **The bodies cannot see whether their events were shared.** Same word on each body, one
    history made of shared pairs, the other not. -/
theorem shared_event_not_from_bodies :
    projA jointW = projA splitW ∧ projB jointW = projB splitW ∧
      PairBuilt jointW ∧ ¬ PairBuilt splitW :=
  ⟨rfl, rfl, jointW_pairBuilt, splitW_not_pairBuilt⟩

/-- Both histories close on each body, so the ZFA verdicts agree too: nothing in either
    perspective separates them. -/
theorem both_close_on_each_body :
    countBalanced (projA jointW) ∧ countBalanced (projB jointW) ∧
      countBalanced (projA splitW) ∧ countBalanced (projB splitW) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold countBalanced; decide)

/-- **No function of the two body words decides whether the history is made of shared
    events.** -/
theorem pairing_not_reconstructible :
    ¬ Reconstructs (fun w : PairHistory => (projA w, projB w)) PairBuilt := by
  rw [not_reconstructs_iff]
  obtain ⟨hA, hB, hj, hs⟩ := shared_event_not_from_bodies
  refine ⟨jointW, splitW, by rw [hA, hB], fun h => hs ?_⟩
  rw [← h]
  exact hj

/-- The territorial records are no better: they are functions of the words. -/
theorem pairing_not_from_records :
    ¬ Reconstructs (fun w : PairHistory => (recordTA w, recordTB w)) PairBuilt := by
  rw [not_reconstructs_iff]
  obtain ⟨hA, hB, hj, hs⟩ := shared_event_not_from_bodies
  refine ⟨jointW, splitW, by simp only [recordTA, recordTB, hA, hB], fun h => hs ?_⟩
  rw [← h]
  exact hj

/-! ## §4 Relays -/

/-- **`C` reads `A`'s events in order through a relay.** -/
theorem relay_agree_on_events {w : List Tok3} (hw : RelayBuilt w) :
    (proj 2 w).map Twist.conj = proj 0 w := by
  obtain ⟨ts, rfl⟩ := hw
  rw [proj0_relay, proj2_relay, map_conj_conj]

end QLF.SharedEvent
