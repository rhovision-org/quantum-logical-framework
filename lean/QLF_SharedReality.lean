import QLF_TerritoryReturn

/-!
# QLF_SharedReality — what overlapping perspectives share, at the level of ZFA

The shared-reality principle (Jim, 2026-11-23): *an event is a fact for two perspectives only
through a joint ZFA closure, or through communication between them.* Occurrence is objective
(`QLF_MultiObserver.observers_agree`). What is perspective-relative is which closures a record
carries. This module proves three pieces of that principle on finite models. It is the
ZFA-level follow-up to [`QLF_PerspectiveHolography`](QLF_PerspectiveHolography.lean), whose
two-body results are about *fold* closure. [`QLF_TerritoryReturn`](QLF_TerritoryReturn.lean)
shows that fold closure is weaker than ZFA (`zfa_not_from_fold`) and that the integer ledger
restores it (`ledger_returns_zfa`).

**§1 The ledger lift (two bodies).** A body's *territorial record* is its fold together with its
ledger (twist counts).

* `single_body_territorial_share_only_constants`: perspectives that each hold one body's
  territorial record share only constant observables. So the PerspectiveHolography result
  survives the lift from fold closure to ZFA.
* `territorial_record_reconstructs`: the joint fold plus the ledger reconstructs the phased
  closure test and ZFA together.
* `zfa_not_from_one_body`: neither body's record decides the two-body ZFA verdict.

**§2 Three bodies: what survives a chain.** Perspectives `AB` and `BC` hold the territorial
records of bodies `{A, B}` and `{B, C}`.

* `shared_iff_overlap`: an observable is reconstructible from both `AB` and `BC` **iff** it is
  reconstructible from body `B`'s record alone. What the chain `AB`, `BC` shares is exactly what
  the overlap carries, no more.
* `endpoints_share_only_constants`: `A` and `C` alone share only constants.
* `zfa_A_not_from_BC`: whether `A` closes is not a fact for `BC`.
* `global_zfa_not_from_pair`: three-body ZFA is a fact for neither pair perspective, while all
  three bodies' records decide it (`global_zfa_from_all`).

**§3 Communication by shared pairs (two bodies).** A shared pair puts `t` on `A` and `t.conj` on
`B` (`sharedPair`).

* `pairBuilt_ledger_transfer`: on histories built from shared pairs, `A`'s ledger is a function
  of `B`'s, so `A`'s ZFA verdict is a fact for `B` (`pairBuilt_zfa_iff`). Restricted to that
  domain, `B`'s record reconstructs it (`pair_domain_reconstructs_zfa`).
* `ledger_transfer_fails_without_pairs`: on general histories it is not.

**§4 Relaying.** A relay is an `AB` shared pair followed by a `BC` pair that re-emits on `B` what
`B` received (`relay`).

* `relay_ledger_transfer`, `relay_zfa_iff`: on relay-built histories `A`'s ZFA verdict is a fact
  for `C`.
* `relay_domain_reconstructs_zfa`: restricted to relay-built histories, `C`'s record reconstructs
  `A`'s verdict.
* `relay_phase_transfer`, `relay_domain_reconstructs_fold`: the relay carries the ordered Pauli
  fold too. Each conjugate twist's matrix is the negative of the original, so `C`'s fold equals
  `A`'s up to `(-1)^n`, and `C`'s record reconstructs `A`'s phase.
* `relay_closes_at_B`: the relay body has zero net territorial action (its word is
  count-balanced). This does not say `B` holds no information; its fold need not be trivial.
* `chain_without_relay_fails`, `link_domain_not_reconstructs_zfa`: a shared pair on each link is
  not enough. Two histories that both carry `AB` and `BC` pairs, uncorrelated, agree on `C`'s
  record while `A` closes in one and not the other.

**§5 Projection invariance.** `no_signal_to_C`, `view_changes_only_through_own_events`: inserting
events on other bodies anywhere in a history leaves a body's territorial record unchanged. This
follows from the definition of `proj`. It shows that the territorial record, unlike
`QLF_ClockIntervention`'s (`record_signals`), does not carry a counterpart's events. It is **not**
physical no-signalling under interventions on correlated histories, which stays open.

**Scope.** The bodies are the commuting, independent bodies of
[`QLF_TensorFromClosure`](QLF_TensorFromClosure.lean), and a perspective is a chosen record map.
That makes §2 and §5 close to automatic: no single token touches two bodies, so nothing reaches a
body except through events on it. §3 and §4 show communication *given* the posit that a shared
pair puts one half on each body; they do not derive that posit, and the relay is a defined
pattern, not a dynamics that selects it. `GlobalZFA` is a closure predicate on every body's word,
not an identification of one event shared by the bodies. Open: physical accessibility,
shared-pair birth, dynamical relay selection, physical no-signalling for correlated histories, and
interacting Lorentz covariance (see `Holography_Audit.md` §5, issue #296; the finite three-body
frontier audit of PR #306 is the independent cross-check of §2). No axioms.

Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

noncomputable section

namespace QLF.SharedReality

open QLF QLF.TensorFromClosure QLF.TensorConservativeReturn QLF.ObservationalEquivalence
open QLF.PerspectiveHolography QLF.TerritoryReturn
open scoped TensorProduct

/-! ## §1 The ledger lift -/

/-- Body `A`'s territorial record: its fold and its ledger. -/
def recordTA (w : PairHistory) : M × (Twist → ℕ) :=
  (twistMatrixFold (projA w), fun t => (projA w).count t)

/-- Body `B`'s territorial record. -/
def recordTB (w : PairHistory) : M × (Twist → ℕ) :=
  (twistMatrixFold (projB w), fun t => (projB w).count t)

/-- **The ledger lift.** Single-body territorial perspectives share only constants. -/
theorem single_body_territorial_share_only_constants {X : Type*} (O : PairHistory → X)
    (hA : Reconstructs recordTA O) (hB : Reconstructs recordTB O) (w : PairHistory) :
    O w = O [] := by
  apply shared_respects_chain recordTA recordTB O hA hB
  refine Relation.EqvGen.trans _ (onlyB w) _ (Relation.EqvGen.rel _ _ (Or.inr ?_))
    (Relation.EqvGen.rel _ _ (Or.inl ?_))
  · simp [recordTB, onlyB, projB_map_true]
  · simp [recordTA, onlyB, projA_map_true]

/-- The joint fold plus the ledger reconstructs the phased closure test and ZFA together. -/
theorem territorial_record_reconstructs :
    Reconstructs (fun w => (foldPair w, ledger w)) (fun w => (closureTests w, TerritoryZFA w)) := by
  obtain ⟨R₁, h₁⟩ := joint_record_reconstructs
  obtain ⟨R₂, h₂⟩ := ledger_returns_zfa
  refine ⟨fun p => (R₁ p.1, R₂ p.2), fun w => ?_⟩
  show (R₁ (foldPair w), R₂ (ledger w)) = (closureTests w, TerritoryZFA w)
  rw [h₁, h₂]

/-- The gauge twist `+` on body `B`. -/
def gaugeStepB : PairHistory := [(true, Twist.plus)]

theorem gaugeStepB_not_zfa : ¬ TerritoryZFA gaugeStepB := by
  rintro ⟨-, h⟩
  unfold countBalanced at h
  exact absurd h.2.2.2 (by decide)

/-- **Neither body decides two-body ZFA.** -/
theorem zfa_not_from_one_body :
    ¬ Reconstructs recordTA TerritoryZFA ∧ ¬ Reconstructs recordTB TerritoryZFA := by
  constructor
  · rw [not_reconstructs_iff]
    refine ⟨gaugeStepB, [], by simp [recordTA, gaugeStepB], fun h => ?_⟩
    exact gaugeStepB_not_zfa (by rw [h]; exact nil_zfa)
  · rw [not_reconstructs_iff]
    refine ⟨gaugeStep, [], by simp [recordTB, gaugeStep], fun h => ?_⟩
    exact gaugeStep_not_zfa (by rw [h]; exact nil_zfa)

/-! ## §2 Three bodies -/

/-- A three-body token: a twist labelled by its body `0 = A`, `1 = B`, `2 = C`. -/
abbrev Tok3 := Fin 3 × Twist

/-- Body `i`'s history inside a three-body word. -/
def proj (i : Fin 3) (w : List Tok3) : List Twist :=
  w.filterMap (fun p => if p.1 = i then some p.2 else none)

/-- A body's history, tagged as body `j`. -/
def tag (j : Fin 3) (l : List Twist) : List Tok3 := l.map (fun t => (j, t))

lemma proj_append (i : Fin 3) (a b : List Tok3) : proj i (a ++ b) = proj i a ++ proj i b := by
  simp [proj, List.filterMap_append]

lemma proj_tag (i j : Fin 3) (l : List Twist) : proj i (tag j l) = if j = i then l else [] := by
  induction l with
  | nil => simp [proj, tag]
  | cons t l ih =>
    by_cases h : j = i
    · simp only [h, ite_true] at ih ⊢
      simp only [proj, tag, List.map_cons, List.filterMap_cons, ite_true] at ih ⊢
      rw [ih]
    · simp only [h, ite_false] at ih ⊢
      simp only [proj, tag, List.map_cons, List.filterMap_cons, h, ite_false] at ih ⊢
      exact ih

/-- Body `i`'s territorial record. -/
def bodyView (i : Fin 3) (w : List Tok3) : M × (Twist → ℕ) :=
  (twistMatrixFold (proj i w), fun t => (proj i w).count t)

lemma bodyView_congr {i : Fin 3} {w w' : List Tok3} (h : proj i w = proj i w') :
    bodyView i w = bodyView i w' := by
  simp [bodyView, h]

/-- Perspective `AB`. -/
def viewAB (w : List Tok3) := (bodyView 0 w, bodyView 1 w)

/-- Perspective `BC`. -/
def viewBC (w : List Tok3) := (bodyView 1 w, bodyView 2 w)

/-- The overlap: body `B` alone. -/
def viewB (w : List Tok3) := bodyView 1 w

/-- `A` and `C` alone. -/
def viewA (w : List Tok3) := bodyView 0 w
def viewC (w : List Tok3) := bodyView 2 w

/-- `w`'s `A` and `B`, followed by `w'`'s `C`. -/
def splice (w w' : List Tok3) : List Tok3 :=
  tag 0 (proj 0 w) ++ tag 1 (proj 1 w) ++ tag 2 (proj 2 w')

lemma proj_splice_0 (w w' : List Tok3) : proj 0 (splice w w') = proj 0 w := by
  simp [splice, proj_append, proj_tag]

lemma proj_splice_1 (w w' : List Tok3) : proj 1 (splice w w') = proj 1 w := by
  simp [splice, proj_append, proj_tag]

lemma proj_splice_2 (w w' : List Tok3) : proj 2 (splice w w') = proj 2 w' := by
  simp [splice, proj_append, proj_tag]

/-- **What a chain shares is what its overlap carries.** -/
theorem shared_iff_overlap {X : Type*} [Nonempty X] (O : List Tok3 → X) :
    (Reconstructs viewAB O ∧ Reconstructs viewBC O) ↔ Reconstructs viewB O := by
  constructor
  · rintro ⟨hAB, hBC⟩
    rw [reconstructs_iff] at hAB hBC ⊢
    intro w w' hB
    have h₁ : O w = O (splice w w') := by
      apply hAB
      simp only [viewAB, bodyView_congr (proj_splice_0 w w'), bodyView_congr (proj_splice_1 w w')]
    have h₂ : O (splice w w') = O w' := by
      apply hBC
      have hB' : bodyView 1 (splice w w') = bodyView 1 w' := by
        rw [bodyView_congr (proj_splice_1 w w')]
        exact hB
      simp only [viewBC, hB', bodyView_congr (proj_splice_2 w w')]
    exact h₁.trans h₂
  · intro hB
    exact ⟨reconstructs_of_refines viewB viewAB Prod.snd (fun _ => rfl) O hB,
      reconstructs_of_refines viewB viewBC Prod.fst (fun _ => rfl) O hB⟩

/-- **`A` and `C` alone share only constants.** -/
theorem endpoints_share_only_constants {X : Type*} (O : List Tok3 → X)
    (hA : Reconstructs viewA O) (hC : Reconstructs viewC O) (w : List Tok3) : O w = O [] := by
  obtain ⟨RA, hRA⟩ := hA
  obtain ⟨RC, hRC⟩ := hC
  have h₁ : O w = O (tag 0 (proj 0 w)) := by
    rw [← hRA w, ← hRA (tag 0 (proj 0 w))]
    congr 1
    apply bodyView_congr
    simp [proj_tag]
  have h₂ : O (tag 0 (proj 0 w)) = O [] := by
    rw [← hRC, ← hRC []]
    congr 1
    apply bodyView_congr
    rw [proj_tag]
    simp [proj]
  exact h₁.trans h₂

/-- Body `i` is count-balanced. -/
def BodyZFA (i : Fin 3) (w : List Tok3) : Prop := countBalanced (proj i w)

/-- Three-body ZFA: every body is count-balanced. -/
def GlobalZFA (w : List Tok3) : Prop := ∀ i, BodyZFA i w

/-- The gauge twist `+` on body `i`. -/
def gauge3 (i : Fin 3) : List Tok3 := [(i, Twist.plus)]

lemma proj_gauge3 (i j : Fin 3) : proj j (gauge3 i) = if i = j then [Twist.plus] else [] := by
  simpa [gauge3, tag] using proj_tag j i [Twist.plus]

lemma not_body_zfa_gauge3 (i : Fin 3) : ¬ BodyZFA i (gauge3 i) := by
  unfold BodyZFA countBalanced
  rw [proj_gauge3, if_pos rfl]
  intro h
  exact absurd h.2.2.2 (by decide)

lemma body_zfa_nil (i : Fin 3) : BodyZFA i [] := by
  unfold BodyZFA countBalanced proj
  simp

/-- **Whether `A` closes is not a fact for `BC`.** -/
theorem zfa_A_not_from_BC : ¬ Reconstructs viewBC (BodyZFA 0) := by
  rw [not_reconstructs_iff]
  refine ⟨gauge3 0, [], ?_, fun h => not_body_zfa_gauge3 0 (by rw [h]; exact body_zfa_nil 0)⟩
  simp only [viewBC]
  rw [bodyView_congr (w' := []) (by rw [proj_gauge3]; simp [proj]),
    bodyView_congr (i := 2) (w' := []) (by rw [proj_gauge3]; simp [proj])]

/-- **Three-body ZFA is a fact for neither pair perspective.** -/
theorem global_zfa_not_from_pair :
    ¬ Reconstructs viewAB GlobalZFA ∧ ¬ Reconstructs viewBC GlobalZFA := by
  have hnil : GlobalZFA [] := fun i => body_zfa_nil i
  constructor
  · rw [not_reconstructs_iff]
    refine ⟨gauge3 2, [], ?_, fun h => ?_⟩
    · simp only [viewAB]
      rw [bodyView_congr (i := 0) (w' := []) (by rw [proj_gauge3]; simp [proj]),
        bodyView_congr (i := 1) (w' := []) (by rw [proj_gauge3]; simp [proj])]
    · have hg : GlobalZFA (gauge3 2) := by rw [h]; exact hnil
      exact not_body_zfa_gauge3 2 (hg 2)
  · rw [not_reconstructs_iff]
    refine ⟨gauge3 0, [], ?_, fun h => ?_⟩
    · simp only [viewBC]
      rw [bodyView_congr (i := 1) (w' := []) (by rw [proj_gauge3]; simp [proj]),
        bodyView_congr (i := 2) (w' := []) (by rw [proj_gauge3]; simp [proj])]
    · have hg : GlobalZFA (gauge3 0) := by rw [h]; exact hnil
      exact not_body_zfa_gauge3 0 (hg 0)

/-- All three bodies' records decide three-body ZFA. -/
theorem global_zfa_from_all :
    Reconstructs (fun w => (bodyView 0 w, bodyView 1 w, bodyView 2 w)) GlobalZFA := by
  let bal : M × (Twist → ℕ) → Prop := fun v =>
    v.2 Twist.up = v.2 Twist.down ∧ v.2 Twist.left = v.2 Twist.right ∧
      v.2 Twist.slash = v.2 Twist.backslash ∧ v.2 Twist.plus = v.2 Twist.minus
  refine ⟨fun v => bal v.1 ∧ bal v.2.1 ∧ bal v.2.2, fun w => ?_⟩
  apply propext
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 0, h 1, h 2⟩

/-! ## §3 Communication by shared pairs -/

/-- A shared pair: `t` on body `A`, its conjugate on body `B`. -/
def sharedPair (t : Twist) : PairHistory := [(false, t), (true, t.conj)]

/-- A history built from shared pairs only. -/
def PairBuilt (w : PairHistory) : Prop := ∃ ts : List Twist, w = ts.flatMap sharedPair

lemma conj_conj' (t : Twist) : t.conj.conj = t := by cases t <;> rfl

lemma count_map_conj (ts : List Twist) (t : Twist) :
    (ts.map Twist.conj).count t = ts.count t.conj := by
  induction ts with
  | nil => rfl
  | cons a ts ih =>
    have key : (a.conj == t) = (a == t.conj) := by cases a <;> cases t <;> rfl
    simp only [List.map_cons, List.count_cons, ih, key]

lemma projA_pairBuilt (ts : List Twist) : projA (ts.flatMap sharedPair) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.flatMap_cons, sharedPair, ih]

lemma projB_pairBuilt (ts : List Twist) :
    projB (ts.flatMap sharedPair) = ts.map Twist.conj := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.flatMap_cons, sharedPair, ih]

/-- **Shared pairs carry `A`'s ledger to `B`.** -/
theorem pairBuilt_ledger_transfer {w : PairHistory} (hw : PairBuilt w) (t : Twist) :
    (projA w).count t = (projB w).count t.conj := by
  obtain ⟨ts, rfl⟩ := hw
  rw [projA_pairBuilt, projB_pairBuilt, count_map_conj, conj_conj']

/-- On pair-built histories `A`'s ZFA verdict is a fact for `B`: the two coincide. -/
theorem pairBuilt_zfa_iff {w : PairHistory} (hw : PairBuilt w) :
    countBalanced (projA w) ↔ countBalanced (projB w) := by
  unfold countBalanced
  simp only [pairBuilt_ledger_transfer hw]
  simp only [Twist.conj]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩

/-- On the pair-built domain, `B`'s record reconstructs `A`'s ZFA verdict. The domain restriction
    is explicit: the record map is defined on pair-built histories only. -/
theorem pair_domain_reconstructs_zfa :
    Reconstructs (fun w : {w : PairHistory // PairBuilt w} => recordTB w.1)
      (fun w => countBalanced (projA w.1)) := by
  rw [reconstructs_iff]
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ he
  have key : ∀ t, (projB w).count t = (projB w').count t := fun t =>
    congrFun (congrArg Prod.snd he) t
  apply propext
  rw [pairBuilt_zfa_iff hw, pairBuilt_zfa_iff hw']
  simp only [countBalanced, key]

/-- **Without shared pairs, `B`'s record carries nothing of `A`'s ledger.** -/
theorem ledger_transfer_fails_without_pairs :
    ¬ Reconstructs recordTB (fun w => countBalanced (projA w)) := by
  rw [not_reconstructs_iff]
  refine ⟨gaugeStep, [], by simp [recordTB, gaugeStep], fun h => ?_⟩
  have h' : countBalanced (projA gaugeStep) := by
    rw [h]; unfold countBalanced; simp
  unfold countBalanced at h'
  exact absurd h'.2.2.2 (by decide)

/-! ## §4 Relaying through a third body -/

/-- A relay of `t` from `A` to `C` through `B`: an `AB` shared pair, then a `BC` shared pair that
    re-emits on `B` what `B` received. -/
def relay (t : Twist) : List Tok3 := [(0, t), (1, t.conj), (1, t), (2, t.conj)]

/-- A three-body history built from relays only. -/
def RelayBuilt (w : List Tok3) : Prop := ∃ ts : List Twist, w = ts.flatMap relay

lemma proj0_relay (ts : List Twist) : proj 0 (ts.flatMap relay) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, proj_append, ih]
    simp [proj, relay]

lemma proj2_relay (ts : List Twist) : proj 2 (ts.flatMap relay) = ts.map Twist.conj := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, proj_append, ih]
    simp [proj, relay]

lemma proj1_relay (ts : List Twist) :
    proj 1 (ts.flatMap relay) = ts.flatMap (fun t => [t.conj, t]) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, List.flatMap_cons, proj_append, ih]
    simp [proj, relay]

/-- **A relay carries `A`'s ledger to `C`.** -/
theorem relay_ledger_transfer {w : List Tok3} (hw : RelayBuilt w) (t : Twist) :
    (proj 0 w).count t = (proj 2 w).count t.conj := by
  obtain ⟨ts, rfl⟩ := hw
  rw [proj0_relay, proj2_relay, count_map_conj, conj_conj']

/-- On relay-built histories, `A`'s ZFA verdict is a fact for `C`. -/
theorem relay_zfa_iff {w : List Tok3} (hw : RelayBuilt w) : BodyZFA 0 w ↔ BodyZFA 2 w := by
  unfold BodyZFA countBalanced
  simp only [relay_ledger_transfer hw]
  simp only [Twist.conj]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩

lemma count_conj_pairs (ts : List Twist) (t : Twist) :
    (ts.flatMap (fun a => [a.conj, a])).count t = (ts.flatMap (fun a => [a.conj, a])).count t.conj := by
  induction ts with
  | nil => rfl
  | cons a ts ih =>
    have k1 : (a.conj == t.conj) = (a == t) := by cases a <;> cases t <;> rfl
    have k2 : (a == t.conj) = (a.conj == t) := by cases a <;> cases t <;> rfl
    simp only [List.flatMap_cons, List.count_append, ih, List.count_cons, List.count_nil, k1, k2]
    omega

/-- **The relay body has zero net territorial action.** `B` re-emits everything it receives, so
    its word is count-balanced. This is a statement about `B`'s ledger only: `B`'s word is
    nonempty and its fold need not be trivial, so it does not say that `B` holds no information. -/
theorem relay_closes_at_B {w : List Tok3} (hw : RelayBuilt w) : BodyZFA 1 w := by
  obtain ⟨ts, rfl⟩ := hw
  unfold BodyZFA countBalanced
  rw [proj1_relay]
  exact ⟨count_conj_pairs ts Twist.up, count_conj_pairs ts Twist.left,
    count_conj_pairs ts Twist.slash, count_conj_pairs ts Twist.plus⟩

/-- On the relay domain, `C`'s record reconstructs `A`'s ZFA verdict. The domain restriction is
    explicit: the record map is defined on relay-built histories only. -/
theorem relay_domain_reconstructs_zfa :
    Reconstructs (fun w : {w : List Tok3 // RelayBuilt w} => viewC w.1)
      (fun w => BodyZFA 0 w.1) := by
  rw [reconstructs_iff]
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ he
  have key : ∀ t, (proj 2 w).count t = (proj 2 w').count t := fun t =>
    congrFun (congrArg Prod.snd he) t
  apply propext
  rw [relay_zfa_iff hw, relay_zfa_iff hw']
  simp only [BodyZFA, countBalanced, key]

/-! ### Phase through a relay -/

private instance lawfulBEqTwist : LawfulBEq Twist where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

lemma conj_toMatrix (t : Twist) : t.conj.toMatrix = -t.toMatrix := by
  cases t <;> simp [Twist.conj, Twist.toMatrix]

lemma fold_map_conj (ts : List Twist) :
    twistMatrixFold (ts.map Twist.conj) = (-1 : ℂ) ^ ts.length • twistMatrixFold ts := by
  induction ts with
  | nil => simp [twistMatrixFold]
  | cons t ts ih =>
    show t.conj.toMatrix * twistMatrixFold (ts.map Twist.conj) =
      (-1 : ℂ) ^ (ts.length + 1) • (t.toMatrix * twistMatrixFold ts)
    rw [ih, conj_toMatrix, Matrix.mul_smul, neg_mul, pow_succ, mul_neg_one, neg_smul, smul_neg]

/-- **A relay carries the ordered phase, not only the ledger.** Every conjugate twist's matrix is
    the negative of the original, so `C`'s fold is `A`'s up to the sign `(-1)^n`, where `n` is the
    number of relays. -/
theorem relay_phase_transfer {w : List Tok3} (hw : RelayBuilt w) :
    twistMatrixFold (proj 0 w) = (-1 : ℂ) ^ (proj 2 w).length • twistMatrixFold (proj 2 w) := by
  obtain ⟨ts, rfl⟩ := hw
  rw [proj0_relay, proj2_relay, fold_map_conj, smul_smul, List.length_map, ← mul_pow]
  norm_num

/-- On the relay domain, `C`'s record reconstructs `A`'s full Pauli fold, phase included. -/
theorem relay_domain_reconstructs_fold :
    Reconstructs (fun w : {w : List Tok3 // RelayBuilt w} => viewC w.1)
      (fun w => twistMatrixFold (proj 0 w.1)) := by
  rw [reconstructs_iff]
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ he
  have hf : twistMatrixFold (proj 2 w) = twistMatrixFold (proj 2 w') := congrArg Prod.fst he
  have hl : (proj 2 w).length = (proj 2 w').length := by
    apply List.Perm.length_eq
    rw [List.perm_iff_count]
    intro t
    exact congrFun (congrArg Prod.snd he) t
  simp only
  rw [relay_phase_transfer hw, relay_phase_transfer hw', hf, hl]

/-! ### Links without a relay -/

/-- An `AB` shared pair. -/
def pairAB (t : Twist) : List Tok3 := [(0, t), (1, t.conj)]

/-- A `BC` shared pair. -/
def pairBC (t : Twist) : List Tok3 := [(1, t), (2, t.conj)]

/-- Histories with shared pairs on both links, the two links uncorrelated. -/
def LinkBuilt (w : List Tok3) : Prop :=
  ∃ as bs : List Twist, w = as.flatMap pairAB ++ bs.flatMap pairBC

/-- Two link-built histories, each with `AB` and `BC` pairs. -/
def linkW₁ : List Tok3 := [Twist.up, Twist.down].flatMap pairAB ++ [Twist.up].flatMap pairBC
def linkW₂ : List Tok3 := [Twist.up, Twist.up].flatMap pairAB ++ [Twist.up].flatMap pairBC

/-- **A pair on each link is not enough.** `linkW₁` and `linkW₂` both carry `AB` and `BC` shared
    pairs and agree on `C`'s record, but `A` closes in one and not the other. -/
theorem chain_without_relay_fails :
    viewC linkW₁ = viewC linkW₂ ∧ BodyZFA 0 linkW₁ ∧ ¬ BodyZFA 0 linkW₂ := by
  refine ⟨?_, ?_, ?_⟩
  · apply bodyView_congr
    simp [linkW₁, linkW₂, proj, pairAB, pairBC]
  · simp [BodyZFA, countBalanced, linkW₁, proj, pairAB, pairBC, Twist.conj]
  · simp [BodyZFA, countBalanced, linkW₂, proj, pairAB, pairBC, Twist.conj]

/-- **So on the link domain, `C`'s record does not reconstruct `A`'s verdict**, in contrast with
    the relay domain (`relay_domain_reconstructs_zfa`). -/
theorem link_domain_not_reconstructs_zfa :
    ¬ Reconstructs (fun w : {w : List Tok3 // LinkBuilt w} => viewC w.1)
      (fun w => BodyZFA 0 w.1) := by
  rw [not_reconstructs_iff]
  obtain ⟨hv, h₁, h₂⟩ := chain_without_relay_fails
  refine ⟨⟨linkW₁, _, _, rfl⟩, ⟨linkW₂, _, _, rfl⟩, hv, fun h => h₂ ?_⟩
  have h' : BodyZFA 0 linkW₁ = BodyZFA 0 linkW₂ := h
  rw [← h']
  exact h₁

/-! ## §5 Projection invariance (no-signalling for the territorial record) -/

/-- **No signal without a shared event.** Inserting any word of events on bodies `A` and `B`
    anywhere in a history leaves `C`'s territorial record unchanged. -/
theorem no_signal_to_C (p q u : List Tok3) (hu : ∀ x ∈ u, x.1 ≠ 2) :
    viewC (p ++ u ++ q) = viewC (p ++ q) := by
  apply bodyView_congr
  have hu' : proj 2 u = [] := by
    unfold proj
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    simp [hu x hx]
  rw [proj_append, proj_append, proj_append, hu', List.append_nil]

/-- **Contrast.** `QLF_ClockIntervention`'s record `(p, q.length)` carries the counterpart's
    length, so it signals. The territorial record carries only a body's own events, so a body's
    record changes only through events on that body: in a shared pair, a relay, or its own. -/
theorem view_changes_only_through_own_events (i : Fin 3) (p q u : List Tok3)
    (hu : ∀ x ∈ u, x.1 ≠ i) : bodyView i (p ++ u ++ q) = bodyView i (p ++ q) := by
  apply bodyView_congr
  have hu' : proj i u = [] := by
    unfold proj
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    simp [hu x hx]
  rw [proj_append, proj_append, proj_append, hu', List.append_nil]

end QLF.SharedReality
