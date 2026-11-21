import QLF_ObservationalEquivalence

/-!
# QLF_PerspectiveHolography — the reconstruction criterion, and the minimal boundary record

Issue #296 asks for a holographic dictionary derived from ZFA closure: a boundary encoding
`D_B` and reconstruction maps `R_B^O` with `R_B^O (D_B h) = O h`. PR #300 ran the factorization
criterion as a finite Python audit. This module proves it, proves what it gives for two
overlapping perspectives, and instantiates it on the two-body joint-closure system of
[`QLF_ObservationalEquivalence`](QLF_ObservationalEquivalence.lean), where the greatest
bisimulation picks out the boundary record.

**§1 Generic (any history type, record and observable).**

* `reconstructs_iff` — the factorization lemma: `O` is reconstructible from `D` iff
  `D h₁ = D h₂ → O h₁ = O h₂`. Standard; stated so every dictionary entry has an exact test.
* `not_reconstructs_iff` — failure is always witnessed by a collision: two histories with the same
  record and different observable values.
* `reconstructs_of_refines` — a finer record reconstructs everything a coarser one does.
* `shared_respects_chain` — an observable both perspectives reconstruct is constant along every
  chain of histories in which consecutive ones share a record in *either* perspective. This is
  the overlap interface, defined from the records alone.
* `perspectives_agree` — two reconstructions of one observable agree on every history.

**§2 Two-body joint closure.** The observable is the full closure test
`closureTests w = fun c z => ClosesWith w c z` (does `w ++ c` close jointly with phase `z`).

* `joint_record_reconstructs` — the joint fold `foldPair` reconstructs it.
* `joint_record_minimal` — and any record that reconstructs it refines `foldPair`. So the joint
  fold is the **coarsest** boundary record for joint closure, which is the greatest-bisimulation
  result (`obsEquiv_iff_pairEquiv`) read as a dictionary entry.
* `closure_verdict_reconstructible` — closure now (`∃ z, ClosesWith w [] z`) is part of it: the
  record cannot identify a closed history with an open one.
* `phase_blind_record_fails` — the record that keeps only *whether* each continuation closes
  cannot reconstruct the phased test; the gauge flip is the collision (`phase_is_needed`).
* `single_body_perspectives_share_only_constants` — the perspectives that see one body each
  share only constant observables: any observable both reconstruct takes one value on all
  two-body histories. Joint closure is visible to neither alone.

**Scope.** A "perspective" here is a record map, not a physical Markov blanket; no causal
accessibility, metric or clock is derived. The two-body premises are those of
`QLF_TensorFromClosure`. Cosmic holography (#296 §6) is untouched. No axioms.
-/

noncomputable section

namespace QLF.PerspectiveHolography

/-! ## §1 The reconstruction criterion -/

section Generic

variable {H B B' X : Type*}

/-- `O` is reconstructible from the record `D`. -/
def Reconstructs (D : H → B) (O : H → X) : Prop :=
  ∃ R : B → X, ∀ h, R (D h) = O h

/-- **The factorization lemma.** -/
theorem reconstructs_iff [Nonempty X] (D : H → B) (O : H → X) :
    Reconstructs D O ↔ ∀ h₁ h₂, D h₁ = D h₂ → O h₁ = O h₂ := by
  classical
  constructor
  · rintro ⟨R, hR⟩ h₁ h₂ he
    rw [← hR h₁, ← hR h₂, he]
  · intro hc
    refine ⟨fun b => if hb : ∃ h, D h = b then O hb.choose else Classical.arbitrary X, ?_⟩
    intro h
    have hb : ∃ h', D h' = D h := ⟨h, rfl⟩
    simp only [hb, dite_true]
    exact hc _ _ hb.choose_spec

/-- **Failure is a collision.** -/
theorem not_reconstructs_iff [Nonempty X] (D : H → B) (O : H → X) :
    ¬ Reconstructs D O ↔ ∃ h₁ h₂, D h₁ = D h₂ ∧ O h₁ ≠ O h₂ := by
  rw [reconstructs_iff]
  push Not
  rfl

/-- A finer record reconstructs everything a coarser one does. -/
theorem reconstructs_of_refines (D : H → B) (D' : H → B') (g : B' → B)
    (hg : ∀ h, g (D' h) = D h) (O : H → X) (hO : Reconstructs D O) : Reconstructs D' O := by
  obtain ⟨R, hR⟩ := hO
  exact ⟨fun b => R (g b), fun h => by simp only [hg, hR]⟩

/-- Histories linked by sharing a record in either perspective. -/
def SharedStep (D₁ : H → B) (D₂ : H → B') (h h' : H) : Prop :=
  D₁ h = D₁ h' ∨ D₂ h = D₂ h'

/-- **The overlap interface.** An observable both perspectives reconstruct is constant along any
    chain of shared records. -/
theorem shared_respects_chain (D₁ : H → B) (D₂ : H → B') (O : H → X)
    (h₁ : Reconstructs D₁ O) (h₂ : Reconstructs D₂ O) {h h' : H}
    (hc : Relation.EqvGen (SharedStep D₁ D₂) h h') : O h = O h' := by
  obtain ⟨R₁, hR₁⟩ := h₁
  obtain ⟨R₂, hR₂⟩ := h₂
  induction hc with
  | rel x y hxy =>
    rcases hxy with e | e
    · rw [← hR₁ x, ← hR₁ y, e]
    · rw [← hR₂ x, ← hR₂ y, e]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Perspective consistency.** Two reconstructions of one observable agree on every history. -/
theorem perspectives_agree (D₁ : H → B) (D₂ : H → B') (O : H → X)
    (R₁ : B → X) (R₂ : B' → X) (hR₁ : ∀ h, R₁ (D₁ h) = O h) (hR₂ : ∀ h, R₂ (D₂ h) = O h)
    (h : H) : R₁ (D₁ h) = R₂ (D₂ h) := by
  rw [hR₁, hR₂]

end Generic

/-! ## §2 Two-body joint closure -/

open QLF QLF.TensorFromClosure QLF.TensorConservativeReturn QLF.ObservationalEquivalence
open QLF.ConservativeReturn
open scoped TensorProduct

/-- The full joint-closure test of a history: which continuations close it, with which phase. -/
def closureTests (w : PairHistory) : PairHistory → ℂ → Prop := fun c z => ClosesWith w c z

lemma closureTests_eq_iff (w w' : PairHistory) :
    closureTests w = closureTests w' ↔ ObsEquiv w w' := by
  constructor
  · intro h c z
    rw [show ClosesWith w c z = closureTests w c z from rfl, h]
    rfl
  · intro h
    funext c z
    exact propext (h c z)

/-- **The joint fold reconstructs the closure test.** -/
theorem joint_record_reconstructs : Reconstructs foldPair closureTests := by
  rw [reconstructs_iff]
  intro w w' he
  exact (closureTests_eq_iff w w').2 ((obsEquiv_iff_pairEquiv w w').2 he)

/-- **The joint fold is the coarsest such record:** any record that reconstructs the closure
    test refines it. -/
theorem joint_record_minimal {B : Type*} (D : PairHistory → B)
    (hD : Reconstructs D closureTests) (w w' : PairHistory) (he : D w = D w') :
    foldPair w = foldPair w' := by
  have h := (reconstructs_iff D closureTests).1 hD w w' he
  exact (obsEquiv_iff_pairEquiv w w').1 ((closureTests_eq_iff w w').1 h)

/-- **Closure preservation:** whether a history closes now is reconstructible from the joint fold. -/
theorem closure_verdict_reconstructible :
    Reconstructs foldPair (fun w => ∃ z : ℂ, ClosesWith w [] z) := by
  rw [reconstructs_iff]
  intro w w' he
  simp only [ClosesWith, List.append_nil, he]

/-- The phase-blind record: which continuations close, without the phase. -/
def bareRecord (w : PairHistory) : PairHistory → Prop := fun c => ∃ z : ℂ, ClosesWith w c z

/-- **A phase-blind record fails.** The gauge flip and the empty history share it but differ on
    the phased test. -/
theorem phase_blind_record_fails : ¬ Reconstructs bareRecord closureTests := by
  rw [not_reconstructs_iff]
  refine ⟨gaugeFlip, [], ?_, ?_⟩
  · funext c
    exact propext (phase_is_needed.1 c)
  · intro h
    exact phase_is_needed.2 ((closureTests_eq_iff _ _).1 h)

/-- What a perspective on body `A` alone sees. -/
def recordA (w : PairHistory) : M := twistMatrixFold (projA w)

/-- What a perspective on body `B` alone sees. -/
def recordB (w : PairHistory) : M := twistMatrixFold (projB w)

/-- Body `B`'s events of a history, as a history. -/
def onlyB (w : PairHistory) : PairHistory := (projB w).map (fun t => (true, t))

lemma projA_map_true (l : List Twist) : projA (l.map (fun t => (true, t))) = [] := by
  induction l with
  | nil => rfl
  | cons t l ih => simpa using ih

lemma projB_map_true (l : List Twist) : projB (l.map (fun t => (true, t))) = l := by
  induction l with
  | nil => rfl
  | cons t l ih => simpa using ih

/-- **Single-body perspectives share only constants.** Any observable reconstructible both from
    body `A`'s record and from body `B`'s record takes the same value on every two-body history. -/
theorem single_body_perspectives_share_only_constants {X : Type*} (O : PairHistory → X)
    (hA : Reconstructs recordA O) (hB : Reconstructs recordB O) (w : PairHistory) :
    O w = O [] := by
  apply shared_respects_chain recordA recordB O hA hB
  refine Relation.EqvGen.trans _ (onlyB w) _ (Relation.EqvGen.rel _ _ (Or.inr ?_))
    (Relation.EqvGen.rel _ _ (Or.inl ?_))
  · simp [recordB, onlyB, projB_map_true]
  · simp [recordA, onlyB, projA_map_true]

/-- **The two-body dictionary, summarized.** -/
theorem two_body_dictionary :
    Reconstructs foldPair closureTests ∧
    (∀ {B : Type} (D : PairHistory → B), Reconstructs D closureTests →
      ∀ w w', D w = D w' → foldPair w = foldPair w') ∧
    ¬ Reconstructs bareRecord closureTests :=
  ⟨joint_record_reconstructs, fun D hD => joint_record_minimal D hD, phase_blind_record_fails⟩

end QLF.PerspectiveHolography
