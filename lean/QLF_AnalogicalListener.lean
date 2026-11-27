/-
# QLF_AnalogicalListener

Gate **CC1** of the cooperative-closure program (`Cooperative_Intelligence.md` §5): a finite,
typed analogical listener.  An analogy `A : B :: C : ?` is a **partial correspondence** from a
source relational structure to a target one.  Its unmapped source elements are its **open
obligations**; it **closes** when every obligation is filled and the source relation is carried
exactly onto the target relation; it is **rejected** when no completion can close.

Proved, for finite source and target with one binary relation each:

1. **Extension never rewrites an established mapping** (`extend_le`, `extend_keeps`).
2. **A closed analogy preserves the source relations** (`closed_preserves`), and filling one
   obligation keeps consistency **iff** a local check against what is already mapped passes
   (`consistent_extend_iff`), so a listener can be grown one contribution at a time.
3. **An invalid correspondence has a counterexample, and consistency is decidable**
   (`not_consistent_iff`, the `Decidable` instance): a pair of mapped elements whose relation is
   not carried.
4. **An unresolved analogy is never promoted**: an open obligation means not closed
   (`open_not_closed`); an inconsistency is permanent under every extension
   (`inconsistent_persists`), so it is rejected (`inconsistent_rejected`); and a closed analogy has
   no open obligation left (`closed_has_no_obligation`).

Worked case (`rutherford_closes`, `wrong_completion_rejected`): sun : planet :: nucleus : ? closes
with *electron* and is rejected with *nucleus*.  `similarity_not_correspondence`: a mapping that
matches every element's label (a similarity) can still fail to carry the relation.

What this module does **not** do: it does not encode a listener as a twist history.  Whether
listener closure is a ZFA closure under an encoding fixed in advance is the open bridge CC4.

No axioms.  Part of [Quantum Logical Framework (QLF)](../README.md).
-/

import Mathlib

namespace QLF.AnalogicalListener

/-! ## Relational structures and partial correspondences -/

set_option linter.unusedSectionVars false

variable {S T : Type*}

/-- A finite relational structure with one binary relation. -/
structure RelStr (α : Type*) where
  rel : α → α → Bool

/-- A partial correspondence from source to target: the analogy built so far. -/
abbrev Corr (S T : Type*) := S → Option T

/-- Whether two (possibly unmapped) images are compatible with a source relation value.  Unmapped
elements impose nothing yet. -/
def compat (RT : RelStr T) : Option T → Option T → Bool → Prop
  | some x, some y, r => RT.rel x y = r
  | _, _, _ => True

instance (RT : RelStr T) [DecidableEq T] (u v : Option T) (r : Bool) :
    Decidable (compat RT u v r) := by
  cases u <;> cases v <;> unfold compat <;> infer_instance

/-- The correspondence carries the source relation exactly, wherever both ends are mapped. -/
def Consistent (RS : RelStr S) (RT : RelStr T) (m : Corr S T) : Prop :=
  ∀ a b, compat RT (m a) (m b) (RS.rel a b)

instance [Fintype S] [DecidableEq T] (RS : RelStr S) (RT : RelStr T) (m : Corr S T) :
    Decidable (Consistent RS RT m) := by
  unfold Consistent; infer_instance

/-- `m'` extends `m`: every established mapping is kept. -/
def Extends (m m' : Corr S T) : Prop := ∀ a x, m a = some x → m' a = some x

/-- An open obligation: a source element not yet mapped. -/
def IsOpen (m : Corr S T) (a : S) : Prop := m a = none

/-- Closure: no open obligation and the relation is carried. -/
def Closed (RS : RelStr S) (RT : RelStr T) (m : Corr S T) : Prop :=
  (∀ a, (m a).isSome) ∧ Consistent RS RT m

/-- Rejection: no extension closes. -/
def Rejected (RS : RelStr S) (RT : RelStr T) (m : Corr S T) : Prop :=
  ∀ m', Extends m m' → ¬ Closed RS RT m'

/-! ## 1. Extension keeps established mappings -/

variable [DecidableEq S]

/-- Fill obligation `a` with `x`; a mapped `a` is left as it is. -/
def extend (m : Corr S T) (a : S) (x : T) : Corr S T :=
  fun b => if b = a ∧ m a = none then some x else m b

theorem extend_le (m : Corr S T) (a : S) (x : T) : Extends m (extend m a x) := by
  intro b y hb
  unfold extend
  split_ifs with h
  · obtain ⟨rfl, hn⟩ := h
    rw [hn] at hb; cases hb
  · exact hb

theorem extend_keeps {m : Corr S T} {b : S} {y : T} (a : S) (x : T) (hb : m b = some y) :
    extend m a x b = some y :=
  extend_le m a x b y hb

theorem extends_trans {m₁ m₂ m₃ : Corr S T} (h₁ : Extends m₁ m₂) (h₂ : Extends m₂ m₃) :
    Extends m₁ m₃ := fun a x h => h₂ a x (h₁ a x h)

/-! ## 2. Closure preserves the source relations; growth is a local check -/

/-- A closed analogy carries every source relation onto the target. -/
theorem closed_preserves {RS : RelStr S} {RT : RelStr T} {m : Corr S T}
    (h : Closed RS RT m) (a b : S) (x y : T) (ha : m a = some x) (hb : m b = some y) :
    RT.rel x y = RS.rel a b := by
  have := h.2 a b
  rw [ha, hb] at this
  exact this

/-- **Growing a listener is local.**  Filling an open obligation `a` with `x` keeps consistency
iff `m` was consistent and `x` agrees with `a` on itself and on every element already mapped. -/
theorem consistent_extend_iff {RS : RelStr S} {RT : RelStr T} {m : Corr S T} {a : S} {x : T}
    (hopen : m a = none) :
    Consistent RS RT (extend m a x) ↔
      Consistent RS RT m ∧ RT.rel x x = RS.rel a a ∧
        ∀ b y, m b = some y → RT.rel x y = RS.rel a b ∧ RT.rel y x = RS.rel b a := by
  have hea : extend m a x a = some x := by simp [extend, hopen]
  have heb : ∀ b, b ≠ a → extend m a x b = m b := by
    intro b hb; simp [extend, hb]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro b c
      by_cases hb : b = a
      · subst hb; rw [hopen]; trivial
      by_cases hc : c = a
      · subst hc; cases m b <;> rw [hopen] <;> trivial
      have := h b c
      rwa [heb b hb, heb c hc] at this
    · have := h a a
      rwa [hea] at this
    · intro b y hby
      have hba : b ≠ a := by rintro rfl; rw [hopen] at hby; cases hby
      have h1 := h a b
      have h2 := h b a
      rw [hea, heb b hba, hby] at h1
      rw [hea, heb b hba, hby] at h2
      exact ⟨h1, h2⟩
  · rintro ⟨hm, haa, hab⟩ b c
    by_cases hb : b = a
    · subst hb
      by_cases hc : c = b
      · subst hc; rw [hea]; exact haa
      · rw [hea, heb c hc]
        cases hmc : m c with
        | none => trivial
        | some y => exact (hab c y hmc).1
    · by_cases hc : c = a
      · subst hc
        rw [hea, heb b hb]
        cases hmb : m b with
        | none => trivial
        | some y => exact (hab b y hmb).2
      · rw [heb b hb, heb c hc]; exact hm b c

/-! ## 3. Invalid correspondences have counterexamples -/

/-- **A decidable counterexample.**  An inconsistent correspondence has two mapped elements whose
source relation is not carried. -/
theorem not_consistent_iff {RS : RelStr S} {RT : RelStr T} {m : Corr S T} :
    ¬ Consistent RS RT m ↔
      ∃ a b x y, m a = some x ∧ m b = some y ∧ RT.rel x y ≠ RS.rel a b := by
  constructor
  · intro h
    unfold Consistent at h
    push_neg at h
    obtain ⟨a, b, hab⟩ := h
    cases ha : m a with
    | none => rw [ha] at hab; exact absurd trivial hab
    | some x =>
      cases hb : m b with
      | none => rw [ha, hb] at hab; exact absurd trivial hab
      | some y =>
        rw [ha, hb] at hab
        exact ⟨a, b, x, y, ha, hb, hab⟩
  · rintro ⟨a, b, x, y, ha, hb, hne⟩ h
    have := h a b
    rw [ha, hb] at this
    exact hne this

/-! ## 4. No promotion while obligations stay open -/

theorem open_not_closed {RS : RelStr S} {RT : RelStr T} {m : Corr S T} {a : S}
    (h : IsOpen m a) : ¬ Closed RS RT m := by
  intro hc
  have := hc.1 a
  rw [show m a = none from h] at this
  exact absurd this (by simp)

theorem closed_has_no_obligation {RS : RelStr S} {RT : RelStr T} {m : Corr S T}
    (h : Closed RS RT m) : ∀ a, ¬ IsOpen m a :=
  fun _ ha => open_not_closed ha h

/-- **Inconsistency is permanent.**  No extension repairs a correspondence that already fails to
carry the relation. -/
theorem inconsistent_persists {RS : RelStr S} {RT : RelStr T} {m m' : Corr S T}
    (hm : ¬ Consistent RS RT m) (hext : Extends m m') : ¬ Consistent RS RT m' := by
  obtain ⟨a, b, x, y, ha, hb, hne⟩ := not_consistent_iff.mp hm
  exact not_consistent_iff.mpr ⟨a, b, x, y, hext a x ha, hext b y hb, hne⟩

/-- So an inconsistent correspondence is rejected. -/
theorem inconsistent_rejected {RS : RelStr S} {RT : RelStr T} {m : Corr S T}
    (hm : ¬ Consistent RS RT m) : Rejected RS RT m :=
  fun _ hext hc => inconsistent_persists hm hext hc.2

/-! ## Worked case: sun : planet :: nucleus : ? -/

/-- Source: `0` = sun, `1` = planet; the relation is *orbits* (`planet orbits sun`). -/
def solar : RelStr (Fin 2) := ⟨fun a b => a = 1 ∧ b = 0⟩

/-- Target: `0` = nucleus, `1` = electron; *orbits* (`electron orbits nucleus`). -/
def atom : RelStr (Fin 2) := ⟨fun a b => a = 1 ∧ b = 0⟩

/-- The analogy so far: sun ↦ nucleus; planet is the open obligation. -/
def sunToNucleus : Corr (Fin 2) (Fin 2) := fun a => if a = 0 then some 0 else none

theorem planet_is_open : IsOpen sunToNucleus 1 := by unfold IsOpen; decide

/-- Filling the obligation with *electron* closes the analogy. -/
theorem rutherford_closes : Closed solar atom (extend sunToNucleus 1 1) := by
  refine ⟨by decide, by decide⟩

/-- Filling it with *nucleus* is rejected: planet orbits sun, but nucleus does not orbit
itself. -/
theorem wrong_completion_rejected : Rejected solar atom (extend sunToNucleus 1 0) :=
  inconsistent_rejected (by decide)

/-- **Similarity is not correspondence.**  Label every element of both structures `0`: any map
matches labels perfectly, yet the identity-reversing map fails to carry *orbits*. -/
theorem similarity_not_correspondence :
    let label : Fin 2 → ℕ := fun _ => 0
    let swap : Corr (Fin 2) (Fin 2) := fun a => some (1 - a)
    (∀ a x, swap a = some x → label a = label x) ∧ ¬ Consistent solar atom swap := by
  refine ⟨fun _ _ _ => rfl, by decide⟩

end QLF.AnalogicalListener
