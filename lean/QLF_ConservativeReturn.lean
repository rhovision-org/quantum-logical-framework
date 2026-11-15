/-!
# QLF_ConservativeReturn — a toy conservative return with count and phase

This is the minimal Lean witness requested for the strange-loop proof programme.
It defines, on a two-element toy ortholattice:

* `Formal` — the finitary formal object (`bot`, `top`) with count and phase
  invariants `(0, false)` and `(1, true)`;
* `History` — a finite twist word, with net twist, `t`-count and phase;
* `ClosedHistory` — a history with net twist zero (the toy ZFA-closure
  condition);
* `F : Formal -> ClosedHistory` — the forward map;
* `R : ClosedHistory -> Formal` — the return map, reading the phase.

Proved:

* `conservative_return : R (F a) = a`;
* `count_recovered` and `phase_recovered`: `F` carries the original count and
  phase into the closed history;
* `F_invariants`: the closed history's invariants equal the formal invariants;
* `F_closed`: every image is closed.

Everything is finite and definitional. There is no Mathlib import, no
continuum object, no probability rule and no optical/detector map. This is a
toy return witness only: the actual bridge records remain `B-OPEN`, and their
`proof_obligation` status is at most `PARTIAL`.

It also packages `QuotientStrangeLoopTrigger`, the quotient version needed by the
tensor-product target `TensorConservativeReturn`: the return holds on physical
closure classes, not on raw factor pairs. The tensor bridge is not instantiated
here; see `verification/strange-loop/tensor_return_target.md`.
-/
namespace QLF.ConservativeReturn

/-- Toy formal side: the two-element ortholattice. -/
inductive Formal | bot | top
  deriving DecidableEq, Repr

namespace Formal

/-- Toy count invariant: `bot` has count 0, `top` count 1. -/
def count : Formal -> Nat
  | .bot => 0
  | .top => 1

/-- Toy phase invariant: `bot` is even/positive, `top` is odd/negative. -/
def phase : Formal -> Bool
  | .bot => false
  | .top => true

/-- The formal count/phase pair recovered by the return map. -/
def invariants (a : Formal) : Nat × Bool :=
  (count a, phase a)

end Formal

/-- A twist and its conjugate. -/
inductive Twist | t | td
  deriving DecidableEq, Repr

/-- A finite twist history. -/
inductive History | nil | cons (x : Twist) (h : History)
  deriving DecidableEq, Repr

namespace History

/-- Net twist: `t` is `+1`, `td` is `-1`. -/
def net : History -> Int
  | .nil => 0
  | .cons .t h => 1 + net h
  | .cons .td h => -1 + net h

/-- Number of `t` twists; the toy count invariant. -/
def twistCount : History -> Nat
  | .nil => 0
  | .cons .t h => 1 + twistCount h
  | .cons .td h => twistCount h

/-- Phase: toggled by each `t`, unchanged by `td`. -/
def phase : History -> Bool
  | .nil => false
  | .cons .t h => !phase h
  | .cons .td h => phase h

/-- The history count/phase pair. -/
def invariants (h : History) : Nat × Bool :=
  (twistCount h, phase h)

end History

/-- A toy ZFA-closed history: net twist zero. -/
structure ClosedHistory where
  history : History
  closed : history.net = 0

namespace ClosedHistory

/-- Invariants read from a closed history. -/
def invariants (h : ClosedHistory) : Nat × Bool :=
  h.history.invariants

end ClosedHistory

/-- Forward map: realize the formal object as a closed history. -/
def F : Formal -> ClosedHistory
  | .bot => ⟨.nil, by decide⟩
  | .top => ⟨.cons .t (.cons .td .nil), by decide⟩

/-- Return map: read the phase of the closed history back into the formal object. -/
def R (h : ClosedHistory) : Formal :=
  if h.history.phase then .top else .bot

/-- **Conservative return:** the formal object is recovered from its image. -/
theorem conservative_return (a : Formal) : R (F a) = a := by
  cases a <;> rfl

/-- Every image of `F` is a closed history. -/
theorem F_closed (a : Formal) : (F a).history.net = 0 :=
  (F a).closed

/-- The count invariant is recovered from the closed history. -/
theorem count_recovered (a : Formal) : (F a).history.twistCount = Formal.count a := by
  cases a <;> rfl

/-- The phase invariant is recovered from the closed history. -/
theorem phase_recovered (a : Formal) : (F a).history.phase = Formal.phase a := by
  cases a <;> rfl

/-- The full count/phase pair is recovered from the closed history. -/
theorem F_invariants (a : Formal) :
    ClosedHistory.invariants (F a) = Formal.invariants a := by
  cases a <;> rfl


/-! ## The trigger as a machine-checked structure -/

/-- The finitary core of the trigger: the toy formal side. -/
abbrev Core := Formal

/-- The closed-history side of the trigger. -/
abbrev ZFAHistory := ClosedHistory

/-- Count read from a closed history. -/
def countOf (h : ZFAHistory) : Nat :=
  h.history.twistCount

/-- Phase read from a closed history. -/
def phaseOf (h : ZFAHistory) : Bool :=
  h.history.phase

/-- Count of a formal core element. -/
def countOfCore (a : Core) : Nat :=
  Formal.count a

/-- Phase of a formal core element. -/
def phaseOfCore (a : Core) : Bool :=
  Formal.phase a

/-- A **strange-loop trigger**: a level-crossing pair `F`/`R` that is conservative on
    the finitary core and whose image carries the original count and phase.

    This is a predicate shape, not a claim that any Paper I bridge instantiates it.
    A bridge must supply its own `Core`, `History`, `closed`, `F`, `R` and invariant
    maps, and prove all five fields. -/
structure StrangeLoopTrigger where
  /-- The finitary formal side. -/
  Core : Type
  /-- The closed-history side. -/
  History : Type
  /-- The toy ZFA-closure predicate. -/
  closed : History -> Prop
  /-- Forward map into closed histories. -/
  forward : Core -> History
  /-- Return map back to the finitary core. -/
  ret : History -> Core
  /-- Count recovered from a history. -/
  countOf : History -> Nat
  /-- Phase recovered from a history. -/
  phaseOf : History -> Bool
  /-- Count of a core element. -/
  countOfCore : Core -> Nat
  /-- Phase of a core element. -/
  phaseOfCore : Core -> Bool
  /-- The conservative-return identity. -/
  composite_id : ∀ c, ret (forward c) = c
  /-- The image is closed. -/
  image_closed : ∀ c, closed (forward c)
  /-- Count recovery. -/
  count_recovered : ∀ c, countOf (forward c) = countOfCore c
  /-- Phase recovery. -/
  phase_recovered : ∀ c, phaseOf (forward c) = phaseOfCore c

/-- The toy instantiation of the trigger. It proves the shape is inhabited; it does
    not instantiate the optical, α, SPARC or Born operational maps. -/
def toyTrigger : StrangeLoopTrigger where
  Core := Core
  History := ZFAHistory
  closed := fun h => h.history.net = 0
  forward := F
  ret := R
  countOf := countOf
  phaseOf := phaseOf
  countOfCore := countOfCore
  phaseOfCore := phaseOfCore
  composite_id := conservative_return
  image_closed := F_closed
  count_recovered := count_recovered
  phase_recovered := phase_recovered

/-- The toy trigger is inhabited. -/
theorem toyTrigger_exists : Nonempty StrangeLoopTrigger :=
  ⟨toyTrigger⟩

/-- The trigger's composite identity, exposed as a theorem. -/
theorem toyTrigger_composite (c : Core) : toyTrigger.ret (toyTrigger.forward c) = c :=
  toyTrigger.composite_id c

/-! ## Toy no-time-loop check -/

namespace History

/-- Length of a history. -/
def length : History -> Nat
  | .nil => 0
  | .cons _ h => 1 + length h

end History

/-- A toy event: prepend one twist, strictly extending the history. -/
def Event (h h' : History) : Prop :=
  ∃ x, h' = .cons x h

/-- Every toy event strictly increases history length. -/
theorem event_length_lt {h h' : History} (e : Event h h') : h.length < h'.length := by
  rcases e with ⟨x, rfl⟩
  simp [History.length]

/-- Any chain of toy events strictly increases history length. -/
theorem transGen_event_length_lt {h h' : History}
    (ht : Relation.TransGen Event h h') : h.length < h'.length := by
  induction ht with
  | single e => exact event_length_lt e
  | tail _ e ih => exact Nat.lt_trans ih (event_length_lt e)

/-- **No toy time loop:** no chain of events returns to its starting history.
    This is the finite analogue of `no_time_loops_from_logic`. -/
theorem no_event_cycle (h : History) : ¬ Relation.TransGen Event h h :=
  fun ht => Nat.lt_irrefl _ (transGen_event_length_lt ht)

/-- A **quotient trigger**: the conservative return holds on physical equivalence
    classes, not on raw syntax. This is the shape the tensor-product bridge needs:
    `F` takes a finite closure class to its tensor/Hilbert representation, `R`
    returns the class, and `R ∘ F = id` holds only up to `coreEquiv`.

    The tensor bridge is not instantiated here. `QLF_TensorFromClosure` supplies
    the forward direction; the missing theorem is an instance of this structure
    with `coreEquiv` the closure-class equivalence and `Tensor` the two-body
    tensor algebra. -/
structure QuotientStrangeLoopTrigger where
  /-- Finite closure-class side. -/
  Core : Type
  /-- Tensor/Hilbert representation side. -/
  Tensor : Type
  /-- Physical equivalence on the finite side. -/
  coreEquiv : Core -> Core -> Prop
  /-- Equivalence is reflexive. -/
  equiv_refl : ∀ c, coreEquiv c c
  /-- Equivalence is symmetric. -/
  equiv_symm : ∀ {c c'}, coreEquiv c c' -> coreEquiv c' c
  /-- Equivalence is transitive. -/
  equiv_trans : ∀ {c c' c''}, coreEquiv c c' -> coreEquiv c' c'' -> coreEquiv c c''
  /-- Forward map to the representation. -/
  forward : Core -> Tensor
  /-- Return map from the representation. -/
  ret : Tensor -> Core
  /-- The forward map respects physical equivalence. -/
  forward_respects : ∀ {c c'}, coreEquiv c c' -> forward c = forward c'
  /-- The return is the identity on physical equivalence classes. -/
  composite_id_on_quotient : ∀ c, coreEquiv (ret (forward c)) c

/-- The toy quotient instance: equivalence is equality and the tensor side is the
    same closed-history toy. This checks the shape only. -/
def toyQuotientTrigger : QuotientStrangeLoopTrigger where
  Core := Core
  Tensor := ZFAHistory
  coreEquiv := Eq
  equiv_refl := fun _ => rfl
  equiv_symm := fun h => h.symm
  equiv_trans := fun h₁ h₂ => h₁.trans h₂
  forward := F
  ret := R
  forward_respects := by
    intro c c' h
    rw [h]
  composite_id_on_quotient := conservative_return

/-- The toy quotient trigger is inhabited. -/
theorem toyQuotientTrigger_exists : Nonempty QuotientStrangeLoopTrigger :=
  ⟨toyQuotientTrigger⟩

end QLF.ConservativeReturn
