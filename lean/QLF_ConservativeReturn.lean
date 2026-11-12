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

end QLF.ConservativeReturn
