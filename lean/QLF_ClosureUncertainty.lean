/-
# QLF_ClosureUncertainty

Finite, executable kernel for the first-completion uncertainty of #269 / PR #271.

This module formalizes the **bounded** object:

* a state type `α`, a step function `step : α → List α`, a closure predicate
  `closed : α → Bool`, and a context predicate `allowed : α → Bool`;
* `completions step closed allowed start R` enumerates the admissible paths of
  length at most `R` that end at the **first** closed state;
* a closed start has the empty path as its unique completion.

The module proves the concrete Stag Hunt and joint-pair checks by `native_decide`
and the generic closed-start uniqueness lemma.  The general finite-cardinality,
subset-monotonicity, and no-potency theorems remain open; this is the first Lean
layer of gate U1, not its completion.
-/

import Mathlib

namespace QLF.ClosureUncertainty

/-! ## The bounded kernel -/

/-- Extend every active path by one allowed step.  The pair stores the current
state and the path ending at it, so no `getLast` proof is needed. -/
def stepLevel {α : Type} (step : α → List α) (allowed : α → Bool)
    (active : List (α × List α)) : List (α × List α) :=
  active.flatMap (fun p =>
    (step p.1).filter allowed |>.map (fun next => (next, p.2 ++ [next])))

/-- One bounded layer of first-completion search.  Newly closed paths are moved
to `completed` and are never expanded further. -/
def completionsAux {α : Type} (step : α → List α) (closed : α → Bool)
    (allowed : α → Bool) :
    Nat → List (α × List α) → List (List α) → List (List α)
  | 0, _, completed => completed
  | n + 1, active, completed =>
      let nexts := stepLevel step allowed active
      let newly := (nexts.filter (fun p => closed p.1)).map (fun p => p.2)
      let still := nexts.filter (fun p => !closed p.1)
      completionsAux step closed allowed n still (completed ++ newly)

/-- All admissible first-completion paths of length at most `R`.

A closed start returns the empty path only.  An inadmissible start returns no
path.  If no completion exists within the horizon, the list is empty; the
derived information `log₂ W` is then undefined, not infinite. -/
def completions {α : Type} (step : α → List α) (closed : α → Bool)
    (allowed : α → Bool) (start : α) (R : Nat) : List (List α) :=
  if allowed start && closed start then
    [[]]
  else if !allowed start then
    []
  else
    completionsAux step closed allowed R [(start, [start])] []

/-- `W_R = |Ω_R|`: the integer count of first-completion paths. -/
def W {α : Type} (step : α → List α) (closed : α → Bool) (start : α)
    (R : Nat) : Nat :=
  (completions step closed (fun _ => true) start R).length

/-- `W_R` under an explicit context. -/
def WIn {α : Type} (step : α → List α) (closed : α → Bool)
    (allowed : α → Bool) (start : α) (R : Nat) : Nat :=
  (completions step closed allowed start R).length

/-- A closed, admissible start has the empty path as its unique first
completion, for every horizon. -/
theorem closed_start_unique {α : Type} (step : α → List α) (closed : α → Bool)
    (allowed : α → Bool) (start : α) (R : Nat)
    (h : allowed start = true) (hc : closed start = true) :
    completions step closed allowed start R = [[]] := by
  simp [completions, h, hc]

/-! ## Stag Hunt: Nash = closure (concrete finite check) -/

inductive Profile where
  | SS
  | SH
  | HS
  | HH
  deriving DecidableEq, Repr

/-- Unilateral moves on the four profiles. -/
def profileStep : Profile → List Profile
  | .SS => [.SH, .HS]
  | .SH => [.SS, .HH]
  | .HS => [.SS, .HH]
  | .HH => [.SH, .HS]

/-- The two pure Nash profiles of the Stag Hunt. -/
def profileClosed : Profile → Bool
  | .SS => true
  | .HH => true
  | _ => false

/-- The full game context. -/
def fullContext : Profile → Bool := fun _ => true

/-- A tighter context that removes the Hare-Hare closure. -/
def tightContext : Profile → Bool
  | .HH => false
  | _ => true

theorem stag_hunt_closed_start :
    W profileStep profileClosed .SS 3 = 1 := by
  native_decide

theorem stag_hunt_two_first_nash :
    W profileStep profileClosed .SH 1 = 2 := by
  native_decide

theorem stag_hunt_two_total :
    W profileStep profileClosed .SH 3 = 2 := by
  native_decide

theorem stag_hunt_tight_one :
    WIn profileStep profileClosed tightContext .SH 3 = 1 := by
  native_decide

theorem stag_hunt_tight_le_full :
    WIn profileStep profileClosed tightContext .SH 3 ≤
      WIn profileStep profileClosed fullContext .SH 3 := by
  native_decide

/-! ## Joint closure: neither component alone, the pair closes -/

inductive Pair where
  | p00
  | p10
  | p01
  | p11
  deriving DecidableEq, Repr

/-- Flip one bit of the pair. -/
def pairStep : Pair → List Pair
  | .p00 => [.p10, .p01]
  | .p10 => [.p00, .p11]
  | .p01 => [.p00, .p11]
  | .p11 => [.p10, .p01]

/-- Only the joint `11` state is closed. -/
def pairClosed : Pair → Bool
  | .p11 => true
  | _ => false

theorem joint_pair_no_one_step :
    W pairStep pairClosed .p00 1 = 0 := by
  native_decide

theorem joint_pair_two_paths :
    W pairStep pairClosed .p00 2 = 2 := by
  native_decide

end QLF.ClosureUncertainty
