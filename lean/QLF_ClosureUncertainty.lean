/-
# QLF_ClosureUncertainty

Finite, executable kernel for the first-completion uncertainty of #269 / PR #271.

This module formalizes the **bounded** object:

* a state type `α`, a step function `step : α → List α`, a closure predicate
  `closed : α → Bool`, and a context predicate `allowed : α → Bool`;
* `completions step closed allowed start R` enumerates the admissible paths of
  length at most `R` that end at the **first** closed state;
* a closed start has the empty path as its unique completion.

The module proves the concrete Stag Hunt and joint-pair checks by `native_decide`,
the generic closed-start uniqueness lemma, and the generic **context
monotonicity** of gate U1 (`completions_sublist_of_context`, `WIn_mono`): a
tighter context yields a sublist of the first-completion paths, so `W` cannot
increase.  Finiteness is structural (`completions` is a `List`), and `closed`
takes no context argument, so conditioning cannot change what counts as closed;
neither needs a theorem.
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

/-! ## Context monotonicity (gate U1, generic)

`allowed'` is *tighter* than `allowed` when every state it admits, `allowed`
admits too.  Tightening the context only deletes paths: each surviving path
passes through the same states and stops at the same first closed state.  So
the first-completion list under the tighter context is a sublist of the list
under the looser one, for every step relation, closure predicate, start and
horizon.  This holds for every instantiation of the kernel (game theory,
flat-history ZFA, the confinement toy) with no change of definitions. -/

/-- One layer of extension is monotone in the active list and in the context. -/
theorem stepLevel_sublist {α : Type} (step : α → List α) {allowed' allowed : α → Bool}
    (hle : ∀ s, allowed' s = true → allowed s = true)
    {active' active : List (α × List α)} (ha : active'.Sublist active) :
    (stepLevel step allowed' active').Sublist (stepLevel step allowed active) := by
  unfold stepLevel
  induction ha with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih =>
    rw [List.flatMap_cons]
    exact ih.trans (List.sublist_append_right _ _)
  | cons_cons a _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.Sublist.append ?_ ih
    exact (List.monotone_filter_right _ (fun s h => hle s h)).map _

/-- The bounded search is monotone in its active and completed lists and in
the context. -/
theorem completionsAux_sublist {α : Type} (step : α → List α) (closed : α → Bool)
    {allowed' allowed : α → Bool} (hle : ∀ s, allowed' s = true → allowed s = true) :
    ∀ (n : Nat) {active' active : List (α × List α)} {done' done : List (List α)},
      active'.Sublist active → done'.Sublist done →
      (completionsAux step closed allowed' n active' done').Sublist
        (completionsAux step closed allowed n active done) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ hd; simpa [completionsAux] using hd
  | succ n ih =>
    intro active' active done' done ha hd
    have hs := stepLevel_sublist step hle ha
    simp only [completionsAux]
    exact ih (hs.filter _) (hd.append ((hs.filter _).map _))

/-- **Context monotonicity.**  A tighter context gives a sublist of the
first-completion paths. -/
theorem completions_sublist_of_context {α : Type} (step : α → List α)
    (closed : α → Bool) {allowed' allowed : α → Bool}
    (hle : ∀ s, allowed' s = true → allowed s = true) (start : α) (R : Nat) :
    (completions step closed allowed' start R).Sublist
      (completions step closed allowed start R) := by
  by_cases h1 : allowed' start = true
  · have h2 : allowed start = true := hle _ h1
    by_cases hc : closed start = true
    · simp [completions, h1, h2, hc]
    · have hc' : closed start = false := by simpa using hc
      simp only [completions, h1, h2, hc', Bool.and_false, Bool.not_true,
        Bool.false_eq_true, ite_false]
      exact completionsAux_sublist step closed hle R (List.Sublist.refl _)
        (List.Sublist.refl _)
  · have h1' : allowed' start = false := by simpa using h1
    simp [completions, h1']

/-- **`W' ≤ W`.**  Restricting the admissible continuations cannot increase
their count. -/
theorem WIn_mono {α : Type} (step : α → List α) (closed : α → Bool)
    {allowed' allowed : α → Bool} (hle : ∀ s, allowed' s = true → allowed s = true)
    (start : α) (R : Nat) :
    WIn step closed allowed' start R ≤ WIn step closed allowed start R :=
  (completions_sublist_of_context step closed hle start R).length_le

/-- Every context is tighter than the full context, so `WIn ≤ W`. -/
theorem WIn_le_W {α : Type} (step : α → List α) (closed : α → Bool)
    (allowed : α → Bool) (start : α) (R : Nat) :
    WIn step closed allowed start R ≤ W step closed start R :=
  WIn_mono step closed (fun _ _ => rfl) start R

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
