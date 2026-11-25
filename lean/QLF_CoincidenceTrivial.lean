/-
# QLF_CoincidenceTrivial

Gate **CO0** of the co-incidence program (issue #283, `Coincidence_QLF.md` §4): without
typed provenance fixed before closure, *every* closed history is a "co-incidence" by an
arbitrary split.  Split a count-balanced history `t :: rest` into its first twist and the
remainder: the first twist alone is open (one twist has nonzero net), the remainder is open
(its net is minus the first twist's), and the two concatenate back to the history.  So the
predicate "two open parts that close together" excludes no closed history, and provenance
cannot be a predicate assigned after the closure is seen.

Closure here is `countBalanced`, which by `count_balanced_pauli_closed` entails Pauli
closure, so it is the full ZFA verdict.

No axioms.  Part of [Quantum Logical Framework (QLF)](../README.md).
-/

import QLF_TwistAlphabet

namespace QLF.CoincidenceTrivial

open QLF

/-- A single twist is never closed. -/
theorem single_twist_open (t : Twist) : ¬ countBalanced [t] := by
  unfold countBalanced
  cases t <;> decide

/-- **CO0 — the triviality boundary.**  Every closed history `t :: rest` splits into two
open parts, `[t]` and `rest`, whose concatenation is the history. -/
theorem co0_trivial_split (t : Twist) (rest : List Twist)
    (h : countBalanced (t :: rest)) :
    ¬ countBalanced [t] ∧ ¬ countBalanced rest ∧ [t] ++ rest = t :: rest := by
  refine ⟨single_twist_open t, ?_, rfl⟩
  intro hr
  unfold countBalanced at h hr
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨r1, r2, r3, r4⟩ := hr
  cases t <;> simp (config := { decide := true }) [List.count_cons] at h1 h2 h3 h4 <;> omega

/-- Corollary: no closed history is a single twist, so every closed history has length at
least two and the split above always has two nonempty parts. -/
theorem closed_length_ge_two {w : List Twist} (h : countBalanced w) (hne : w ≠ []) :
    2 ≤ w.length := by
  match w, hne with
  | [t], _ => exact absurd h (single_twist_open t)
  | _ :: _ :: _, _ => simp

end QLF.CoincidenceTrivial
