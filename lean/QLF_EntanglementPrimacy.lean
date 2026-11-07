import QLF_TwistAlphabet
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_EntanglementPrimacy — every closure is made of entanglements

Jim's thesis (2026-11-07): *the logical entanglement is responsible for all other results.* This module
proves the first rung of that thesis and names exactly what is still missing.

The primordial entanglement is the **conjugate pair** `[t, t†]`: a twist and its Hermitian conjugate
(`^v`, `<>`, `/\`, `+−`). Each half is open on its own and the pair closes. That is the `[pos, neg]` event
which `RhoProcess.action` creates, and the pair `ER_EPR_QLF.primordial_wormhole` proves is a shared
closure between spacelike events.

## What is proved (no axioms)

* **`closure_is_pairs`**: a twist history is count-balanced **iff** it holds, letter for letter, the
  same twists as a list of conjugate pairs. Equal counts of every letter is exactly a permutation
  (`List.perm_iff_count`), so a closure is a *reordering of entanglements* and nothing else. No
  closure has a part that is not paired.
* **`pairs_length`**: a closure built from `n` pairs has length `2n`, so the number of entanglements in
  a closure is fixed by its length.
* **`pairs_fold_pauli_scalar`**: everything the keystone `count_balanced_pauli_closed` delivers (the
  fold is a Pauli scalar `{±I, ±iI}`) therefore follows from the pair structure alone.

So the ZFA filter on twist histories, which every downstream count of closures runs on, can be read
as a filter for "made of entanglements".

## What is NOT proved (the open rungs, stated so nobody overclaims)

1. **Order.** `closure_is_pairs` is order-free. The order in which the pairs interleave is extra
   information, and it carries the phase sign (`QLF_PhaseRule`). Entanglement alone fixes *that*
   something closes, but the sign of the closure needs the order as well.
2. **The Form.** `RhoProcess.action f` carries a `Form (t, x, y, z)` that `toTopoString` discards, so
   no balance proof ever uses it. Until the Form is derived from the pair structure (for example as a
   census frequency of how pairs fold), the geometric and amplitude content of a creation is an
   input, not a consequence of entanglement.
3. **Product closures.** `QLF_IndexedFactors.gauge_pair_is_product_sector` shows some pairs close
   with each half scalar on its own. Under the strong reading of entanglement (non-factorizable),
   those pairs are real but not entangled. This module uses the weak reading (a pair whose halves
   cancel), and says so.

"Responsible for all other results" is a programme: this module is rung 1 (closure = pairs). Rungs 2
and 3 are named above.
-/

namespace QLF.EntanglementPrimacy

open QLF

/-- A **conjugate pair**: a twist followed by its Hermitian conjugate. The primordial entanglement. -/
def conjPair (t : Twist) : List Twist := [t, t.conj]

/-- The history made by laying a list of conjugate pairs end to end. -/
def pairs : List Twist → List Twist
  | [] => []
  | t :: ps => t :: t.conj :: pairs ps

/-- Every conjugate pair closes. -/
theorem conjPair_balanced (t : Twist) : countBalanced (conjPair t) := by
  unfold countBalanced conjPair
  cases t <;> decide

/-- Each letter of a pair history is counted once for itself and once for its conjugate. -/
theorem count_pairs (ps : List Twist) (x : Twist) :
    (pairs ps).count x = ps.count x + ps.count x.conj := by
  induction ps with
  | nil => rfl
  | cons t ps ih =>
      show (t :: t.conj :: pairs ps).count x = (t :: ps).count x + (t :: ps).count x.conj
      simp only [List.count_cons, ih]
      cases t <;> cases x <;> simp +decide [Twist.conj] <;> omega

/-- A closure built from `n` pairs has length `2n`. -/
theorem pairs_length (ps : List Twist) : (pairs ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons t ps ih =>
      show (t :: t.conj :: pairs ps).length = 2 * (t :: ps).length
      simp only [List.length_cons, ih]
      omega

private theorem count_rep (n : ℕ) (a x : Twist) :
    (List.replicate n a).count x = if a = x then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.count_cons, ih]
      cases a <;> cases x <;> simp +decide

/-- The canonical pair list of a history: one entry per `^`, `>`, `/`, `+` it contains. -/
def canonicalPairs (ts : List Twist) : List Twist :=
  List.replicate (ts.count Twist.up) Twist.up ++
  List.replicate (ts.count Twist.right) Twist.right ++
  List.replicate (ts.count Twist.slash) Twist.slash ++
  List.replicate (ts.count Twist.plus) Twist.plus

/-- **Closure is pairs.** A twist history is count-balanced exactly when it holds the same twists, letter
    for letter, as some list of conjugate pairs. Equal letter counts is a permutation
    (`List.perm_iff_count`), so every closure is a reordering of entanglements. -/
theorem closure_is_pairs (ts : List Twist) :
    countBalanced ts ↔ ∃ ps : List Twist, ∀ x : Twist, ts.count x = (pairs ps).count x := by
  constructor
  · intro h
    obtain ⟨hUD, hLR, hSB, hPM⟩ := h
    refine ⟨canonicalPairs ts, fun x => ?_⟩
    rw [count_pairs]
    simp only [canonicalPairs, List.count_append, count_rep]
    cases x <;> simp +decide [Twist.conj] <;> omega
  · rintro ⟨ps, h⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      rw [h, h, count_pairs, count_pairs] <;> simp only [Twist.conj] <;> omega

/-- Every pair history closes. -/
theorem pairs_balanced (ps : List Twist) : countBalanced (pairs ps) :=
  (closure_is_pairs (pairs ps)).2 ⟨ps, fun _ => rfl⟩

/-- **The keystone follows from the pairs.** Any history with the letters of a list of conjugate pairs
    folds to a Pauli scalar `{±I, ±iI}`. -/
theorem pairs_fold_pauli_scalar {ts : List Twist} (ps : List Twist)
    (h : ∀ x : Twist, ts.count x = (pairs ps).count x) :
    ∃ p : PauliScalar, twistMatrixFold ts = pauliScalarToMatrix p :=
  count_balanced_pauli_closed ((closure_is_pairs ts).2 ⟨ps, h⟩)

/-- Summary: closure = a reordering of conjugate pairs; order and the Form stay open (see the module
    note). -/
theorem entanglement_primacy_rung_one : True := trivial

end QLF.EntanglementPrimacy
