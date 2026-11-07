import QLF_TwistAlphabet
import QLF_PhaseRule
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

## Rung 2: the order (no axioms)

* **`fold_pairs`**: `n` pairs laid end to end fold to `(−1)ⁿ · I`, one `−I` per pair.
* **`negCount_eq_pairs`**: every conjugate pair holds exactly one sign-carrying twist (`v`, `<`, `\\`, `−`),
  so the first factor of the proven phase rule (`QLF_PhaseRule.phase_rule`) *is* the number of
  entanglements.
* **`closure_phase_from_pairs`**: a closure built from `n` pairs folds to
  `(−1)ⁿ · (−1)^(inversions of its axis word) · I`. The phase has exactly two sources: the pairs, and
  the crossings of distinct spatial axes made by reordering them.
* **`reorder_is_crossing_sign`**: any closure equals its pairs laid end to end, times
  `(−1)^(crossings)`.

Honest scope for rung 2: the arithmetic was already in `phase_rule`. What is new is the reading,
which is now a theorem: the first factor counts entanglements, and the order contributes nothing
but a crossing sign.

## What is NOT proved (the open rung, stated so nobody overclaims)

1. **The Form.** `RhoProcess.action f` carries a `Form (t, x, y, z)` that `toTopoString` discards, so
   no balance proof ever uses it. Until the Form is derived from the pair structure (for example as a
   census frequency of how pairs fold), the geometric and amplitude content of a creation is an
   input, not a consequence of entanglement.
2. **Product closures.** `QLF_IndexedFactors.gauge_pair_is_product_sector` shows some pairs close
   with each half scalar on its own. Under the strong reading of entanglement (non-factorizable),
   those pairs are real but not entangled. This module uses the weak reading (a pair whose halves
   cancel), and says so.

"Responsible for all other results" is a programme: rungs 1 (closure = pairs) and 2 (phase = pairs ×
crossings) are proved here. Rung 3, the Form, is the open one.
-/

namespace QLF.EntanglementPrimacy

open QLF QLF.PhaseRule

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

-- ==========================================
-- Rung 2: the order contributes exactly a crossing sign
-- ==========================================

/-- Laid end to end, `n` conjugate pairs fold to `(−1)ⁿ · I`: each adjacent pair is `−I`
    (`hermitian_pair_folds_to_negI`). -/
theorem fold_pairs (ps : List Twist) :
    twistMatrixFold (pairs ps) = ((-1 : ℂ) ^ ps.length) • (1 : M) := by
  induction ps with
  | nil => simp [pairs, twistMatrixFold]
  | cons t ps ih =>
      show t.toMatrix * (t.conj.toMatrix * twistMatrixFold (pairs ps)) = _
      rw [← mul_assoc, hermitian_pair_folds_to_negI, ih, List.length_cons, pow_succ,
        neg_one_mul, ← neg_smul, mul_neg_one]

private theorem negCount_eq_counts (ts : List Twist) :
    negCount ts = ts.count Twist.down + ts.count Twist.left +
      ts.count Twist.backslash + ts.count Twist.minus := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [negCount] at ih ⊢
      simp only [List.countP_cons, List.count_cons, ih]
      cases t <;> simp +decide [isNegTwist] <;> omega

private theorem length_eq_counts (ts : List Twist) :
    ts.length = ts.count Twist.up + ts.count Twist.down + ts.count Twist.left +
      ts.count Twist.right + ts.count Twist.slash + ts.count Twist.backslash +
      ts.count Twist.plus + ts.count Twist.minus := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.length_cons, List.count_cons, ih]
      cases t <;> simp +decide <;> omega

/-- **The sign-carrying twists count the entanglements.** Every conjugate pair holds exactly one
    negative twist (`v`, `<`, `\`, `−`), so in a closure with the letters of `n` pairs, the first factor
    of the phase rule, `negCount`, is `n`. -/
theorem negCount_eq_pairs {ts : List Twist} (ps : List Twist)
    (h : ∀ x : Twist, ts.count x = (pairs ps).count x) :
    negCount ts = ps.length := by
  rw [negCount_eq_counts, h, h, h, h, count_pairs, count_pairs, count_pairs, count_pairs,
    length_eq_counts ps]
  simp only [Twist.conj]
  omega

/-- **Rung 2: phase = entanglements × crossings.** A closure with the letters of `n` conjugate pairs
    folds to `(−1)ⁿ · (−1)^(inversions of its axis word) · I`. The first factor is the pairs, one `−I`
    each; the second is the order, one sign per crossing of two distinct spatial axes. Nothing else
    enters the phase. -/
theorem closure_phase_from_pairs {ts : List Twist} (ps : List Twist)
    (h : ∀ x : Twist, ts.count x = (pairs ps).count x) :
    twistMatrixFold ts =
      ((-1 : ℂ) ^ ps.length * (-1 : ℂ) ^ invCount (axisWord ts)) • (1 : M) := by
  rw [phase_rule ((closure_is_pairs ts).2 ⟨ps, h⟩), pow_add, negCount_eq_pairs ps h]

/-- **Reordering costs only the crossing sign.** Any closure folds to its pairs laid end to end, times
    `(−1)^(crossings)`. -/
theorem reorder_is_crossing_sign {ts : List Twist} (ps : List Twist)
    (h : ∀ x : Twist, ts.count x = (pairs ps).count x) :
    twistMatrixFold ts = ((-1 : ℂ) ^ invCount (axisWord ts)) • twistMatrixFold (pairs ps) := by
  rw [closure_phase_from_pairs ps h, fold_pairs, smul_smul, mul_comm]

/-- Summary: closure = a reordering of conjugate pairs (rung 1); phase = pairs × crossings (rung 2);
    the Form stays open (see the module note). -/
theorem entanglement_primacy_status : True := trivial

end QLF.EntanglementPrimacy
