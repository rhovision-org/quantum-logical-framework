import QLF_TwistAlphabet
import QLF_PhaseRule
import RhoQuCalc
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_EntanglementPrimacy — every closure is made of entanglements

Jim's thesis (2026-11-07): *the logical entanglement is responsible for all other results.* This module
proves three rungs of that thesis for the twist layer and names exactly what is still missing.

The primordial entanglement is the **conjugate pair** `[t, t†]`: a twist and its Hermitian conjugate
(`^v`, `<>`, `/\`, `+−`). Each half is open on its own and the pair closes. That is the `[pos, neg]` event
which `RhoProcess.action` creates, and the pair `ER_EPR_QLF.primordial_wormhole` proves is a shared
closure between spacelike events.

## Rung 1: what closes (no axioms)

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

## Rung 3: the Form (no axioms)

Kill condition, stated before CI ran: rung 3 fails if a creation's `Form` cannot be written as a
function of twist counts, or if the Form of a closure can be non-zero.

* **`parallelSum_eq_strandForm`**: a strand's parallel composition is exactly the `Form` whose
  coordinates are its net signed twist counts `(#+ − #−, #> − #<, #^ − #v, #/ − #\)`. So
  `action (strandForm ts)` creates nothing the twists did not already supply (`action_strandForm`).
* **`countBalanced_iff_strandForm_zero`**: the Form is zero **exactly** on closures. A closed
  entanglement carries no Form at all.
* **`halves_cancel`**: a strand and its conjugate carry opposite Forms and add to zero.

So the Form is not extra stuff created beside the entanglement. It is the signed record of the
**unpaired half**: which side of each pair a strand holds. That is the precise sense in which the
creation operator creates only entanglements.

## What is still NOT proved (stated so nobody overclaims)

1. **Real coordinates.** Derived Forms have integer coordinates. `action f` accepts any real `f`;
   real values enter only as ratios (frequencies over a census), and the normalisation of a pure
   state (`t = ½`, `x² + y² + z² = ¼`) is not derived here. `QLF_Realizability` is the reason to
   expect no more than rationals in a finite region, but that link is not formalised in this module.
2. **Product closures.** `QLF_IndexedFactors.gauge_pair_is_product_sector` shows some pairs close
   with each half scalar on its own. Under the strong reading of entanglement (non-factorizable),
   those pairs are real but not entangled. This module uses the weak reading (a pair whose halves
   cancel), and says so.

Rungs 1–3 of "the logical entanglement is responsible for all other results" are proved here for the
twist layer: what closes (pairs), its phase (pairs × crossings) and its Form (the open half). Every
result built on those three inherits the reading; results that use real-valued Forms or the strong
reading of entanglement do not yet.
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

-- ==========================================
-- Rung 3: the Form is the open half of an entanglement
-- ==========================================

/-- Gauge coordinate of a twist: `+ ↦ 1`, `− ↦ −1`, else `0`. -/
def twT : Twist → ℤ
  | Twist.plus => 1
  | Twist.minus => -1
  | _ => 0

/-- `σx` coordinate: `> ↦ 1`, `< ↦ −1`, else `0`. -/
def twX : Twist → ℤ
  | Twist.right => 1
  | Twist.left => -1
  | _ => 0

/-- `σy` coordinate: `^ ↦ 1`, `v ↦ −1`, else `0`. -/
def twY : Twist → ℤ
  | Twist.up => 1
  | Twist.down => -1
  | _ => 0

/-- `σz` coordinate: `/ ↦ 1`, `\ ↦ −1`, else `0`. -/
def twZ : Twist → ℤ
  | Twist.slash => 1
  | Twist.backslash => -1
  | _ => 0

/-- Net signed count of a strand on each axis. -/
def netT (ts : List Twist) : ℤ := (ts.map twT).sum
def netX (ts : List Twist) : ℤ := (ts.map twX).sum
def netY (ts : List Twist) : ℤ := (ts.map twY).sum
def netZ (ts : List Twist) : ℤ := (ts.map twZ).sum

/-- **The Form of a strand**: its net signed twist count on each axis. -/
noncomputable def strandForm (ts : List Twist) : Form :=
  ⟨(netT ts : ℝ), (netX ts : ℝ), (netY ts : ℝ), (netZ ts : ℝ)⟩

/-- The parallel composition of a strand's twists (`RhoProcess.parallel` evaluates to a sum). -/
noncomputable def parallelSum (ts : List Twist) : M := (ts.map Twist.toMatrix).sum

/-- `Form.toMatrix` is the Pauli expansion `t·I + x·σx + y·σy + z·σz`. -/
theorem form_toMatrix_decomp (f : Form) :
    f.toMatrix = (f.t : ℂ) • (1 : M) + (f.x : ℂ) • σx + (f.y : ℂ) • σy + (f.z : ℂ) • σz := by
  rw [Matrix.one_fin_two]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Form.toMatrix, σx, σy, σz, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const] <;>
    ring

/-- Each twist is one signed unit on one axis. -/
theorem toMatrix_decomp (t : Twist) :
    t.toMatrix = ((twT t : ℤ) : ℂ) • (1 : M) + ((twX t : ℤ) : ℂ) • σx +
      ((twY t : ℤ) : ℂ) • σy + ((twZ t : ℤ) : ℂ) • σz := by
  cases t <;> simp [Twist.toMatrix, twT, twX, twY, twZ]

theorem parallelSum_decomp (ts : List Twist) :
    parallelSum ts = ((netT ts : ℤ) : ℂ) • (1 : M) + ((netX ts : ℤ) : ℂ) • σx +
      ((netY ts : ℤ) : ℂ) • σy + ((netZ ts : ℤ) : ℂ) • σz := by
  induction ts with
  | nil => simp [parallelSum, netT, netX, netY, netZ]
  | cons t ts ih =>
      simp only [parallelSum, netT, netX, netY, netZ, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, toMatrix_decomp t]
      push_cast
      simp only [add_smul]
      abel

/-- **The Form is read off the twists.** A strand's parallel composition is exactly the `Form` whose
    coordinates are its net signed twist counts. Nothing is handed in: `action (strandForm ts)`
    creates the matrix the strand's own twists add up to (`action_strandForm`). -/
theorem parallelSum_eq_strandForm (ts : List Twist) :
    parallelSum ts = (strandForm ts).toMatrix := by
  rw [parallelSum_decomp, form_toMatrix_decomp]
  simp only [strandForm, Complex.ofReal_intCast]

theorem action_strandForm (ts : List Twist) :
    (RhoProcess.action (strandForm ts)).eval = parallelSum ts := by
  simp only [RhoProcess.eval, parallelSum_eq_strandForm]

private theorem netT_eq (ts : List Twist) :
    netT ts = (ts.count Twist.plus : ℤ) - ts.count Twist.minus := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [netT] at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.count_cons, ih]
      cases t <;> simp +decide [twT] <;> omega

private theorem netX_eq (ts : List Twist) :
    netX ts = (ts.count Twist.right : ℤ) - ts.count Twist.left := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [netX] at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.count_cons, ih]
      cases t <;> simp +decide [twX] <;> omega

private theorem netY_eq (ts : List Twist) :
    netY ts = (ts.count Twist.up : ℤ) - ts.count Twist.down := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [netY] at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.count_cons, ih]
      cases t <;> simp +decide [twY] <;> omega

private theorem netZ_eq (ts : List Twist) :
    netZ ts = (ts.count Twist.slash : ℤ) - ts.count Twist.backslash := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [netZ] at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.count_cons, ih]
      cases t <;> simp +decide [twZ] <;> omega

/-- **A closure carries no Form.** A strand is a closure exactly when its Form is zero, so the Form is
    nothing but the record of what is still unpaired. -/
theorem countBalanced_iff_strandForm_zero (ts : List Twist) :
    countBalanced ts ↔ strandForm ts = ⟨0, 0, 0, 0⟩ := by
  simp only [strandForm, Form.mk.injEq, Int.cast_eq_zero, netT_eq, netX_eq, netY_eq, netZ_eq]
  constructor
  · rintro ⟨hUD, hLR, hSB, hPM⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- Conjugation reverses each twist's matrix. -/
theorem toMatrix_conj (t : Twist) : t.conj.toMatrix = -t.toMatrix := by
  cases t <;> simp [Twist.conj, Twist.toMatrix]

private theorem sum_map_conj (ts : List Twist) :
    ((ts.map Twist.conj).map Twist.toMatrix).sum = -(ts.map Twist.toMatrix).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, toMatrix_conj, ih, neg_add]

/-- **The two halves of an entanglement carry opposite Forms.** A strand and its conjugate add to
    zero, so a creation's Form is the half it holds, and the other half holds the negative. -/
theorem halves_cancel (ts : List Twist) : parallelSum (ts ++ ts.map Twist.conj) = 0 := by
  simp only [parallelSum, List.map_append, List.sum_append, sum_map_conj]
  abel

/-- Summary: closure = a reordering of conjugate pairs (rung 1); phase = pairs × crossings (rung 2);
    Form = the open half's net signed count, zero exactly on closures (rung 3). See the module note
    for what stays open. -/
theorem entanglement_primacy_status : True := trivial

end QLF.EntanglementPrimacy
