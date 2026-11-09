import QLF_TwistAlphabet
import QLF_PhaseRule
import RhoQuCalc
import QLF_JointClosure
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_EntanglementPrimacy — every closure is made of entanglements

Jim's thesis (2026-11-07): *the logical entanglement is responsible for all other results.* This module
proves six rungs of that thesis for the twist layer and names exactly what is still missing.

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

## Rung 4: real Forms and pure states (no axioms)

* **`strand_realizes`**: every integer vector `(a, b, c, d) ∈ ℤ⁴` is the net signed count of some
  strand, so derived Forms fill the whole integer lattice.
* **`rational_form_is_frequency`**: every Form with rational coordinates is the **frequency** of a
  strand (`freqForm ts N`: net counts divided by a normalisation `N`). `N` is not the strand's length:
  the event-window reading is `N = ts.length`, and the theorems below say which results survive it.
* **`net_abs_le_length`**: a strand is at least as long as its nets,
  `|#+ − #−| + |#> − #<| + |#^ − #v| + |#/ − #\| ≤ length`, since each twist moves one axis by one.
* **`pure_state_plus_up`**: the two-twist strand `+^` read over its own two events is the pure state
  `(½, 0, ½, 0)`.
* **`rational_pure_state_is_frequency`**: every pure qubit state with a rational Bloch vector is a
  frequency of a strand.
* **`form_approximated`** / **`form_approximated_freq`**: every real Form, irrational coordinates
  included, has strand nets within one unit of `N · f`, so for `N > 0` some strand frequency is within
  `1/N` of it, and it is a limit of strand frequencies. This is integer-count approximation under a
  normalisation `N`; the strand may need more than `N` twists.
* **`pure_state_family`**: for integers `m, n, k`, the strand with nets
  `(m²+n²+k², 2mk, 2nk, m²+n²−k²)` normalised by `N = 2(m²+n²+k²)` is a pure state.
* **`window_pure_on_axis`**: read over its own events (`length ≤ N`, one twist per event), a strand
  is pure **only on an axis**: at most one spatial net is non-zero, so the state is one of the six
  axis states `±x, ±y, ±z` (`pure_state_plus_up` is one). Example: `pure_state_family` at
  `m = n = k = 1` has `N = 6` but nets `(3, 2, 2, 1)`, which need eight twists.

## Rung 4b: pure strand frequencies are dense (no axioms)

* **`stereo_on_sphere`**, **`stereo_inverse`**, **`stereo_continuous`**: inverse stereographic
  projection maps the plane onto the pure Bloch sphere minus its north pole, continuously, and
  `(2x, 2y)/(1 − 2z)` inverts it.
* **`pure_strand_frequencies_dense`**: for every pure state `f` and `ε > 0` some strand frequency is
  itself pure and within `ε` of `f` on every coordinate. The north pole is `+/` exactly; elsewhere a
  rational plane point near the preimage gives, after clearing denominators, an instance of
  `pure_state_family`.

So the real numbers in a Form enter only as ratios of counts to a normalisation. Pure-state
normalisation `t = ½` is a choice of `N` (the gauge net is half of it), not an extra postulate. But
if `N` must be the number of events, only the six axis states are pure frequencies; every other pure
state needs `N` to be a normalisation shorter than the strand.

## Rung 5: the strong reading (no axioms)

Strong entanglement of a pair `[t, t†]` means neither half folds to a scalar alone, so the pair has
no product form.

* **`stronglyEntangled_iff_spatial`**: a pair is strongly entangled **exactly** when it is spatial.
  The six spatial letters (`^v`, `<>`, `/\`) give non-factorizable pairs; the gauge pair `+−` is a
  product, because each half folds to `±I` on its own.
* **`no_gauge_all_strongly_entangled`**: a closure with no gauge twists is made only of strong
  entanglements.

So the strong sentence "only entanglements are real" is true on the spatial sector and false on
exactly one kind of pair, the gauge pair, whose open half carries only the `t` coordinate of the
Form (rung 3). The exception is located, not hidden.

## Rung 6: from one pair to two bodies (no axioms)

Read a pair `[t, t†]` as the twist's axis acting on both sites of a two-body state
(`QLF_JointClosure.joint`), so the two sites must carry opposite values for the action to cancel.

* **`singlet_cancels_iff_strong`**: the singlet absorbs a pair's axis (net action zero) **exactly**
  when the pair is strongly entangled. The gauge pair acts on the singlet as the scalar `±2`.
* **`strong_pairs_cancel_iff_singlet`**: the singlet is the **unique** two-body state on which every
  strong pair cancels. Rung 5's per-pair notion and the two-body joint closure pick out one state.

## What is still NOT proved (stated so nobody overclaims)

1. **Irrational Forms are limits, not frequencies.** A Form with an irrational coordinate is the
   frequency of no finite strand, but `form_approximated_freq` puts some strand's frequency within
   `1/N` of it at every normalisation `N > 0`, so it is a limit of strand frequencies, and
   `pure_strand_frequencies_dense` (rung 4b) makes the approximants of a pure state pure themselves.
   Not formalised: the link to `QLF_Realizability`, which is the reason to expect no more than
   rationals in a finite region.
2. **What `N` is physically.** Rung 4 reaches `t = ½` by choosing the normalisation `N`; it does
   not derive that the physical `N` makes the gauge net half of it. And `window_pure_on_axis` shows
   the choice is forced away from the plainest reading: if `N` counts events one twist each, the
   only pure frequencies are the six axis states. Off-axis pure states need `N` below the strand's
   length (several twists per event, or a normalisation that is not an event count), and which of
   those is physical is open.
3. **The two-body reading is a choice.** Rung 6 maps a pair to the joint action of its axis on two
   sites. That map is the natural one (each site holds one half), but it is chosen, not derived from
   the twist histories; deriving the tensor product itself stays open (`closed_iff_singlet` already
   assumes it).

Rungs 1–6 of "the logical entanglement is responsible for all other results" are proved here for the
twist layer: what closes (pairs), its phase (pairs × crossings), its Form (the open half), every
rational Form and pure state (frequencies of strands under a normalisation; within a one-twist-per-
event window only the axis states are pure), which pairs are entangled in the strong
sense (exactly the spatial ones), and that those pairs single out the two-body singlet.
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
  | Twist.up => 0
  | Twist.down => 0
  | Twist.left => 0
  | Twist.right => 0
  | Twist.slash => 0
  | Twist.backslash => 0
  | Twist.plus => 1
  | Twist.minus => -1

/-- `σx` coordinate: `> ↦ 1`, `< ↦ −1`, else `0`. -/
def twX : Twist → ℤ
  | Twist.up => 0
  | Twist.down => 0
  | Twist.left => -1
  | Twist.right => 1
  | Twist.slash => 0
  | Twist.backslash => 0
  | Twist.plus => 0
  | Twist.minus => 0

/-- `σy` coordinate: `^ ↦ 1`, `v ↦ −1`, else `0`. -/
def twY : Twist → ℤ
  | Twist.up => 1
  | Twist.down => -1
  | Twist.left => 0
  | Twist.right => 0
  | Twist.slash => 0
  | Twist.backslash => 0
  | Twist.plus => 0
  | Twist.minus => 0

/-- `σz` coordinate: `/ ↦ 1`, `\ ↦ −1`, else `0`. -/
def twZ : Twist → ℤ
  | Twist.up => 0
  | Twist.down => 0
  | Twist.left => 0
  | Twist.right => 0
  | Twist.slash => 1
  | Twist.backslash => -1
  | Twist.plus => 0
  | Twist.minus => 0

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
      Matrix.of_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] <;>
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

-- ==========================================
-- Rung 4: real Forms and pure states as frequencies
-- ==========================================

theorem netT_cons (t : Twist) (ts : List Twist) : netT (t :: ts) = twT t + netT ts := by
  simp [netT]
theorem netX_cons (t : Twist) (ts : List Twist) : netX (t :: ts) = twX t + netX ts := by
  simp [netX]
theorem netY_cons (t : Twist) (ts : List Twist) : netY (t :: ts) = twY t + netY ts := by
  simp [netY]
theorem netZ_cons (t : Twist) (ts : List Twist) : netZ (t :: ts) = twZ t + netZ ts := by
  simp [netZ]

theorem netT_append (l₁ l₂ : List Twist) : netT (l₁ ++ l₂) = netT l₁ + netT l₂ := by
  simp [netT]
theorem netX_append (l₁ l₂ : List Twist) : netX (l₁ ++ l₂) = netX l₁ + netX l₂ := by
  simp [netX]
theorem netY_append (l₁ l₂ : List Twist) : netY (l₁ ++ l₂) = netY l₁ + netY l₂ := by
  simp [netY]
theorem netZ_append (l₁ l₂ : List Twist) : netZ (l₁ ++ l₂) = netZ l₁ + netZ l₂ := by
  simp [netZ]

/-- **A strand is at least as long as its nets.** Each twist moves one axis by one unit, so the
    absolute net counts summed over the four axes never exceed the number of twists. This is what
    separates a normalisation `N` from an event count: a strand read as one twist per event cannot
    carry nets larger than its own length. -/
theorem net_abs_le_length (ts : List Twist) :
    |netT ts| + |netX ts| + |netY ts| + |netZ ts| ≤ (ts.length : ℤ) := by
  induction ts with
  | nil => simp [netT, netX, netY, netZ]
  | cons t ts ih =>
    rw [netT_cons, netX_cons, netY_cons, netZ_cons, List.length_cons]
    push_cast
    cases t <;> simp only [twT, twX, twY, twZ, zero_add] <;>
      linarith [abs_add_le (1 : ℤ) (netT ts), abs_add_le (-1 : ℤ) (netT ts),
        abs_add_le (1 : ℤ) (netX ts), abs_add_le (-1 : ℤ) (netX ts),
        abs_add_le (1 : ℤ) (netY ts), abs_add_le (-1 : ℤ) (netY ts),
        abs_add_le (1 : ℤ) (netZ ts), abs_add_le (-1 : ℤ) (netZ ts),
        (abs_one : |(1 : ℤ)| = 1), abs_neg (1 : ℤ)]

/-- One axis at a time: a strand with any integer net on a chosen axis and zero on the others. The
    twist pair `(p, n)` is the axis's positive and negative letter. -/
private theorem exists_on_axis (p n : Twist) (f : List Twist → ℤ)
    (hp : ∀ ts, f (p :: ts) = f ts + 1) (hn : ∀ ts, f (n :: ts) = f ts - 1)
    (g₁ g₂ g₃ : List Twist → ℤ)
    (hg₁ : ∀ ts, g₁ (p :: ts) = g₁ ts ∧ g₁ (n :: ts) = g₁ ts)
    (hg₂ : ∀ ts, g₂ (p :: ts) = g₂ ts ∧ g₂ (n :: ts) = g₂ ts)
    (hg₃ : ∀ ts, g₃ (p :: ts) = g₃ ts ∧ g₃ (n :: ts) = g₃ ts)
    (h0 : f [] = 0 ∧ g₁ [] = 0 ∧ g₂ [] = 0 ∧ g₃ [] = 0) (k : ℤ) :
    ∃ ts : List Twist, f ts = k ∧ g₁ ts = 0 ∧ g₂ ts = 0 ∧ g₃ ts = 0 := by
  refine Int.induction_on k ⟨[], h0⟩ ?_ ?_
  · rintro i ⟨ts, h1, h2, h3, h4⟩
    refine ⟨p :: ts, ?_, ?_, ?_, ?_⟩
    · rw [hp, h1]
    · rw [(hg₁ ts).1, h2]
    · rw [(hg₂ ts).1, h3]
    · rw [(hg₃ ts).1, h4]
  · rintro i ⟨ts, h1, h2, h3, h4⟩
    refine ⟨n :: ts, ?_, ?_, ?_, ?_⟩
    · rw [hn, h1]
    · rw [(hg₁ ts).2, h2]
    · rw [(hg₂ ts).2, h3]
    · rw [(hg₃ ts).2, h4]

/-- **Every integer Form is a strand.** For any `(a, b, c, d) ∈ ℤ⁴` some strand has exactly those net
    signed counts, so derived Forms fill the whole integer lattice. -/
theorem strand_realizes (a b c d : ℤ) :
    ∃ ts : List Twist, netT ts = a ∧ netX ts = b ∧ netY ts = c ∧ netZ ts = d := by
  obtain ⟨l₁, h₁, h₁x, h₁y, h₁z⟩ := exists_on_axis Twist.plus Twist.minus netT
    (fun ts => by rw [netT_cons]; simp only [twT]; ring)
    (fun ts => by rw [netT_cons]; simp only [twT]; ring)
    netX netY netZ
    (fun ts => by simp [netX_cons, twX])
    (fun ts => by simp [netY_cons, twY])
    (fun ts => by simp [netZ_cons, twZ])
    ⟨rfl, rfl, rfl, rfl⟩ a
  obtain ⟨l₂, h₂, h₂t, h₂y, h₂z⟩ := exists_on_axis Twist.right Twist.left netX
    (fun ts => by rw [netX_cons]; simp only [twX]; ring)
    (fun ts => by rw [netX_cons]; simp only [twX]; ring)
    netT netY netZ
    (fun ts => by simp [netT_cons, twT])
    (fun ts => by simp [netY_cons, twY])
    (fun ts => by simp [netZ_cons, twZ])
    ⟨rfl, rfl, rfl, rfl⟩ b
  obtain ⟨l₃, h₃, h₃t, h₃x, h₃z⟩ := exists_on_axis Twist.up Twist.down netY
    (fun ts => by rw [netY_cons]; simp only [twY]; ring)
    (fun ts => by rw [netY_cons]; simp only [twY]; ring)
    netT netX netZ
    (fun ts => by simp [netT_cons, twT])
    (fun ts => by simp [netX_cons, twX])
    (fun ts => by simp [netZ_cons, twZ])
    ⟨rfl, rfl, rfl, rfl⟩ c
  obtain ⟨l₄, h₄, h₄t, h₄x, h₄y⟩ := exists_on_axis Twist.slash Twist.backslash netZ
    (fun ts => by rw [netZ_cons]; simp only [twZ]; ring)
    (fun ts => by rw [netZ_cons]; simp only [twZ]; ring)
    netT netX netY
    (fun ts => by simp [netT_cons, twT])
    (fun ts => by simp [netX_cons, twX])
    (fun ts => by simp [netY_cons, twY])
    ⟨rfl, rfl, rfl, rfl⟩ d
  refine ⟨l₁ ++ l₂ ++ l₃ ++ l₄, ?_, ?_, ?_, ?_⟩ <;>
    simp only [netT_append, netX_append, netY_append, netZ_append] <;> omega

/-- **The frequency Form** of a strand read over a window of `N` events: net signed counts per event. -/
noncomputable def freqForm (ts : List Twist) (N : ℕ) : Form :=
  ⟨(netT ts : ℝ) / N, (netX ts : ℝ) / N, (netY ts : ℝ) / N, (netZ ts : ℝ) / N⟩

/-- **Every rational Form is a frequency of a strand.** Real values enter the Form only as ratios of
    net counts to a window, and every ratio is reached. -/
theorem rational_form_is_frequency (a b c d : ℤ) (N : ℕ) :
    ∃ ts : List Twist,
      freqForm ts N = ⟨(a : ℝ) / N, (b : ℝ) / N, (c : ℝ) / N, (d : ℝ) / N⟩ := by
  obtain ⟨ts, h1, h2, h3, h4⟩ := strand_realizes a b c d
  exact ⟨ts, by simp only [freqForm, h1, h2, h3, h4]⟩

/-- A Form is a **pure qubit state** when `t = ½` and its Bloch vector has length `½`. -/
noncomputable def IsPure (f : Form) : Prop := f.t = 1 / 2 ∧ f.x ^ 2 + f.y ^ 2 + f.z ^ 2 = 1 / 4

/-- **A pure state from two twists.** The strand `+^` read over its own two events is the pure state
    `(½, 0, ½, 0)`: half a gauge unit and half a `σy` unit per event. -/
theorem pure_state_plus_up : IsPure (freqForm [Twist.plus, Twist.up] 2) := by
  unfold IsPure
  norm_num [freqForm, netT, netX, netY, netZ, twT, twX, twY, twZ]

/-- **Every pure state with a rational Bloch vector is a frequency of a strand.** Write the vector
    over a common denominator `N` (so `t = ½` means the gauge net is `N/2`): some strand has exactly
    those nets. -/
theorem rational_pure_state_is_frequency (a b c d : ℤ) (N : ℕ)
    (hpure : IsPure ⟨(a : ℝ) / N, (b : ℝ) / N, (c : ℝ) / N, (d : ℝ) / N⟩) :
    ∃ ts : List Twist, IsPure (freqForm ts N) ∧
      freqForm ts N = ⟨(a : ℝ) / N, (b : ℝ) / N, (c : ℝ) / N, (d : ℝ) / N⟩ := by
  obtain ⟨ts, hts⟩ := rational_form_is_frequency a b c d N
  refine ⟨ts, ?_, hts⟩
  rw [hts]
  exact hpure

/-- **Every real Form is approached by strand frequencies.** For any Form `f` and any window `N`, some
    strand's net counts sit within one unit of `N · f` on every axis, so its frequency
    (`freqForm`, nets divided by `N`) is within `1/N` of `f`. As the window grows the frequencies
    converge to `f`, irrational coordinates included. -/
theorem form_approximated (f : Form) (N : ℕ) :
    ∃ ts : List Twist,
      |(netT ts : ℝ) - N * f.t| ≤ 1 ∧ |(netX ts : ℝ) - N * f.x| ≤ 1 ∧
      |(netY ts : ℝ) - N * f.y| ≤ 1 ∧ |(netZ ts : ℝ) - N * f.z| ≤ 1 := by
  obtain ⟨ts, h1, h2, h3, h4⟩ :=
    strand_realizes ⌊(N : ℝ) * f.t⌋ ⌊(N : ℝ) * f.x⌋ ⌊(N : ℝ) * f.y⌋ ⌊(N : ℝ) * f.z⌋
  refine ⟨ts, ?_, ?_, ?_, ?_⟩
  · rw [h1, abs_le]
    have := Int.floor_le ((N : ℝ) * f.t)
    have := Int.lt_floor_add_one ((N : ℝ) * f.t)
    constructor <;> linarith
  · rw [h2, abs_le]
    have := Int.floor_le ((N : ℝ) * f.x)
    have := Int.lt_floor_add_one ((N : ℝ) * f.x)
    constructor <;> linarith
  · rw [h3, abs_le]
    have := Int.floor_le ((N : ℝ) * f.y)
    have := Int.lt_floor_add_one ((N : ℝ) * f.y)
    constructor <;> linarith
  · rw [h4, abs_le]
    have := Int.floor_le ((N : ℝ) * f.z)
    have := Int.lt_floor_add_one ((N : ℝ) * f.z)
    constructor <;> linarith

/-- **The `1/N` reading of `form_approximated`.** For a window `N > 0`, some strand's frequency is
    within `1/N` of `f` on every coordinate. Here `N` is a normalisation: the strand may be longer
    than `N` (`net_abs_le_length` bounds it below, nothing bounds it above), so this is integer-count
    approximation, not realization within `N` events. -/
theorem form_approximated_freq (f : Form) (N : ℕ) (hN : 0 < N) :
    ∃ ts : List Twist,
      |(freqForm ts N).t - f.t| ≤ 1 / N ∧ |(freqForm ts N).x - f.x| ≤ 1 / N ∧
      |(freqForm ts N).y - f.y| ≤ 1 / N ∧ |(freqForm ts N).z - f.z| ≤ 1 / N := by
  obtain ⟨ts, h1, h2, h3, h4⟩ := form_approximated f N
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  have key : ∀ a s : ℝ, |a - N * s| ≤ 1 → |a / N - s| ≤ 1 / N := by
    intro a s h
    have e : a / N - s = (a - N * s) / N := by
      rw [sub_div, mul_comm, mul_div_assoc, div_self hn0, mul_one]
    rw [e, abs_div, abs_of_pos hn]
    gcongr
  exact ⟨ts, key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4⟩

/-- **A family of pure states made of strands.** For integers `m, n, k` (not all zero), the strand
    with nets `(m² + n² + k², 2mk, 2nk, m² + n² − k²)`, normalised by `N = 2(m² + n² + k²)`, is a
    pure qubit state. Its Bloch vector is the inverse stereographic image of the rational point
    `(m/k, n/k)`, which is why the four nets satisfy `(2mk)² + (2nk)² + (m² + n² − k²)² =
    (m² + n² + k²)²`. Pure states are limits of these *pure* strand frequencies
    (`pure_strand_frequencies_dense`). `N` is a normalisation, not the strand's
    length: off an axis the strand is longer than `N` (`window_pure_on_axis`). -/
theorem pure_state_family (m n k : ℤ) (N : ℕ) (hN : (N : ℤ) = 2 * (m ^ 2 + n ^ 2 + k ^ 2))
    (hN0 : N ≠ 0) :
    ∃ ts : List Twist, IsPure (freqForm ts N) := by
  obtain ⟨ts, h1, h2, h3, h4⟩ :=
    strand_realizes (m ^ 2 + n ^ 2 + k ^ 2) (2 * m * k) (2 * n * k) (m ^ 2 + n ^ 2 - k ^ 2)
  refine ⟨ts, ?_⟩
  have hNR : (N : ℝ) = 2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + (k : ℝ) ^ 2) := by exact_mod_cast hN
  have hD : (m : ℝ) ^ 2 + (n : ℝ) ^ 2 + (k : ℝ) ^ 2 ≠ 0 := by
    intro h0
    apply hN0
    have : (N : ℝ) = 0 := by rw [hNR, h0, mul_zero]
    exact_mod_cast this
  have hi : (2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + (k : ℝ) ^ 2)) *
      (2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + (k : ℝ) ^ 2))⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero hD)
  unfold IsPure
  simp only [freqForm, h1, h2, h3, h4]
  push_cast
  rw [hNR]
  constructor
  · linear_combination (1 / 2 : ℝ) * hi
  · linear_combination (1 / 4 * (2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + (k : ℝ) ^ 2) *
      (2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + (k : ℝ) ^ 2))⁻¹ + 1)) * hi

/-- The real inequality behind `window_pure_on_axis`: non-negative `a, b, c` with `a + b + c ≤ n/2`
    and `a² + b² + c² = n²/4` have every pairwise product zero, so at most one is non-zero. -/
private theorem at_most_one_nonzero (a b c n : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hn : 0 ≤ n) (hsum : a + b + c ≤ n / 2) (hS : a ^ 2 + b ^ 2 + c ^ 2 = n ^ 2 / 4) :
    a * b = 0 ∧ b * c = 0 ∧ a * c = 0 := by
  have hsq : (a + b + c) * (a + b + c) ≤ n / 2 * (n / 2) :=
    mul_le_mul hsum hsum (by linarith) (by linarith)
  have h1 := mul_nonneg ha hb
  have h2 := mul_nonneg hb hc
  have h3 := mul_nonneg ha hc
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hsq, hS, h1, h2, h3]

/-- **Inside its own window, a strand is pure only on an axis.** If a strand of at most `N` twists
    (one twist per event) has a pure frequency over the window `N`, then at most one of its spatial
    nets is non-zero: the state is one of the six axis states `±x, ±y, ±z`. The gauge net must be
    `N/2` for `t = ½`, leaving at most `N/2` twists for the Bloch vector, and a vector of length `½`
    whose coordinates sum in absolute value to at most `½` lies on an axis. So `pure_state_plus_up`
    is the generic case, and every off-axis pure state (`pure_state_family` with two of `m, n, k`
    non-zero, for instance `m = n = k = 1`: `N = 6` but nets `(3, 2, 2, 1)` need eight twists) is a
    frequency only when `N` is a normalisation, not the event count. -/
theorem window_pure_on_axis (ts : List Twist) (N : ℕ) (hlen : ts.length ≤ N)
    (hp : IsPure (freqForm ts N)) :
    netX ts * netY ts = 0 ∧ netY ts * netZ ts = 0 ∧ netX ts * netZ ts = 0 := by
  unfold IsPure at hp
  obtain ⟨ht, hs⟩ := hp
  simp only [freqForm] at ht hs
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      norm_num at ht
    · exact h
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  have hT : (netT ts : ℝ) = N / 2 := by
    rw [div_eq_iff hn0] at ht
    linarith
  have hS : (netX ts : ℝ) ^ 2 + (netY ts : ℝ) ^ 2 + (netZ ts : ℝ) ^ 2 = (N : ℝ) ^ 2 / 4 := by
    rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, div_eq_iff (pow_ne_zero 2 hn0)] at hs
    linarith
  rw [← sq_abs (netX ts : ℝ), ← sq_abs (netY ts : ℝ), ← sq_abs (netZ ts : ℝ)] at hS
  have hb := net_abs_le_length ts
  have hbR : |(netT ts : ℝ)| + |(netX ts : ℝ)| + |(netY ts : ℝ)| + |(netZ ts : ℝ)| ≤
      (ts.length : ℝ) := by exact_mod_cast hb
  have hlenR : (ts.length : ℝ) ≤ N := by exact_mod_cast hlen
  rw [hT, abs_of_pos (half_pos hn)] at hbR
  obtain ⟨p1, p2, p3⟩ := at_most_one_nonzero |(netX ts : ℝ)| |(netY ts : ℝ)| |(netZ ts : ℝ)| N
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hn.le (by linarith) hS
  rw [← abs_mul, abs_eq_zero] at p1 p2 p3
  exact ⟨by exact_mod_cast p1, by exact_mod_cast p2, by exact_mod_cast p3⟩

-- ==========================================
-- Rung 4b: pure strand frequencies are dense on the Bloch sphere
-- ==========================================

/-- Inverse stereographic projection from the north pole onto the Bloch sphere of radius `½`,
    `x` coordinate. -/
noncomputable def stereoX (u v : ℝ) : ℝ := u / (u ^ 2 + v ^ 2 + 1)
/-- Inverse stereographic projection, `y` coordinate. -/
noncomputable def stereoY (u v : ℝ) : ℝ := v / (u ^ 2 + v ^ 2 + 1)
/-- Inverse stereographic projection, `z` coordinate. -/
noncomputable def stereoZ (u v : ℝ) : ℝ := (u ^ 2 + v ^ 2 - 1) / (2 * (u ^ 2 + v ^ 2 + 1))

/-- The inverse stereographic image of every plane point is a pure Bloch vector (length `½`). -/
theorem stereo_on_sphere (u v : ℝ) :
    stereoX u v ^ 2 + stereoY u v ^ 2 + stereoZ u v ^ 2 = 1 / 4 := by
  have h : u ^ 2 + v ^ 2 + 1 ≠ 0 := by positivity
  have hi : (u ^ 2 + v ^ 2 + 1) * (u ^ 2 + v ^ 2 + 1)⁻¹ = 1 := mul_inv_cancel₀ h
  simp only [stereoX, stereoY, stereoZ, div_eq_mul_inv, mul_inv]
  linear_combination (((u ^ 2 + v ^ 2 + 1) * (u ^ 2 + v ^ 2 + 1)⁻¹ + 1) / 4) * hi

/-- **Stereographic projection inverts it.** Every pure Bloch vector except the north pole
    `(0, 0, ½)` is the image of the plane point `(2x, 2y)/(1 − 2z)`. -/
theorem stereo_inverse (x y z : ℝ) (hs : x ^ 2 + y ^ 2 + z ^ 2 = 1 / 4) (hz : z ≠ 1 / 2) :
    stereoX (2 * x / (1 - 2 * z)) (2 * y / (1 - 2 * z)) = x ∧
    stereoY (2 * x / (1 - 2 * z)) (2 * y / (1 - 2 * z)) = y ∧
    stereoZ (2 * x / (1 - 2 * z)) (2 * y / (1 - 2 * z)) = z := by
  have hw : (1 - 2 * z) ≠ 0 := by
    intro h
    apply hz
    linarith
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = 2 * x / (1 - 2 * z) := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v : ℝ, v = 2 * y / (1 - 2 * z) := ⟨_, rfl⟩
  rw [← hu_def, ← hv_def]
  have hu : 2 * x = u * (1 - 2 * z) := by
    rw [hu_def]
    exact (div_eq_iff hw).mp rfl
  have hv : 2 * y = v * (1 - 2 * z) := by
    rw [hv_def]
    exact (div_eq_iff hw).mp rfl
  have hS2 : (u ^ 2 + v ^ 2 + 1) * (1 - 2 * z) * (1 - 2 * z) = 2 * (1 - 2 * z) := by
    linear_combination (-(u * (1 - 2 * z) + 2 * x)) * hu + (-(v * (1 - 2 * z) + 2 * y)) * hv +
      4 * hs
  have hS : (u ^ 2 + v ^ 2 + 1) * (1 - 2 * z) = 2 := mul_right_cancel₀ hw hS2
  have hS0 : u ^ 2 + v ^ 2 + 1 ≠ 0 := by positivity
  unfold stereoX stereoY stereoZ
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_iff hS0]
    apply mul_right_cancel₀ hw
    linear_combination (-1 : ℝ) * hu - x * hS
  · rw [div_eq_iff hS0]
    apply mul_right_cancel₀ hw
    linear_combination (-1 : ℝ) * hv - y * hS
  · rw [div_eq_iff (mul_ne_zero two_ne_zero hS0)]
    apply mul_right_cancel₀ hw
    linear_combination (1 - 2 * z) * hS

/-- The three coordinates of the inverse stereographic map are continuous on the plane. -/
theorem stereo_continuous :
    Continuous (fun p : ℝ × ℝ => stereoX p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => stereoY p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => stereoZ p.1 p.2) := by
  have hd : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 + 1) := by fun_prop
  have hn3 : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 - 1) := by fun_prop
  have hd2 : Continuous (fun p : ℝ × ℝ => 2 * (p.1 ^ 2 + p.2 ^ 2 + 1)) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · unfold stereoX
    apply Continuous.div continuous_fst hd
    intro p
    show p.1 ^ 2 + p.2 ^ 2 + 1 ≠ 0
    positivity
  · unfold stereoY
    apply Continuous.div continuous_snd hd
    intro p
    show p.1 ^ 2 + p.2 ^ 2 + 1 ≠ 0
    positivity
  · unfold stereoZ
    apply Continuous.div hn3 hd2
    intro p
    show 2 * (p.1 ^ 2 + p.2 ^ 2 + 1) ≠ 0
    positivity

/-- `pure_state_family` at `(m, n, k) = K · (q, r, 1)` has frequency `(½, stereo(q, r))`: the
    family is the inverse stereographic image of `(m/k, n/k)`, and the scale `K` cancels. -/
private theorem family_coords (q r K : ℝ) (hK : K ≠ 0) :
    ((q * K) ^ 2 + (r * K) ^ 2 + K ^ 2) / (2 * ((q * K) ^ 2 + (r * K) ^ 2 + K ^ 2)) = 1 / 2 ∧
    2 * (q * K) * K / (2 * ((q * K) ^ 2 + (r * K) ^ 2 + K ^ 2)) = stereoX q r ∧
    2 * (r * K) * K / (2 * ((q * K) ^ 2 + (r * K) ^ 2 + K ^ 2)) = stereoY q r ∧
    ((q * K) ^ 2 + (r * K) ^ 2 - K ^ 2) / (2 * ((q * K) ^ 2 + (r * K) ^ 2 + K ^ 2)) =
      stereoZ q r := by
  have hs : q ^ 2 + r ^ 2 + 1 ≠ 0 := by positivity
  have hd : 2 * ((q * K) ^ 2 + (r * K) ^ 2 + K ^ 2) = 2 * K ^ 2 * (q ^ 2 + r ^ 2 + 1) := by ring
  have hd0 : 2 * K ^ 2 * (q ^ 2 + r ^ 2 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hK)) hs
  unfold stereoX stereoY stereoZ
  rw [hd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_eq_iff hd0]
    ring
  · rw [div_eq_iff hd0, div_mul_eq_mul_div, eq_div_iff hs]
    ring
  · rw [div_eq_iff hd0, div_mul_eq_mul_div, eq_div_iff hs]
    ring
  · rw [div_eq_iff hd0, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero two_ne_zero hs)]
    ring

/-- **Pure strand frequencies are dense among pure states.** For every pure qubit state `f` and every
    `ε > 0` there is a strand and a normalisation `N` whose frequency is itself a pure state and lies
    within `ε` of `f` on each Bloch coordinate (`t = ½` on both). The north pole is hit exactly by
    `+/` over `N = 2`. Every other pure state is the inverse stereographic image of a plane point;
    rational plane points are dense and the map is continuous, and a rational point
    `(q, r)` is `pure_state_family` at `(m, n, k) = (q, r, 1) · den q · den r`. So every pure state
    is a limit of pure strand frequencies, with no classical fact cited. `N` is a normalisation here:
    off an axis the strand is longer than `N` (`window_pure_on_axis`). -/
theorem pure_strand_frequencies_dense (f : Form) (hf : IsPure f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (ts : List Twist) (N : ℕ), IsPure (freqForm ts N) ∧
      |(freqForm ts N).x - f.x| < ε ∧ |(freqForm ts N).y - f.y| < ε ∧
      |(freqForm ts N).z - f.z| < ε := by
  unfold IsPure at hf
  obtain ⟨_, hs⟩ := hf
  by_cases hz : f.z = 1 / 2
  · -- the north pole, exactly: the strand `+/` normalised by `2`
    have hz2 : f.z ^ 2 = 1 / 4 := by
      rw [hz]
      norm_num
    have hxy : f.x ^ 2 + f.y ^ 2 = 0 := by linarith
    have hx : f.x = 0 := by nlinarith [sq_nonneg f.x, sq_nonneg f.y]
    have hy : f.y = 0 := by nlinarith [sq_nonneg f.x, sq_nonneg f.y]
    refine ⟨[Twist.plus, Twist.slash], 2, ?_, ?_, ?_, ?_⟩
    · unfold IsPure
      norm_num [freqForm, netT, netX, netY, netZ, twT, twX, twY, twZ]
    · rw [hx]
      norm_num [freqForm, netX, twX, hε]
    · rw [hy]
      norm_num [freqForm, netY, twY, hε]
    · rw [hz]
      norm_num [freqForm, netZ, twZ, hε]
  · -- every other pure state: approach its stereographic preimage by rational points
    obtain ⟨hX, hY, hZ⟩ := stereo_inverse f.x f.y f.z hs hz
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 * f.x / (1 - 2 * f.z) := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 2 * f.y / (1 - 2 * f.z) := ⟨_, rfl⟩
    rw [← hu, ← hv] at hX hY hZ
    obtain ⟨cx, cy, cz⟩ := stereo_continuous
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuous_iff.mp cx (u, v) ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuous_iff.mp cy (u, v) ε hε
    obtain ⟨δ₃, hδ₃, h₃⟩ := Metric.continuous_iff.mp cz (u, v) ε hε
    obtain ⟨δ, hδ, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ ∧ δ ≤ δ₃ :=
      ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), min_le_left _ _,
        (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u - δ < u + δ by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show v - δ < v + δ by linarith)
    have hd : dist ((q : ℝ), (r : ℝ)) (u, v) < δ := by
      simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have ex := h₁ _ (lt_of_lt_of_le hd hδ1)
    have ey := h₂ _ (lt_of_lt_of_le hd hδ2)
    have ez := h₃ _ (lt_of_lt_of_le hd hδ3)
    simp only [Real.dist_eq] at ex ey ez
    rw [hX] at ex
    rw [hY] at ey
    rw [hZ] at ez
    -- clear the denominators of `(q, r)` into integers `(m, n, k)`
    have hqd : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hrd : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
    have hq : (q : ℝ) * q.den = q.num := (eq_div_iff hqd).mp (Rat.cast_def q)
    have hr : (r : ℝ) * r.den = r.num := (eq_div_iff hrd).mp (Rat.cast_def r)
    have hK : (q.den : ℝ) * r.den ≠ 0 := mul_ne_zero hqd hrd
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) = q * ((q.den : ℝ) * r.den) :=
      ⟨q.num * r.den, by push_cast; rw [← hq]; ring⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) = r * ((q.den : ℝ) * r.den) :=
      ⟨r.num * q.den, by push_cast; rw [← hr]; ring⟩
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℝ) = (q.den : ℝ) * r.den :=
      ⟨q.den * r.den, by push_cast; ring⟩
    obtain ⟨ts, h1, h2, h3, h4⟩ :=
      strand_realizes (m ^ 2 + n ^ 2 + k ^ 2) (2 * m * k) (2 * n * k) (m ^ 2 + n ^ 2 - k ^ 2)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = 2 * (m ^ 2 + n ^ 2 + k ^ 2) :=
      ⟨_, Int.toNat_of_nonneg (by positivity)⟩
    have hNR : (N : ℝ) = 2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + (k : ℝ) ^ 2) := by exact_mod_cast hN
    obtain ⟨c1, c2, c3, c4⟩ := family_coords (q : ℝ) (r : ℝ) ((q.den : ℝ) * r.den) hK
    have ct : (freqForm ts N).t = 1 / 2 := by
      simp only [freqForm, h1]
      push_cast
      rw [hNR, hm, hn, hk]
      exact c1
    have cx' : (freqForm ts N).x = stereoX q r := by
      simp only [freqForm, h2]
      push_cast
      rw [hNR, hm, hn, hk]
      exact c2
    have cy' : (freqForm ts N).y = stereoY q r := by
      simp only [freqForm, h3]
      push_cast
      rw [hNR, hm, hn, hk]
      exact c3
    have cz' : (freqForm ts N).z = stereoZ q r := by
      simp only [freqForm, h4]
      push_cast
      rw [hNR, hm, hn, hk]
      exact c4
    refine ⟨ts, N, ?_, ?_, ?_, ?_⟩
    · unfold IsPure
      rw [ct, cx', cy', cz']
      exact ⟨rfl, stereo_on_sphere _ _⟩
    · rw [cx']
      exact ex
    · rw [cy']
      exact ey
    · rw [cz']
      exact ez

-- ==========================================
-- Rung 5: the strong reading — which pairs cannot be split
-- ==========================================

/-- A twist is **half-open** when, folded alone, it is not a scalar: it cannot stand as a closure on
    its own. -/
def HalfOpen (t : Twist) : Prop := ∀ c : ℂ, twistMatrixFold [t] ≠ c • (1 : M)

/-- **Strong entanglement** of the pair `[t, t†]`: neither half closes alone, so the pair has no
    product form (the reading of `QLF_IndexedFactors.shared_closure_not_factorizable`). -/
def StronglyEntangled (t : Twist) : Prop := HalfOpen t ∧ HalfOpen t.conj

private theorem scalar_entries {A : M} {c : ℂ} (h : A = c • (1 : M)) :
    A 0 1 = 0 ∧ A 0 0 = A 1 1 := by
  subst h
  simp [Matrix.smul_apply, Matrix.one_apply]

private theorem fold_single (t : Twist) : twistMatrixFold [t] = t.toMatrix := by
  show t.toMatrix * 1 = t.toMatrix
  rw [mul_one]

/-- A spatial twist folded alone is never a scalar. -/
theorem spatial_half_open (t : Twist) (ht : axisOf t ≠ Axis.I) : HalfOpen t := by
  intro c hc
  rw [fold_single] at hc
  have h := scalar_entries hc
  cases t <;> simp [axisOf] at ht <;> norm_num [Twist.toMatrix, σx, σy, σz] at h

theorem plus_not_half_open : ¬ HalfOpen Twist.plus := fun h =>
  h 1 (by rw [fold_single]; simp [Twist.toMatrix])

theorem minus_not_half_open : ¬ HalfOpen Twist.minus := fun h =>
  h (-1) (by rw [fold_single]; simp [Twist.toMatrix])

/-- **Rung 5: a pair is strongly entangled exactly when it is spatial.** The six spatial pairs
    (`^v`, `<>`, `/\`) cannot be split into independent halves; the gauge pair `+−` can, because each
    half folds to `±I` on its own. -/
theorem stronglyEntangled_iff_spatial (t : Twist) :
    StronglyEntangled t ↔ axisOf t ≠ Axis.I := by
  constructor
  · intro h hI
    have hg : t = Twist.plus ∨ t = Twist.minus := by
      cases t <;> simp [axisOf] at hI ⊢
    rcases hg with rfl | rfl
    · exact plus_not_half_open h.1
    · exact minus_not_half_open h.1
  · intro ht
    refine ⟨spatial_half_open t ht, spatial_half_open t.conj ?_⟩
    cases t <;> simp [axisOf, Twist.conj] at ht ⊢

/-- **A closure with no gauge twists is made only of strong entanglements.** Every pair in its
    canonical decomposition (`closure_is_pairs`) is non-factorizable. -/
theorem no_gauge_all_strongly_entangled (ts : List Twist) (hplus : ts.count Twist.plus = 0) :
    ∀ t ∈ canonicalPairs ts, StronglyEntangled t := by
  intro t ht
  rw [stronglyEntangled_iff_spatial]
  cases t <;> simp [canonicalPairs, hplus, axisOf] at ht ⊢

-- ==========================================
-- Rung 6: a strong pair is an axis that cancels on the singlet
-- ==========================================

/-- Spatial twists are traceless. -/
theorem trace_spatial (t : Twist) (ht : axisOf t ≠ Axis.I) : Matrix.trace t.toMatrix = 0 := by
  cases t <;> simp [axisOf] at ht <;> simp [Twist.toMatrix, σx, σy, σz, Matrix.trace, Fin.sum_univ_two]

/-- **Rung 6: a pair is strongly entangled exactly when its axis cancels on the two-body singlet.**
    Reading the pair `[t, t†]` as the twist's axis acting on both sites of a two-body state
    (`QLF_JointClosure.joint`), the singlet absorbs it (net action zero) iff the pair is strong. The
    gauge pair does not cancel: it acts on the singlet as the scalar `±2`. -/
theorem singlet_cancels_iff_strong (t : Twist) :
    Matrix.mulVec (JointClosure.joint t.toMatrix) JointClosure.s = 0 ↔ StronglyEntangled t := by
  rw [stronglyEntangled_iff_spatial, JointClosure.singlet_trace]
  constructor
  · intro h hI
    have hg : t = Twist.plus ∨ t = Twist.minus := by
      cases t <;> simp [axisOf] at hI ⊢
    have h01 := congrFun h (0, 1)
    rcases hg with rfl | rfl <;>
      norm_num [JointClosure.s, Twist.toMatrix, Matrix.trace, Fin.sum_univ_two] at h01
  · intro ht
    rw [trace_spatial t ht, zero_smul]

/-- **The singlet is the unique two-body state on which every strong pair cancels.** Strong pairs
    (rung 5) and the joint closure (`closed_iff_singlet`) pick out the same state. -/
theorem strong_pairs_cancel_iff_singlet (ψ : Fin 2 × Fin 2 → ℂ) :
    (∀ t : Twist, StronglyEntangled t →
        Matrix.mulVec (JointClosure.joint t.toMatrix) ψ = 0) ↔
      ψ = ψ (0, 1) • JointClosure.s := by
  constructor
  · intro h
    apply (JointClosure.closed_iff_singlet ψ).1
    exact ⟨h Twist.right ((stronglyEntangled_iff_spatial _).2 (by simp [axisOf])),
      h Twist.slash ((stronglyEntangled_iff_spatial _).2 (by simp [axisOf]))⟩
  · intro hψ t ht
    rw [hψ, Matrix.mulVec_smul, (singlet_cancels_iff_strong t).2 ht, smul_zero]

/-- Summary: closure = a reordering of conjugate pairs (rung 1); phase = pairs × crossings (rung 2);
    Form = the open half's net signed count, zero exactly on closures (rung 3); every rational Form,
    and every rational pure state, is a frequency of a strand (rung 4); under the strong reading, exactly the
    spatial pairs are entangled and the gauge pair is a product (rung 5); a strong pair is exactly an
    axis that cancels on the singlet, and the singlet is the one state all strong pairs cancel on
    (rung 6). See the module note for what
    stays open. -/
theorem entanglement_primacy_status : True := trivial

end QLF.EntanglementPrimacy
