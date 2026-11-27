import QLF_ColourClosure
import QLF_Majorana
import QLF_ElectronClosure

/-!
# QLF_VacuumCorrelation — what a neutrino word shares with the vacuum, and what organization adds

Part of the [Quantum Logical Framework (QLF)](../README.md). Companion document:
[`Vacuum_Correlation.md`](../Vacuum_Correlation.md).

Three structural gates proposed after `QLF_ColourClosure` (#327), proved here with no axioms.

* **N0, the neutrino word is a vacuum closure.** The minimal neutrino word `^v` and the same word with
  a vacuum label give the same reading (twist counts, Pauli fold, closing delay), because the reading
  is a function of the word (`neutrino_vacuum_same_reading`, bookkeeping). The fold sees less still:
  in every context, inserting `^v` folds the same as inserting any Hermitian pair `[t, t†]` on any axis
  (`neutrino_block_fold_blind`), and `^v` and `v^` give the same reading although they are different
  words (`nu_reading_order_blind`). So a neutrino, if it differs from vacuum activity at all, differs
  by a relation to something else: provenance or interleaving (gate N1, open).
* **V0, common-mode closures cancel.** A closed part inserted into both branches of a comparison
  leaves their relative Pauli phase unchanged, in both directions (`common_mode_cancels`). Inserted
  into one branch only, it shifts the relative phase (`one_branch_closure_shifts_phase`): an
  independent closure is detectable only relationally, and then only as a phase.
* **V1, organization carries phase.** `^v><` (two independent closures) and `^>v<` (one interleaved
  closure) are rearrangements of the same four twists, both closed, both at delay `0`, both colour
  neutral, and they fold to `+I` and `−I` (`same_inventory_opposite_phase`). In every context the
  interleaving flips the sign (`interleaving_flips_phase`), and the interleaved word is prime: no
  proper prefix closes (`interleaved_prime`).
* **H1, the minimal handed closures.** Length-2 closures fold to `−I` and are all self-conjugate
  (`length_two_closures`). On one pair from each of two spatial axes the fold is `−I` exactly when the
  pairs cross, which happens for 8 of the 24 orderings, and every such ordering is not
  self-conjugate (`two_axis_classification`). With a gauge pair the fold is always `+I`
  (`gauge_pair_never_negI`). For the `y, x` axes the 8 are the electron loop `^<v>` and its mirror
  `^>v<`, each with its four rotations (`electron_class`). So the shortest spatial closures that are
  both handed (not self-conjugate) and carry the half-spin sign have length 4, and they are the
  24 electron-class loops on the three spatial planes. The full eight-twist length-4 census is
  exact computational in [`vacuum_correlation_census.py`](../vacuum_correlation_census.py), which
  also shows the pattern stops there: at length 6, 48 of the 720 one-pair-per-axis orderings are
  self-conjugate with `−I`. (That enumeration stays in Python: kernel `decide` over 720 orderings
  needed about 13 GB in #327.)

**Scope.** The labels "neutrino", "vacuum" and "electron" are QLF's word assignments
([`QLF_Majorana`](QLF_Majorana.lean), [`QLF_ElectronClosure`](QLF_ElectronClosure.lean)). Nothing here
derives a mass, an oscillation, a coupling or the α residual; those are the bridges H4–H7, N3–N5 and
V2–V6 registered in [`Principles.md`](../Principles.md).
-/

set_option linter.unusedVariables false

namespace QLF.VacuumCorrelation

open QLF QLF.Majorana QLF.Manifestation QLF.ColourClosure

-- ============================================================================
-- §0  A computable fold
-- ============================================================================

/-- One step of the symbolic fold: multiply a normal form `(phase, axis)` on the left by a twist. -/
def nfStep (t : Twist) (acc : NF) : NF :=
  ((twistNF t).1 * acc.1 * cocycle (twistNF t).2 acc.2, axisMul (twistNF t).2 acc.2)

/-- The **symbolic Pauli fold** of a history: its normal form `(phase, axis)`, computed without
    matrices, so that `decide` can read it. -/
def nfFold (ts : List Twist) : NF := ts.foldr nfStep (PauliScalar.one, Axis.I)

/-- The symbolic fold is the matrix fold. -/
theorem fold_eq_nfFold (ts : List Twist) :
    twistMatrixFold ts = coePS (nfFold ts).1 • axisMatrix (nfFold ts).2 := by
  induction ts with
  | nil => simp [twistMatrixFold, nfFold, axisMatrix, coePS]
  | cons t rest ih =>
    show t.toMatrix * twistMatrixFold rest
        = coePS ((twistNF t).1 * (nfFold rest).1 * cocycle (twistNF t).2 (nfFold rest).2)
          • axisMatrix (axisMul (twistNF t).2 (nfFold rest).2)
    rw [ih, twist_toMatrix_smul, smul_mul_smul', axisMatrix_mul_smul, smul_smul,
        ← coePS_mul, ← coePS_mul]

/-- A history whose symbolic fold is `(p, I)` folds to the Pauli scalar `p`. -/
theorem fold_of_nfFold {ts : List Twist} {p : PauliScalar} (h : nfFold ts = (p, Axis.I)) :
    twistMatrixFold ts = pauliScalarToMatrix p := by
  rw [fold_eq_nfFold, h, pauliScalarToMatrix_eq]
  rfl

/-- Boolean count balance, for `decide` over lists of words. -/
def cbB (ts : List Twist) : Bool :=
  ts.count Twist.up == ts.count Twist.down && ts.count Twist.left == ts.count Twist.right &&
  ts.count Twist.slash == ts.count Twist.backslash && ts.count Twist.plus == ts.count Twist.minus

theorem cbB_iff (ts : List Twist) : cbB ts = true ↔ countBalanced ts := by
  simp [cbB, countBalanced, and_assoc]

-- ============================================================================
-- §1  N0 — the neutrino word is a vacuum closure
-- ============================================================================

/-- The eight twists, in a fixed order. -/
def allTwists : List Twist :=
  [Twist.up, Twist.down, Twist.left, Twist.right, Twist.slash, Twist.backslash, Twist.plus,
    Twist.minus]

/-- What an observer reads from a word without further relations: the eight twist counts, the
    Pauli fold, and the closing delay. -/
structure Reading where
  counts : List ℕ
  fold : NF
  delay : ℕ
deriving DecidableEq

def reading (ts : List Twist) : Reading := ⟨allTwists.map ts.count, nfFold ts, distance ts⟩

/-- Where a word came from. Not part of the word. -/
inductive Source where
  | neutrino
  | vacuum
deriving DecidableEq

/-- A word together with its provenance. -/
structure Labelled where
  source : Source
  word : List Twist

/-- The minimal neutrino word `^v` ([`QLF_Majorana`](QLF_Majorana.lean)). -/
def nu : List Twist := [Twist.up, Twist.down]

/-- **N0 (bookkeeping).** Any observable that is a function of the word, the reading included, takes
    the same value on a neutrino-labelled word and the same word labelled vacuum. Provenance is not
    in the word. -/
theorem no_word_observable_separates {β : Type} (f : List Twist → β) (w : List Twist) :
    f (Labelled.mk Source.neutrino w).word = f (Labelled.mk Source.vacuum w).word := rfl

theorem neutrino_vacuum_same_reading :
    reading (Labelled.mk Source.neutrino nu).word = reading (Labelled.mk Source.vacuum nu).word :=
  rfl

/-- The neutrino word's reading: one `^`, one `v`, fold `−I`, delay `0`. -/
theorem nu_reading :
    reading nu = ⟨[1, 1, 0, 0, 0, 0, 0, 0], (PauliScalar.negOne, Axis.I), 0⟩ := by decide

/-- **The reading does not see the order of the pair.** `^v` and `v^` are different words with the
    same reading. -/
theorem nu_reading_order_blind :
    reading [Twist.down, Twist.up] = reading nu ∧ [Twist.down, Twist.up] ≠ nu := by decide

/-- The neutrino word is its own antiparticle, so conjugation gives no handle either. -/
theorem nu_self_conjugate : Majorana nu := neutrino_majorana

/-- The fold of a Hermitian pair `[t, t†]` is `−I`. -/
theorem pair_fold (t : Twist) : twistMatrixFold [t, Twist.conj t] = -1 := by
  show t.toMatrix * ((Twist.conj t).toMatrix * 1) = -1
  rw [mul_one, hermitian_pair_folds_to_negI]

/-- **N0 (fold layer).** In every context `b … c`, inserting the neutrino block `^v` gives the same
    fold as inserting any Hermitian pair `[t, t†]`, on any of the four axes. The fold cannot tell a
    neutrino block from a vacuum pair of another axis. -/
theorem neutrino_block_fold_blind (t : Twist) (b c : List Twist) :
    twistMatrixFold (b ++ nu ++ c) = twistMatrixFold (b ++ [t, Twist.conj t] ++ c) := by
  simp only [ClosureUnitarity.fold_append]
  rw [pair_fold, show nu = [Twist.up, Twist.conj Twist.up] from rfl, pair_fold]

-- ============================================================================
-- §2  V0 — common-mode closures cancel from relative phase
-- ============================================================================

/-- `u` and `v` differ by the relative Pauli phase `q`. -/
def RelPhase (u v : List Twist) (q : PauliScalar) : Prop :=
  twistMatrixFold u = pauliScalarToMatrix q * twistMatrixFold v

theorem psm_inv (p : PauliScalar) :
    ∃ p' : PauliScalar, pauliScalarToMatrix p' * pauliScalarToMatrix p = 1 := by
  cases p
  · exact ⟨PauliScalar.one, by rw [pauliScalarToMatrix_mul]; rfl⟩
  · exact ⟨PauliScalar.negI, by rw [pauliScalarToMatrix_mul]; rfl⟩
  · exact ⟨PauliScalar.negOne, by rw [pauliScalarToMatrix_mul]; rfl⟩
  · exact ⟨PauliScalar.i, by rw [pauliScalarToMatrix_mul]; rfl⟩

/-- **V0.** A closed part `a`, inserted anywhere into both branches of a comparison, leaves their
    relative phase unchanged: `b c` and `b' c'` differ by `q` exactly when `b a c` and `b' a c'` do.
    Common-mode vacuum activity cancels from a relative-phase observable. -/
theorem common_mode_cancels {a : List Twist} (ha : countBalanced a) (b c b' c' : List Twist)
    (q : PauliScalar) :
    RelPhase (b ++ c) (b' ++ c') q ↔ RelPhase (b ++ a ++ c) (b' ++ a ++ c') q := by
  obtain ⟨p, hp⟩ := closed_insertion_is_phase ha
  obtain ⟨p', hp'⟩ := psm_inv p
  unfold RelPhase
  rw [hp b c, hp b' c']
  have comm : pauliScalarToMatrix q * pauliScalarToMatrix p
      = pauliScalarToMatrix p * pauliScalarToMatrix q := psm_comm p _
  constructor
  · intro h
    rw [h, ← mul_assoc, ← mul_assoc, comm]
  · intro h
    calc twistMatrixFold (b ++ c)
        = pauliScalarToMatrix p' * (pauliScalarToMatrix p * twistMatrixFold (b ++ c)) := by
          rw [← mul_assoc, hp', one_mul]
      _ = pauliScalarToMatrix p' * (pauliScalarToMatrix q
            * (pauliScalarToMatrix p * twistMatrixFold (b' ++ c'))) := by rw [h]
      _ = pauliScalarToMatrix p' * (pauliScalarToMatrix p
            * (pauliScalarToMatrix q * twistMatrixFold (b' ++ c'))) := by
          rw [← mul_assoc (pauliScalarToMatrix q), comm, mul_assoc]
      _ = pauliScalarToMatrix q * twistMatrixFold (b' ++ c') := by
          rw [← mul_assoc, hp', one_mul]

/-- **The limit of V0.** Inserted into one branch only, a vacuum pair is not invisible: `^v` placed
    in front of the empty history shifts the relative phase to `−1`. An independent closure is
    detectable relationally, and only as a phase, which by `neutrino_block_fold_blind` is the same
    for every Hermitian pair. -/
theorem one_branch_closure_shifts_phase (v : List Twist) :
    RelPhase (nu ++ v) v PauliScalar.negOne := by
  unfold RelPhase
  rw [ClosureUnitarity.fold_append, show nu = [Twist.up, Twist.conj Twist.up] from rfl, pair_fold]
  rfl

-- ============================================================================
-- §3  V1 — same twists, same balance, opposite phase
-- ============================================================================

/-- `^v><`: two independent closures, `^v` then `><`. -/
def independent : List Twist := [Twist.up, Twist.down, Twist.right, Twist.left]

/-- `^>v<`: the same four twists, interleaved into one closure. -/
def interleaved : List Twist := [Twist.up, Twist.right, Twist.down, Twist.left]

theorem independent_fold : twistMatrixFold independent = 1 :=
  fold_of_nfFold (p := PauliScalar.one) (by decide)

theorem interleaved_fold : twistMatrixFold interleaved = -1 :=
  fold_of_nfFold (p := PauliScalar.negOne) (by decide)

/-- **V1.** `^v><` and `^>v<` are rearrangements of one inventory; both close, both have delay `0`,
    both are colour neutral; their folds are `+I` and `−I`. Net action is the same, phase is not. -/
theorem same_inventory_opposite_phase :
    independent.Perm interleaved ∧ countBalanced independent ∧ countBalanced interleaved ∧
    distance independent = 0 ∧ distance interleaved = 0 ∧
    colourTotal independent = 0 ∧ colourTotal interleaved = 0 ∧
    twistMatrixFold independent = 1 ∧ twistMatrixFold interleaved = -1 := by
  refine ⟨by decide, (cbB_iff _).1 (by decide), (cbB_iff _).1 (by decide), by decide, by decide,
    by decide, by decide, independent_fold, interleaved_fold⟩

/-- The independent word is two closures in sequence. -/
theorem independent_splits :
    independent = nu ++ [Twist.right, Twist.left] ∧ countBalanced nu ∧
    countBalanced [Twist.right, Twist.left] :=
  ⟨rfl, (cbB_iff _).1 (by decide), (cbB_iff _).1 (by decide)⟩

/-- **The interleaved word is prime**: no proper non-empty prefix of `^>v<` closes, so it is not a
    concatenation of closures. -/
theorem interleaved_prime :
    ∀ k ∈ [1, 2, 3], ¬ countBalanced (interleaved.take k) := by
  intro k hk h
  rw [← cbB_iff] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> revert h <;> decide

/-- **Interleaving flips the phase in every context.** Whatever surrounds them, the interleaved
    arrangement folds to minus the independent one. -/
theorem interleaving_flips_phase (b c : List Twist) :
    twistMatrixFold (b ++ interleaved ++ c) = -twistMatrixFold (b ++ independent ++ c) := by
  simp only [ClosureUnitarity.fold_append, independent_fold, interleaved_fold, mul_one, mul_neg,
    neg_mul]

-- ============================================================================
-- §4  H1 — the minimal handed closures
-- ============================================================================

/-- **Length 2.** Every closure of length 2 folds to `−I` and is its own antiparticle: the one-axis
    pairs carry the half-spin sign but no handedness. (Checked over all 64 two-letter words.) -/
theorem length_two_closures :
    allTwists.all (fun a => allTwists.all (fun b =>
      !cbB [a, b] || (nfFold [a, b] == (PauliScalar.negOne, Axis.I) &&
        antiparticle [a, b] == [a, b]))) = true := by decide

/-- The orderings of one pair from each of two axes. -/
def minimalTwoAxis (s t : Twist) : List (List Twist) :=
  List.permutations' [s, Twist.conj s, t, Twist.conj t]

/-- A word has a conjugate pair in adjacent positions. -/
def hasAdjacentPair : List Twist → Bool
  | a :: b :: rest => b == Twist.conj a || hasAdjacentPair (b :: rest)
  | _ => false

/-- The H1 predicate on one axis pair: every ordering folds to a Pauli scalar on the trivial axis;
    it folds to `−I` exactly when no conjugate pair is adjacent (the two pairs cross); every such
    ordering is not self-conjugate; and there are 8 of them. -/
def classifies (s t : Twist) : Bool :=
  (minimalTwoAxis s t).all (fun w =>
      ((nfFold w).2 == Axis.I) &&
      ((nfFold w == (PauliScalar.negOne, Axis.I)) == !hasAdjacentPair w) &&
      (nfFold w != (PauliScalar.negOne, Axis.I) || antiparticle w != w)) &&
  ((minimalTwoAxis s t).filter (fun w => nfFold w == (PauliScalar.negOne, Axis.I))).length == 8

/-- **H1 on the three spatial planes.** For each pair of spatial axes, of the 24 orderings of one
    pair from each axis, the fold is `−I` exactly when the pairs cross; that happens for 8; and none
    of those 8 is its own antiparticle. -/
theorem two_axis_classification :
    classifies Twist.up Twist.left = true ∧ classifies Twist.up Twist.slash = true ∧
    classifies Twist.left Twist.slash = true := by decide

/-- **With a gauge pair the sign never appears.** A gauge twist folds to `±I` and commutes with
    everything, so every ordering of a spatial pair with the gauge pair folds to `+I`. -/
theorem gauge_pair_never_negI :
    [Twist.up, Twist.left, Twist.slash].all (fun s =>
      (minimalTwoAxis s Twist.plus).all (fun w => nfFold w == (PauliScalar.one, Axis.I))) = true := by
  decide

/-- **The electron class.** On the `y, x` plane the eight `−I` orderings are the electron loop
    `^<v>` and its mirror `^>v<`, each with its four rotations. -/
theorem electron_class :
    ((minimalTwoAxis Twist.up Twist.left).filter
        (fun w => nfFold w == (PauliScalar.negOne, Axis.I))).Perm
      [ [Twist.up, Twist.left, Twist.down, Twist.right],
        [Twist.left, Twist.down, Twist.right, Twist.up],
        [Twist.down, Twist.right, Twist.up, Twist.left],
        [Twist.right, Twist.up, Twist.left, Twist.down],
        [Twist.up, Twist.right, Twist.down, Twist.left],
        [Twist.right, Twist.down, Twist.left, Twist.up],
        [Twist.down, Twist.left, Twist.up, Twist.right],
        [Twist.left, Twist.up, Twist.right, Twist.down] ] := by decide

/-- The electron loop of [`QLF_ElectronClosure`](QLF_ElectronClosure.lean) is in the class, and the
    interleaved word of V1 is its mirror. -/
theorem electron_in_class :
    electronCycle ∈ (minimalTwoAxis Twist.up Twist.left) ∧
    nfFold electronCycle = (PauliScalar.negOne, Axis.I) ∧ ¬ Majorana electronCycle ∧
    antiparticle interleaved ≠ interleaved := by
  refine ⟨by decide, by decide, electron_not_majorana, by decide⟩

end QLF.VacuumCorrelation
