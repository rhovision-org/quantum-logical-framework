/-
# QLF_DiversityPhase

The two facts that settle the phase and axis clauses of the D3T diversity relation
(`Diversity_Obligation_D3T.md`, issue #290, PR #299), so that D8c2 can be run on
continuation profiles alone.

1. **The fold is multiplicative** (`twistMatrixFold_append`): the ordered Pauli fold of
   `a ++ b` is the product of the folds.  So the whole-prefix fold of a base, together with
   the fold of an extension, determines the joint closure phase
   (`prefix_fold_determines_phase`).  D3T.6 failed because its boundary record keeps one fold
   *per provenance stream*, and the per-stream folds do not fix the fold of their
   interleaving: `stream_folds_miss_interleaving` exhibits the same two streams, `^v` and
   `<>`, scheduled two ways with folds `+I` and `−I`.  Adding the whole-prefix fold to the
   record repairs phase sufficiency by this theorem, so a census retest would be bookkeeping.

2. **The axis clause is entailed by the net clause** (`axis_match_of_countBalanced_append`):
   if two streams have complementary net action (`countBalanced (a ++ b)`), their Pauli axes
   are equal.  The axis is a function of the twist-count parities
   (`axisProd_append_vec`), and complementary nets have equal parities.  So D3T's per-stream
   axis-match condition removes no candidate that the net-match condition admits.

Together with the keystone `count_balanced_pauli_closed` (count balance ⟹ Pauli scalar), (2)
also explains why the "net-zero, no fold" null model of `Diversity_Interface_D3.md` §4
matched ZFA exactly on every base in #297/#298: for these relations the null *is* ZFA.  A
D8c2 null model must therefore remove something other than the fold.

No axioms.  Part of [Quantum Logical Framework (QLF)](../README.md).
-/

import QLF_TwistAlphabet

namespace QLF.DiversityPhase

open QLF

/-! ## 1. The fold is multiplicative -/

private theorem foldr_mul_eq (a : List Twist) (X : M) :
    a.foldr (fun t acc => t.toMatrix * acc) X = twistMatrixFold a * X := by
  induction a with
  | nil => simp [twistMatrixFold]
  | cons t rest ih =>
    simp only [List.foldr_cons, ih, twistMatrixFold, mul_assoc]

/-- **Fold multiplicativity.** -/
theorem twistMatrixFold_append (a b : List Twist) :
    twistMatrixFold (a ++ b) = twistMatrixFold a * twistMatrixFold b := by
  rw [twistMatrixFold, List.foldr_append, foldr_mul_eq]
  rfl

/-- **The whole-prefix fold determines the joint phase.**  Two bases with the same fold give
the same joint fold with every extension. -/
theorem prefix_fold_determines_phase {a a' : List Twist}
    (h : twistMatrixFold a = twistMatrixFold a') (b : List Twist) :
    twistMatrixFold (a ++ b) = twistMatrixFold (a' ++ b) := by
  rw [twistMatrixFold_append, twistMatrixFold_append, h]

private theorem pair_up_down :
    twistMatrixFold [Twist.up, Twist.down] = -(1 : M) := by
  have h := hermitian_pair_folds_to_negI Twist.up
  simpa [twistMatrixFold, Twist.conj] using h

private theorem pair_left_right :
    twistMatrixFold [Twist.left, Twist.right] = -(1 : M) := by
  have h := hermitian_pair_folds_to_negI Twist.left
  simpa [twistMatrixFold, Twist.conj] using h

/-- **Per-stream folds do not fix the fold of an interleaving.**  Stream A is `^v` and
stream B is `<>`.  Scheduled `A A B B` the history `^v<>` folds to `+I`; scheduled `A B A B`
the history `^<v>` folds to `−I`.  Both schedules have the same two projections, hence the
same per-stream obligations `(net, axis, phase)`, so D3T's boundary record cannot separate
them. -/
theorem stream_folds_miss_interleaving :
    twistMatrixFold [Twist.up, Twist.down, Twist.left, Twist.right] = 1 ∧
    twistMatrixFold [Twist.up, Twist.left, Twist.down, Twist.right] = -(1 : M) ∧
    (1 : M) ≠ -(1 : M) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : [Twist.up, Twist.down, Twist.left, Twist.right]
        = [Twist.up, Twist.down] ++ [Twist.left, Twist.right] := rfl
    rw [e, twistMatrixFold_append, pair_up_down, pair_left_right]
    simp
  · simpa [pauliScalarToMatrix] using interleaved_xlvr_folds_to_negI
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp at h00
    norm_num at h00

/-! ## 2. The axis clause is entailed by the net clause -/

/-- The axis vector of a concatenation is the sum of the axis vectors. -/
theorem axisProd_append_vec (a b : List Twist) :
    axisToVec (axisProd (a ++ b)) = axisToVec (axisProd a) + axisToVec (axisProd b) := by
  rw [axisToVec_axisProd, axisToVec_axisProd, axisToVec_axisProd, List.map_append,
    List.sum_append]

private theorem axisToVec_injective (x y : Axis) (h : axisToVec x = axisToVec y) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

private theorem zmod2_pair_add_eq_zero (u v : ZMod 2 × ZMod 2) (h : u + v = 0) : u = v := by
  revert u v
  decide

/-- **Complementary nets have equal Pauli axes.**  `countBalanced (a ++ b)` says the net
action of `b` cancels that of `a`; it forces `axisProd a = axisProd b`. -/
theorem axis_match_of_countBalanced_append {a b : List Twist}
    (h : countBalanced (a ++ b)) : axisProd a = axisProd b := by
  apply axisToVec_injective
  apply zmod2_pair_add_eq_zero
  rw [← axisProd_append_vec, axisProd_eq_I_of_countBalanced h]
  rfl

end QLF.DiversityPhase
