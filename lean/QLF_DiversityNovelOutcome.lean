import QLF_ConformalComparison
import QLF_EdgeSign
-- Narrow imports: this module stays off `import Mathlib`.

/-!
# QLF_DiversityNovelOutcome — complementary composition creates a closure type (#290 E1)

Issue #290 asks whether emergence favors diversity, and names the Lean milestone
`complementary_composition_creates_novel_closure` (Theorem E1, gate D8b). The test is
pre-registered in [`Diversity_Novel_Outcome_E1.md`](../Diversity_Novel_Outcome_E1.md) §1 and run by
[`diversity_novel_outcome.py`](../diversity_novel_outcome.py).

The type of a closed history is its fold, `+1` or `−1`. Composition is concatenation.

* **`self_compose_balanced_iff`.** `a ++ a` is closed exactly when `a` is: an open history never
  closes with itself.
* **`self_composition_type_one`.** Whenever `a ++ a` is closed it folds to `+1`. So homogeneous
  composition reaches one type.
* **`complementary_composition_creates_novel_closure`.** The open histories `^<` and `v>` compose
  to a closure of type `−1`, and so do `^` and `v`. That type has no homogeneous generator.

This is gate D8b on the concatenation relation. It says nothing about an advantage (D8c),
persistence (D9) or physical relevance (D10).

No axioms.
-/

namespace QLF.DiversityNovelOutcome

open QLF QLF.ClosureUnitarity QLF.EdgeSign QLF.PhaseRule QLF.ConformalComparison

theorem count_self_append (a : List Twist) (t : Twist) :
    (a ++ a).count t = 2 * a.count t := by
  rw [List.count_append]; ring

/-- **An open history never closes with itself.** -/
theorem self_compose_balanced_iff (a : List Twist) :
    countBalanced (a ++ a) ↔ countBalanced a := by
  unfold countBalanced
  simp only [count_self_append]
  omega

theorem connectionPhase_sq (ts : List Twist) : connectionPhase ts * connectionPhase ts = 1 := by
  rw [connectionPhase_eq_predictedPhase, predictedPhase, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **Homogeneous composition reaches one type.** -/
theorem self_composition_type_one {a : List Twist} (h : countBalanced (a ++ a)) :
    twistMatrixFold (a ++ a) = 1 := by
  have ha : countBalanced a := (self_compose_balanced_iff a).1 h
  rw [fold_append, fold_eq_connectionPhase ha, smul_mul_smul_comm, Matrix.one_mul, ← Int.cast_mul,
    connectionPhase_sq]
  simp

/-- **Complementary composition creates the `−1` type.** Two open histories close together with
    fold `−1`, which no self-composition reaches. -/
theorem complementary_composition_creates_novel_closure :
    ¬ countBalanced [Twist.up, Twist.left] ∧ ¬ countBalanced [Twist.down, Twist.right] ∧
      countBalanced ([Twist.up, Twist.left] ++ [Twist.down, Twist.right]) ∧
      twistMatrixFold ([Twist.up, Twist.left] ++ [Twist.down, Twist.right]) = -1 ∧
      ∀ a : List Twist, countBalanced (a ++ a) → twistMatrixFold (a ++ a) ≠ -1 := by
  refine ⟨by unfold countBalanced; decide, by unfold countBalanced; decide,
    by unfold countBalanced; decide, interleaved_xlvr_folds_to_negI, ?_⟩
  intro a h hneg
  rw [self_composition_type_one h] at hneg
  have := congrFun (congrFun hneg 0) 0
  norm_num at this

/-- The minimal witness: `^` and `v` close together with fold `−1`. -/
theorem minimal_complementary_pair :
    twistMatrixFold [Twist.up, Twist.down] = -1 := by
  rw [show [Twist.up, Twist.down] = [Twist.up] ++ [Twist.up.conj] from rfl, fold_append,
    fold_singleton, fold_singleton]
  exact hermitian_pair_is_pauli_scalar Twist.up

end QLF.DiversityNovelOutcome
