import QLF_ClosureUnitarity
-- Narrow imports, as in QLF_ClosureUnitarity: this module stays off `import Mathlib`.

/-!
# QLF_ConformalComparison — does ZFA have a local scale symmetry? (#302 C1)

Issue #302 C1 asks whether QLF's closure rule carries a *local* scale symmetry, the first step
of an intrinsic Weyl (conformal-gravity) route. The test is pre-registered in
[`Conformal_Comparison.md`](../Conformal_Comparison.md) §1 and run by
[`conformal_comparison.py`](../conformal_comparison.py).

The class tested is the position-dependent letter substitution: each twist of a history is
replaced by `k_p` copies of itself (a local dilation). This module proves the dilation facts the
run reports.

* **`count_dilate`.** A global dilation by `k` multiplies every twist count by `k`.
* **`dilate_balanced`.** So a global dilation preserves count balance, hence ZFA.
* **`fold_dilate_odd`.** An odd dilation leaves the Pauli fold unchanged: every twist squares to
  the identity (`twist_sq`), so `t^{2m+1} = t`.
* **`fold_dilate_even`.** An even dilation folds every history to `1`: the phase is erased.
* **`local_dilation_breaks_balance`.** A position-dependent dilation does not preserve balance:
  `[^, v]` with scales `(3, 1)` gives `[^, ^, ^, v]`, which is not count-balanced.

So within letter substitutions the scale symmetry is global, not local (W1–W3 of the
pre-registration). This is a scoped obstruction, not a statement about every QLF transformation.

No axioms.
-/

namespace QLF.ConformalComparison

open QLF QLF.ClosureUnitarity

/-- The global dilation: every twist repeated `k` times. -/
def dilate (k : ℕ) (h : List Twist) : List Twist := h.flatMap (List.replicate k)

/-- The local dilation: twist `i` repeated `ks i` times. -/
def dilateLocal : List (Twist × ℕ) → List Twist
  | [] => []
  | (t, k) :: rest => List.replicate k t ++ dilateLocal rest

theorem dilate_nil (k : ℕ) : dilate k [] = [] := rfl

theorem dilate_cons (k : ℕ) (t : Twist) (h : List Twist) :
    dilate k (t :: h) = List.replicate k t ++ dilate k h := by
  simp [dilate, List.flatMap_cons]

theorem count_cons_twist (s t : Twist) (h : List Twist) :
    (s :: h).count t = List.count t [s] + h.count t := by
  rw [show s :: h = [s] ++ h from rfl, List.count_append]

theorem count_replicate_twist (k : ℕ) (s t : Twist) :
    (List.replicate k s).count t = k * (List.count t [s]) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, count_cons_twist, ih]
      ring

/-- **A global dilation multiplies every count by `k`.** -/
theorem count_dilate (k : ℕ) (h : List Twist) (t : Twist) :
    (dilate k h).count t = k * h.count t := by
  induction h with
  | nil => simp [dilate_nil]
  | cons s h ih =>
      rw [dilate_cons, List.count_append, ih, count_replicate_twist,
        show s :: h = [s] ++ h from rfl, List.count_append]
      ring

/-- **A global dilation preserves count balance.** -/
theorem dilate_balanced (k : ℕ) {h : List Twist} (hb : countBalanced h) :
    countBalanced (dilate k h) := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  exact ⟨by rw [count_dilate, count_dilate, h1], by rw [count_dilate, count_dilate, h2],
    by rw [count_dilate, count_dilate, h3], by rw [count_dilate, count_dilate, h4]⟩

theorem fold_replicate_odd (m : ℕ) (t : Twist) :
    twistMatrixFold (List.replicate (2 * m + 1) t) = t.toMatrix := by
  induction m with
  | zero => simp [fold_singleton]
  | succ m ih =>
      have : 2 * (m + 1) + 1 = 2 + (2 * m + 1) := by ring
      rw [this, List.replicate_add, fold_append, ih]
      simp [twistMatrixFold, twist_sq]

theorem fold_replicate_even (m : ℕ) (t : Twist) :
    twistMatrixFold (List.replicate (2 * m) t) = 1 := by
  induction m with
  | zero => simp [twistMatrixFold]
  | succ m ih =>
      have : 2 * (m + 1) = 2 + 2 * m := by ring
      rw [this, List.replicate_add, fold_append, ih]
      simp [twistMatrixFold, twist_sq]

/-- **An odd dilation leaves the fold unchanged.** -/
theorem fold_dilate_odd (m : ℕ) (h : List Twist) :
    twistMatrixFold (dilate (2 * m + 1) h) = twistMatrixFold h := by
  induction h with
  | nil => rfl
  | cons t h ih =>
      rw [dilate_cons, fold_append, fold_replicate_odd, ih,
        show t :: h = [t] ++ h from rfl, fold_append, fold_singleton]

/-- **An even dilation erases the phase: every history folds to `1`.** -/
theorem fold_dilate_even (m : ℕ) (h : List Twist) :
    twistMatrixFold (dilate (2 * m) h) = 1 := by
  induction h with
  | nil => rfl
  | cons t h ih =>
      rw [dilate_cons, fold_append, fold_replicate_even, ih, Matrix.one_mul]

/-- **A local dilation breaks balance.** `[^, v]` is balanced; scaling its first letter by `3`
    and its second by `1` gives `[^, ^, ^, v]`, which is not. -/
theorem local_dilation_breaks_balance :
    countBalanced [Twist.up, Twist.down] ∧
      ¬ countBalanced (dilateLocal [(Twist.up, 3), (Twist.down, 1)]) := by
  unfold countBalanced dilateLocal
  decide

end QLF.ConformalComparison
