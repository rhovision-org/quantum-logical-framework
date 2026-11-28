import Mathlib.Data.Nat.Factorization.Basic

/-!
# QLF_ConsciousUpdateRule — two update rules for the conscious race (#278)

Companion: [`Conscious_Update_Rule.md`](../Conscious_Update_Rule.md), run by
[`conscious_update_rule.py`](../conscious_update_rule.py). Eligible closures race; the one with
least remaining distance is promoted. Under the **independent** rule only the winner restarts;
under the **reset** rule every candidate restarts.

* **`independent_count`.** Under the independent rule a closure of period `T` is promoted at the
  multiples of `T`, so `H / T` times by time `H`.
* **`independent_mode`.** That count is antitone in `T`: the highest-frequency closure is the modal
  expression.
* **`reset_threshold`, `reset_percept_below`.** Under the reset rule the state after a promotion is
  the initial state (that is the rule), so `winner q` takes every promotion; for the frozen periods
  `(2q, 5q, 7q, 8)` it is the external closure exactly when `2q > 8`.

So both rules make the highest-frequency eligible closure the modal expression, and both switch it
at the same quieting threshold. Only the reset rule makes it the only expression.

No QLF axioms.
-/

namespace QLF.ConsciousUpdateRule

open Finset

/-- **Independent clocks:** promotions of a period-`T` closure by time `H`. -/
theorem independent_count (H T : ℕ) : #{t ∈ Ioc 0 H | T ∣ t} = H / T :=
  Nat.Ioc_filter_dvd_card_eq_div H T

/-- **The mode is the fastest clock.** -/
theorem independent_mode (H T₁ T₂ : ℕ) (h₁ : 0 < T₁) (h : T₁ ≤ T₂) :
    #{t ∈ Ioc 0 H | T₂ ∣ t} ≤ #{t ∈ Ioc 0 H | T₁ ∣ t} := by
  rw [independent_count, independent_count]
  exact Nat.div_le_div_left h h₁

/-- The four eligible candidates, in tie-break order. -/
inductive Cand | percept | thought | feeling | external
  deriving DecidableEq, Repr

/-- Periods after quieting the internal closures by `q`. -/
def period (q : ℕ) : Cand → ℕ
  | .percept => 2 * q
  | .thought => 5 * q
  | .feeling => 7 * q
  | .external => 8

/-- The winner of one race from full distances: least period, ties to the earlier candidate. -/
def winner (q : ℕ) : Cand :=
  let c := [Cand.percept, Cand.thought, Cand.feeling, Cand.external]
  c.foldl (fun best k => if period q k < period q best then k else best) Cand.percept

/-- **The reset threshold.** For `q = 1, …, 6` the external closure wins iff `2q > 8`. -/
theorem reset_threshold : ∀ q ∈ [1, 2, 3, 4, 5, 6], (winner q = Cand.external ↔ 8 < 2 * q) := by
  decide

/-- Below the threshold the percept wins. -/
theorem reset_percept_below : ∀ q ∈ [1, 2, 3, 4], winner q = Cand.percept := by
  decide

end QLF.ConsciousUpdateRule
