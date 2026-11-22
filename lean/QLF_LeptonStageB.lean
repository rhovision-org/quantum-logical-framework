import QLF_EdgeSign
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# QLF_LeptonStageB — the frozen lepton ladder's separating data (#140, Stage B)

[`Lepton_Mass_Ratio_Protocol.md`](../Lepton_Mass_Ratio_Protocol.md) freezes three rungs:
`e = ^<v>`, `μ = ^^<vv>`, `τ = ^^</>vv\`. [`Lepton_Stage_B.md`](../Lepton_Stage_B.md) asks what the
protocol's admissible observables distinguish among them; the census is
[`lepton_stage_b.py`](../lepton_stage_b.py). This module anchors the parts that are closure facts.

* **`rung_balanced`, `rung_first_return`.** Each rung is count-balanced and no proper nonempty
  prefix is.
* **`rung_fold`.** Each rung folds to `−1`: the fold sign does not separate them.
* **`rung_length`.** The lengths are `4 + 2k` for `k = 0, 1, 2`.

The orbit multiplicities `24 · 2^k`, the axis content `2, 2, 3` and `B = 0` are computed by the
census. Together they show that the separating data on the ladder are one progression in `k`.

No QLF axioms.
-/

namespace QLF.LeptonStageB

open QLF QLF.EdgeSign

def eRung : List Twist := [Twist.up, Twist.left, Twist.down, Twist.right]
def muRung : List Twist := [Twist.up, Twist.up, Twist.left, Twist.down, Twist.down, Twist.right]
def tauRung : List Twist :=
  [Twist.up, Twist.up, Twist.left, Twist.slash, Twist.right, Twist.down, Twist.down, Twist.backslash]

/-- The rung of generation `k`. -/
def rung : Fin 3 → List Twist
  | 0 => eRung
  | 1 => muRung
  | 2 => tauRung

theorem rung_length (k : Fin 3) : (rung k).length = 4 + 2 * k.val := by
  fin_cases k <;> rfl

theorem rung_balanced (k : Fin 3) : countBalanced (rung k) := by
  fin_cases k <;> (unfold countBalanced; decide)

/-- **First return:** no proper nonempty prefix of a rung is count-balanced. -/
theorem rung_first_return (k : Fin 3) :
    ∀ n, 0 < n → n < (rung k).length → ¬ countBalanced ((rung k).take n) := by
  fin_cases k <;> (intro n h0 h1; unfold countBalanced; simp only [rung, eRung, muRung, tauRung,
    List.length_cons, List.length_nil] at h1 ⊢; interval_cases n <;> decide)

theorem rung_phase (k : Fin 3) : connectionPhase (rung k) = -1 := by
  fin_cases k <;> decide

/-- **Every rung folds to `−1`.** -/
theorem rung_fold (k : Fin 3) : twistMatrixFold (rung k) = -1 := by
  rw [fold_eq_connectionPhase (rung_balanced k), rung_phase]
  simp

end QLF.LeptonStageB
