import QLF_TensorFromClosure

/-!
# A shared pair carries the Minkowski sign

Part of the [Quantum Logical Framework (QLF)](../README.md), stage 4c of the relativity dependency
chain ([`Relativity_Principle.md`](../Relativity_Principle.md) §6b, "Which contact?"). On one strand
every Hermitian pair folds to the same `−I`, gauge or spatial (`shared_pair_fold_axis_blind`), so a
contact weighted by that fold is Euclidean and picks a frame. A pair shared between two strands is
not a sequence on one strand: body `A` performs `t` and body `B` performs `t†`, and its action is
the composite `t ⊗ t†` (`splitPair_fold`). On the two-body state every shared strong pair fixes,
the singlet (`split_strong_iff_singlet`), that action is a sign, and the sign is the Minkowski one.

* **`minkowskiSign`**: `+1` on the gauge axis, `−1` on each spatial axis.
* **`splitPair_singlet_sign`**: every shared pair acts on the singlet as `−minkowskiSign`:
  `−1` for a gauge pair, `+1` for a spatial one.
* **`splitPair_singlet_relative_sign`**: so a gauge pair and a spatial pair act on the singlet with
  opposite signs, where on one strand their folds agree.

This is the weight that reading (A) gives a shared pair; with the walk's currents `J⁰ = 1`,
`Jⁱ = αᵢ` it makes the contact `Σ_a w_a Jᵃ ⊗ Jᵃ` the vector contact `−(1⊗1 − Σ αᵢ ⊗ αᵢ)`, checked by
the pre-registered [`shared_pair_sign_check.py`](../shared_pair_sign_check.py). That the weight of a
shared pair is its signed phase on the selected state, and that the walk's current along a twist's
axis is `αᵢ`, are the reading; the sign is proved. No axioms.
-/

namespace QLF.SharedPairSign

open QLF QLF.PhaseRule QLF.TensorFromClosure Matrix
open scoped Kronecker

/-- The Minkowski sign of a twist's axis: `+1` for the gauge axis, `−1` for a spatial one. -/
def minkowskiSign : Axis → ℂ
  | Axis.I => 1
  | _ => -1

/-- **A shared pair acts on the singlet as minus the Minkowski sign of its axis.** -/
theorem splitPair_singlet_sign (t : Twist) :
    cfold embA embB (splitPair t) *ᵥ JointClosure.s = (-minkowskiSign (axisOf t)) • JointClosure.s := by
  rw [splitPair_fold]
  cases t <;>
  · funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [Twist.toMatrix, Twist.conj, σx, σy, σz, JointClosure.s, mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply, minkowskiSign, axisOf]

/-- **Gauge and spatial pairs act on the singlet with opposite signs**, where on one strand their
    folds are the same `−I`. -/
theorem splitPair_singlet_relative_sign :
    cfold embA embB (splitPair Twist.plus) *ᵥ JointClosure.s =
      -(cfold embA embB (splitPair Twist.right) *ᵥ JointClosure.s) := by
  rw [splitPair_singlet_sign, splitPair_singlet_sign]
  simp [minkowskiSign, axisOf]

end QLF.SharedPairSign
