import QLF_PlaquetteArea

/-!
# QLF_ClassFactoring — what a geometry read from one closed history can carry

Issue #301, milestone 2. Milestone 1 ([`Continuum_Limit.md`](../Continuum_Limit.md)) was rejected
because its edge labels were finer than the closure class (K3), while a coarser labeling was
constant on closure (K7). The proposal for milestone 2 was a 3D map that **factors through the
closure class**. This module measures how much such a map can carry when it is read from a single
closed history.

The phased closure test of a single history `h` asks, for each continuation `c`, whether `h ++ c`
closes and with which phase. Closing depends only on the net action, and the phase on the fold
(`twistMatrixFold_append`), so the class is the pair `(net, fold)`
(`QLF_PerspectiveHolography.joint_record_minimal` is the two-body form). On closed histories the
net is zero, so a map that factors through the class is a function of the fold alone.

* `fold_eq_classBit`: the fold of a closed history is `sgn(classBit) • I`, where
  `classBit = #neg + A_XY + A_XZ + A_YZ (mod 2)` is the negative-twist parity plus the parity of the
  three projected areas (`QLF_PlaquetteArea.fold_eq_projected_phase`).
* `class_function_factors`: **any** function of closed histories that respects the fold is a
  function of `classBit`. So a class-factoring geometry read from one closed history carries at most
  one bit.
* `classBit_separates`: the bit is real. `[]` and the plaquette `^>v<` differ in it.
* `circulation_invisible`: the circulation is not. `[]` and the doubled plaquette `^>v<^>v<` have
  the same bit, but projected `XY` areas `0` and `−2`. Milestone 1 found that Regge curvature on its
  complex is the circulation, so the curvature of a single closed loop is invisible to the class,
  apart from one parity bit.

**Consequence for #301.** K3 (the geometry is a class function) and K7 (it varies on closure) can
hold together for single closed histories only with a two-valued geometry. A geometry with more
content must be read from something other than one history: for example from the census, the
count of all the ways between two places, which is a class function because it counts every
representative. That is the route milestone 2 pre-registers
([`Continuum_Limit.md`](../Continuum_Limit.md) §4). No axioms.

Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.ClassFactoring

open QLF QLF.PhaseRule QLF.EdgeSign QLF.PlaquetteArea

/-- The sum of the three projected areas. -/
def areaSum (ts : List Twist) : ℤ :=
  projArea Axis.X Axis.Y ts + projArea Axis.X Axis.Z ts + projArea Axis.Y Axis.Z ts

/-- The one bit a closed history shows its closure class: negative-twist parity plus area parity. -/
def classBit (ts : List Twist) : ZMod 2 := (negCount ts : ZMod 2) + (areaSum ts : ZMod 2)

/-- **The fold of a closed history is its class bit.** -/
theorem fold_eq_classBit {ts : List Twist} (h : countBalanced ts) :
    twistMatrixFold ts = ((sgn (classBit ts) : ℤ) : ℂ) • (1 : M) := by
  rw [fold_eq_projected_phase h, classBit, sgn_add, sgn_natCast]
  rfl

/-- **A class-factoring map of closed histories carries at most one bit.** Any `Φ` that gives
    closed histories with the same fold the same value is a function of `classBit`. -/
theorem class_function_factors {X : Type*} (Φ : List Twist → X)
    (hΦ : ∀ a b, countBalanced a → countBalanced b →
      twistMatrixFold a = twistMatrixFold b → Φ a = Φ b)
    {a b : List Twist} (ha : countBalanced a) (hb : countBalanced b)
    (hbit : classBit a = classBit b) : Φ a = Φ b :=
  hΦ a b ha hb (by rw [fold_eq_classBit ha, fold_eq_classBit hb, hbit])

/-- The plaquette `^>v<`. -/
def plaq : List Twist := [Twist.up, Twist.right, Twist.down, Twist.left]

/-- The doubled plaquette `^>v<^>v<`. -/
def plaq2 : List Twist := plaq ++ plaq

/-- **The bit is real:** the empty history and the plaquette differ in it. -/
theorem classBit_separates :
    countBalanced ([] : List Twist) ∧ countBalanced plaq ∧
      classBit ([] : List Twist) ≠ classBit plaq := by
  refine ⟨?_, ?_, ?_⟩
  · unfold countBalanced; decide
  · unfold countBalanced; decide
  · decide

/-- **The circulation is invisible:** the empty history and the doubled plaquette have the same
    class bit, but different enclosed `XY` area. -/
theorem circulation_invisible :
    countBalanced plaq2 ∧ classBit ([] : List Twist) = classBit plaq2 ∧
      projArea Axis.X Axis.Y ([] : List Twist) = 0 ∧ projArea Axis.X Axis.Y plaq2 = -2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold countBalanced; decide
  · decide
  · decide
  · decide

end QLF.ClassFactoring
