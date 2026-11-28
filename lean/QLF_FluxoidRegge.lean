import QLF_LinkClosure
import Mathlib

/-!
# QLF_FluxoidRegge — what a fluxoid labeling of a lattice can and cannot carry

Issue #301 milestone 1 proposes to label the edges of a lattice with fluxoid integers taken from a
history, read the labels as Regge edge lengths, and identify ZFA with a face identity `∂f ≡ 0`.
The kill conditions are pre-registered in [`Continuum_Limit.md`](../Continuum_Limit.md) §1, and the
numerical run is [`fluxoid_regge.py`](../fluxoid_regge.py). This module proves the parts that are
exact and do not need angles.

The labeling is the link current `walkCurrent` of [`QLF_LinkClosure`](QLF_LinkClosure.lean).

## What is proved

* **`div_smooth`.** Smoothing a link field with any kernel `K` (the binomial Bernstein weights
  included) commutes with the lattice divergence: `div (K ⋆ J) = K ⋆ div J`. The kernel is
  translation-invariant, so it commutes with differences.
* **`smooth_preserves_closure`.** So smoothing the current of a returning history keeps
  `div = 0` everywhere. The closure identity survives smoothing (kill condition K5 passes). It holds
  for every kernel, so it is structural, not evidence.
* **`plaquette_closed`, `plaquette_circulates`.** On `(ℤ₃)²` the history `>^<v` returns to its
  start and is count-balanced, yet its current circulates around its plaquette with total `4`. So
  ZFA is not the face identity `∂f ≡ 0` (K1 fails). ZFA is the vertex identity `div = 0`,
  `div_walkCurrent`.
* **`current_not_class_function`.** The empty history and `>^<v` have the same net count on every
  axis, so they lie in one closure class, but their currents differ. A geometry read off the current
  is not a function of the class (the Lean core of K3).
* **`axisLabel_closed`.** The other labeling, by net count per axis, is zero on every count-balanced
  history. It is a class function only because it is constant on closure (K7).

No axioms.
-/

namespace QLF.FluxoidRegge

open QLF.LinkClosure QLF.LinkAction

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {n : ℕ}

/-- Translation-invariant smoothing of a link field by a kernel `K`. -/
def smooth (K : S → ℝ) (J : Fin n → S → ℝ) : Fin n → S → ℝ :=
  fun k x => ∑ s, K s * J k (x - s)

omit [DecidableEq S] in
/-- **Smoothing commutes with the divergence.** -/
theorem div_smooth (e : Fin n → S) (K : S → ℝ) (J : Fin n → S → ℝ) (x : S) :
    Maxwell.div e (smooth K J) x = ∑ s, K s * Maxwell.div e J (x - s) := by
  unfold Maxwell.div smooth
  simp only [Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [sub_right_comm x (e i) s]

omit [DecidableEq S] in
/-- Smoothing maps divergence-free link fields to divergence-free link fields. -/
theorem smooth_div_free (e : Fin n → S) (K : S → ℝ) (J : Fin n → S → ℝ)
    (hJ : ∀ x, Maxwell.div e J x = 0) (x : S) :
    Maxwell.div e (smooth K J) x = 0 := by
  rw [div_smooth]
  exact Finset.sum_eq_zero (fun s _ => by rw [hJ, mul_zero])

/-- **Smoothing preserves the closure identity.** The smoothed current of a returning history is
    divergence-free everywhere. -/
theorem smooth_preserves_closure (e : Fin n → S) (K : S → ℝ) (p : S) (w : List (Step n))
    (hw : endpoint e p w = p) (x : S) :
    Maxwell.div e (smooth K (walkCurrent e p w)) x = 0 :=
  smooth_div_free e K _ (fun y => by rw [div_walkCurrent, hw, sub_self]) x

/-- The axis labeling: every edge on axis `k` carries the history's net count on `k`. -/
def axisLabel (w : List (Step n)) (k : Fin n) (_x : S) : ℤ := netCount w k

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
/-- **The axis labeling is zero on closure.** -/
theorem axisLabel_closed (w : List (Step n)) (hw : ∀ k, netCount w k = 0) (k : Fin n) (x : S) :
    axisLabel w k x = 0 := hw k

/-! ### The plaquette on `(ℤ₃)²` -/

/-- The two lattice directions of `(ℤ₃)²`. -/
def e2 : Fin 2 → ZMod 3 × ZMod 3 := ![(1, 0), (0, 1)]

/-- The plaquette history `>^<v`: right, up, left, down. -/
def plaquette : List (Step 2) := [(0, true), (1, true), (0, false), (1, false)]

/-- The plaquette returns to its start. -/
theorem plaquette_closed : endpoint e2 0 plaquette = 0 := by decide

/-- The plaquette is count-balanced on both axes. -/
theorem plaquette_balanced (k : Fin 2) : netCount plaquette k = 0 := by
  fin_cases k <;> decide

/-- The current of the plaquette on its four edges. -/
theorem plaquette_current :
    walkCurrent e2 0 plaquette 0 0 = 1 ∧ walkCurrent e2 0 plaquette 1 (1, 0) = 1 ∧
      walkCurrent e2 0 plaquette 0 (0, 1) = -1 ∧ walkCurrent e2 0 plaquette 1 0 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [walkCurrent, stepCurrent, plaquette, e2] <;> decide

/-- The oriented circulation of a link field around the plaquette at `x`. -/
def circulation (J : Fin 2 → ZMod 3 × ZMod 3 → ℝ) (x : ZMod 3 × ZMod 3) : ℝ :=
  J 0 x + J 1 (x + e2 0) - J 0 (x + e2 1) - J 1 x

/-- **ZFA is not the face identity.** The plaquette closes, yet its current circulates. -/
theorem plaquette_circulates : circulation (walkCurrent e2 0 plaquette) 0 = 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := plaquette_current
  have a : (0 : ZMod 3 × ZMod 3) + e2 0 = (1, 0) := by decide
  have b : (0 : ZMod 3 × ZMod 3) + e2 1 = (0, 1) := by decide
  simp only [circulation, a, b]
  rw [h1, h2, h3, h4]
  norm_num

/-- **The current is not a function of the closure class.** Two histories with the same net count
    on every axis, both returning, carry different currents. -/
theorem current_not_class_function :
    (∀ k, netCount plaquette k = netCount ([] : List (Step 2)) k) ∧
      endpoint e2 0 plaquette = endpoint e2 0 [] ∧
      walkCurrent e2 0 plaquette ≠ walkCurrent e2 0 [] := by
  refine ⟨fun k => by rw [plaquette_balanced]; rfl, plaquette_closed, fun h => ?_⟩
  have h1 := plaquette_current.1
  rw [h] at h1
  simp [walkCurrent] at h1

end QLF.FluxoidRegge
