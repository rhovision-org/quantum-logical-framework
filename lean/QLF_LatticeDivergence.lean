import QLF_BianchiClosure
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_LatticeDivergence — the divergence calculus, built on the closure walk's lattice

[`QLF_BianchiClosure`](QLF_BianchiClosure.lean) derived `G_ab + Λ g_ab = κ T_ab` from the metric form
over an *interface*, `DivergenceCalculus`. [`QLF_LatticeCalculus`](QLF_LatticeCalculus.lean) showed
the interface is inhabited, with a forward-difference instance on `ℤ` in which only one direction is
live. This module builds the four-dimensional instance with the Minkowski signature, on the lattice
the substrate already walks on: `ℤ⁴`, where the eight twists are the steps `±e_a`
([`Closure_Walk.md`](../Closure_Walk.md)).

* `∂_b f` is the forward difference `f(p + e_b) − f(p)`.
* `∇^a A_ab` is `Σ_a η^aa (A_ab(p + e_a) − A_ab(p))`, signature `(+,−,−,−)`.

Every law of the interface holds as a theorem (`latticeCalculus`). Metric compatibility holds because
`η^aa η_ab = δ_ab`, so the divergence of `f g_ab` picks out the single difference `Δ_b f`.
Connectedness holds because the lattice is connected: a field whose four differences all vanish is
invariant under every step `±e_a`, and every site is reached from the origin by steps
(`const_of_differences_zero`).

## R6a first: an instance alone is not evidence

The interface is satisfied trivially on a one-point space, with `div = 0` and `grad = 0`
(`unit_calculus`). So "an instance exists" says nothing about spacetime. The content here is the
particular instance, and what it fixes: on the whole substrate lattice, `Λ` is **one constant**
(`lattice_einstein_field_equations`), because a lattice step reaches every site.

## Scope

What stays a hypothesis: the discrete contracted Bianchi identity and discrete conservation for the
fields one feeds in. Forward differences obey no exact Leibniz rule, so a discrete Ricci tensor built
from a lattice metric need not satisfy `∇^a R_ab = ½ ∂_b R` exactly. Whether the substrate's own
curvature does is the curvature question (`Einstein_Equations.md` §6a), not settled here. The first
arrow (local Rindler + Raychaudhuri) is also untouched.
-/

namespace QLF.LatticeDivergence

open QLF.NullTensor QLF.Bianchi

/-- The substrate lattice: four integer coordinates, `t, x, y, z`. -/
abbrev Site := Fin 4 → ℤ

/-- The unit step along axis `a`. -/
def step (a : Fin 4) : Site := Pi.single a 1

/-- The metric diagonal in signature `(+,−,−,−)`; `η^aa = η_aa` on the diagonal. -/
def etaL : Fin 4 → ℝ := ![1, -1, -1, -1]

/-- Components `A_ab` of a symmetric tensor. -/
def cmp (S : SymTensor4) : Fin 4 → Fin 4 → ℝ :=
  ![![S.tt, S.tx, S.ty, S.tz],
    ![S.tx, S.xx, S.xy, S.xz],
    ![S.ty, S.xy, S.yy, S.yz],
    ![S.tz, S.xz, S.yz, S.zz]]

theorem cmp_add (A B : SymTensor4) (a b : Fin 4) :
    cmp (A + B) a b = cmp A a b + cmp B a b := by
  fin_cases a <;> fin_cases b <;> simp [cmp]

theorem cmp_smul (c : ℝ) (A : SymTensor4) (a b : Fin 4) :
    cmp (c • A) a b = c * cmp A a b := by
  fin_cases a <;> fin_cases b <;> simp [cmp]

/-- The lattice gradient `∂_b f = f(p + e_b) − f(p)`. -/
def lgrad (f : ScalarField Site) : CovectorField Site :=
  fun p b => f (p + step b) - f p

/-- The lattice divergence `∇^a A_ab = Σ_a η^aa (A_ab(p + e_a) − A_ab(p))`. -/
def ldiv (A : TensorField Site) : CovectorField Site :=
  fun p b => ∑ a, etaL a * (cmp (A (p + step a)) a b - cmp (A p) a b)

/-! ### Connectedness: vanishing differences force a constant -/

/-- A field invariant under one step `e_a` is invariant under every integer multiple of it. -/
theorem shift_invariant (f : ScalarField Site) (a : Fin 4)
    (h : ∀ p, f (p + step a) = f p) (n : ℤ) (p : Site) : f (p + n • step a) = f p := by
  refine Int.induction_on n (by simp) (fun k ih => ?_) (fun k ih => ?_)
  · have hs : p + ((k : ℤ) + 1) • step a = (p + (k : ℤ) • step a) + step a := by
      rw [add_smul, one_smul, add_assoc]
    rw [hs, h, ih]
  · have hstep := h (p + (-(k : ℤ) - 1) • step a)
    have hs : p + (-(k : ℤ) - 1) • step a + step a = p + (-(k : ℤ)) • step a := by
      rw [add_assoc, sub_smul, one_smul, sub_add_cancel]
    rw [hs, ih] at hstep
    exact hstep.symm

/-- Every site is a sum of axis steps from the origin. -/
theorem site_decomp (p : Site) :
    p = (((0 : Site) + p 0 • step 0) + p 1 • step 1) + p 2 • step 2 + p 3 • step 3 := by
  funext i
  fin_cases i <;> simp [step, Pi.single_apply]

/-- **Connectedness of the lattice.** A scalar whose four forward differences vanish everywhere is
    constant. -/
theorem const_of_differences_zero (f : ScalarField Site) (h : lgrad f = 0) :
    ∃ c : ℝ, ∀ p, f p = c := by
  have hstep : ∀ a p, f (p + step a) = f p := by
    intro a p
    have := congrFun (congrFun h p) a
    simp only [lgrad, Pi.zero_apply] at this
    linarith
  refine ⟨f 0, fun p => ?_⟩
  rw [site_decomp p, shift_invariant f 3 (hstep 3), shift_invariant f 2 (hstep 2),
    shift_invariant f 1 (hstep 1), shift_invariant f 0 (hstep 0)]

/-! ### The instance -/

theorem ldiv_add (A B : TensorField Site) :
    ldiv (fun p => A p + B p) = fun p => ldiv A p + ldiv B p := by
  funext p b
  simp only [ldiv, cmp_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

theorem ldiv_smul (c : ℝ) (A : TensorField Site) :
    ldiv (fun p => c • A p) = fun p => c • ldiv A p := by
  funext p b
  simp only [ldiv, cmp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- **Metric compatibility on the lattice**: `∇^a (f g_ab) = ∂_b f`, because `η^aa η_ab = δ_ab`. -/
theorem ldiv_metricMultiple (f : ScalarField Site) :
    ldiv (fun p => metricMultiple (f p)) = lgrad f := by
  funext p b
  fin_cases b <;>
    simp [ldiv, lgrad, cmp, etaL, metricMultiple, Fin.sum_univ_four] <;> ring

theorem lgrad_add (f g : ScalarField Site) :
    lgrad (fun p => f p + g p) = fun p => lgrad f p + lgrad g p := by
  funext p b
  simp only [lgrad, Pi.add_apply]
  ring

theorem lgrad_smul (c : ℝ) (f : ScalarField Site) :
    lgrad (fun p => c * f p) = fun p => c • lgrad f p := by
  funext p b
  simp only [lgrad, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The divergence calculus on the substrate lattice `ℤ⁴`.** Every interface law is a theorem. -/
def latticeCalculus : DivergenceCalculus Site where
  div := ldiv
  grad := lgrad
  div_add := ldiv_add
  div_smul := ldiv_smul
  div_metricMultiple := ldiv_metricMultiple
  grad_add := lgrad_add
  grad_smul := lgrad_smul
  const_of_grad_eq_zero := const_of_differences_zero

/-- **R6a measurement.** The interface is also satisfied on a single point with `div = 0` and
    `grad = 0`, so the existence of *an* instance carries no physical content. -/
def unit_calculus : DivergenceCalculus Unit where
  div := fun _ _ _ => 0
  grad := fun _ _ _ => 0
  div_add := by intro A B; funext p b; simp
  div_smul := by intro c A; funext p b; simp
  div_metricMultiple := by intro f; rfl
  grad_add := by intro f g; funext p b; simp
  grad_smul := by intro c f; funext p b; simp
  const_of_grad_eq_zero := by intro f _; exact ⟨f (), fun p => by cases p; rfl⟩

/-- **The field equations on the substrate lattice.** If `R_ab = κ T_ab + f g_ab` at every site,
    and the lattice forms of contracted Bianchi and conservation hold, then
    `G_ab + Λ g_ab = κ T_ab` with **one** `Λ` for the whole lattice. The divergence calculus is no
    longer a hypothesis; Bianchi and conservation still are. -/
theorem lattice_einstein_field_equations (κ : ℝ) (Ric T : TensorField Site) (f : ScalarField Site)
    (hform : ∀ p, Ric p = κ • T p + metricMultiple (f p))
    (hbianchi : ldiv Ric = fun p => (1 / 2 : ℝ) • lgrad (scalarCurv Ric) p)
    (hcons : ldiv T = 0) :
    ∃ Λ : ℝ, ∀ p, einsteinTensor Ric p + metricMultiple Λ = κ • T p :=
  einstein_field_equations latticeCalculus κ Ric T f hform hbianchi hcons

end QLF.LatticeDivergence
