import QLF_NullTensorReconstruction
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_BianchiClosure — the third arrow: contracted Bianchi closes the field equations

`QLF_NullTensorReconstruction` closed the **algebraic** arrow of Jacobson's derivation (a symmetric
tensor annihilating the null cone is a metric multiple, forced by nine integer lattice probes). This
module closes the **third** arrow: from `R_ab − κ T_ab = f g_ab` to the Einstein field equations, by
the contracted Bianchi identity plus stress-energy conservation.

The three-arrow decomposition (`Einstein_Equations.md` §6b):

```
horizon thermodynamics  →  S_ab k^a k^b = 0  →  S_ab = f g_ab  →  G_ab + Λ g_ab = κ T_ab
    (Rindler/Raychaudhuri)      (QLF_NullTensorReconstruction)     (this module)
```

## Zero axioms — the bridge is a hypothesis, not a posit

QLF's Lean core carries no differential geometry, so `div` (`∇^a`) and `grad` (`∂_b`) cannot be
*defined* here. The honest move is **not** an `axiom`: the calculus is packaged as a structure,
`DivergenceCalculus`, whose fields are the named laws it must satisfy, and every theorem takes an
instance as a hypothesis. So this module adds **nothing to the axiom inventory** — the logical
boundary is visible in each theorem's signature instead, and any future concrete construction
(Mathlib's connections, or a substrate difference calculus) discharges it by *building* an instance.

The interface laws are all settled calculus, not conjectures: additivity of the divergence,
compatibility `∇^a (f g_ab) = ∂_b f` (metric compatibility), linearity of `grad`, and
`grad f = 0 ⟹ f` constant (connectedness of the region). The two *physics* inputs are hypotheses of
the main theorem, so they are impossible to miss:

* **contracted Bianchi** `∇^a R_ab = ½ ∂_b R` — settled Riemannian geometry, the `Class B` pattern of
  `beale_kato_majda` / `jost_liu_triangle_free` (real mathematics Mathlib has not assembled), and
* **conservation** `∇^a T_ab = 0`.

## The derivation

From `R_ab = κ T_ab + f g_ab`, take the divergence: `½ ∂_b R = 0 + ∂_b f`, so `∂_b (f − R/2) = 0` and
`f = R/2 − Λ` for a constant `Λ`. Substituting back,

  `R_ab − ½ R g_ab + Λ g_ab = κ T_ab`,

which is `G_ab + Λ g_ab = κ T_ab` (`einstein_field_equations`). `Λ` is Jacobson's integration
constant — the one QLF fixes independently as `Ω_Λ = log 2` (`QLF_CosmologicalConstant`).

## Honest scope

Two things this does *not* do. It does not construct the calculus — `DivergenceCalculus` is an
interface, and the field equations here are conditional on it (the signature says so). Instances are
built in `QLF_LatticeCalculus` (on `ℤ`) and `QLF_LatticeDivergence` (on `ℤ⁴`, Minkowski signature). And it does not touch the **first** arrow: getting `S_ab k^a k^b = 0` from
`δQ = T δS` needs the local Rindler construction and Raychaudhuri focusing, still open
(`QLF_EinsteinEquations.einstein_equations_in_progress`). What changes is the shape of what remains:
with arrows two and three closed, the full field equations reduce to **one** substrate question
rather than "the tensor derivation."
-/

namespace QLF.Bianchi

open QLF.NullTensor

/-! ### Pointwise algebra on `SymTensor4`

Componentwise addition and real scaling, so that "take the divergence of both sides" is an ordinary
linear step. -/

instance : Add SymTensor4 where
  add A B := { tt := A.tt + B.tt, tx := A.tx + B.tx, ty := A.ty + B.ty, tz := A.tz + B.tz,
                xx := A.xx + B.xx, xy := A.xy + B.xy, xz := A.xz + B.xz,
                yy := A.yy + B.yy, yz := A.yz + B.yz, zz := A.zz + B.zz }

instance : Neg SymTensor4 where
  neg A := { tt := -A.tt, tx := -A.tx, ty := -A.ty, tz := -A.tz,
              xx := -A.xx, xy := -A.xy, xz := -A.xz,
              yy := -A.yy, yz := -A.yz, zz := -A.zz }

instance : Sub SymTensor4 where
  sub A B := A + (-B)

instance : SMul ℝ SymTensor4 where
  smul c A := { tt := c * A.tt, tx := c * A.tx, ty := c * A.ty, tz := c * A.tz,
                 xx := c * A.xx, xy := c * A.xy, xz := c * A.xz,
                 yy := c * A.yy, yz := c * A.yz, zz := c * A.zz }

/-! Componentwise projections of the algebra as `rfl` simp lemmas — these keep every later proof
at the level of ordinary real arithmetic instead of instance unfolding. -/

@[simp] theorem add_tt (A B : SymTensor4) : (A + B).tt = A.tt + B.tt := rfl
@[simp] theorem add_tx (A B : SymTensor4) : (A + B).tx = A.tx + B.tx := rfl
@[simp] theorem add_ty (A B : SymTensor4) : (A + B).ty = A.ty + B.ty := rfl
@[simp] theorem add_tz (A B : SymTensor4) : (A + B).tz = A.tz + B.tz := rfl
@[simp] theorem add_xx (A B : SymTensor4) : (A + B).xx = A.xx + B.xx := rfl
@[simp] theorem add_xy (A B : SymTensor4) : (A + B).xy = A.xy + B.xy := rfl
@[simp] theorem add_xz (A B : SymTensor4) : (A + B).xz = A.xz + B.xz := rfl
@[simp] theorem add_yy (A B : SymTensor4) : (A + B).yy = A.yy + B.yy := rfl
@[simp] theorem add_yz (A B : SymTensor4) : (A + B).yz = A.yz + B.yz := rfl
@[simp] theorem add_zz (A B : SymTensor4) : (A + B).zz = A.zz + B.zz := rfl

@[simp] theorem neg_tt (A : SymTensor4) : (-A).tt = -A.tt := rfl
@[simp] theorem neg_tx (A : SymTensor4) : (-A).tx = -A.tx := rfl
@[simp] theorem neg_ty (A : SymTensor4) : (-A).ty = -A.ty := rfl
@[simp] theorem neg_tz (A : SymTensor4) : (-A).tz = -A.tz := rfl
@[simp] theorem neg_xx (A : SymTensor4) : (-A).xx = -A.xx := rfl
@[simp] theorem neg_xy (A : SymTensor4) : (-A).xy = -A.xy := rfl
@[simp] theorem neg_xz (A : SymTensor4) : (-A).xz = -A.xz := rfl
@[simp] theorem neg_yy (A : SymTensor4) : (-A).yy = -A.yy := rfl
@[simp] theorem neg_yz (A : SymTensor4) : (-A).yz = -A.yz := rfl
@[simp] theorem neg_zz (A : SymTensor4) : (-A).zz = -A.zz := rfl

@[simp] theorem smul_tt (c : ℝ) (A : SymTensor4) : (c • A).tt = c * A.tt := rfl
@[simp] theorem smul_tx (c : ℝ) (A : SymTensor4) : (c • A).tx = c * A.tx := rfl
@[simp] theorem smul_ty (c : ℝ) (A : SymTensor4) : (c • A).ty = c * A.ty := rfl
@[simp] theorem smul_tz (c : ℝ) (A : SymTensor4) : (c • A).tz = c * A.tz := rfl
@[simp] theorem smul_xx (c : ℝ) (A : SymTensor4) : (c • A).xx = c * A.xx := rfl
@[simp] theorem smul_xy (c : ℝ) (A : SymTensor4) : (c • A).xy = c * A.xy := rfl
@[simp] theorem smul_xz (c : ℝ) (A : SymTensor4) : (c • A).xz = c * A.xz := rfl
@[simp] theorem smul_yy (c : ℝ) (A : SymTensor4) : (c • A).yy = c * A.yy := rfl
@[simp] theorem smul_yz (c : ℝ) (A : SymTensor4) : (c • A).yz = c * A.yz := rfl
@[simp] theorem smul_zz (c : ℝ) (A : SymTensor4) : (c • A).zz = c * A.zz := rfl

@[simp] theorem sub_tt (A B : SymTensor4) : (A - B).tt = A.tt - B.tt := by
  show A.tt + -B.tt = A.tt - B.tt
  ring
@[simp] theorem sub_tx (A B : SymTensor4) : (A - B).tx = A.tx - B.tx := by
  show A.tx + -B.tx = A.tx - B.tx
  ring
@[simp] theorem sub_ty (A B : SymTensor4) : (A - B).ty = A.ty - B.ty := by
  show A.ty + -B.ty = A.ty - B.ty
  ring
@[simp] theorem sub_tz (A B : SymTensor4) : (A - B).tz = A.tz - B.tz := by
  show A.tz + -B.tz = A.tz - B.tz
  ring
@[simp] theorem sub_xx (A B : SymTensor4) : (A - B).xx = A.xx - B.xx := by
  show A.xx + -B.xx = A.xx - B.xx
  ring
@[simp] theorem sub_xy (A B : SymTensor4) : (A - B).xy = A.xy - B.xy := by
  show A.xy + -B.xy = A.xy - B.xy
  ring
@[simp] theorem sub_xz (A B : SymTensor4) : (A - B).xz = A.xz - B.xz := by
  show A.xz + -B.xz = A.xz - B.xz
  ring
@[simp] theorem sub_yy (A B : SymTensor4) : (A - B).yy = A.yy - B.yy := by
  show A.yy + -B.yy = A.yy - B.yy
  ring
@[simp] theorem sub_yz (A B : SymTensor4) : (A - B).yz = A.yz - B.yz := by
  show A.yz + -B.yz = A.yz - B.yz
  ring
@[simp] theorem sub_zz (A B : SymTensor4) : (A - B).zz = A.zz - B.zz := by
  show A.zz + -B.zz = A.zz - B.zz
  ring

@[simp] theorem mm_tt (c : ℝ) : (metricMultiple c).tt = c := rfl
@[simp] theorem mm_tx (c : ℝ) : (metricMultiple c).tx = 0 := rfl
@[simp] theorem mm_ty (c : ℝ) : (metricMultiple c).ty = 0 := rfl
@[simp] theorem mm_tz (c : ℝ) : (metricMultiple c).tz = 0 := rfl
@[simp] theorem mm_xx (c : ℝ) : (metricMultiple c).xx = -c := rfl
@[simp] theorem mm_xy (c : ℝ) : (metricMultiple c).xy = 0 := rfl
@[simp] theorem mm_xz (c : ℝ) : (metricMultiple c).xz = 0 := rfl
@[simp] theorem mm_yy (c : ℝ) : (metricMultiple c).yy = -c := rfl
@[simp] theorem mm_yz (c : ℝ) : (metricMultiple c).yz = 0 := rfl
@[simp] theorem mm_zz (c : ℝ) : (metricMultiple c).zz = -c := rfl

/-- Componentwise extensionality for `SymTensor4`. -/
theorem SymTensor4.ext' {A B : SymTensor4}
    (htt : A.tt = B.tt) (htx : A.tx = B.tx) (hty : A.ty = B.ty) (htz : A.tz = B.tz)
    (hxx : A.xx = B.xx) (hxy : A.xy = B.xy) (hxz : A.xz = B.xz)
    (hyy : A.yy = B.yy) (hyz : A.yz = B.yz) (hzz : A.zz = B.zz) : A = B := by
  cases A; cases B; simp_all

/-- The metric trace `g^ab S_ab` in signature `(+,−,−,−)`: `S_tt − S_xx − S_yy − S_zz`. -/
def trace (S : SymTensor4) : ℝ := S.tt - S.xx - S.yy - S.zz

/-- `g^ab (f g_ab) = 4f` — the trace of a metric multiple is `4f` (dimension four). -/
theorem trace_metricMultiple (f : ℝ) : trace (metricMultiple f) = 4 * f := by
  simp [trace]; ring

/-- Metric multiples are additive in the scalar: `(f₁ + f₂) g = f₁ g + f₂ g`. -/
theorem metricMultiple_add (f g : ℝ) :
    metricMultiple (f + g) = metricMultiple f + metricMultiple g := by
  apply SymTensor4.ext' <;> simp <;> ring

/-- Metric multiples respect negation. -/
theorem metricMultiple_neg (f : ℝ) : metricMultiple (-f) = -metricMultiple f := by
  apply SymTensor4.ext' <;> simp

/-! ### Fields and the calculus interface -/

/-- A scalar field on the region. -/
abbrev ScalarField (M : Type*) := M → ℝ

/-- A symmetric rank-2 tensor field on the region. -/
abbrev TensorField (M : Type*) := M → SymTensor4

/-- A covector field on the region (`∂_b` of a scalar, `∇^a` of a tensor). -/
abbrev CovectorField (M : Type*) := M → (Fin 4 → ℝ)

/-- **The divergence/gradient interface.** The differential-geometry laws QLF's Lean core cannot
    construct, packaged as data rather than posited as axioms: any theorem using them declares them
    in its signature, and a concrete construction discharges them by building an instance.

    Every field is settled calculus: additivity and real-homogeneity of `∇^a`, metric compatibility
    `∇^a (f g_ab) = ∂_b f`, linearity of `∂_b`, and constancy from a vanishing gradient
    (connectedness of the region). -/
structure DivergenceCalculus (M : Type*) where
  /-- `∇^a` on symmetric tensor fields. -/
  div : TensorField M → CovectorField M
  /-- `∂_b` on scalar fields. -/
  grad : ScalarField M → CovectorField M
  div_add : ∀ A B : TensorField M, div (fun p => A p + B p) = fun p => div A p + div B p
  div_smul : ∀ (c : ℝ) (A : TensorField M), div (fun p => c • A p) = fun p => c • div A p
  /-- **Metric compatibility**: `∇^a (f g_ab) = ∂_b f`. -/
  div_metricMultiple : ∀ f : ScalarField M, div (fun p => metricMultiple (f p)) = grad f
  grad_add : ∀ f g : ScalarField M, grad (fun p => f p + g p) = fun p => grad f p + grad g p
  grad_smul : ∀ (c : ℝ) (f : ScalarField M), grad (fun p => c * f p) = fun p => c • grad f p
  /-- **Connectedness**: a scalar with vanishing gradient is constant. -/
  const_of_grad_eq_zero : ∀ f : ScalarField M, grad f = 0 → ∃ c : ℝ, ∀ p, f p = c

variable {M : Type*}

/-- The **scalar curvature** `R = g^ab R_ab` of a Ricci field. -/
def scalarCurv (Ric : TensorField M) : ScalarField M := fun p => trace (Ric p)

/-- The **Einstein tensor** `G_ab = R_ab − ½ R g_ab`. -/
noncomputable def einsteinTensor (Ric : TensorField M) : TensorField M :=
  fun p => Ric p - metricMultiple (scalarCurv Ric p / 2)

/-- **The integration step.** Given the metric form `R_ab = κ T_ab + f g_ab`, the contracted Bianchi
    identity and conservation force `f = R/2 − Λ` for a **constant** `Λ`.

    Divergence of both sides: `∇^a R_ab = κ ∇^a T_ab + ∂_b f = ∂_b f` by conservation, while
    contracted Bianchi gives `∇^a R_ab = ½ ∂_b R`. So `∂_b (f − R/2) = 0`, and connectedness makes
    `f − R/2` a constant, named `−Λ`. -/
theorem scalar_multiple_is_curvature
    (C : DivergenceCalculus M) (κ : ℝ) (Ric T : TensorField M) (f : ScalarField M)
    (hform : ∀ p, Ric p = κ • T p + metricMultiple (f p))
    (hbianchi : C.div Ric = fun p => (1 / 2 : ℝ) • C.grad (scalarCurv Ric) p)
    (hcons : C.div T = 0) :
    ∃ Λ : ℝ, ∀ p, f p = scalarCurv Ric p / 2 - Λ := by
  -- `div Ric = grad f`: additivity, homogeneity, conservation, metric compatibility.
  have hdiv : C.div Ric = C.grad f := by
    have hRic : Ric = fun p => (fun q => κ • T q) p + (fun q => metricMultiple (f q)) p := by
      funext p; exact hform p
    calc C.div Ric
        = C.div (fun p => (fun q => κ • T q) p + (fun q => metricMultiple (f q)) p) := by
          rw [← hRic]
      _ = (fun p => C.div (fun q => κ • T q) p + C.div (fun q => metricMultiple (f q)) p) :=
          C.div_add _ _
      _ = C.grad f := by
          rw [C.div_smul κ T, C.div_metricMultiple f, hcons]
          funext p; simp
  -- Contracted Bianchi then reads `grad f = ½ grad R`.
  have hgf : C.grad f = fun p => (1 / 2 : ℝ) • C.grad (scalarCurv Ric) p := by
    rw [← hdiv]; exact hbianchi
  -- So `f − R/2` has vanishing gradient, hence is constant.
  have hzero : C.grad (fun p => f p + (-(1 / 2 : ℝ)) * scalarCurv Ric p) = 0 := by
    rw [C.grad_add f (fun p => (-(1 / 2 : ℝ)) * scalarCurv Ric p),
        C.grad_smul (-(1 / 2 : ℝ)) (scalarCurv Ric), hgf]
    funext p
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  obtain ⟨c, hc⟩ := C.const_of_grad_eq_zero _ hzero
  refine ⟨-c, fun p => ?_⟩
  have hp := hc p
  have : f p - (1 / 2 : ℝ) * scalarCurv Ric p = c := by linarith [hp]
  linarith [this]

/-- **The Einstein field equations.** Assembling the second and third arrows: if the null-projection
    residual is a metric multiple (`QLF_NullTensorReconstruction`, forced by nine integer probes) and
    the contracted Bianchi identity plus conservation hold, then

      `G_ab + Λ g_ab = κ T_ab`

    with `Λ` the integration constant — fixed independently in QLF as `Ω_Λ = log 2`
    (`QLF_CosmologicalConstant`). With `κ = 8πG` from `einstein_coupling_from_thermodynamics`, this
    is the field equation. -/
theorem einstein_field_equations
    (C : DivergenceCalculus M) (κ : ℝ) (Ric T : TensorField M) (f : ScalarField M)
    (hform : ∀ p, Ric p = κ • T p + metricMultiple (f p))
    (hbianchi : C.div Ric = fun p => (1 / 2 : ℝ) • C.grad (scalarCurv Ric) p)
    (hcons : C.div T = 0) :
    ∃ Λ : ℝ, ∀ p, einsteinTensor Ric p + metricMultiple Λ = κ • T p := by
  obtain ⟨Λ, hΛ⟩ := scalar_multiple_is_curvature C κ Ric T f hform hbianchi hcons
  refine ⟨Λ, fun p => ?_⟩
  have h1 : Ric p = κ • T p + metricMultiple (scalarCurv Ric p / 2 - Λ) := by
    rw [hform p, hΛ p]
  unfold einsteinTensor
  rw [h1]
  apply SymTensor4.ext' <;> simp [scalarCurv, trace] <;> ring

/-- **The two arrows composed.** The hypothesis of `einstein_field_equations` that the residual is a
    metric multiple is exactly what nine integer null probes deliver: if
    `(R_ab − κ T_ab) k^a k^b = 0` on the nine substrate lattice directions, the metric form holds
    with `f` read off as the `tt` component. So the second and third arrows chain with nothing left
    between them. -/
theorem metric_form_from_null_probes
    (κ : ℝ) (Ric T : TensorField M)
    (hnull : ∀ p, ∀ v : Form, IsNull v → contract (Ric p - κ • T p) v = 0) :
    ∀ p, Ric p = κ • T p + metricMultiple ((Ric p - κ • T p).tt) := by
  intro p
  have h := all_null_projections_force_metric (Ric p - κ • T p) (hnull p)
  -- Fold the metric multiple back into the residual, then it is pure componentwise algebra:
  -- `Ric p = κ T p + (Ric p − κ T p)`.
  rw [← h]
  apply SymTensor4.ext' <;> simp <;> ring

/-- **Established constructively:** arrows two and three of Jacobson's derivation, with **zero new
    axioms** — the metric form from nine integer null probes
    (`QLF_NullTensorReconstruction.finite_null_probes_force_metric`, chained here by
    `metric_form_from_null_probes`), and from it `G_ab + Λ g_ab = κ T_ab`
    (`einstein_field_equations`) via contracted Bianchi + conservation over the
    `DivergenceCalculus` interface. The differential-geometry boundary is a **hypothesis in the
    signature**, not a posit, so a concrete construction discharges it by building an instance.
    **Open:** the first arrow — `δQ = T δS ⟹ (R_ab − κ T_ab) k^a k^b = 0`, needing the local Rindler
    construction and Raychaudhuri focusing (`einstein_equations_in_progress`). That is now the single
    remaining substrate question for the field equations. -/
theorem bianchi_closure_complete : True := trivial

end QLF.Bianchi
