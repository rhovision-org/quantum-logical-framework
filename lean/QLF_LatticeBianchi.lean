import QLF_LatticeDivergence
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_LatticeBianchi — the contracted Bianchi identity and conservation, as lattice theorems

[`QLF_LatticeDivergence`](QLF_LatticeDivergence.lean) built the divergence calculus on the substrate
lattice `ℤ⁴` and ran the third arrow of Jacobson's derivation over it, but two inputs stayed
hypotheses of `lattice_einstein_field_equations`: the contracted Bianchi identity (`hbianchi`) and
conservation of the source (`hcons`). This module proves the first and settles what the second is.

## What is proved

* **`lattice_contracted_bianchi`.** For the *linearized* Ricci tensor of any metric perturbation
  `h_ab` on `ℤ⁴`,

    `R_ab = ½ (Δ^c Δ_a h_cb + Δ^c Δ_b h_ca − □ h_ab − Δ_a Δ_b h)`,

  built from the same forward differences `Δ_a f(p) = f(p + e_a) − f(p)` that the divergence uses,
  the identity `∇^a R_ab = ½ ∂_b R` holds **exactly**, for every `h`. No continuum limit and no
  error term. The reason is the one behind `d² = 0` in discrete exterior calculus: lattice shifts
  commute (`p + e_a + e_b = p + e_b + e_a`), so the operators `Δ_a` commute and the continuum
  cancellation goes through term for term.
* **`einstein_divergence_free`.** Equivalently, `∇^a G_ab = 0` for the linearized Einstein tensor.
* **`conservation_of_field_equations`.** If the linearized field equations
  `G_ab + Λ g_ab = κ T_ab` hold with `κ ≠ 0`, the source is conserved, `∇^a T_ab = 0`. Conservation
  is a consequence of the field equations, as in general relativity.
* **`conservation_iff_constant_lambda`.** On Jacobson's route the field equations are not yet
  available; the input is the metric form `R_ab = κ T_ab + f g_ab`. There, conservation is
  **equivalent** to `f = R/2 − Λ` with one constant `Λ`. So the hypothesis `hcons` can no longer be
  dropped or weakened: it is exactly the statement that the cosmological term does not vary.
* **`linearized_lattice_einstein_field_equations`.** `lattice_einstein_field_equations` with
  `hbianchi` discharged: from the metric form and conservation, `G_ab + Λ g_ab = κ T_ab`.
* **`ricC_pureGauge`.** The linearized Ricci tensor is invariant under the lattice gauge change
  `h_ab ↦ h_ab + Δ_a ξ_b + Δ_b ξ_a` (a discrete infinitesimal diffeomorphism). This is the other
  face of the same identity: by Noether's second theorem, gauge invariance of the curvature and
  `∇^a G_ab = 0` come together.

## R6a: what this does and does not carry

Every identity here holds for **every** perturbation `h`, random noise included. By the method's
rule 4 ([`ScientificApproach.md`](../ScientificApproach.md)) that makes it mathematics of the
**forward map**, not evidence about the substrate: it strengthens the gravity side of the derivation
and adds no bridge. It is also known mathematics. The linearized Bianchi identity and its gauge
invariance are textbook (Fierz–Pauli; e.g. Carroll, *Spacetime and Geometry*, §7.1), and exact
lattice versions rest on the commuting difference operators of lattice field theory and discrete
exterior calculus. The gauge-field analogue, `dF = 0` on plaquettes, is already proved in
[`QLF_LatticeGauge`](QLF_LatticeGauge.lean) (`bianchi`).

## Scope

* **Linearized only.** A full nonlinear discrete Ricci tensor from a lattice metric (Regge calculus,
  for instance) satisfies the Bianchi identity only approximately, and nothing here touches it. The
  nonlinear identity stays a hypothesis wherever it is used.
* **The first arrow is untouched.** Getting the metric form from `δQ = T δS` needs the local Rindler
  construction and Raychaudhuri focusing ([`Einstein_Equations.md`](../Einstein_Equations.md) §6b). It
  stays open. The write-up is §6f there.
* **Conservation of a substrate source** (a stress tensor counted from closures) is not derived. What
  is proved is that conservation follows from the field equations, and that on Jacobson's route it
  is equivalent to a constant `Λ`.

No axioms.
-/

namespace QLF.LatticeDivergence

open QLF.NullTensor QLF.Bianchi

/-! ## Forward differences and the component fields -/

/-- The forward difference of a scalar field along axis `a`: `Δ_a g(p) = g(p + e_a) − g(p)`. -/
def D (a : Fin 4) (g : Site → ℝ) : Site → ℝ := fun p => g (p + step a) - g p

/-- **Lattice shifts commute**, so forward differences commute: `Δ_a Δ_b = Δ_b Δ_a`. -/
theorem D_comm (a b : Fin 4) (g : Site → ℝ) : D a (D b g) = D b (D a g) := by
  funext p
  simp only [D, add_right_comm p (step a) (step b)]
  ring

/-- The component field `h_cd` of a symmetric tensor field. -/
def hc (h : TensorField Site) (c d : Fin 4) : Site → ℝ := fun p => cmp (h p) c d

/-- The trace `h = η^cc h_cc`. -/
def htr (h : TensorField Site) : Site → ℝ := fun p => ∑ c, etaL c * hc h c c p

@[simp] theorem etaL_0 : etaL 0 = 1 := rfl
@[simp] theorem etaL_1 : etaL 1 = -1 := rfl
@[simp] theorem etaL_2 : etaL 2 = -1 := rfl
@[simp] theorem etaL_3 : etaL 3 = -1 := rfl

@[simp] theorem hc_00 (h : TensorField Site) (p : Site) : hc h 0 0 p = (h p).tt :=
  rfl
@[simp] theorem hc_01 (h : TensorField Site) (p : Site) : hc h 0 1 p = (h p).tx :=
  rfl
@[simp] theorem hc_02 (h : TensorField Site) (p : Site) : hc h 0 2 p = (h p).ty :=
  rfl
@[simp] theorem hc_03 (h : TensorField Site) (p : Site) : hc h 0 3 p = (h p).tz :=
  rfl
@[simp] theorem hc_10 (h : TensorField Site) (p : Site) : hc h 1 0 p = (h p).tx :=
  rfl
@[simp] theorem hc_11 (h : TensorField Site) (p : Site) : hc h 1 1 p = (h p).xx :=
  rfl
@[simp] theorem hc_12 (h : TensorField Site) (p : Site) : hc h 1 2 p = (h p).xy :=
  rfl
@[simp] theorem hc_13 (h : TensorField Site) (p : Site) : hc h 1 3 p = (h p).xz :=
  rfl
@[simp] theorem hc_20 (h : TensorField Site) (p : Site) : hc h 2 0 p = (h p).ty :=
  rfl
@[simp] theorem hc_21 (h : TensorField Site) (p : Site) : hc h 2 1 p = (h p).xy :=
  rfl
@[simp] theorem hc_22 (h : TensorField Site) (p : Site) : hc h 2 2 p = (h p).yy :=
  rfl
@[simp] theorem hc_23 (h : TensorField Site) (p : Site) : hc h 2 3 p = (h p).yz :=
  rfl
@[simp] theorem hc_30 (h : TensorField Site) (p : Site) : hc h 3 0 p = (h p).tz :=
  rfl
@[simp] theorem hc_31 (h : TensorField Site) (p : Site) : hc h 3 1 p = (h p).xz :=
  rfl
@[simp] theorem hc_32 (h : TensorField Site) (p : Site) : hc h 3 2 p = (h p).yz :=
  rfl
@[simp] theorem hc_33 (h : TensorField Site) (p : Site) : hc h 3 3 p = (h p).zz :=
  rfl

/-- The linearized Ricci components
    `R_ab = ½ (Δ^c Δ_a h_cb + Δ^c Δ_b h_ca − □ h_ab − Δ_a Δ_b h)`, indices raised with `η`. -/
noncomputable def ricC (h : TensorField Site) (a b : Fin 4) (p : Site) : ℝ :=
  (1 / 2 : ℝ) * (∑ c, etaL c * D c (D a (hc h c b)) p + ∑ c, etaL c * D c (D b (hc h c a)) p
    - ∑ c, etaL c * D c (D c (hc h a b)) p - D a (D b (htr h)) p)

theorem hc_symm (h : TensorField Site) (c d : Fin 4) : hc h c d = hc h d c := by
  funext p
  fin_cases c <;> fin_cases d <;> rfl

/-- The linearized Ricci components are symmetric. -/
theorem ricC_symm (h : TensorField Site) (a b : Fin 4) (p : Site) :
    ricC h a b p = ricC h b a p := by
  simp only [ricC, hc_symm h a b, D_comm a b]
  ring

/-- The **linearized Ricci tensor** of the perturbation `h`, as a symmetric tensor field. -/
noncomputable def linRicci (h : TensorField Site) : TensorField Site := fun p =>
  { tt := ricC h 0 0 p,
    tx := ricC h 0 1 p,
    ty := ricC h 0 2 p,
    tz := ricC h 0 3 p,
    xx := ricC h 1 1 p,
    xy := ricC h 1 2 p,
    xz := ricC h 1 3 p,
    yy := ricC h 2 2 p,
    yz := ricC h 2 3 p,
    zz := ricC h 3 3 p }

theorem cmp_linRicci (h : TensorField Site) (a b : Fin 4) (p : Site) :
    cmp (linRicci h p) a b = ricC h a b p := by
  fin_cases a <;> fin_cases b <;> simp [cmp, linRicci] <;> exact ricC_symm h _ _ p

theorem scalarCurv_linRicci (h : TensorField Site) (p : Site) :
    scalarCurv (linRicci h) p = ∑ c, etaL c * ricC h c c p := by
  simp [scalarCurv, trace, linRicci, Fin.sum_univ_four]
  ring

/-! ## The contracted Bianchi identity -/

/-- The site normal form used by the brute-force identities: adjacent steps are sorted. -/
theorem site_swap (q : Site) (a b : Fin 4) : q + step a + step b = q + step b + step a :=
  add_right_comm _ _ _

/-- **Contracted Bianchi, in components**: `Σ_a η^aa Δ_a R_ab = ½ Δ_b (η^cc R_cc)`, for every `h`.
    Every term is a value of `h` at a shifted site; once the shifts are sorted the identity is
    polynomial, the continuum cancellation term for term. -/
theorem bianchi_components (h : TensorField Site) (b : Fin 4) (p : Site) :
    ∑ a, etaL a * D a (ricC h a b) p =
      (1 / 2 : ℝ) * D b (fun q => ∑ c, etaL c * ricC h c c q) p := by
  fin_cases b <;>
  simp only [ricC, D, htr, Fin.sum_univ_four, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    etaL_0, etaL_1, etaL_2, etaL_3, hc_00, hc_01, hc_02, hc_03, hc_10, hc_11, hc_12, hc_13,
    hc_20, hc_21, hc_22, hc_23, hc_30, hc_31, hc_32, hc_33] <;>
  simp only [site_swap] <;>
  ring

/-- **The discrete contracted Bianchi identity on `ℤ⁴`**, in the form `lattice_einstein_field_equations`
    takes as its hypothesis `hbianchi`: `∇^a R_ab = ½ ∂_b R` for the linearized Ricci tensor of
    every perturbation `h`. -/
theorem lattice_contracted_bianchi (h : TensorField Site) :
    ldiv (linRicci h) = fun p => (1 / 2 : ℝ) • lgrad (scalarCurv (linRicci h)) p := by
  funext p b
  have hL : ldiv (linRicci h) p b = ∑ a, etaL a * D a (ricC h a b) p := by
    simp only [ldiv, cmp_linRicci, D]
  have hR : lgrad (scalarCurv (linRicci h)) p b =
      D b (fun q => ∑ c, etaL c * ricC h c c q) p := by
    simp only [lgrad, scalarCurv_linRicci, D]
  rw [hL, Pi.smul_apply, hR, smul_eq_mul, bianchi_components]

/-! ## The Einstein tensor is divergence-free -/

theorem ldiv_sub (A B : TensorField Site) :
    ldiv (fun p => A p - B p) = fun p => ldiv A p - ldiv B p := by
  funext p b
  have hs : ∀ (X Y : SymTensor4) (a c : Fin 4), cmp (X - Y) a c = cmp X a c - cmp Y a c := by
    intro X Y a c
    fin_cases a <;> fin_cases c <;> simp [cmp]
  simp only [ldiv, hs, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- **`∇^a G_ab = 0`** for the linearized Einstein tensor of every perturbation. -/
theorem einstein_divergence_free (h : TensorField Site) :
    ldiv (einsteinTensor (linRicci h)) = 0 := by
  have hG : einsteinTensor (linRicci h) =
      fun p => linRicci h p - metricMultiple ((1 / 2 : ℝ) * scalarCurv (linRicci h) p) := by
    funext p
    simp only [einsteinTensor]
    congr 2
    ring
  rw [hG, ldiv_sub, ldiv_metricMultiple, lattice_contracted_bianchi]
  funext p b
  simp [lgrad]
  ring

/-! ## Conservation -/

/-- **Conservation follows from the field equations.** If `G_ab + Λ g_ab = κ T_ab` holds at every
    site with `κ ≠ 0`, then `∇^a T_ab = 0`. -/
theorem conservation_of_field_equations (h T : TensorField Site) (κ Λ : ℝ) (hκ : κ ≠ 0)
    (hfe : ∀ p, einsteinTensor (linRicci h) p + metricMultiple Λ = κ • T p) :
    ldiv T = 0 := by
  have hT : T = fun p => κ⁻¹ • (einsteinTensor (linRicci h) p + metricMultiple ((fun _ => Λ) p)) := by
    funext p
    rw [hfe p]
    apply SymTensor4.ext' <;> simp [hκ]
  have hconst : ldiv (fun p => metricMultiple ((fun _ : Site => Λ) p)) = 0 := by
    rw [ldiv_metricMultiple]
    funext p b
    simp [lgrad]
  rw [hT, ldiv_smul, ldiv_add, einstein_divergence_free, hconst]
  funext p b
  simp

/-- **On Jacobson's route, conservation is a constant `Λ`.** Given the metric form
    `R_ab = κ T_ab + f g_ab` with `κ ≠ 0`, the source is conserved **iff** `f = R/2 − Λ` for one
    constant `Λ`. With the Bianchi identity a theorem, `hcons` says exactly that the cosmological
    term does not vary from site to site. -/
theorem conservation_iff_constant_lambda (h T : TensorField Site) (f : ScalarField Site)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hform : ∀ p, linRicci h p = κ • T p + metricMultiple (f p)) :
    ldiv T = 0 ↔ ∃ Λ : ℝ, ∀ p, f p = scalarCurv (linRicci h) p / 2 - Λ := by
  -- Divergence of the metric form: `∇^a R_ab = κ ∇^a T_ab + ∂_b f`.
  have hdiv : ldiv (linRicci h) = fun p => κ • ldiv T p + lgrad f p := by
    have hR : linRicci h = fun p => (fun q => κ • T q) p + (fun q => metricMultiple (f q)) p := by
      funext p; exact hform p
    rw [hR, ldiv_add, ldiv_smul, ldiv_metricMultiple]
  constructor
  · intro hcons
    exact scalar_multiple_is_curvature latticeCalculus κ (linRicci h) T f hform
      (lattice_contracted_bianchi h) hcons
  · rintro ⟨Λ, hΛ⟩
    -- `∂_b f = ½ ∂_b R`, so Bianchi leaves `κ ∇^a T_ab = 0`.
    have hgf : lgrad f = fun p => (1 / 2 : ℝ) • lgrad (scalarCurv (linRicci h)) p := by
      funext p b
      simp only [lgrad, hΛ, Pi.smul_apply, smul_eq_mul]
      ring
    have hB := lattice_contracted_bianchi h
    rw [hdiv, ← hgf] at hB
    funext p b
    have := congrFun (congrFun hB p) b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have h0 : κ * ldiv T p b = 0 := by linarith
    simpa [hκ] using h0

/-- **The lattice field equations with Bianchi discharged.** From the metric form and
    conservation alone, `G_ab + Λ g_ab = κ T_ab` with one `Λ` for the whole lattice. The remaining
    hypotheses are the metric form (the first two arrows) and conservation (equivalently, a
    constant `Λ`, `conservation_iff_constant_lambda`). -/
theorem linearized_lattice_einstein_field_equations (h T : TensorField Site) (f : ScalarField Site)
    (κ : ℝ) (hform : ∀ p, linRicci h p = κ • T p + metricMultiple (f p)) (hcons : ldiv T = 0) :
    ∃ Λ : ℝ, ∀ p, einsteinTensor (linRicci h) p + metricMultiple Λ = κ • T p :=
  lattice_einstein_field_equations κ (linRicci h) T f hform (lattice_contracted_bianchi h) hcons

/-! ## Gauge invariance: the other face of Bianchi -/

/-- The components `Δ_a ξ_b + Δ_b ξ_a` of a pure-gauge perturbation. -/
def pgC (ξ : Fin 4 → Site → ℝ) (a b : Fin 4) (p : Site) : ℝ := D a (ξ b) p + D b (ξ a) p

/-- A **pure-gauge perturbation** `h_ab = Δ_a ξ_b + Δ_b ξ_a`: a discrete infinitesimal
    diffeomorphism generated by the covector field `ξ`. -/
def pureGauge (ξ : Fin 4 → Site → ℝ) : TensorField Site := fun p =>
  { tt := pgC ξ 0 0 p,
    tx := pgC ξ 0 1 p,
    ty := pgC ξ 0 2 p,
    tz := pgC ξ 0 3 p,
    xx := pgC ξ 1 1 p,
    xy := pgC ξ 1 2 p,
    xz := pgC ξ 1 3 p,
    yy := pgC ξ 2 2 p,
    yz := pgC ξ 2 3 p,
    zz := pgC ξ 3 3 p }

set_option maxHeartbeats 4000000 in
/-- **Pure gauge carries no curvature.** The linearized Ricci tensor of `Δ_a ξ_b + Δ_b ξ_a`
    vanishes identically, for every `ξ`. -/
theorem ricC_pureGauge (ξ : Fin 4 → Site → ℝ) (a b : Fin 4) (p : Site) :
    ricC (pureGauge ξ) a b p = 0 := by
  fin_cases a <;> fin_cases b <;>
  simp only [ricC, D, htr, pureGauge, pgC, Fin.sum_univ_four, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, etaL_0, etaL_1, etaL_2, etaL_3, hc_00, hc_01, hc_02, hc_03,
    hc_10, hc_11, hc_12, hc_13, hc_20, hc_21, hc_22, hc_23, hc_30, hc_31, hc_32, hc_33] <;>
  simp only [site_swap] <;>
  ring_nf

theorem ricC_add (h g : TensorField Site) (a b : Fin 4) (p : Site) :
    ricC (fun q => h q + g q) a b p = ricC h a b p + ricC g a b p := by
  have hcadd : ∀ c d, hc (fun q => h q + g q) c d = fun q => hc h c d q + hc g c d q := by
    intro c d; funext q; simp [hc, cmp_add]
  simp only [ricC, htr, D, hcadd, Fin.sum_univ_four]
  ring

/-- **Gauge invariance of the linearized curvature**: `h ↦ h + (Δ_a ξ_b + Δ_b ξ_a)` leaves the
    linearized Ricci tensor unchanged. -/
theorem linRicci_gauge_invariant (h : TensorField Site) (ξ : Fin 4 → Site → ℝ) :
    linRicci (fun p => h p + pureGauge ξ p) = linRicci h := by
  funext p
  simp only [linRicci, ricC_add, ricC_pureGauge, add_zero]

end QLF.LatticeDivergence
