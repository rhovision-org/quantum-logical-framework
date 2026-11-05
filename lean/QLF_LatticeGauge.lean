import QLF_LocalGauge

/-!
# QLF_LatticeGauge — plaquettes, field strength and the Bianchi identity

Issue #207. [`QLF_LocalGauge`](QLF_LocalGauge.lean) put the walk on a ring, where the only loop is the
ring itself. This module puts it on any finite lattice (any finite abelian group of sites, such as the
3-torus `ZMod N × ZMod N × ZMod N`) with a phase on every link along every axis, and asks what the
smallest loops carry.

* **`axisStep_norm`, `axisStep_covariant`.** A realizable step along any axis `e` is unitary for every
  link field, and covariant under a site-dependent phase once that axis's links shift by
  `θ(x + e) − θ(x)`. A walk built from steps along several axes inherits both.
* **`plaquette`.** The field strength on the square spanned by axes `e`, `f` at site `x` is the
  phase around it: `F(x) = a_e(x) + a_f(x+e) − a_e(x+f) − a_f(x)`.
* **`plaquette_invariant`.** Every local phase change leaves every plaquette unchanged, and
  **`pure_gauge_no_field`**: a link field that is just a phase change of nothing has `F = 0`.
  The plaquette is the gauge-invariant content of the links.
* **`plaquette_antisymm`.** `F_{fe} = −F_{ef}`: field strength is oriented.
* **`bianchi`.** On the cube spanned by three axes, the six faces' fluxes cancel:
  `Δ_e F_{fg} + Δ_f F_{ge} + Δ_g F_{ef} = 0`. This is the discrete `dF = 0`, the source-free half
  of Maxwell's equations: no magnetic monopoles and Faraday's law. It is an identity of the links, not
  a law put in.
* **`total_plaquette_zero`.** On a closed finite lattice the plaquettes of one plane sum to zero:
  the total flux through a closed surface is zero.

**Credit.** Link phases, plaquettes and the lattice Bianchi identity are Wilson's lattice gauge
theory (*Phys. Rev. D* **10**, 2445 (1974)). QLF supplies the hop (a realizable twist step) and the
phase (the gauge axis, [`QLF_GaugeAxis`](QLF_GaugeAxis.lean)). The substrate's own fold sign is one
particular link field, the ℤ₂ edge-sign connection of [`QLF_EdgeSign`](QLF_EdgeSign.lean), whose
plaquettes carry flux `π` on mixed spatial planes. **Not here:** the other half of Maxwell's
equations (Gauss and Ampère), which needs a dynamics for the links. No axioms.
-/

namespace QLF.LatticeGauge

open Matrix
open QLF.ClosureChannels
open QLF.LocalGauge (ph ph_add nsq V)

variable {S : Type*} [AddCommGroup S] [Fintype S]

/-- One realizable step along axis `e` with link phases `a` on that axis. -/
noncomputable def axisStep (t : Twist) (e : S) (a : S → ℝ) (ψ : S → V) : S → V :=
  fun x => ph (a (x - e)) • (fix t *ᵥ ψ (x - e)) + ph (-(a x)) • (fix t.conj *ᵥ ψ (x + e))

/-- A phase that varies from site to site. -/
noncomputable def localPhase (θ : S → ℝ) (ψ : S → V) : S → V := fun x => ph (θ x) • ψ x

/-- Axis-`e` link phases after a local phase change. -/
def shiftLinks (e : S) (θ : S → ℝ) (a : S → ℝ) : S → ℝ := fun x => a x + θ (x + e) - θ x

omit [Fintype S] in
/-- **Gauge covariance along any axis.** -/
theorem axisStep_covariant (t : Twist) (e : S) (a θ : S → ℝ) (ψ : S → V) :
    axisStep t e (shiftLinks e θ a) (localPhase θ ψ) = localPhase θ (axisStep t e a ψ) := by
  funext x
  simp only [axisStep, localPhase, shiftLinks, Matrix.mulVec_smul, smul_smul, smul_add,
    sub_add_cancel]
  have h1 : ph (a (x - e) + θ x - θ (x - e)) * ph (θ (x - e)) = ph (θ x) * ph (a (x - e)) := by
    rw [← ph_add, ← ph_add]; congr 1; ring
  have h2 : ph (-(a x + θ (x + e) - θ x)) * ph (θ (x + e)) = ph (θ x) * ph (-(a x)) := by
    rw [← ph_add, ← ph_add]; congr 1; ring
  rw [h1, h2]

/-- The total norm of a lattice state. -/
def total (ψ : S → V) : ℂ := ∑ x, nsq (ψ x)

/-- **Every axis step is unitary**, for every link field. -/
theorem axisStep_norm (t : Twist) (e : S) (a : S → ℝ) (ψ : S → V) :
    total (axisStep t e a ψ) = total ψ := by
  unfold total axisStep
  have hx : ∀ x : S, nsq (ph (a (x - e)) • (fix t *ᵥ ψ (x - e)) +
      ph (-(a x)) • (fix t.conj *ᵥ ψ (x + e))) =
      nsq (fix t *ᵥ ψ (x - e)) + nsq (fix t.conj *ᵥ ψ (x + e)) := by
    intro x
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
      LocalGauge.nsq_add _ _ (LocalGauge.ortho t _ _) (LocalGauge.ortho' t _ _),
      Matrix.mulVec_smul, Matrix.mulVec_smul, LocalGauge.nsq_ph, LocalGauge.nsq_ph]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib]
  have e1 : ∑ x : S, nsq (fix t *ᵥ ψ (x - e)) = ∑ x : S, nsq (fix t *ᵥ ψ x) :=
    Fintype.sum_equiv (Equiv.subRight e) _ _ (fun _ => rfl)
  have e2 : ∑ x : S, nsq (fix t.conj *ᵥ ψ (x + e)) = ∑ x : S, nsq (fix t.conj *ᵥ ψ x) :=
    Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
  rw [e1, e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => (LocalGauge.nsq_split t (ψ x)).symm)

/-- **Steps along two axes compose to a unitary, covariant step** (and so on for any number). -/
theorem twoAxis_norm (t u : Twist) (e f : S) (a b : S → ℝ) (ψ : S → V) :
    total (axisStep u f b (axisStep t e a ψ)) = total ψ := by
  rw [axisStep_norm, axisStep_norm]

omit [Fintype S] in
theorem twoAxis_covariant (t u : Twist) (e f : S) (a b θ : S → ℝ) (ψ : S → V) :
    axisStep u f (shiftLinks f θ b) (axisStep t e (shiftLinks e θ a) (localPhase θ ψ)) =
      localPhase θ (axisStep u f b (axisStep t e a ψ)) := by
  rw [axisStep_covariant, axisStep_covariant]

/-! ## Field strength -/

/-- The phase around the plaquette spanned by axes `e`, `f` at `x`, with link fields `a` (axis `e`)
    and `b` (axis `f`). -/
def plaquette (e f : S) (a b : S → ℝ) (x : S) : ℝ := a x + b (x + e) - a (x + f) - b x

omit [Fintype S] in
/-- **Field strength is gauge invariant.** -/
theorem plaquette_invariant (e f : S) (a b θ : S → ℝ) (x : S) :
    plaquette e f (shiftLinks e θ a) (shiftLinks f θ b) x = plaquette e f a b x := by
  simp only [plaquette, shiftLinks]
  rw [show x + e + f = x + f + e by abel]
  ring

omit [Fintype S] in
/-- **A pure gauge carries no field.** -/
theorem pure_gauge_no_field (e f : S) (θ : S → ℝ) (x : S) :
    plaquette e f (shiftLinks e θ 0) (shiftLinks f θ 0) x = 0 := by
  rw [plaquette_invariant]; simp [plaquette]

omit [Fintype S] in
/-- **Field strength is oriented.** -/
theorem plaquette_antisymm (e f : S) (a b : S → ℝ) (x : S) :
    plaquette f e b a x = -plaquette e f a b x := by
  simp only [plaquette]; ring

/-- The lattice difference along axis `e`. -/
def diff (e : S) (F : S → ℝ) (x : S) : ℝ := F (x + e) - F x

omit [Fintype S] in
/-- **The Bianchi identity.** Around the cube spanned by axes `e`, `f`, `g`, with link fields `a`,
    `b`, `c` on those axes, the oriented face fluxes cancel: the discrete `dF = 0`. -/
theorem bianchi (e f g : S) (a b c : S → ℝ) (x : S) :
    diff e (plaquette f g b c) x + diff f (plaquette g e c a) x +
      diff g (plaquette e f a b) x = 0 := by
  simp only [diff, plaquette]
  rw [show x + e + f = x + f + e by abel, show x + e + g = x + g + e by abel,
    show x + f + g = x + g + f by abel]
  ring

/-- **Zero total flux on a closed lattice.** The plaquettes of one plane sum to zero. -/
theorem total_plaquette_zero (e f : S) (a b : S → ℝ) : ∑ x, plaquette e f a b x = 0 := by
  have ha : ∑ x : S, a (x + f) = ∑ x : S, a x :=
    Fintype.sum_equiv (Equiv.addRight f) _ _ (fun _ => rfl)
  have hb : ∑ x : S, b (x + e) = ∑ x : S, b x :=
    Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
  simp only [plaquette, Finset.sum_sub_distrib, Finset.sum_add_distrib, ha, hb]
  ring

/-! ## The 3-torus -/

/-- The finite 3-torus of side `N`. -/
abbrev Torus3 (N : ℕ) := ZMod N × ZMod N × ZMod N

/-- Its three unit axes. -/
def ex (N : ℕ) : Torus3 N := (1, 0, 0)
def ey (N : ℕ) : Torus3 N := (0, 1, 0)
def ez (N : ℕ) : Torus3 N := (0, 0, 1)

/-- **No monopoles on the 3-torus**: the Bianchi identity at every cube. -/
theorem torus_bianchi (N : ℕ) (ax ay az : Torus3 N → ℝ) (x : Torus3 N) :
    diff (ex N) (plaquette (ey N) (ez N) ay az) x + diff (ey N) (plaquette (ez N) (ex N) az ax) x +
      diff (ez N) (plaquette (ex N) (ey N) ax ay) x = 0 :=
  bianchi _ _ _ _ _ _ x

end QLF.LatticeGauge
