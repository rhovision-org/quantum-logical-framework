import QLF_GaussLaw

/-!
# QLF_WalkCoupling — the walk's current is its response to a link phase

Issue #207. [`QLF_GaussLaw`](QLF_GaussLaw.lean) derived both halves of Maxwell from a finite action
in which the charge `ρ` and current `J` were given, and [`QLF_Maxwell`](QLF_Maxwell.lean) showed the
walk supplies a conserved pair. This module ties the two together from the walk's side: the
walk's current is not just *a* conserved quantity, it is exactly how the walk responds to a change
of one link phase, which is what the coupling `−Σ J · a` in the link action means.

Take one realizable step along axis `e` with link phases `a` (`axisStep` of
[`QLF_LatticeGauge`](QLF_LatticeGauge.lean)) and move the phase of the single link `y` by `ε`.

* **`link_overlap`.** The overlap of the step with and without the change is exactly
  `⟨U_a ψ, U_{a+εδ_y} ψ⟩ = Σₓ ‖ψ(x)‖² + (e^{iε} − 1)·F + (e^{−iε} − 1)·B`,
  where `F = ‖fix t ψ(y)‖²` is what hops forward across the link and `B = ‖fix t̄ ψ(y+e)‖²` what
  hops back. Only the two hops across `y` see the change, and because the realizable parts are
  orthogonal they do not interfere.
* **`link_response`.** Hence, for every `ε`,
  `⟨U_a ψ, U_{a+εδ_y} ψ⟩ − ⟨U_a ψ, U_{a−εδ_y} ψ⟩ = (e^{iε} − e^{−iε}) · J(y)`,
  with `J` the walk's current of `QLF_Maxwell`. The current is the odd part of the walk's response
  to its link phase: the lattice form of `J = δS_matter/δa`. No derivative or limit is taken.

So the walk is a source of the right kind in two independent ways: its current is conserved
(`QLF_Maxwell.continuity`, which is what gauge invariance of the link action requires,
`QLF_GaussLaw.gauge_invariant_iff_continuity`), and it is the quantity the link phase couples to.

**Not here.** A single action whose stationarity gives both the walk and the field equations at
once (the walk is a unitary step, not a stationary point), the back-reaction of the links on the
walk over many steps, and compact or non-abelian links. No axioms.

**Credit.** Current as the response to a gauge field is standard (the lattice current as the
derivative of the action with respect to the link variable is in Wilson 1974 and Kogut–Susskind
1975); for quantum walks, gauge-field coupling and its conserved current are studied by
Arnault and Debbasch ("Quantum walks and discrete gauge theories", arXiv:1508.00038) and Márquez-Martín, Arnault, Di Molfetta
and Pérez (*Phys. Rev. A* **98**, 032333 (2018)). QLF supplies the step (realizable twist parts) and
the orthogonality that makes the response exact.
-/

namespace QLF.WalkCoupling

open Matrix
open QLF.ClosureChannels
open QLF.LocalGauge (ph ph_add nsq V)
open QLF.LatticeGauge (axisStep)

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

/-- The overlap of two lattice states. -/
def ip (u v : S → V) : ℂ := ∑ x, star (u x) ⬝ᵥ v x

/-- The link field with the single link `y` moved by `ε`. -/
def bumpLink (a : S → ℝ) (ε : ℝ) (y : S) : S → ℝ := fun z => a z + if z = y then ε else 0

lemma star_ph (r : ℝ) : star (ph r) = ph (-r) := by
  unfold ph
  rw [QLF.ClosureChannels.star_exp_kI]
  push_cast; ring_nf

omit [Fintype S] [DecidableEq S] in
/-- At one site the overlap separates into the forward and backward hops. -/
lemma site_overlap (t : Twist) (u w : V) (α α' β β' : ℝ) :
    star (ph α • (fix t *ᵥ u) + ph β • (fix t.conj *ᵥ w)) ⬝ᵥ
        (ph α' • (fix t *ᵥ u) + ph β' • (fix t.conj *ᵥ w)) =
      ph (α' - α) * nsq (fix t *ᵥ u) + ph (β' - β) * nsq (fix t.conj *ᵥ w) := by
  have h1 := LocalGauge.ortho t u w
  have h2 := LocalGauge.ortho' t w u
  rw [star_add, star_smul, star_smul, add_dotProduct, dotProduct_add, dotProduct_add,
    smul_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul, h1, h2]
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add, star_ph]
  unfold nsq
  rw [show α' - α = -α + α' by ring, show β' - β = -β + β' by ring, ph_add, ph_add]
  ring

/-- **The overlap under one link-phase change**, exactly. -/
theorem link_overlap (t : Twist) (e : S) (a : S → ℝ) (ψ : S → V) (y : S) (ε : ℝ) :
    ip (axisStep t e a ψ) (axisStep t e (bumpLink a ε y) ψ) =
      ∑ x, nsq (ψ x) + (ph ε - 1) * nsq (fix t *ᵥ ψ y) +
        (ph (-ε) - 1) * nsq (fix t.conj *ᵥ ψ (y + e)) := by
  unfold ip axisStep
  simp only [site_overlap]
  have hα : ∀ x : S, bumpLink a ε y (x - e) - a (x - e) = if x = y + e then ε else 0 := by
    intro x
    simp only [bumpLink, add_sub_cancel_left, sub_eq_iff_eq_add]
  have hβ : ∀ x : S, -bumpLink a ε y x - -a x = -(if x = y then ε else 0) := by
    intro x; simp only [bumpLink]; ring
  simp only [hα, hβ]
  have hsplit : ∀ x : S,
      ph (if x = y + e then ε else 0) * nsq (fix t *ᵥ ψ (x - e)) +
        ph (-(if x = y then ε else 0)) * nsq (fix t.conj *ᵥ ψ (x + e)) =
      (nsq (fix t *ᵥ ψ (x - e)) + nsq (fix t.conj *ᵥ ψ (x + e))) +
        ((if x = y + e then (ph ε - 1) * nsq (fix t *ᵥ ψ (x - e)) else 0) +
          (if x = y then (ph (-ε) - 1) * nsq (fix t.conj *ᵥ ψ (x + e)) else 0)) := by
    intro x
    have h0 : ph 0 = 1 := by simp [ph]
    by_cases h1 : x = y + e <;> by_cases h2 : x = y
    · simp only [if_pos h1, if_pos h2]; ring
    · simp only [if_pos h1, if_neg h2, neg_zero, h0]; ring
    · simp only [if_neg h1, if_pos h2, h0]; ring
    · simp only [if_neg h1, if_neg h2, neg_zero, h0]; ring
  rw [Finset.sum_congr rfl (fun x _ => hsplit x)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    add_sub_cancel_right]
  -- the unchanged part is the total norm (the step is unitary)
  have e1 : ∑ x : S, nsq (fix t *ᵥ ψ (x - e)) = ∑ x : S, nsq (fix t *ᵥ ψ x) :=
    Fintype.sum_equiv (Equiv.subRight e) _ _ (fun _ => rfl)
  have e2 : ∑ x : S, nsq (fix t.conj *ᵥ ψ (x + e)) = ∑ x : S, nsq (fix t.conj *ᵥ ψ x) :=
    Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
  have htot : ∑ x : S, (nsq (fix t *ᵥ ψ (x - e)) + nsq (fix t.conj *ᵥ ψ (x + e))) =
      ∑ x, nsq (ψ x) := by
    rw [Finset.sum_add_distrib, e1, e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => (LocalGauge.nsq_split t (ψ x)).symm)
  rw [← Finset.sum_add_distrib, htot]
  ring

/-- **The walk's current is its response to a link phase**: the odd part of the overlap is
    `(e^{iε} − e^{−iε})` times the current across the link, for every `ε`. -/
theorem link_response (t : Twist) (e : S) (a : S → ℝ) (ψ : S → V) (y : S) (ε : ℝ) :
    ip (axisStep t e a ψ) (axisStep t e (bumpLink a ε y) ψ) -
        ip (axisStep t e a ψ) (axisStep t e (bumpLink a (-ε) y) ψ) =
      (ph ε - ph (-ε)) * Maxwell.current t e ψ y := by
  rw [link_overlap, link_overlap, neg_neg]
  unfold Maxwell.current
  ring

end QLF.WalkCoupling
