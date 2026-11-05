import QLF_GaugeAxis

/-!
# QLF_LocalGauge — a local phase needs a link field, and the flux is what it carries

Issue #207. [`QLF_GaugeAxis`](QLF_GaugeAxis.lean) found the gauge step to be a phase `e^{iω}` that
is the same everywhere. This module lets the phase vary from place to place and asks what that costs.

The walk lives on a ring of `N` sites (`ZMod N`, finite, no continuum). Each site carries a spin
vector. One step moves the part a twist `t` leaves unchanged (`fix t`) one site forward and the
conjugate part one site back, and each hop picks up the phase on the link it crosses (`a x` on the
link from `x` to `x + 1`).

* **`ringWalk_norm`.** The walk is unitary: it preserves the total norm `Σₓ ‖ψ(x)‖²` for every
  choice of link phases. The two parts are orthogonal (`fix_mul_conj`), so nothing interferes.
* **`ringWalk_covariant`.** A phase that varies by site, `ψ(x) ↦ e^{iθ(x)} ψ(x)`, commutes with the
  walk once the link phases shift by the difference across each link,
  `a(x) ↦ a(x) + θ(x+1) − θ(x)`. So a local phase is consistent only with a link field to absorb it.
* **`global_phase_trivial`.** A constant `θ` shifts no link. The global tick of `QLF_GaugeAxis` is
  the special case that needs no field, which is how the two are told apart.
* **`flux_invariant`.** The total phase around the ring, `Σₓ a(x)`, is unchanged by every local
  phase change. **`gauge_equiv_of_flux_eq`**: two link fields with the same flux are related by a
  local phase change. So the flux is the *whole* gauge-invariant content of the links on a ring:
  the Aharonov–Bohm phase.

**Credit.** The gauge principle is Weyl's (*Z. Phys.* **56**, 330 (1929)); link variables and
holonomies as the lattice form are Wilson's (*Phys. Rev. D* **10**, 2445 (1974)). What QLF adds is
where the pieces come from: the hop is a realizable twist step, and the phase it carries is the
gauge axis of `QLF_GaugeAxis`. No axioms.
-/

namespace QLF.LocalGauge

open Matrix
open QLF.ClosureChannels

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev V := Fin 2 → ℂ

/-- A unit phase. -/
noncomputable def ph (r : ℝ) : ℂ := Complex.exp (r * Complex.I)

theorem ph_add (r s : ℝ) : ph (r + s) = ph r * ph s := by
  unfold ph; rw [← Complex.exp_add]; push_cast; ring_nf

theorem star_ph_mul (r : ℝ) : star (ph r) * ph r = 1 := by
  unfold ph
  rw [QLF.ClosureChannels.star_exp_kI, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- Squared length of a spin vector. -/
def nsq (v : V) : ℂ := star v ⬝ᵥ v

variable {N : ℕ} [NeZero N]

/-- One walk step on the ring with link phases `a`. -/
noncomputable def ringWalk (t : Twist) (a : ZMod N → ℝ) (ψ : ZMod N → V) : ZMod N → V :=
  fun x => ph (a (x - 1)) • (fix t *ᵥ ψ (x - 1)) + ph (-(a x)) • (fix t.conj *ᵥ ψ (x + 1))

/-- A phase that varies from site to site. -/
noncomputable def localPhase (θ : ZMod N → ℝ) (ψ : ZMod N → V) : ZMod N → V :=
  fun x => ph (θ x) • ψ x

/-- The link phases after a local phase change. -/
def shiftLinks (θ : ZMod N → ℝ) (a : ZMod N → ℝ) : ZMod N → ℝ :=
  fun x => a x + θ (x + 1) - θ x

omit [NeZero N] in
/-- **Gauge covariance.** A local phase change commutes with the walk once the links absorb it. -/
theorem ringWalk_covariant (t : Twist) (a θ : ZMod N → ℝ) (ψ : ZMod N → V) :
    ringWalk t (shiftLinks θ a) (localPhase θ ψ) = localPhase θ (ringWalk t a ψ) := by
  funext x
  simp only [ringWalk, localPhase, shiftLinks, Matrix.mulVec_smul, smul_smul, smul_add,
    sub_add_cancel]
  have h1 : ph (a (x - 1) + θ x - θ (x - 1)) * ph (θ (x - 1)) = ph (θ x) * ph (a (x - 1)) := by
    rw [← ph_add, ← ph_add]; congr 1; ring
  have h2 : ph (-(a x + θ (x + 1) - θ x)) * ph (θ (x + 1)) = ph (θ x) * ph (-(a x)) := by
    rw [← ph_add, ← ph_add]; congr 1; ring
  rw [h1, h2]

omit [NeZero N] in
/-- **A global phase needs no field**: a constant phase change shifts no link. -/
theorem global_phase_trivial (c : ℝ) (a : ZMod N → ℝ) : shiftLinks (fun _ => c) a = a := by
  funext x; simp [shiftLinks]

/-- The total phase around the ring. -/
def flux (a : ZMod N → ℝ) : ℝ := ∑ x, a x

/-- **The flux is gauge invariant.** -/
theorem flux_invariant (θ a : ZMod N → ℝ) : flux (shiftLinks θ a) = flux a := by
  unfold flux shiftLinks
  have h : ∑ x : ZMod N, θ (x + 1) = ∑ x : ZMod N, θ x :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h, add_sub_cancel_right]

/-- **The flux is all there is.** Two link fields with the same flux differ by a local phase
    change. -/
theorem gauge_equiv_of_flux_eq (a b : ZMod N → ℝ) (h : flux a = flux b) :
    ∃ θ : ZMod N → ℝ, shiftLinks θ a = b := by
  -- θ(x) = Σ_{j < x.val} (b j − a j), read through the canonical representative of `x`.
  let d : ZMod N → ℝ := fun x => b x - a x
  let θ : ZMod N → ℝ := fun x => ∑ j ∈ Finset.range (x.val), d (j : ZMod N)
  have hd : ∑ j ∈ Finset.range N, d (j : ZMod N) = 0 := by
    have hs : ∑ x : ZMod N, d x = 0 := by
      simp only [d, Finset.sum_sub_distrib]; unfold flux at h; linarith
    rw [← hs]
    refine Finset.sum_bij' (fun n _ => (n : ZMod N)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · intro n _; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro n hn; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro n _; rfl
  refine ⟨θ, ?_⟩
  funext x
  simp only [shiftLinks]
  have key : θ (x + 1) - θ x = d x := by
    simp only [θ]
    by_cases hx : x.val + 1 < N
    · have hv : (x + 1).val = x.val + 1 := by
        rw [ZMod.val_add, ZMod.val_one'' (by omega), Nat.mod_eq_of_lt hx]
      rw [hv, Finset.sum_range_succ, ZMod.natCast_zmod_val]
      ring
    · have hxN : x.val + 1 = N := by have := ZMod.val_lt x; omega
      have h0 : x + 1 = 0 := by
        have e : ((x.val + 1 : ℕ) : ZMod N) = x + 1 := by
          rw [Nat.cast_succ, ZMod.natCast_zmod_val]
        rw [← e, hxN, ZMod.natCast_self]
      have hv : (x + 1).val = 0 := by rw [h0, ZMod.val_zero]
      rw [hv, Finset.sum_range_zero]
      have hs : ∑ j ∈ Finset.range (x.val + 1), d (j : ZMod N) = 0 := by rw [hxN]; exact hd
      rw [Finset.sum_range_succ, ZMod.natCast_zmod_val] at hs
      linarith
  simp only [d] at key
  linarith

/-! ## Unitarity -/

lemma star_mulVec_dot (A B : M) (u v : V) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ v) = star u ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec]

lemma ortho (t : Twist) (u v : V) : star (fix t *ᵥ u) ⬝ᵥ (fix t.conj *ᵥ v) = 0 := by
  rw [star_mulVec_dot, fix_herm, fix_mul_conj, Matrix.zero_mulVec, dotProduct_zero]

lemma ortho' (t : Twist) (u v : V) : star (fix t.conj *ᵥ u) ⬝ᵥ (fix t *ᵥ v) = 0 := by
  rw [star_mulVec_dot, fix_herm, fix_conj_mul, Matrix.zero_mulVec, dotProduct_zero]

lemma nsq_add (p q : V) (h1 : star p ⬝ᵥ q = 0) (h2 : star q ⬝ᵥ p = 0) :
    nsq (p + q) = nsq p + nsq q := by
  unfold nsq
  rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, h1, h2]
  ring

lemma nsq_ph (r : ℝ) (v : V) : nsq (ph r • v) = nsq v := by
  unfold nsq
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, star_ph_mul,
    one_mul]

lemma nsq_split (t : Twist) (u : V) : nsq u = nsq (fix t *ᵥ u) + nsq (fix t.conj *ᵥ u) := by
  rw [← nsq_add _ _ (ortho t u u) (ortho' t u u), ← Matrix.add_mulVec, fix_add_conj,
    Matrix.one_mulVec]

/-- The total norm of a ring state. -/
def total (ψ : ZMod N → V) : ℂ := ∑ x, nsq (ψ x)

/-- **The ring walk is unitary** for every choice of link phases. -/
theorem ringWalk_norm (t : Twist) (a : ZMod N → ℝ) (ψ : ZMod N → V) :
    total (ringWalk t a ψ) = total ψ := by
  unfold total ringWalk
  have hx : ∀ x : ZMod N, nsq (ph (a (x - 1)) • (fix t *ᵥ ψ (x - 1)) +
      ph (-(a x)) • (fix t.conj *ᵥ ψ (x + 1))) =
      nsq (fix t *ᵥ ψ (x - 1)) + nsq (fix t.conj *ᵥ ψ (x + 1)) := by
    intro x
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
      nsq_add _ _ (ortho t _ _) (ortho' t _ _), Matrix.mulVec_smul, Matrix.mulVec_smul,
      nsq_ph, nsq_ph]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib]
  have e1 : ∑ x : ZMod N, nsq (fix t *ᵥ ψ (x - 1)) = ∑ x : ZMod N, nsq (fix t *ᵥ ψ x) :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)
  have e2 : ∑ x : ZMod N, nsq (fix t.conj *ᵥ ψ (x + 1)) =
      ∑ x : ZMod N, nsq (fix t.conj *ᵥ ψ x) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [e1, e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => (nsq_split t (ψ x)).symm)

end QLF.LocalGauge
