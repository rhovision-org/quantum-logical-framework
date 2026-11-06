import QLF_NonAbelian

/-!
# QLF_NonAbelianAction — the Wilson action for matrix links

Issue #207. [`QLF_NonAbelian`](QLF_NonAbelian.lean) put unitary colour matrices on the links and
proved the plaquette trace gauge invariant. This module turns that trace into an action. The
plaquette term of a unitary holonomy `W` is

  `N − Re tr W = ½ tr((W − 1)ᴴ (W − 1))`,

half the squared distance of `W` from the identity. That identity does the work:

* **`plaq_nonneg`, `plaq_eq_zero_iff`.** Each plaquette term is non-negative, and it vanishes
  exactly when the holonomy is the identity.
* **`wilson_gauge`.** The summed action is unchanged by every site-dependent unitary colour
  rotation.
* **`wilson_nonneg`, `wilson_eq_zero_iff`.** The action is non-negative, and it is zero exactly on
  flat links: every plaquette holonomy is the identity.
* **`pure_gauge_flat`.** Links that are a colour rotation of the trivial links,
  `U_k(x) = g(x)ᴴ g(x + e_k)`, are flat, so they have zero action.
* **`holonomy_abelian`, `wilson_abelian`.** For `N = 1` with phase links `e^{i a}`, the holonomy is
  `e^{i F}` and the action is exactly the compact action of
  [`QLF_CompactLinks`](QLF_CompactLinks.lean). The matrix action extends it, it does not replace it.

**Not here.** The variation of this action (the non-abelian field equation), its energy and
dynamics, the non-abelian Gauss law, and which colour group the twists select. No axioms.

**Credit.** The action is Wilson's (*Phys. Rev. D* **10**, 2445 (1974)); the gauge field is Yang
and Mills's (*Phys. Rev.* **96**, 191 (1954)). Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.NonAbelianAction

open Matrix QLF.NonAbelian ComplexOrder

variable {S : Type*} [AddCommGroup S] [Fintype S] {N n : ℕ}

/-- The plaquette term `N − Re tr W`. -/
noncomputable def plaq (w : L N) : ℝ := (N : ℝ) - (trace w).re

/-- **The plaquette term is half the squared distance from the identity.** -/
lemma defect_eq (w : L N) (hw : Unitary w) :
    trace ((w - 1)ᴴ * (w - 1)) = ((2 * plaq w : ℝ) : ℂ) := by
  have h : (w - 1)ᴴ * (w - 1) = 1 + 1 - wᴴ - w := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hw.1, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [h, trace_sub, trace_sub, trace_add, trace_one, trace_conjTranspose, Fintype.card_fin]
  unfold plaq
  apply Complex.ext <;> simp; ring

lemma defect_nonneg (w : L N) : 0 ≤ (trace ((w - 1)ᴴ * (w - 1))).re := by
  have := (posSemidef_conjTranspose_mul_self (w - 1)).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

/-- **Each plaquette term is non-negative.** -/
theorem plaq_nonneg (w : L N) (hw : Unitary w) : 0 ≤ plaq w := by
  have h := defect_nonneg w
  rw [defect_eq w hw, Complex.ofReal_re] at h
  linarith

/-- **A plaquette term vanishes exactly at the identity.** -/
theorem plaq_eq_zero_iff (w : L N) (hw : Unitary w) : plaq w = 0 ↔ w = 1 := by
  constructor
  · intro h
    have h0 : trace ((w - 1)ᴴ * (w - 1)) = 0 := by rw [defect_eq w hw, h]; simp
    exact sub_eq_zero.mp (trace_conjTranspose_mul_self_eq_zero_iff.mp h0)
  · rintro rfl
    unfold plaq
    rw [trace_one, Fintype.card_fin]; simp

omit [AddCommGroup S] [Fintype S] in
lemma unitary_mul {u v : L N} (hu : Unitary u) (hv : Unitary v) : Unitary (u * v) := by
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_mul, show vᴴ * uᴴ * (u * v) = vᴴ * (uᴴ * u) * v by
      simp only [Matrix.mul_assoc], hu.1, Matrix.mul_one, hv.1]
  · rw [conjTranspose_mul, show u * v * (vᴴ * uᴴ) = u * (v * vᴴ) * uᴴ by
      simp only [Matrix.mul_assoc], hv.2, Matrix.mul_one, hu.2]

omit [Fintype S] in
/-- The plaquette holonomy of unitary links is unitary. -/
lemma holonomy_unitary (e : Fin n → S) (U : Fin n → S → L N) (hU : ∀ k x, Unitary (U k x))
    (i j : Fin n) (x : S) : Unitary (holonomy e U i j x) := by
  unfold holonomy
  exact unitary_mul (unitary_mul (unitary_mul (hU _ _) (hU _ _)) (unitary_ct (hU _ _)))
    (unitary_ct (hU _ _))

/-- **Wilson's action for matrix links**, summed over ordered plaquettes. -/
noncomputable def wilson (e : Fin n → S) (U : Fin n → S → L N) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, ∑ x, plaq (holonomy e U i j x)

/-- **The Wilson action is gauge invariant.** -/
theorem wilson_gauge (e : Fin n → S) (U : Fin n → S → L N) (g : S → L N)
    (hg : ∀ x, Unitary (g x)) :
    wilson e (fun k => rotateLinks (e k) g (U k)) = wilson e U := by
  unfold wilson plaq
  simp only [wilson_loop_invariant e U g hg]

/-- **The Wilson action is non-negative.** -/
theorem wilson_nonneg (e : Fin n → S) (U : Fin n → S → L N) (hU : ∀ k x, Unitary (U k x)) :
    0 ≤ wilson e U := by
  unfold wilson
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun x _ => plaq_nonneg _ (holonomy_unitary e U hU i j x))

/-- **The Wilson action vanishes exactly on flat links.** -/
theorem wilson_eq_zero_iff (e : Fin n → S) (U : Fin n → S → L N)
    (hU : ∀ k x, Unitary (U k x)) :
    wilson e U = 0 ↔ ∀ i j x, holonomy e U i j x = 1 := by
  have hp := fun i j x => plaq_nonneg _ (holonomy_unitary e U hU i j x)
  unfold wilson
  constructor
  · intro h i j x
    have hs : ∑ i, ∑ j, ∑ x, plaq (holonomy e U i j x) = 0 := by linarith
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun x _ => hp i j x)).mp hs i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      Finset.sum_nonneg fun x _ => hp i j x)).mp h1 j (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp i j x)).mp h2 x
      (Finset.mem_univ _)
    exact (plaq_eq_zero_iff _ (holonomy_unitary e U hU i j x)).mp h3
  · intro h
    simp only [h, (plaq_eq_zero_iff (1 : L N) ⟨by simp, by simp⟩).mpr rfl, Finset.sum_const_zero,
      mul_zero]

omit [Fintype S] in
/-- **Pure-gauge links are flat.** -/
theorem pure_gauge_flat (e : Fin n → S) (g : S → L N) (hg : ∀ x, Unitary (g x)) (i j : Fin n)
    (x : S) :
    holonomy e (fun k => rotateLinks (e k) g (fun _ => 1)) i j x = 1 := by
  rw [holonomy_gauge e (fun _ _ => 1) g hg]
  unfold holonomy
  simp [(hg x).1]

/-- Pure-gauge links have zero action. -/
theorem pure_gauge_action (e : Fin n → S) (g : S → L N) (hg : ∀ x, Unitary (g x)) :
    wilson e (fun k => rotateLinks (e k) g (fun _ => 1)) = 0 := by
  rw [wilson_gauge e (fun _ _ => 1) g hg]
  unfold wilson holonomy
  simp [plaq, trace_one]

/-! ## The abelian case -/

/-- A phase link as a `1 × 1` matrix. -/
noncomputable def phaseLink (θ : ℝ) : L 1 := fun _ _ => Complex.exp (θ * Complex.I)

omit [Fintype S] in
/-- **For `N = 1` the holonomy of phase links is `e^{iF}`.** -/
theorem holonomy_abelian (e : Fin n → S) (a : Fin n → S → ℝ) (i j : Fin n) (x : S) :
    holonomy e (fun k y => phaseLink (a k y)) i j x =
      phaseLink (QLF.LinkAction.F e a i j x) := by
  funext p q
  unfold holonomy
  simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_one, Fin.isValue]
  unfold phaseLink
  simp only [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  unfold QLF.LinkAction.F
  push_cast; ring

/-- **For `N = 1` the matrix action is the compact action of `QLF_CompactLinks`.** -/
theorem wilson_abelian [DecidableEq S] (e : Fin n → S) (a : Fin n → S → ℝ) :
    wilson e (fun k y => phaseLink (a k y)) = QLF.CompactLinks.wilson e a := by
  unfold wilson QLF.CompactLinks.wilson
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun x _ => ?_
  rw [holonomy_abelian]
  unfold plaq phaseLink
  simp only [Matrix.trace, Fin.sum_univ_one]
  rw [Nat.cast_one]
  exact congrArg (1 - ·) (Complex.exp_ofReal_mul_I_re _)

end QLF.NonAbelianAction
