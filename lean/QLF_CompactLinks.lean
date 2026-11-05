import QLF_FieldEnergy

/-!
# QLF_CompactLinks — compact links: the Wilson plaquette action

Issue #207. The walk sees a link phase only through `e^{ia}`, so `a` and `a + 2π` are the same link
for it. The field action of [`QLF_LinkAction`](QLF_LinkAction.lean) was the quadratic one,
`¼ΣF²`, which does not share that periodicity. This module uses Wilson's compact action
`W(a) = ½ Σ (1 − cos F)`, summed over ordered plaquettes, which does, and shows that its first
variation is still exact.

* **`ip_curl`.** For any antisymmetric plaquette field `G`, `⟨B, curl G⟩ = ½ Σ G·F(B)`: the summation
  by parts of [`QLF_FieldEnergy`](QLF_FieldEnergy.lean), for any `G`.
* **`F_bump_cases`.** When no axis step is zero, a single link enters each plaquette at most once,
  so the plaquette of a unit link variation is `−1`, `0` or `1`.
* **`wilson_variation`.** Moving the single link `(k, y)` by `±ε`,
  `W(a + εδ) − W(a − εδ) = 2 sin ε · curl(sin F)(k, y)`, exactly, for every `ε`. The compact
  restoring force is `curl(sin F)`.
* **`walk_response_sin`.** The walk responds to the same change with the same factor:
  `⟨U_a ψ, U_{a+εδ} ψ⟩ − ⟨U_a ψ, U_{a−εδ} ψ⟩ = 2i sin ε · J(y)`.
  So the compact Ampère law `curl(sin F) = J` is where the two responses balance, for every `ε`,
  with no small-angle step.
* **`wilson_periodic`, `walk_periodic`, `wilson_gauge`.** Both the action and the walk are
  unchanged when one link phase moves by `2π`, and the action is gauge invariant.
* **`compact_conserves_current`, `compact_gauss_preserved`.** The compact Ampère law forces
  `div J = 0`, and the compact update `E' = E + τ curl(sin F) − J` keeps Gauss's law, as the
  quadratic one did.

Since `1 − cos F = F²/2 − F⁴/24 + …`, the Wilson action agrees with `¼ΣF²` for small plaquettes.
**Not here.** The compact field's energy and stability (`sin F` is not linear, so `QLF_FieldEnergy`
does not apply), and non-abelian links. No axioms.

**Credit.** The compact plaquette action is Wilson's (*Phys. Rev. D* **10**, 2445 (1974)); its
Hamiltonian form is Kogut and Susskind's (*Phys. Rev. D* **11**, 395 (1975)).
-/

namespace QLF.CompactLinks

open QLF.LinkAction (F F_antisymm F_linear bump gaugeShift F_gauge)
open QLF.FieldEnergy (ip)
open QLF.LocalGauge (ph)
open Real

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {n : ℕ}

omit [DecidableEq S] in
/-- **Summation by parts** for any antisymmetric plaquette field `G`. -/
theorem ip_curl (e : Fin n → S) (G : Fin n → Fin n → S → ℝ) (hG : ∀ i j x, G j i x = -G i j x)
    (B : Fin n → S → ℝ) :
    ip B (Maxwell.curl e G) = (1 / 2) * ∑ i, ∑ j, ∑ x, G i j x * F e B i j x := by
  have hT : ip B (Maxwell.curl e G) = ∑ i, ∑ j, ∑ x, G i j x * (B i x - B i (x + e j)) := by
    unfold ip Maxwell.curl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hs : ∑ x, B i x * G i j (x - e j) = ∑ x, B i (x + e j) * G i j x :=
      Fintype.sum_equiv (Equiv.subRight (e j)) _ _ (fun x => by simp)
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hs]
    congr 1
    · exact Finset.sum_congr rfl (fun x _ => by ring)
    · exact Finset.sum_congr rfl (fun x _ => by ring)
  have hT' : ∑ i, ∑ j, ∑ x, G i j x * (B j (x + e i) - B j x) =
      ∑ i, ∑ j, ∑ x, G i j x * (B i x - B i (x + e j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun x _ => ?_)))
    rw [hG i j x]; ring
  have hF : ∀ i j x, F e B i j x = (B i x - B i (x + e j)) + (B j (x + e i) - B j x) := by
    intros; simp only [F]; ring
  rw [hT]
  simp only [hF, mul_add, Finset.sum_add_distrib, hT']
  ring

omit [AddCommGroup S] in
/-- Pairing with a unit link variation reads off one link. -/
lemma ip_bump (k : Fin n) (y : S) (X : Fin n → S → ℝ) : ip (bump k y) X = X k y := by
  unfold ip bump
  have : ∀ i, ∑ x, (if i = k ∧ x = y then (1 : ℝ) else 0) * X i x = if i = k then X i y else 0 := by
    intro i
    by_cases h : i = k
    · subst h; simp
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Fintype S] in
/-- **A unit link variation enters each plaquette at most once.** -/
theorem F_bump_cases (e : Fin n → S) (he : ∀ i, e i ≠ 0) (k : Fin n) (y : S) (i j : Fin n)
    (x : S) :
    F e (bump k y) i j x = -1 ∨ F e (bump k y) i j x = 0 ∨ F e (bump k y) i j x = 1 := by
  by_cases hij : i = j
  · subst hij; right; left; simp only [F]; ring
  have hj : ∀ z : S, z + e j ≠ z := fun z h => he j (by simpa using h)
  have hi : ∀ z : S, z + e i ≠ z := fun z h => he i (by simpa using h)
  simp only [F, bump]
  by_cases hki : i = k <;> by_cases hkj : j = k
  · exact absurd (hki.trans hkj.symm) hij
  · simp only [hki, hkj, true_and, false_and, ite_false]
    split_ifs with h1 h2 <;> first | (exfalso; exact hj x (h2.trans h1.symm)) | norm_num
  · simp only [hki, hkj, true_and, false_and, ite_false]
    split_ifs with h1 h2 <;> first | (exfalso; exact hi x (h1.trans h2.symm)) | norm_num
  · simp [hki, hkj]

/-- Wilson's compact plaquette action, summed over ordered plaquettes. -/
noncomputable def wilson (e : Fin n → S) (a : Fin n → S → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, ∑ x, (1 - cos (F e a i j x))

/-- The compact field strength `sin F`. -/
noncomputable def sinF (e : Fin n → S) (a : Fin n → S → ℝ) : Fin n → Fin n → S → ℝ :=
  fun i j x => sin (F e a i j x)

omit [Fintype S] [DecidableEq S] in
lemma sinF_antisymm (e : Fin n → S) (a : Fin n → S → ℝ) (i j : Fin n) (x : S) :
    sinF e a j i x = -sinF e a i j x := by
  simp only [sinF, F_antisymm e a i j x, Real.sin_neg]

lemma plaquette_diff (Fa ε f : ℝ) (hf : f = -1 ∨ f = 0 ∨ f = 1) :
    (1 - cos (Fa + ε * f)) - (1 - cos (Fa + -ε * f)) = 2 * sin ε * (sin Fa * f) := by
  rcases hf with h | h | h <;> subst h <;>
    simp only [mul_one, mul_neg, neg_neg, mul_zero, add_zero, Real.cos_add,
      sub_eq_add_neg, Real.cos_neg, Real.sin_neg] <;> ring

/-- **The first variation of the Wilson action is exact**:
    `W(a + εδ) − W(a − εδ) = 2 sin ε · curl(sin F)(k, y)` for every `ε`. -/
theorem wilson_variation (e : Fin n → S) (he : ∀ i, e i ≠ 0) (a : Fin n → S → ℝ) (k : Fin n)
    (y : S) (ε : ℝ) :
    wilson e (fun l z => a l z + ε * bump k y l z) -
        wilson e (fun l z => a l z + -ε * bump k y l z) =
      2 * sin ε * Maxwell.curl e (sinF e a) k y := by
  unfold wilson
  simp only [F_linear]
  rw [← mul_sub]
  simp only [← Finset.sum_sub_distrib]
  simp only [fun i j x => plaquette_diff (F e a i j x) ε _ (F_bump_cases e he k y i j x)]
  have hsum : ∑ i, ∑ j, ∑ x, sin (F e a i j x) * F e (bump k y) i j x =
      2 * Maxwell.curl e (sinF e a) k y := by
    have h := ip_curl e (sinF e a) (sinF_antisymm e a) (bump k y)
    rw [ip_bump] at h
    rw [h]; simp only [sinF]; ring
  simp only [← Finset.mul_sum]
  rw [hsum]; ring

/-- The Wilson action is unchanged when one link moves by `2π`. -/
theorem wilson_periodic (e : Fin n → S) (he : ∀ i, e i ≠ 0) (a : Fin n → S → ℝ) (k : Fin n)
    (y : S) : wilson e (fun l z => a l z + (2 * π) * bump k y l z) = wilson e a := by
  unfold wilson
  simp only [F_linear]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun x _ => ?_)))
  rcases F_bump_cases e he k y i j x with h | h | h <;> rw [h]
  · rw [show F e a i j x + 2 * π * -1 = F e a i j x - 2 * π by ring, Real.cos_sub_two_pi]
  · simp
  · rw [mul_one, Real.cos_add_two_pi]

omit [DecidableEq S] in
/-- The Wilson action is gauge invariant. -/
theorem wilson_gauge (e : Fin n → S) (θ : S → ℝ) (a : Fin n → S → ℝ) :
    wilson e (gaugeShift e θ a) = wilson e a := by
  simp only [wilson, F_gauge]

/-! ## The walk responds with the same factor -/

lemma ph_sub_neg (ε : ℝ) : ph ε - ph (-ε) = 2 * sin ε * Complex.I := by
  have a1 : (ph ε).re = cos ε := Complex.exp_ofReal_mul_I_re ε
  have a2 : (ph (-ε)).re = cos (-ε) := Complex.exp_ofReal_mul_I_re (-ε)
  have b1 : (ph ε).im = sin ε := Complex.exp_ofReal_mul_I_im ε
  have b2 : (ph (-ε)).im = sin (-ε) := Complex.exp_ofReal_mul_I_im (-ε)
  apply Complex.ext
  · rw [Complex.sub_re, a1, a2, Real.cos_neg]
    simp [Complex.mul_re]
  · rw [Complex.sub_im, b1, b2, Real.sin_neg]
    simp [Complex.mul_im, -Complex.ofReal_sin]
    ring

lemma ph_add_two_pi (r : ℝ) : ph (r + 2 * π) = ph r := by
  unfold ph
  rw [show ((r + 2 * π : ℝ) : ℂ) * Complex.I = r * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma ph_sub_two_pi (r : ℝ) : ph (r - 2 * π) = ph r := by
  rw [← ph_add_two_pi (r - 2 * π)]; ring_nf

/-- **The walk's response is `2i sin ε` times its current**, the same factor as the field's. -/
theorem walk_response_sin (t : QLF.Twist) (e : S) (a : S → ℝ) (ψ : S → QLF.LocalGauge.V) (y : S)
    (ε : ℝ) :
    WalkCoupling.ip (LatticeGauge.axisStep t e a ψ)
        (LatticeGauge.axisStep t e (WalkCoupling.bumpLink a ε y) ψ) -
        WalkCoupling.ip (LatticeGauge.axisStep t e a ψ)
          (LatticeGauge.axisStep t e (WalkCoupling.bumpLink a (-ε) y) ψ) =
      2 * sin ε * Complex.I * Maxwell.current t e ψ y := by
  rw [WalkCoupling.link_response, ph_sub_neg]

omit [Fintype S] in
/-- **The walk does not see a `2π` shift of one link.** -/
theorem walk_periodic (t : QLF.Twist) (e : S) (a : S → ℝ) (ψ : S → QLF.LocalGauge.V) (y : S) :
    LatticeGauge.axisStep t e (WalkCoupling.bumpLink a (2 * π) y) ψ =
      LatticeGauge.axisStep t e a ψ := by
  funext x
  unfold LatticeGauge.axisStep WalkCoupling.bumpLink
  congr 2
  · split_ifs
    · exact ph_add_two_pi _
    · simp
  · split_ifs
    · rw [neg_add, ← sub_eq_add_neg]; exact ph_sub_two_pi _
    · simp

/-! ## Current conservation and Gauss's law -/

omit [Fintype S] [DecidableEq S] in
/-- **The compact Ampère law forces a conserved current.** -/
theorem compact_conserves_current (e : Fin n → S) (a J : Fin n → S → ℝ)
    (h : ∀ k y, Maxwell.curl e (sinF e a) k y = J k y) (x : S) : Maxwell.div e J x = 0 := by
  have : J = Maxwell.curl e (sinF e a) := by funext k y; exact (h k y).symm
  rw [this]; exact Maxwell.div_curl e _ (sinF_antisymm e a) x

omit [Fintype S] [DecidableEq S] in
/-- **The compact update keeps Gauss's law**: if `div E = ρ` and the charge is conserved, then
    `E' = E + τ curl(sin F) − J` has `div E' = ρ'`. -/
theorem compact_gauss_preserved (e : Fin n → S) (τ : ℝ) (a E J : Fin n → S → ℝ) (ρ ρ' : S → ℝ)
    (x : S) (hgauss : Maxwell.div e E x = ρ x) (hcont : ρ' x - ρ x + Maxwell.div e J x = 0) :
    Maxwell.div e (fun i y => E i y + τ * Maxwell.curl e (sinF e a) i y - J i y) x = ρ' x := by
  have hc : (fun i y => E i y + τ * Maxwell.curl e (sinF e a) i y - J i y) =
      fun i y => E i y + Maxwell.curl e (fun i j z => τ * sinF e a i j z) i y - J i y := by
    funext i y; simp only [Maxwell.curl, Finset.mul_sum, mul_sub]
  rw [hc]
  exact Maxwell.gauss_preserved e E J _ (fun i j z => by rw [sinF_antisymm]; ring) ρ ρ' x
    hgauss hcont

end QLF.CompactLinks
