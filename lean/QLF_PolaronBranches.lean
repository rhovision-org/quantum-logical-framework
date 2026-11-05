import Mathlib

/-!
# QLF_PolaronBranches — polaron branches as poles, absent branches as zeros

Issue #207 §10.5 (*polaron branch poles/zeros*). [`QLF_Polarons`](QLF_Polarons.lean) proved that a
polaron is an irreducible shared closure of an open impurity with an open bath. This module gives
that closure its resolvent. An impurity level `ε` shares a closure of amplitude `g_k` with each
bath mode `ω_k`. The impurity's resolvent is `G(E) = 1/f(E)` with

`f(E) = E − ε − Σ_k g_k² / (E − ω_k)`,

the impurity's own kernel plus the round trip through each bath mode (the many-mode form of
[`QLF_SharedClosure`](QLF_SharedClosure.lean)'s `feshbach_entry`).

* **`branch_iff`.** At an energy away from the bath modes, the coupled system has an eigenstate
  exactly when `f(E) = 0`: **the branches are the poles of `G`**.
* **`attractive_exists`.** If the lowest bath mode is coupled, a branch exists below it.
* **`attractive_below`, `repulsive_above`.** A branch below every bath mode lies below the bare
  impurity (the attractive polaron); a branch above every bath mode lies above it (the repulsive
  polaron). Which side is fixed by the sign of the round trip, not chosen.
* **`resolvent_eq`, `zero_at_bath`.** `G = N/D` with `N = Π(E − ω_k)`; at each coupled bath energy
  `N = 0` while `D ≠ 0`, so **`G` has a true zero there**: the impurity cannot appear at a bath
  mode's energy. Absent branches are zeros.
* **`residue_lt_one_iff`, `residue_is_weight`.** A branch carries weight
  `Z = 1/(1 + Σ g_k²/(E − ω_k)²)`, which is the impurity's share of the branch eigenstate and is
  `< 1` exactly when the impurity is coupled; the rest is spread over the bath modes (broadening
  as weight over nearby channels). **`f_deriv`**: `Z = 1/f′(E)`, the residue of `G` at the pole.

The effective mass (the pole's momentum dependence) needs a momentum-labelled bath and is not
here. No axioms.

**Credit.** The impurity-in-a-bath resolvent is Fano's (*Phys. Rev.* **124**, 1866 (1961)) and
Anderson's (*Phys. Rev.* **124**, 41 (1961)); attractive and repulsive polaron branches are the
Fermi-polaron picture reviewed by Massignan, Zaccanti and Bruun (*Rep. Prog. Phys.* **77**, 034401
(2014)). Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.PolaronBranches

open Finset

variable {ι : Type*} [Fintype ι] (ε : ℝ) (ω g : ι → ℝ)

/-- The impurity's inverse resolvent: its own kernel plus the round trip through each bath mode. -/
noncomputable def f (E : ℝ) : ℝ := E - ε - ∑ k, g k ^ 2 / (E - ω k)

/-- The eigen-equations of the impurity ⊕ bath system, impurity amplitude `v₀`, bath amplitudes `w`. -/
def Eig (E v₀ : ℝ) (w : ι → ℝ) : Prop :=
  ε * v₀ + ∑ k, g k * w k = E * v₀ ∧ ∀ k, g k * v₀ + ω k * w k = E * w k

/-- **The branches are the poles of the impurity resolvent.** -/
theorem branch_iff (E : ℝ) (hE : ∀ k, E ≠ ω k) :
    (∃ v₀ w, (v₀ ≠ 0 ∨ w ≠ 0) ∧ Eig ε ω g E v₀ w) ↔ f ε ω g E = 0 := by
  have hne : ∀ k, E - ω k ≠ 0 := fun k => sub_ne_zero.mpr (hE k)
  constructor
  · rintro ⟨v₀, w, hnz, h1, h2⟩
    have hw : ∀ k, w k = g k * v₀ / (E - ω k) := fun k => by
      rw [eq_div_iff (hne k)]; linear_combination (-1 : ℝ) * h2 k
    have hv : v₀ ≠ 0 := by
      rintro rfl
      rcases hnz with h | h
      · exact h rfl
      · exact h (funext fun k => by rw [hw k]; simp)
    have hsum : ∑ k, g k * w k = v₀ * ∑ k, g k ^ 2 / (E - ω k) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
      rw [hw k]; field_simp
    rw [hsum] at h1
    have : v₀ * f ε ω g E = 0 := by unfold f; linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left hv
  · intro hf
    refine ⟨1, fun k => g k / (E - ω k), Or.inl one_ne_zero, ?_, fun k => ?_⟩
    · have : ∑ k, g k * (g k / (E - ω k)) = ∑ k, g k ^ 2 / (E - ω k) :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [this]; unfold f at hf; linarith
    · field_simp [hne k]; ring

lemma sum_neg_of (E : ℝ) (hE : ∀ k, E < ω k) (hg : ∃ k, g k ≠ 0) :
    ∑ k, g k ^ 2 / (E - ω k) < 0 := by
  obtain ⟨j, hj⟩ := hg
  apply Finset.sum_neg'
  · intro k _; exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hE k])
  · exact ⟨j, Finset.mem_univ _, div_neg_of_pos_of_neg (by positivity) (by linarith [hE j])⟩

lemma sum_pos_of (E : ℝ) (hE : ∀ k, ω k < E) (hg : ∃ k, g k ≠ 0) :
    0 < ∑ k, g k ^ 2 / (E - ω k) := by
  obtain ⟨j, hj⟩ := hg
  apply Finset.sum_pos'
  · intro k _; exact div_nonneg (sq_nonneg _) (by linarith [hE k])
  · exact ⟨j, Finset.mem_univ _, div_pos (by positivity) (by linarith [hE j])⟩

/-- **The attractive branch lies below the bare impurity.** -/
theorem attractive_below (E : ℝ) (hf : f ε ω g E = 0) (hE : ∀ k, E < ω k)
    (hg : ∃ k, g k ≠ 0) : E < ε := by
  have := sum_neg_of ω g E hE hg
  unfold f at hf; linarith

/-- **The repulsive branch lies above the bare impurity.** -/
theorem repulsive_above (E : ℝ) (hf : f ε ω g E = 0) (hE : ∀ k, ω k < E)
    (hg : ∃ k, g k ≠ 0) : ε < E := by
  have := sum_pos_of ω g E hE hg
  unfold f at hf; linarith

variable [DecidableEq ι]

/-- **The attractive branch exists**: if the lowest bath mode `ω_j` is coupled, `f` has a root
    below it. -/
theorem attractive_exists (j : ι) (hj : ∀ k, ω j ≤ ω k) (hg : g j ≠ 0) :
    ∃ E, E < ω j ∧ f ε ω g E = 0 := by
  set S := ∑ k, g k ^ 2
  set c := |ε - ω j| + 2
  have hc : 0 < c := by positivity
  have hgj : 0 < g j ^ 2 := by positivity
  set δ := min 1 (g j ^ 2 / c)
  have hδ : 0 < δ := lt_min one_pos (div_pos hgj hc)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  set E₁ := min (ε - S - 1) (ω j - 1)
  set E₂ := ω j - δ
  have hE₁ : E₁ ≤ ω j - 1 := min_le_right _ _
  have h12 : E₁ ≤ E₂ := by linarith
  -- continuity on the interval
  have hlt : ∀ x ∈ Set.Icc E₁ E₂, ∀ k, x - ω k ≠ 0 := fun x hx k => by
    have := hx.2; have := hj k; intro h; linarith
  have hcont : ContinuousOn (f ε ω g) (Set.Icc E₁ E₂) := by
    unfold f
    refine (continuousOn_id.sub continuousOn_const).sub
      (continuousOn_finsetSum _ fun k _ => ?_)
    exact continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun x hx => hlt x hx k
  -- f(E₁) < 0
  have hf1 : f ε ω g E₁ < 0 := by
    have hb : ∀ k ∈ (univ : Finset ι), -(g k ^ 2) ≤ g k ^ 2 / (E₁ - ω k) := fun k _ => by
      have hd : E₁ - ω k ≤ -1 := by linarith [hj k]
      rw [le_div_iff_of_neg (by linarith)]
      nlinarith [sq_nonneg (g k)]
    have := Finset.sum_le_sum hb
    rw [Finset.sum_neg_distrib] at this
    unfold f
    have : E₁ ≤ ε - S - 1 := min_le_left _ _
    linarith
  -- f(E₂) > 0
  have hf2 : 0 < f ε ω g E₂ := by
    have hrest : ∀ k ∈ (univ : Finset ι).erase j, g k ^ 2 / (E₂ - ω k) ≤ 0 := fun k _ =>
      div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hj k])
    have hs := Finset.add_sum_erase (univ : Finset ι) (fun k => g k ^ 2 / (E₂ - ω k))
      (Finset.mem_univ j)
    have hr := Finset.sum_nonpos hrest
    have hjt : g j ^ 2 / (E₂ - ω j) = -(g j ^ 2 / δ) := by
      rw [show E₂ - ω j = -δ by ring, div_neg]
    have hbig : c ≤ g j ^ 2 / δ := by
      rw [le_div_iff₀ hδ]
      calc c * δ ≤ c * (g j ^ 2 / c) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
        _ = g j ^ 2 := by field_simp
    have hab : ε - ω j ≤ |ε - ω j| := le_abs_self _
    unfold f
    linarith
  obtain ⟨E, hE, hfE⟩ := intermediate_value_Icc h12 hcont ⟨hf1.le, hf2.le⟩
  exact ⟨E, by linarith [hE.2], hfE⟩

/-- Numerator of the impurity resolvent. -/
noncomputable def N (E : ℝ) : ℝ := ∏ k, (E - ω k)
/-- Denominator of the impurity resolvent. -/
noncomputable def D (E : ℝ) : ℝ :=
  (E - ε) * N ω E - ∑ k, g k ^ 2 * ∏ l ∈ univ.erase k, (E - ω l)

lemma D_eq (E : ℝ) (hE : ∀ k, E ≠ ω k) : D ε ω g E = N ω E * f ε ω g E := by
  have hne : ∀ k, E - ω k ≠ 0 := fun k => sub_ne_zero.mpr (hE k)
  unfold D f N
  rw [mul_sub, mul_sub, Finset.mul_sum]
  have : ∀ k ∈ (univ : Finset ι), g k ^ 2 * ∏ l ∈ univ.erase k, (E - ω l) =
      (∏ k, (E - ω k)) * (g k ^ 2 / (E - ω k)) := by
    intro k hk
    rw [← Finset.mul_prod_erase univ (fun l => E - ω l) hk]
    field_simp [hne k]
  rw [Finset.sum_congr rfl this]; ring

/-- **The resolvent is `N/D`.** -/
theorem resolvent_eq (E : ℝ) (hE : ∀ k, E ≠ ω k) :
    N ω E / D ε ω g E = 1 / f ε ω g E := by
  have hN : N ω E ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hE k)
  rw [D_eq ε ω g E hE, div_mul_eq_div_div, div_self hN]

/-- **A coupled bath mode is a true zero of the impurity resolvent**: `N = 0`, `D ≠ 0`. -/
theorem zero_at_bath (hω : Function.Injective ω) (j : ι) (hg : g j ≠ 0) :
    N ω (ω j) = 0 ∧ D ε ω g (ω j) ≠ 0 := by
  have hN : N ω (ω j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  refine ⟨hN, ?_⟩
  unfold D
  rw [hN, mul_zero, zero_sub, neg_ne_zero]
  rw [Finset.sum_eq_single j]
  · refine mul_ne_zero (pow_ne_zero 2 hg) (Finset.prod_ne_zero_iff.mpr fun l hl => ?_)
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hl) (hω h).symm
  · intro k _ hk
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hk h.symm, Finset.mem_univ j⟩)
      (sub_self _), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- A branch's weight `Z = 1/(1 + Σ g_k²/(E − ω_k)²)`. -/
noncomputable def Z (E : ℝ) : ℝ := 1 / (1 + ∑ k, (g k / (E - ω k)) ^ 2)

omit [DecidableEq ι] in
lemma one_le_den (E : ℝ) : 1 ≤ 1 + ∑ k, (g k / (E - ω k)) ^ 2 := by
  have := Finset.sum_nonneg (fun k (_ : k ∈ (univ : Finset ι)) => sq_nonneg (g k / (E - ω k)))
  linarith

omit [DecidableEq ι] in
/-- **The weight is the impurity's share of the branch eigenstate.** -/
theorem residue_is_weight (E : ℝ) :
    Z ω g E = 1 ^ 2 / (1 ^ 2 + ∑ k, (g k / (E - ω k)) ^ 2) := by
  simp [Z]

omit [DecidableEq ι] in
/-- **The weight is below one exactly when the impurity is coupled.** -/
theorem residue_lt_one_iff (E : ℝ) (hE : ∀ k, E ≠ ω k) :
    Z ω g E < 1 ↔ ∃ k, g k ≠ 0 := by
  have hd := one_le_den ω g E
  unfold Z
  rw [div_lt_one (by linarith)]
  constructor
  · intro h
    by_contra hc
    simp only [not_exists, not_not] at hc
    simp [hc] at h
  · rintro ⟨j, hj⟩
    have : 0 < ∑ k, (g k / (E - ω k)) ^ 2 :=
      Finset.sum_pos' (fun k _ => sq_nonneg _)
        ⟨j, Finset.mem_univ _, by
          have := div_ne_zero hj (sub_ne_zero.mpr (hE j)); positivity⟩
    linarith

omit [DecidableEq ι] in
/-- **`Z = 1/f′(E)`**: the weight is the residue of the resolvent at the pole. -/
theorem f_deriv (E : ℝ) (hE : ∀ k, E ≠ ω k) :
    HasDerivAt (f ε ω g) (1 + ∑ k, (g k / (E - ω k)) ^ 2) E := by
  have hne : ∀ k, E - ω k ≠ 0 := fun k => sub_ne_zero.mpr (hE k)
  have hk : ∀ k ∈ (univ : Finset ι), HasDerivAt (fun x => g k ^ 2 / (x - ω k))
      (-(g k / (E - ω k)) ^ 2) E := by
    intro k _
    have h := (hasDerivAt_const E (g k ^ 2)).div ((hasDerivAt_id' E).sub_const (ω k)) (hne k)
    exact h.congr_deriv (by rw [zero_mul, zero_sub, mul_one, neg_div, div_pow])
  have h := ((hasDerivAt_id' E).sub_const ε).fun_sub (HasDerivAt.fun_sum hk)
  show HasDerivAt (fun x => x - ε - ∑ k, g k ^ 2 / (x - ω k)) _ E
  exact h.congr_deriv (by rw [Finset.sum_neg_distrib, sub_neg_eq_add])

end QLF.PolaronBranches
