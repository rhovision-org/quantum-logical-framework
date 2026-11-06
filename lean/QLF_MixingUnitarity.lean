import Mathlib

/-!
# QLF_MixingUnitarity — CKM and PMNS as restrictions of channel unitarity

Issue #207 (*CKM/PMNS as restrictions of general channel unitarity*). A mixing matrix is the
block of a unitary channel map that connects the flavour channels we can see. Channel unitarity
(`QLF_ClosureUnitarity`, [`QLF_OpticalTheorem`](QLF_OpticalTheorem.lean)) then says three things
about the block, and they are the three standard tests of CKM and PMNS.

* **`column_split`, `block_unitary_iff`.** For a unitary `U` on visible ⊕ hidden channels, each
  visible column of the visible block has norm `1 − (leak into hidden channels)`, and the block is
  unitary on its columns exactly when nothing leaks. A first-row deficit
  `|V_ud|² + |V_us|² + |V_ub|² < 1` is therefore a leak into channels outside the block, the same
  balance as a resonance's ([`QLF_Resonance`](QLF_Resonance.lean)).
* **`triangle_closes`.** For a `3 × 3` unitary `V`, two distinct rows give three complex numbers
  `V_{ik} V̄_{jk}` that sum to zero: a **unitarity triangle**. Orthogonality of two flavour
  channels is a closure, zero net amplitude.
* **`closed_triangle_area`, `jarlskog_invariant`.** A closed triangle has the same signed area from
  every pair of sides, `Im(a b̄) = Im(b c̄) = Im(c ā)`. So the Jarlskog invariant
  `J = Im(t₀ t̄₁)` of a triangle does not depend on which two sides are used; `J = 0` exactly when
  the triangle is flat (`jarlskog_zero_iff_flat`). CP violation is the area a closure encloses.

No axioms.

**Credit.** Cabibbo (*Phys. Rev. Lett.* **10**, 531 (1963)); Kobayashi and Maskawa (*Prog. Theor.
Phys.* **49**, 652 (1973)); Pontecorvo (*Sov. Phys. JETP* **26**, 984 (1968)); Maki, Nakagawa and
Sakata (*Prog. Theor. Phys.* **28**, 870 (1962)); the invariant is Jarlskog's (*Phys. Rev. Lett.*
**55**, 1039 (1985)). Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.MixingUnitarity

open Matrix Complex

/-! ## The visible block of a unitary channel map -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **A visible column's norm is one minus its leak into hidden channels.** -/
theorem column_split (U : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (hU : Uᴴ * U = 1) (j : ι) :
    ∑ i, normSq (U (Sum.inl i) (Sum.inl j)) + ∑ k, normSq (U (Sum.inr k) (Sum.inl j)) = 1 := by
  have h := congrFun (congrFun hU (Sum.inl j)) (Sum.inl j)
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, Matrix.one_apply_eq]
    at h
  have e : ∀ z : ℂ, star z * z = ((normSq z : ℝ) : ℂ) := fun z => by
    rw [normSq_eq_conj_mul_self]; rfl
  simp only [e] at h
  exact_mod_cast h

/-- **The visible block is unitary on its columns exactly when nothing leaks.** -/
theorem block_unitary_iff (U : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (hU : Uᴴ * U = 1) :
    (∀ j, ∑ i, normSq (U (Sum.inl i) (Sum.inl j)) = 1) ↔
      ∀ k j, U (Sum.inr k) (Sum.inl j) = 0 := by
  constructor
  · intro h k j
    have hs := column_split U hU j
    rw [h j] at hs
    have h0 : ∑ k, normSq (U (Sum.inr k) (Sum.inl j)) = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => normSq_nonneg _)).mp h0 k
      (Finset.mem_univ _)
    exact normSq_eq_zero.mp this
  · intro h j
    have hs := column_split U hU j
    simp only [h, map_zero, Finset.sum_const_zero, add_zero] at hs
    exact hs

/-! ## Unitarity triangles -/

/-- **Two distinct rows of a unitary close**: `Σ_k V_{ik} V̄_{jk} = 0`. -/
theorem triangle_closes (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : V * Vᴴ = 1) {i j : Fin 3}
    (hij : i ≠ j) :
    V i 0 * star (V j 0) + V i 1 * star (V j 1) + V i 2 * star (V j 2) = 0 := by
  have h := congrFun (congrFun hV i) j
  simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_three, Matrix.one_apply_ne hij]
    at h
  exact h

/-- **A closed triangle has one signed area.** -/
theorem closed_triangle_area (a b c : ℂ) (h : a + b + c = 0) :
    (a * star b).im = (b * star c).im ∧ (b * star c).im = (c * star a).im := by
  have hc : c = -a - b := by linear_combination h
  subst hc
  simp only [Complex.mul_im, star_def, conj_re, conj_im, sub_re, neg_re, sub_im, neg_im]
  constructor <;> ring

/-- **The Jarlskog invariant does not depend on the pair of sides.** -/
theorem jarlskog_invariant (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : V * Vᴴ = 1) {i j : Fin 3}
    (hij : i ≠ j) :
    (V i 0 * star (V j 0) * star (V i 1 * star (V j 1))).im =
        (V i 1 * star (V j 1) * star (V i 2 * star (V j 2))).im ∧
      (V i 1 * star (V j 1) * star (V i 2 * star (V j 2))).im =
        (V i 2 * star (V j 2) * star (V i 0 * star (V j 0))).im :=
  closed_triangle_area _ _ _ (triangle_closes V hV hij)

/-- **No area, no CP violation**: the invariant vanishes exactly when two sides are collinear
    over the reals. -/
theorem jarlskog_zero_iff_flat (a b : ℂ) (hb : b ≠ 0) :
    (a * star b).im = 0 ↔ ∃ r : ℝ, a = r * b := by
  constructor
  · intro h
    set x := (a * star b).re with hx
    refine ⟨x / normSq b, ?_⟩
    have hn : (normSq b : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos.mpr hb).ne'
    have hab : a * star b = (x : ℂ) := by
      apply Complex.ext
      · simp [hx]
      · rw [Complex.ofReal_im]; exact h
    have key : a * (star b * b) = (x : ℂ) * b := by rw [← mul_assoc, hab]
    rw [star_def, ← normSq_eq_conj_mul_self] at key
    rw [Complex.ofReal_div]
    field_simp
    linear_combination key
  · rintro ⟨r, rfl⟩
    rw [mul_assoc, star_def, mul_conj]
    simp

end QLF.MixingUnitarity
