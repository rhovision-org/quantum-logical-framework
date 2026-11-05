import QLF_TsirelsonBound

/-!
# QLF_JointClosure — the joint closure of two spins is the singlet, and it saturates Tsirelson

Issue #207. [`QLF_Tsirelson`](QLF_Tsirelson.lean) and [`QLF_TsirelsonBound`](QLF_TsirelsonBound.lean)
proved that the CHSH value of any state is at most `2√2`, and that a twist pair reaches it with
some state. This module names the state and says why it is that one.

A two-site state `ψ` is a **joint closure** when the two sites' actions cancel on every axis:
`(σₐ ⊗ 1 + 1 ⊗ σₐ) ψ = 0` for `a = x, y, z`. That is ZFA for a pair: zero net action on each axis.

* **`singlet_trace`.** For every `2 × 2` matrix `X`, `(X ⊗ 1 + 1 ⊗ X) s = tr X · s` on the singlet
  `s = |01⟩ − |10⟩`. So every traceless action cancels on `s`: **`singlet_closed`**.
* **`closed_iff_singlet`.** Conversely, a state whose `x` and `z` actions both cancel is a
  multiple of `s`. **The joint closure is unique: it is the singlet.**
* **`singlet_corr`.** `⟨s| X ⊗ Y |s⟩ = tr X tr Y − tr(XY)`: on traceless observables the
  correlation is `−tr(XY)`, perfect anticorrelation along any shared axis.
* **`singlet_bell_pair`, `singlet_chsh`, `singlet_saturates`.** With `a₀ = σz`, `a₁ = σx` and
  `b₀, b₁ = −(σz ± σx)/√2`, the CHSH expectation on `s` is `2√2 ⟨s, s⟩`: **equality** in
  `tsirelson_bound`.

So the state that reaches Tsirelson's bound is not a choice. It is the only state whose two halves
close together on every axis, and the quantum excess over Bell's `2` is what that joint closure
carries. No axioms.

**Credit.** The singlet's correlation `−a·b` and its maximal CHSH violation are Bell's (*Physics* **1**,
195 (1964)) and Clauser, Horne, Shimony and Holt's (*Phys. Rev. Lett.* **23**, 880 (1969)); the
bound is Cirel'son's (*Lett. Math. Phys.* **4**, 93 (1980)). The singlet as the unique state of
zero total spin is standard angular-momentum addition. Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.JointClosure

open Matrix QLF.Tsirelson

/-- The singlet `|01⟩ − |10⟩`. -/
def s : Fin 2 × Fin 2 → ℂ := fun ij => if ij = (0, 1) then 1 else if ij = (1, 0) then -1 else 0

/-- The joint action of `X` on both sites. -/
noncomputable def joint (X : Matrix (Fin 2) (Fin 2) ℂ) : Q := onA X + onB X

/-- **Every action meets the singlet as its trace.** -/
theorem singlet_trace (X : Matrix (Fin 2) (Fin 2) ℂ) : joint X *ᵥ s = trace X • s := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [joint, onA, onB, s, mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, kroneckerMap_apply, trace] <;> ring

/-- **Every traceless action cancels on the singlet.** -/
theorem singlet_closed (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : trace X = 0) : joint X *ᵥ s = 0 := by
  rw [singlet_trace, hX, zero_smul]

theorem closed_x : joint σx *ᵥ s = 0 := singlet_closed _ (by simp [σx, trace, Fin.sum_univ_two])
theorem closed_y : joint σy *ᵥ s = 0 := singlet_closed _ (by simp [σy, trace, Fin.sum_univ_two])
theorem closed_z : joint σz *ᵥ s = 0 := singlet_closed _ (by simp [σz, trace, Fin.sum_univ_two])

/-- **The joint closure is the singlet**: cancelling on the `x` and `z` axes forces `ψ ∝ s`. -/
theorem closed_iff_singlet (ψ : Fin 2 × Fin 2 → ℂ) :
    (joint σx *ᵥ ψ = 0 ∧ joint σz *ᵥ ψ = 0) ↔ ψ = ψ (0, 1) • s := by
  constructor
  · rintro ⟨hx, hz⟩
    have z00 := congrFun hz (0, 0)
    have z11 := congrFun hz (1, 1)
    have x01 := congrFun hx (0, 0)
    simp [joint, onA, onB, σx, σz, mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, kroneckerMap_apply] at z00 z11 x01
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [s, z00, z11] <;> linear_combination x01
  · intro h
    rw [h, mulVec_smul, mulVec_smul, closed_x, closed_z, smul_zero]
    exact ⟨rfl, rfl⟩

/-- **The singlet correlation**: `⟨s| X ⊗ Y |s⟩ = tr X tr Y − tr(XY)`. -/
theorem singlet_corr (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    star s ⬝ᵥ ((onA X * onB Y) *ᵥ s) = trace X * trace Y - trace (X * Y) := by
  simp [onA, onB, s, mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, kroneckerMap_apply, trace]
  ring

theorem singlet_norm : star s ⬝ᵥ s = 2 := by
  simp [s, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; norm_num

/-- `√2` as a complex number. -/
noncomputable def r : ℂ := (Real.sqrt 2 : ℂ)

lemma r_sq : r * r = 2 := by
  simp only [r]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma star_r : star r = r := Complex.conj_ofReal _

/-- Bob's two observables, `−(σz ± σx)/√2`. -/
noncomputable def b0 : Matrix (Fin 2) (Fin 2) ℂ := -(r / 2) • (σz + σx)
noncomputable def b1 : Matrix (Fin 2) (Fin 2) ℂ := -(r / 2) • (σz - σx)

lemma b0_sq : b0 * b0 = 1 := by
  have h := r_sq
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [b0, σz, σx, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h / 2

lemma b1_sq : b1 * b1 = 1 := by
  have h := r_sq
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [b1, σz, σx, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h / 2

lemma σx_herm : σxᴴ = σx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σx]
lemma σz_herm : σzᴴ = σz := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σz]

lemma b0_herm : b0ᴴ = b0 := by
  simp only [b0, conjTranspose_smul, conjTranspose_add, σx_herm, σz_herm, star_neg, star_div₀,
    star_r]; congr 1; simp

lemma b1_herm : b1ᴴ = b1 := by
  simp only [b1, conjTranspose_smul, conjTranspose_sub, σx_herm, σz_herm, star_neg, star_div₀,
    star_r]; congr 1; simp

/-- The singlet's observables form a Bell pair. -/
theorem singlet_bell_pair : BellPair (onA σz) (onA σx) (onB b0) (onB b1) :=
  ⟨by rw [onA_mul, sigma_z_sq, onA_one], by rw [onA_mul, sigma_x_sq, onA_one],
   by rw [onB_mul, b0_sq, onB_one], by rw [onB_mul, b1_sq, onB_one],
   onA_onB _ _, onA_onB _ _, onA_onB _ _, onA_onB _ _⟩

/-- **The singlet's CHSH value is `2√2 ⟨s, s⟩`.** -/
theorem singlet_chsh :
    star s ⬝ᵥ (chsh (onA σz) (onA σx) (onB b0) (onB b1) *ᵥ s) = 2 * r * (star s ⬝ᵥ s) := by
  simp only [chsh, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, singlet_corr,
    singlet_norm]
  simp [b0, b1, σz, σx, trace, Fin.sum_univ_two]
  ring

/-- **The joint closure saturates Tsirelson's bound**: equality in `tsirelson_bound`. -/
theorem singlet_saturates :
    (star s ⬝ᵥ (chsh (onA σz) (onA σx) (onB b0) (onB b1) *ᵥ s)).re =
      2 * Real.sqrt 2 * (star s ⬝ᵥ s).re := by
  rw [singlet_chsh, singlet_norm]; simp [r]

end QLF.JointClosure
