import QLF_LightCone

set_option linter.unusedVariables false

/-!
# QLF_Tsirelson — **composite systems: Bell violation is the twist Clifford relation**

Continues [`QLF_LightCone`](QLF_LightCone.lean) and [`QLF_RealizableWalk`](QLF_RealizableWalk.lean)
(issue #207). See [`Closure_Unitarity.md`](../Closure_Unitarity.md) §13.

Two sites, each measuring one of two two-outcome observables (`x² = 1`), with the sites' observables
commuting. The CHSH combination (Clauser, Horne, Shimony and Holt, Phys. Rev. Lett. 23, 880 (1969))
`C = a₀b₀ + a₀b₁ + a₁b₀ − a₁b₁` obeys, in **any** ring,

> **`chsh_sq`** — `C² = 4 − [a₀, a₁][b₀, b₁]`.

So everything depends on whether each site's two observables commute:

* **`chsh_classical`** — if they commute (a joint value exists), `C² = 4`, so `|C| ≤ 2`: Bell's bound.
* **`chsh_anti`**, **`chsh_tsirelson`** — if they anticommute, `(C² − 4)² = 16`, so
  `C²(C² − 8) = 0` and every eigenvalue of `C` lies in `{0, ±2√2}`: Tsirelson's value
  (Cirel'son, Lett. Math. Phys. 4, 93 (1980)) in the maximal, anticommuting case.

Twists on different spatial axes anticommute (the Clifford relation behind the light-cone zeros,
`QLF_LightCone`). Taking `up` and `left` on each of two sites:

* **`twist_bell_pair`** — they form a Bell pair (each squares to `1`, sites commute);
* **`twistChsh_herm`** — the CHSH operator is Hermitian;
* **`twistChsh_tsirelson`** — `C²(C² − 8) = 0`;
* **`twistChsh_sq_e00`** — `C²|00⟩ = 8|00⟩` (a statement about `C²`; `|00⟩` itself has zero CHSH
  expectation);
* **`twistChsh_saturates`** — the explicit state `v = C|00⟩ + 2√2|00⟩` is non-zero and
  `Cv = 2√2·v`, so the value `2√2` is attained by a state.

**Scope.** `chsh_tsirelson` is the *maximal, anticommuting* case: it fixes the spectrum when both
sites' observables anticommute exactly. It is not the general Tsirelson bound `‖C‖ ≤ 2√2` for
arbitrary Hermitian `±1` observables; observables that fail to commute without anticommuting give
intermediate CHSH values. That general bound, `|⟨C⟩| ≤ 2√2` for every state and every Hermitian
`±1` observables, is proved by a sum-of-squares certificate in
[`QLF_TsirelsonBound`](QLF_TsirelsonBound.lean) (`tsirelson_bound`, `tsirelson_bound_neg`).

The reading: a twist pair that cannot be given joint values *is* a pair that does not commute, and
that is the whole of the quantum excess over Bell. No continuum, no Hilbert-space postulate beyond
two-by-two matrices on each site. No axioms.
-/

namespace QLF.Tsirelson

open Matrix

section Ring

variable {R : Type*} [Ring R]

/-- The CHSH combination. -/
def chsh (a0 a1 b0 b1 : R) : R := a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1

/-- Two two-outcome observables per side, sides commuting. -/
structure BellPair (a0 a1 b0 b1 : R) : Prop where
  a0_sq : a0 * a0 = 1
  a1_sq : a1 * a1 = 1
  b0_sq : b0 * b0 = 1
  b1_sq : b1 * b1 = 1
  c00 : a0 * b0 = b0 * a0
  c01 : a0 * b1 = b1 * a0
  c10 : a1 * b0 = b0 * a1
  c11 : a1 * b1 = b1 * a1

private theorem sq_left {x : R} (h : x * x = 1) (y : R) : x * (x * y) = y := by
  rw [← mul_assoc, h, one_mul]

private theorem swap_left {x y : R} (h : x * y = y * x) (z : R) : y * (x * z) = x * (y * z) := by
  rw [← mul_assoc, ← mul_assoc, h]

theorem chsh_sq {a0 a1 b0 b1 : R} (h : BellPair a0 a1 b0 b1) :
    chsh a0 a1 b0 b1 * chsh a0 a1 b0 b1 =
      4 - (a0 * a1 - a1 * a0) * (b0 * b1 - b1 * b0) := by
  rw [show (4:R) = 1 + 1 + 1 + 1 by norm_num]
  have e1 := sq_left h.a0_sq; have e2 := sq_left h.a1_sq
  have e3 := sq_left h.b0_sq; have e4 := sq_left h.b1_sq
  have s1 := swap_left h.c00; have s2 := swap_left h.c01
  have s3 := swap_left h.c10; have s4 := swap_left h.c11
  simp only [chsh, add_mul, mul_add, sub_mul, mul_sub, mul_assoc, e1, e2, s1, s2, s3, s4,
    h.a0_sq, h.a1_sq, h.b0_sq, h.b1_sq, mul_one]
  abel

/-- **Classical bound.** If one side's observables commute (a joint value exists), `C² = 4`. -/
theorem chsh_classical {a0 a1 b0 b1 : R} (h : BellPair a0 a1 b0 b1) (hc : a0 * a1 = a1 * a0) :
    chsh a0 a1 b0 b1 * chsh a0 a1 b0 b1 = 4 := by
  rw [chsh_sq h, hc, sub_self, zero_mul, sub_zero]

/-- **Twist bound.** If each side's observables anticommute, `(C² − 4)² = 16`. -/
theorem chsh_anti {a0 a1 b0 b1 : R} (h : BellPair a0 a1 b0 b1)
    (ha : a1 * a0 = -(a0 * a1)) (hb : b1 * b0 = -(b0 * b1)) :
    (chsh a0 a1 b0 b1 * chsh a0 a1 b0 b1 - 4) * (chsh a0 a1 b0 b1 * chsh a0 a1 b0 b1 - 4) = 16 := by
  rw [chsh_sq h, ha, hb]
  have pp : a0 * a1 * (a0 * a1) = -1 := by
    rw [mul_assoc, ← mul_assoc a1, ha, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, h.a0_sq, one_mul, h.a1_sq]
  have qq : b0 * b1 * (b0 * b1) = -1 := by
    rw [mul_assoc, ← mul_assoc b1, hb, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, h.b0_sq, one_mul, h.b1_sq]
  have pq : a0 * a1 * (b0 * b1) = b0 * b1 * (a0 * a1) := by
    simp only [mul_assoc, swap_left h.c00, swap_left h.c01]
    rw [← mul_assoc a1 b0, h.c10, mul_assoc, h.c11]
  set p := a0 * a1; set q := b0 * b1
  have e : (4 - (p - -p) * (q - -q) - 4) = -(4 * (p * q)) := by noncomm_ring
  rw [e, neg_mul_neg]
  have : 4 * (p * q) * (4 * (p * q)) = 16 * ((p * p) * (q * q)) := by
    have e2 : 4 * (p * q) * (4 * (p * q)) = 16 * (p * q * (p * q)) := by noncomm_ring
    rw [e2, mul_assoc p q, ← mul_assoc q p q, ← pq]
    simp only [mul_assoc]
  rw [this, pp, qq, neg_mul_neg, one_mul, mul_one]

/-- Hence `C²(C² − 8) = 0`: the spectrum of `C` lies in `{0, ±2√2}`. -/
theorem chsh_tsirelson {a0 a1 b0 b1 : R} (h : BellPair a0 a1 b0 b1)
    (ha : a1 * a0 = -(a0 * a1)) (hb : b1 * b0 = -(b0 * b1)) :
    chsh a0 a1 b0 b1 * chsh a0 a1 b0 b1 * (chsh a0 a1 b0 b1 * chsh a0 a1 b0 b1 - 8) = 0 := by
  set c := chsh a0 a1 b0 b1 * chsh a0 a1 b0 b1
  have e : c * (c - 8) = (c - 4) * (c - 4) - 16 := by
    simp only [mul_sub, sub_mul]
    rw [(Commute.ofNat_left 4 c).eq,
      show (4:R) * 4 = 16 by norm_num, show c * 8 = c * 4 + c * 4 by rw [← mul_add]; norm_num]
    abel
  rw [e, chsh_anti h ha hb, sub_self]

end Ring

section Twists

open Kronecker
open QLF.ClosureChannels

/-- Two-site operators: `(Fin 2 × Fin 2)`-indexed matrices. -/
abbrev Q := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- A twist observable on site A. -/
noncomputable def onA (X : Matrix (Fin 2) (Fin 2) ℂ) : Q := X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
/-- A twist observable on site B. -/
noncomputable def onB (X : Matrix (Fin 2) (Fin 2) ℂ) : Q := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ X

theorem onA_mul (X Y : Matrix (Fin 2) (Fin 2) ℂ) : onA X * onA Y = onA (X * Y) := by
  rw [onA, onA, onA, ← mul_kronecker_mul, one_mul]

theorem onB_mul (X Y : Matrix (Fin 2) (Fin 2) ℂ) : onB X * onB Y = onB (X * Y) := by
  rw [onB, onB, onB, ← mul_kronecker_mul, one_mul]

theorem onA_onB (X Y : Matrix (Fin 2) (Fin 2) ℂ) : onA X * onB Y = onB Y * onA X := by
  rw [onA, onB, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one, one_mul, mul_one]

theorem onA_one : onA 1 = 1 := by rw [onA, one_kronecker_one]
theorem onB_one : onB 1 = 1 := by rw [onB, one_kronecker_one]

theorem onA_sq (t : Twist) : onA t.toMatrix * onA t.toMatrix = 1 := by
  rw [onA_mul, ClosureUnitarity.twist_sq, onA_one]
theorem onB_sq (t : Twist) : onB t.toMatrix * onB t.toMatrix = 1 := by
  rw [onB_mul, ClosureUnitarity.twist_sq, onB_one]

/-- The twist Bell pair: `up`, `left` on each site. -/
theorem twist_bell_pair : BellPair (onA Twist.up.toMatrix) (onA Twist.left.toMatrix)
    (onB Twist.up.toMatrix) (onB Twist.left.toMatrix) :=
  ⟨onA_sq _, onA_sq _, onB_sq _, onB_sq _, onA_onB _ _, onA_onB _ _, onA_onB _ _, onA_onB _ _⟩

theorem left_up_anti : Twist.left.toMatrix * Twist.up.toMatrix =
    -(Twist.up.toMatrix * Twist.left.toMatrix) := by
  simpa using left_up (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- The CHSH operator built from twists. -/
noncomputable def twistChsh : Q := chsh (onA Twist.up.toMatrix) (onA Twist.left.toMatrix)
    (onB Twist.up.toMatrix) (onB Twist.left.toMatrix)

/-- **Twists reach the quantum (Tsirelson) value.** `C²(C² − 8) = 0`. -/
theorem twistChsh_tsirelson : twistChsh * twistChsh * (twistChsh * twistChsh - 8) = 0 :=
  chsh_tsirelson twist_bell_pair
    (by rw [onA_mul, onA_mul, left_up_anti, onA, onA]; ext ⟨i, j⟩ ⟨k, l⟩; simp [kroneckerMap_apply])
    (by rw [onB_mul, onB_mul, left_up_anti, onB, onB]; ext ⟨i, j⟩ ⟨k, l⟩; simp [kroneckerMap_apply])

theorem onA_herm (t : Twist) : (onA t.toMatrix)ᴴ = onA t.toMatrix := by
  rw [onA, conjTranspose_kronecker, ClosureUnitarity.twist_herm, conjTranspose_one]

theorem onB_herm (t : Twist) : (onB t.toMatrix)ᴴ = onB t.toMatrix := by
  rw [onB, conjTranspose_kronecker, ClosureUnitarity.twist_herm, conjTranspose_one]

/-- The twist CHSH operator is Hermitian (an observable). -/
theorem twistChsh_herm : twistChshᴴ = twistChsh := by
  simp only [twistChsh, chsh, conjTranspose_add, conjTranspose_sub, conjTranspose_mul, onA_herm,
    onB_herm, ← onA_onB]

/-- `up · left = i σ_z`. -/
theorem up_left_eq : Twist.up.toMatrix * Twist.left.toMatrix = !![Complex.I, 0; 0, -Complex.I] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Twist.toMatrix, σx, σy, Matrix.mul_apply, Fin.sum_univ_two]

/-- The product basis vector `|00⟩`. -/
noncomputable def e00 : Fin 2 × Fin 2 → ℂ := Pi.single (0, 0) 1

/-- **`2√2` is attained:** `|00⟩` is an eigenvector of `C²` with eigenvalue `8`. -/
theorem twistChsh_sq_e00 : (twistChsh * twistChsh) *ᵥ e00 = (8 : ℂ) • e00 := by
  rw [twistChsh, chsh_sq twist_bell_pair, onA_mul, onA_mul, onB_mul, onB_mul, left_up_anti,
    up_left_eq]
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [e00, onA, onB, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.mul_apply, kroneckerMap_apply, Pi.single_apply, Matrix.one_apply, Matrix.ofNat_apply]
  all_goals ring_nf; simp [Complex.I_sq]; norm_num

/-- `C|00⟩` has no `|00⟩` component. -/
theorem twistChsh_e00_00 : (twistChsh *ᵥ e00) (0, 0) = 0 := by
  simp [twistChsh, chsh, e00, onA, onB, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, kroneckerMap_apply,
    Pi.single_apply, Matrix.one_apply, Twist.toMatrix, σx, σy]

/-- The saturating state: `v = C|00⟩ + 2√2 |00⟩`. -/
noncomputable def tsirelsonState : Fin 2 × Fin 2 → ℂ :=
  twistChsh *ᵥ e00 + (2 * (Real.sqrt 2 : ℂ)) • e00

/-- **Tsirelson's value is attained by an explicit state:** `v ≠ 0` and `C v = 2√2 v`. -/
theorem twistChsh_saturates :
    tsirelsonState ≠ 0 ∧
      twistChsh *ᵥ tsirelsonState = (2 * (Real.sqrt 2 : ℂ)) • tsirelsonState := by
  have hs : (2 * (Real.sqrt 2 : ℂ)) * (2 * (Real.sqrt 2 : ℂ)) = 8 := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    linear_combination 4 * h2
  constructor
  · intro h
    have h0 := congrFun h (0, 0)
    simp only [tsirelsonState, Pi.add_apply, Pi.smul_apply, twistChsh_e00_00, Pi.zero_apply,
      zero_add] at h0
    simp only [e00, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
    have : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    exact mul_ne_zero two_ne_zero this h0
  · rw [tsirelsonState, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      twistChsh_sq_e00, smul_add, smul_smul, hs, add_comm]

end Twists
end QLF.Tsirelson
