import Mathlib
import QLF_TwistAlphabet

/-!
# QLF_PauliFrame — **the Pauli frame is forced on a spin-½ atom**

Obligation O5 of [`Framing.md`](../Framing.md) §6, the structural choice "the signed distinctions are
the signed axes of the Pauli frame". The alphabet is the signed axis frame
([`QLF_AlphabetNecessity`](QLF_AlphabetNecessity.lean)); what is left is why the axes are the Pauli
matrices. This module proves that, on a two-dimensional state space, nothing else is possible.

An **axis** is a two-outcome observable, an involution `A * A = 1`. Two axes are **incompatible** in
the strongest sense when they anticommute, `A * B = -(B * A)`: each reverses the other's outcomes,
which is A11 (incompatible observables exist) taken at full strength. On `2 × 2` complex matrices:

* `trace_zero_of_anti` — an axis incompatible with another is traceless (balanced outcomes).
* `coeffs_zero` — two incompatible axes `A`, `B` with `1` and `A * B` are linearly independent, so
  `{1, A, B, AB}` is a basis (`span_frame`).
* `third_axis` — **a third axis incompatible with both is `± i · A * B`**: fixed by the first two up
  to one sign, the handedness.
* `frame_product` — so `A * B * C = ∓ i`, the Pauli relation `σx σy σz = i` up to that sign.
* `no_fourth_axis` — **there is no fourth**: at most three mutually incompatible axes. This is why the
  fourth (gauge) pair of the alphabet folds to `± I` and commutes with everything
  (`gauge_commutes`) instead of being a fourth spin axis.
* `pauli_is_a_frame` — the twist matrices `σx`, `σy`, `σz` are such a frame, with `σx σy = i σz`.

What stays a choice: that the atom is two-dimensional (spin-½, Cartan 1913; the information atom of
[`QLF_SpinorInformation`](QLF_SpinorInformation.lean)) and that incompatibility is read at full
strength. Given those, the frame is forced except for the sign of the third axis. No axioms.
-/

namespace QLF.PauliFrame

open Matrix

/-- A point of the frame: `a + bA + cB + dAB`. -/
def fs (A B : M) (a b c d : ℂ) : M := a • (1 : M) + b • A + c • B + d • (A * B)

variable {A B C D : M}

/-- An axis incompatible with an involution is traceless. -/
theorem trace_zero_of_anti (hB : B * B = 1) (h : A * B = -(B * A)) : A.trace = 0 := by
  have h1 : B * A * B = -A := by
    rw [mul_assoc, h, mul_neg, ← mul_assoc, hB, one_mul]
  have h2 : (B * A * B).trace = A.trace := by
    rw [Matrix.trace_mul_comm (B * A) B, ← mul_assoc, hB, one_mul]
  rw [h1, Matrix.trace_neg] at h2
  have h3 : (2 : ℂ) * A.trace = 0 := by linear_combination -h2
  simpa using h3

/-- The product of two incompatible axes is traceless. -/
theorem trace_mul_zero_of_anti (h : A * B = -(B * A)) : (A * B).trace = 0 := by
  have h2 : (A * B).trace = -(A * B).trace := by
    conv_lhs => rw [h]
    rw [Matrix.trace_neg, Matrix.trace_mul_comm B A]
  have h3 : (2 : ℂ) * (A * B).trace = 0 := by linear_combination h2
  simpa using h3

/-- The four traces that read off coordinates in the frame `{1, A, B, AB}`. -/
theorem trace_coeffs (hA : A * A = 1) (hB : B * B = 1) (h : A * B = -(B * A)) (a b c d : ℂ) :
    (fs A B a b c d).trace = 2 * a ∧ (A * fs A B a b c d).trace = 2 * b ∧
      (B * fs A B a b c d).trace = 2 * c ∧ (A * B * fs A B a b c d).trace = -2 * d := by
  have tA := trace_zero_of_anti hB h
  have h' : B * A = -(A * B) := by rw [h, neg_neg]
  have tB := trace_zero_of_anti hA h'
  have tAB := trace_mul_zero_of_anti h
  have hAAB : A * (A * B) = B := by rw [← mul_assoc, hA, one_mul]
  have hBAB : B * (A * B) = -A := by rw [← mul_assoc, h', neg_mul, mul_assoc, hB, mul_one]
  have hABA : A * B * A = -B := by rw [mul_assoc, h', mul_neg, ← mul_assoc, hA, one_mul]
  have hABB : A * B * B = A := by rw [mul_assoc, hB, mul_one]
  have hABAB : A * B * (A * B) = -1 := by rw [← mul_assoc, hABA, neg_mul, hB]
  have t1 : (1 : M).trace = 2 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [fs, Matrix.trace_add, Matrix.trace_smul, t1, tA, tB, tAB, smul_eq_mul]; ring
  · simp only [fs, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hA, hAAB, Matrix.trace_add,
      Matrix.trace_smul, t1, tA, tB, tAB, smul_eq_mul]; ring
  · simp only [fs, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hB, h', hBAB, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_neg, t1, tA, tB, tAB, smul_eq_mul]; ring
  · simp only [fs, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hABA, hABB, hABAB,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_neg, t1, tA, tB, tAB, smul_eq_mul]; ring

/-- **Two incompatible axes span a frame**: `1, A, B, AB` are linearly independent. -/
theorem coeffs_zero (hA : A * A = 1) (hB : B * B = 1) (h : A * B = -(B * A)) {a b c d : ℂ}
    (hs : fs A B a b c d = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨t0, t1, t2, t3⟩ := trace_coeffs hA hB h a b c d
  simp only [hs, Matrix.mul_zero, Matrix.trace_zero] at t0 t1 t2 t3
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-1/2 : ℂ) * t0
  · linear_combination (-1/2 : ℂ) * t1
  · linear_combination (-1/2 : ℂ) * t2
  · linear_combination (1/2 : ℂ) * t3

/-- The frame as a family of four matrices. -/
def frame (A B : M) : Fin 4 → M := ![1, A, B, A * B]

theorem frame_independent (hA : A * A = 1) (hB : B * B = 1) (h : A * B = -(B * A)) :
    LinearIndependent ℂ (frame A B) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  simp only [frame, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons] at hg
  obtain ⟨h0, h1, h2, h3⟩ := coeffs_zero hA hB h (a := g 0) (b := g 1) (c := g 2) (d := g 3)
    (by rw [fs]; exact hg)
  intro i; fin_cases i <;> assumption

/-- **The frame spans**: every `2 × 2` matrix is `a + bA + cB + dAB`. -/
theorem span_frame (hA : A * A = 1) (hB : B * B = 1) (h : A * B = -(B * A)) (X : M) :
    ∃ a b c d : ℂ, X = fs A B a b c d := by
  have hspan := LinearIndependent.span_eq_top_of_card_eq_finrank (frame_independent hA hB h)
    (by rw [Module.finrank_matrix]; simp)
  have hX : X ∈ Submodule.span ℂ (Set.range (frame A B)) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hX
  refine ⟨g 0, g 1, g 2, g 3, ?_⟩
  rw [← hg, Fin.sum_univ_four, fs]
  simp [frame]

/-- **The third axis is forced up to sign**: an involution incompatible with two incompatible axes
    `A`, `B` is `i · AB` or `−i · AB`. -/
theorem third_axis (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1) (hAB : A * B = -(B * A))
    (hAC : A * C = -(C * A)) (hBC : B * C = -(C * B)) :
    C = Complex.I • (A * B) ∨ C = -(Complex.I • (A * B)) := by
  obtain ⟨a, b, c, d, hX⟩ := span_frame hA hB hAB C
  obtain ⟨t0, t1, t2, _⟩ := trace_coeffs hA hB hAB a b c d
  rw [← hX] at t0 t1 t2
  rw [trace_zero_of_anti hA (by rw [hAC, neg_neg] : C * A = -(A * C))] at t0
  rw [trace_mul_zero_of_anti hAC] at t1
  rw [trace_mul_zero_of_anti hBC] at t2
  have ha : a = 0 := by linear_combination (-1/2 : ℂ) * t0
  have hb : b = 0 := by linear_combination (-1/2 : ℂ) * t1
  have hc : c = 0 := by linear_combination (-1/2 : ℂ) * t2
  subst ha hb hc
  simp only [fs, zero_smul, zero_add] at hX
  have hABA : A * B * A = -B := by
    rw [mul_assoc, (by rw [hAB, neg_neg] : B * A = -(A * B)), mul_neg, ← mul_assoc, hA, one_mul]
  have hABAB : A * B * (A * B) = -1 := by rw [← mul_assoc, hABA, neg_mul, hB]
  have hd : d * d = -1 := by
    have e := hC
    rw [hX, Matrix.smul_mul, Matrix.mul_smul, hABAB, smul_smul] at e
    have := congrFun (congrFun e 0) 0
    simp at this
    linear_combination -this
  have : (d - Complex.I) * (d + Complex.I) = 0 := by
    linear_combination hd - Complex.I_sq
  rcases mul_eq_zero.mp this with h1 | h1
  · left; rw [hX, show d = Complex.I by linear_combination h1]
  · right; rw [hX, show d = -Complex.I by linear_combination h1, neg_smul]

/-- **The Pauli relation, up to the handedness sign**: `A B C = −i` or `+i`. -/
theorem frame_product (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1) (hAB : A * B = -(B * A))
    (hAC : A * C = -(C * A)) (hBC : B * C = -(C * B)) :
    A * B * C = -(Complex.I • (1 : M)) ∨ A * B * C = Complex.I • (1 : M) := by
  have hABA : A * B * A = -B := by
    rw [mul_assoc, (by rw [hAB, neg_neg] : B * A = -(A * B)), mul_neg, ← mul_assoc, hA, one_mul]
  have hABAB : A * B * (A * B) = -1 := by rw [← mul_assoc, hABA, neg_mul, hB]
  rcases third_axis hA hB hC hAB hAC hBC with h | h
  · left; rw [h, Matrix.mul_smul, hABAB, smul_neg]
  · right; rw [h, Matrix.mul_neg, Matrix.mul_smul, hABAB, smul_neg, neg_neg]

/-- **No fourth axis**: at most three mutually incompatible two-outcome observables on a spin-½
    atom. -/
theorem no_fourth_axis (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1) (hD : D * D = 1)
    (hAB : A * B = -(B * A)) (hAC : A * C = -(C * A)) (hBC : B * C = -(C * B))
    (hAD : A * D = -(D * A)) (hBD : B * D = -(D * B)) (hCD : C * D = -(D * C)) : False := by
  have one_ne : (1 : M) ≠ -1 := by
    intro e; have := congrFun (congrFun e 0) 0; norm_num at this
  have same : D = C → False := fun e => by
    rw [e, hC] at hCD; exact one_ne hCD
  have opp : D = -C → False := fun e => by
    rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_neg, hC] at hCD; exact one_ne hCD.symm
  rcases third_axis hA hB hC hAB hAC hBC with hc | hc <;>
    rcases third_axis hA hB hD hAB hAD hBD with hd | hd
  · exact same (by rw [hd, hc])
  · exact opp (by rw [hd, hc])
  · exact opp (by rw [hd, hc, neg_neg])
  · exact same (by rw [hd, hc])

/-- **The twist matrices are such a frame**: involutions, pairwise anticommuting, and
    `σx σy = i σz`, so the alphabet's third axis carries the `+` sign. -/
theorem pauli_is_a_frame :
    QLF.σx * QLF.σx = 1 ∧ QLF.σy * QLF.σy = 1 ∧ QLF.σz * QLF.σz = 1 ∧
      QLF.σx * QLF.σy = -(QLF.σy * QLF.σx) ∧ QLF.σx * QLF.σz = -(QLF.σz * QLF.σx) ∧
      QLF.σy * QLF.σz = -(QLF.σz * QLF.σy) ∧ QLF.σx * QLF.σy = Complex.I • QLF.σz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [QLF.σx, QLF.σy, QLF.σz, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The gauge pair commutes with every axis**: it folds to `± I`, the only place a fourth pair can
    go once `no_fourth_axis` rules out a fourth spin axis. -/
theorem gauge_commutes (X : M) :
    QLF.Twist.plus.toMatrix * X = X * QLF.Twist.plus.toMatrix ∧
      QLF.Twist.minus.toMatrix * X = X * QLF.Twist.minus.toMatrix := by
  constructor <;> simp [QLF.Twist.toMatrix]

end QLF.PauliFrame
