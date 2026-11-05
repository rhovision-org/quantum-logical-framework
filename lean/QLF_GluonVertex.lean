import QLF_ColourFlux
import Mathlib

/-!
# QLF_GluonVertex — the three-gluon colour vertex is a colour closure (G1, colour part)

Issue #207, target **G1**. [`QLF_ColourFlux`](QLF_ColourFlux.lean) identified the eight twists with
the eight nonzero vectors of `F₃²` (`colVec`), and read a colour line as the Weyl qutrit over that
plane. This module builds the qutrit's Weyl operators as `3 × 3` matrices,
`W(a, b)ᵢⱼ = [i = j + a] ω^{b j}` with `ω = e^{2πi/3}`, and computes the colour factor of the
three-gluon vertex, `V(p, q, r) = tr(W(p) [W(q), W(r)])`.

* **`W_mul`.** `W(p) W(q) = ω^{p₂ q₁} W(p + q)`: the Weyl operators multiply by adding labels.
* **`trace_W`.** `tr W(p) = 3` if `p = 0` and `0` otherwise, so the eight `p ≠ 0` are traceless:
  a basis of `sl(3)`, the complexified colour algebra.
* **`vertex_ne_zero_iff`.** `V(p, q, r) ≠ 0` **iff** `p + q + r = 0` and `⟨q, r⟩ ≠ 0`. The vertex
  exists exactly when the three colour labels **close** (sum to zero in `F₃²`) and are not collinear.
* **`gluon_vertex_iff`.** For gluons labelled by twists: the vertex is nonzero iff the three
  twists are colour balanced and the last two lie on different axes; then all three axes differ
  (`vertex_axes_distinct`).
* **`two_gluon_commute`.** Two gluons can close only as `t` and its reverse, which commute, so no
  two-gluon colour closure has a bracket: the three-gluon vertex is the **smallest** colour closure
  with a nonzero amplitude, a prime closure.
* **`vertex_count`.** Exactly 48 ordered twist triples carry a nonzero vertex (8 unordered).

So the colour factor of the three-gluon vertex is a closure condition on the colour plane, the
same shape as count balance for twists. **Not here:** the spin and momentum part of the vertex
(the Yang–Mills kinematic factor), G2's gluing into four-gluon amplitudes, and the identification of
this `sl(3)` with physical `su(3)` beyond the colour factor. No axioms.

**Credit.** The clock-and-shift basis of `sl(N)` with structure constants proportional to
`sin(2π⟨p, q⟩/N)` is Fairlie, Fletcher and Zachos's (*Phys. Lett. B* **218**, 203 (1989)); the
operators are Weyl's and Sylvester's. Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.GluonVertex

open Matrix QLF QLF.ColourFlux Fin.CommRing

/-- `ω = e^{2πi/3}`. -/
noncomputable def ω : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma ω_sq : ω ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  apply Complex.ext <;> simp [ω, sq, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_sq]

lemma ω_cube : ω ^ 3 = 1 := by
  rw [pow_succ, ω_sq]
  apply Complex.ext <;> simp [ω, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_sq]

lemma ω_sum : 1 + ω + ω ^ 2 = 0 := by
  rw [ω_sq]; apply Complex.ext <;> simp [ω]; ring

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- `ω^k` for `k ∈ F₃`. -/
noncomputable def wp (k : F3) : ℂ := ω ^ k.val

lemma pow_mod3 (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ω_cube, one_pow, one_mul]

lemma wp_add (a b : F3) : wp (a + b) = wp a * wp b := by
  unfold wp; rw [← pow_add, Fin.val_add, ← pow_mod3]

lemma ω_ne_one : ω ≠ 1 := fun e => by
  have := congrArg Complex.re e; simp [ω] at this; norm_num at this

lemma ω_sq_ne_one : ω ^ 2 ≠ 1 := fun e => by
  have := congrArg Complex.re e; rw [ω_sq] at this; simp at this; norm_num at this

lemma ω4 : ω ^ 4 = ω := by rw [pow_mod3]; norm_num

lemma wp_ne_zero (k : F3) : wp k ≠ 0 := by
  unfold wp; apply pow_ne_zero; intro h; have := congrArg Complex.re h; simp [ω] at this

lemma wp_eq_one (k : F3) (h : wp k = 1) : k = 0 := by
  fin_cases k
  · rfl
  · exact absurd (by simpa [wp] using h) ω_ne_one
  · exact absurd (by simpa [wp] using h) ω_sq_ne_one

lemma wp_injective (a b : F3) (h : wp a = wp b) : a = b := by
  have h1 : wp (a - b) * wp b = wp b * 1 := by rw [← wp_add, sub_add_cancel, mul_one, h]
  have h2 := wp_eq_one _ (mul_right_cancel₀ (wp_ne_zero b) (by rw [h1, mul_comm]))
  exact sub_eq_zero.mp h2

/-- **The Weyl operator** `W(a, b) = X^a Z^b` on the colour qutrit. -/
noncomputable def W (p : V) : Matrix F3 F3 ℂ := fun i j => if i = j + p.1 then wp (p.2 * j) else 0

/-- **Weyl operators multiply by adding labels.** -/
theorem W_mul (p q : V) : W p * W q = wp (p.2 * q.1) • W (p + q) := by
  ext i k
  simp only [Matrix.mul_apply, W, Matrix.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add,
    ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single (k + q.1)]
  · simp only [ite_true]
    by_cases hi : i = k + q.1 + p.1
    · subst hi
      have e : k + q.1 + p.1 = k + (p.1 + q.1) := by ring
      simp only [e, ite_true]
      rw [← wp_add, ← wp_add]
      congr 1; ring
    · have hi' : ¬ i = k + (p.1 + q.1) := fun h => hi (by rw [h]; ring)
      simp only [hi, hi', ite_false]
  · intro j _ hj; simp [hj]
  · simp

/-- **The eight `W(p)`, `p ≠ 0`, are traceless.** -/
theorem trace_W (p : V) : trace (W p) = if p = 0 then 3 else 0 := by
  obtain ⟨a, b⟩ := p
  have hs := ω_sum
  fin_cases a <;> fin_cases b <;>
    simp [trace, W, Fin.sum_univ_three, wp, Prod.ext_iff] <;>
    linear_combination hs

/-- The colour factor of the three-gluon vertex. -/
noncomputable def vertex (p q r : V) : ℂ := trace (W p * (W q * W r - W r * W q))

lemma trace_triple (p q r : V) :
    trace (W p * (W q * W r)) = wp (q.2 * r.1) * wp (p.2 * (q + r).1) * trace (W (p + q + r)) := by
  rw [W_mul, Matrix.mul_smul, W_mul, smul_smul, trace_smul, smul_eq_mul, ← add_assoc]

theorem vertex_eq (p q r : V) : vertex p q r =
    (wp (q.2 * r.1) * wp (p.2 * (q + r).1) - wp (r.2 * q.1) * wp (p.2 * (r + q).1)) *
      trace (W (p + q + r)) := by
  unfold vertex
  rw [Matrix.mul_sub, trace_sub, trace_triple, trace_triple,
    show p + r + q = p + q + r by abel]
  ring

/-- **The three-gluon vertex exists iff the colour labels close and are not collinear.** -/
theorem vertex_ne_zero_iff (p q r : V) : vertex p q r ≠ 0 ↔ p + q + r = 0 ∧ symp q r ≠ 0 := by
  rw [vertex_eq, trace_W]
  by_cases h : p + q + r = 0
  · simp only [h, ite_true, true_and]
    rw [add_comm r q, ← wp_add, ← wp_add]
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    rw [Ne, mul_eq_zero, sub_eq_zero, not_or, and_iff_left h3]
    constructor
    · intro hne hs; apply hne; congr 1; unfold symp at hs; linear_combination -hs
    · intro hne hs; apply hne; have := wp_injective _ _ hs; unfold symp; linear_combination -this
  · simp [h]

/-! ## Gluons labelled by twists -/

/-- The vertex of three gluons labelled by twists. -/
noncomputable def gluonVertex (t u v : Twist) : ℂ := vertex (colVec t) (colVec u) (colVec v)

theorem symp_ne_zero_iff (t u : Twist) :
    symp (colVec t) (colVec u) ≠ 0 ↔ axisLine t ≠ axisLine u := by
  cases t <;> cases u <;> decide

/-- **Gluon vertex selection rule**: colour balance and distinct axes. -/
theorem gluon_vertex_iff (t u v : Twist) :
    gluonVertex t u v ≠ 0 ↔ colVec t + colVec u + colVec v = 0 ∧ axisLine u ≠ axisLine v := by
  unfold gluonVertex; rw [vertex_ne_zero_iff, symp_ne_zero_iff]

/-- In a nonzero vertex all three gluons lie on different axes. -/
theorem vertex_axes_distinct (t u v : Twist) (h : gluonVertex t u v ≠ 0) :
    axisLine t ≠ axisLine u ∧ axisLine t ≠ axisLine v ∧ axisLine u ≠ axisLine v := by
  rw [gluon_vertex_iff] at h
  revert h
  cases t <;> cases u <;> cases v <;> decide

/-- **Two gluons close only as a twist and its reverse, and those commute.** -/
theorem two_gluon_commute (t u : Twist) (h : colVec t + colVec u = 0) :
    u = revTwist t ∧ W (colVec t) * W (colVec u) = W (colVec u) * W (colVec t) := by
  have hu : u = revTwist t := by revert h; cases t <;> cases u <;> decide
  refine ⟨hu, ?_⟩
  subst hu
  rw [colVec_rev, W_mul, W_mul, add_comm (-colVec t)]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg]
  congr 1; ring

/-- **48 ordered twist triples carry a nonzero three-gluon vertex.** -/
theorem vertex_count :
    ((allTwists.toFinset ×ˢ allTwists.toFinset ×ˢ allTwists.toFinset).filter
      (fun x => colVec x.1 + colVec x.2.1 + colVec x.2.2 = 0 ∧
        axisLine x.2.1 ≠ axisLine x.2.2)).card = 48 := by
  decide

end QLF.GluonVertex
