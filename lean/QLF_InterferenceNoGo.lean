import QLF_KraftMeasure
import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# QLF_InterferenceNoGo — what an interfering event weight must be

Pre-registered in [`Interference_NoGo.md`](../Interference_NoGo.md) §2 (statements N1–N5), before
any of the proofs below were written.

[`QLF_KraftMeasure`](QLF_KraftMeasure.lean) proved that one weight, the normalized-event weight
`(Σa)²/(Σw)`, cannot interfere constructively (`no_constructive_interference`). This module asks
what that failure has in common with every other candidate, and answers for a whole class.

A **tally readout** weighs an event `E` (a finite set of ways) as `μ(E) = Φ(T(E))`, where each way
carries a tally `v(h)` in a real vector space and the tally is additive, `T(E) = Σ_{h∈E} v(h)`. The
additive measures, the KraftMeasure weight and the Born weight are all of this shape. Then:

* **N1** `additive_no_interference` — an additive weight has `I₂ = 0`. Bookkeeping, recorded as the
  base case.
* **N2** `matched_pair_scale`, `matched_pair_factor` — if `Φ` is homogeneous of degree `k`, a matched
  pair (two disjoint events with equal tally, i.e. two coherent equal-amplitude paths) weighs
  `2^(k−1)` times the sum of its parts. **N2a** `degree_one_matched_no_interference`: degree 1 gives
  no interference on a matched pair, convex or not. **N2b** `quantum_factor_iff_degree_two`: the
  quantum factor `2` holds iff `k = 2`. **N2c** `kraftΦ_degree_one`,
  `kraft_matched_no_interference`, `kraft_matched_agrees`: the KraftMeasure weight is degree 1, and
  the two modules agree on its matched pairs.
* **N3** `sublinear_subadditive`, `sublinear_no_constructive_interference` — a convex, degree-1
  readout is sub-additive, so it never interferes constructively. This is the general form of
  `no_constructive_interference`.
* **N4** `unsigned_no_dark_fringe` — with non-negative tallies, and `Φ` vanishing only at `0`, two
  events cannot cancel: no dark fringe from a census of unsigned counts.
* **N5** `born_I₂`, `born_degree_two`, `born_matched_factor`, `born_dark_fringe`, `born_I₃` — the
  squared complex tally does both, and its interference is purely pairwise (`I₃ = 0`, Sorkin).

So an event weight that interferes both ways is not a classical quantity on closures: the additive
object scales as the square root of the weight (N2b) and carries a sign or phase (N4), and the weight
is its square (N5). These are theorems about the **shape** of a weight; they do not identify the
amplitude with a census quantity and do not derive the Born rule. No axioms.
-/

namespace QLF.InterferenceNoGo

open Finset

variable {ι : Type} [DecidableEq ι]

/-- The pairwise interference term of an event weight. -/
def I₂ (μ : Finset ι → ℝ) (A B : Finset ι) : ℝ := μ (A ∪ B) - μ A - μ B

/-- Sorkin's third-order interference term. -/
def I₃ (μ : Finset ι → ℝ) (A B C : Finset ι) : ℝ :=
  μ (A ∪ B ∪ C) - μ (A ∪ B) - μ (A ∪ C) - μ (B ∪ C) + μ A + μ B + μ C

/-- The additive tally of an event. -/
def tally {V : Type} [AddCommMonoid V] (v : ι → V) (E : Finset ι) : V := ∑ h ∈ E, v h

/-- A tally readout: the event weight `Φ(T(E))`. -/
def readout {V : Type} [AddCommMonoid V] (Φ : V → ℝ) (v : ι → V) (E : Finset ι) : ℝ :=
  Φ (tally v E)

/-- Tallies add over disjoint events. -/
theorem tally_union {V : Type} [AddCommMonoid V] (v : ι → V) {A B : Finset ι}
    (h : Disjoint A B) : tally v (A ∪ B) = tally v A + tally v B :=
  Finset.sum_union h

/-! ## N1 — additive weights do not interfere -/

/-- **N1.** An additive event weight has no interference of either sign. (Restates additivity.) -/
theorem additive_no_interference (μ : Finset ι → ℝ)
    (hadd : ∀ A B : Finset ι, Disjoint A B → μ (A ∪ B) = μ A + μ B)
    {A B : Finset ι} (h : Disjoint A B) : I₂ μ A B = 0 := by
  unfold I₂
  rw [hadd A B h]
  ring

/-! ## N2 — the matched-pair factor fixes the degree -/

section Homogeneous

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- **N2.** A matched pair under a degree-`k` readout weighs `2^k` times one of its halves. -/
theorem matched_pair_scale (Φ : V → ℝ) (k : ℕ)
    (hΦ : ∀ c : ℝ, 0 < c → ∀ x : V, Φ (c • x) = c ^ k * Φ x)
    (v : ι → V) {A B : Finset ι} (hd : Disjoint A B) (hm : tally v A = tally v B) :
    readout Φ v (A ∪ B) = 2 ^ k * readout Φ v A := by
  unfold readout
  rw [tally_union v hd, ← hm, ← two_smul ℝ (tally v A), hΦ 2 (by norm_num)]

/-- The two halves of a matched pair weigh the same. -/
theorem matched_halves (Φ : V → ℝ) (v : ι → V) {A B : Finset ι}
    (hm : tally v A = tally v B) : readout Φ v B = readout Φ v A := by
  unfold readout
  rw [hm]

/-- **N2**, as a factor on the sum of the parts: `2^(k−1)`. -/
theorem matched_pair_factor (Φ : V → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hΦ : ∀ c : ℝ, 0 < c → ∀ x : V, Φ (c • x) = c ^ k * Φ x)
    (v : ι → V) {A B : Finset ι} (hd : Disjoint A B) (hm : tally v A = tally v B) :
    readout Φ v (A ∪ B) = 2 ^ (k - 1) * (readout Φ v A + readout Φ v B) := by
  rw [matched_pair_scale Φ k hΦ v hd hm, matched_halves Φ v hm]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-- **N2a.** A degree-1 readout gives a matched pair no interference at all — convexity plays no
role. -/
theorem degree_one_matched_no_interference (Φ : V → ℝ)
    (hΦ : ∀ c : ℝ, 0 < c → ∀ x : V, Φ (c • x) = c ^ 1 * Φ x)
    (v : ι → V) {A B : Finset ι} (hd : Disjoint A B) (hm : tally v A = tally v B) :
    I₂ (readout Φ v) A B = 0 := by
  unfold I₂
  rw [matched_pair_scale Φ 1 hΦ v hd hm, matched_halves Φ v hm]
  ring

/-- **N2b.** The quantum matched-pair factor — two coherent equal paths weigh twice the sum of
their parts — holds **iff the readout has degree two**. -/
theorem quantum_factor_iff_degree_two (Φ : V → ℝ) (k : ℕ)
    (hΦ : ∀ c : ℝ, 0 < c → ∀ x : V, Φ (c • x) = c ^ k * Φ x)
    (v : ι → V) {A B : Finset ι} (hd : Disjoint A B) (hm : tally v A = tally v B)
    (hA : readout Φ v A ≠ 0) :
    readout Φ v (A ∪ B) = 2 * (readout Φ v A + readout Φ v B) ↔ k = 2 := by
  rw [matched_pair_scale Φ k hΦ v hd hm, matched_halves Φ v hm]
  constructor
  · intro h
    have h4 : (2 : ℝ) ^ k = 2 ^ 2 := by
      have h' : (2 : ℝ) ^ k * readout Φ v A = 2 ^ 2 * readout Φ v A := by linarith
      exact mul_right_cancel₀ hA h'
    have h4' : (2 : ℕ) ^ k = 2 ^ 2 := by exact_mod_cast h4
    exact Nat.pow_right_injective (le_refl 2) h4'
  · rintro rfl
    ring

end Homogeneous

/-! ### N2c — the KraftMeasure normalized-event weight is degree one -/

/-- The KraftMeasure normalized-event readout: tally `(a, w)` = (signed total, multiplicity mass),
weight `a²/w`. -/
noncomputable def kraftΦ (x : ℝ × ℝ) : ℝ := x.1 ^ 2 / x.2

/-- **N2c.** `kraftΦ` is homogeneous of degree one (everywhere, so in particular on `w > 0`). -/
theorem kraftΦ_degree_one : ∀ c : ℝ, 0 < c → ∀ x : ℝ × ℝ, kraftΦ (c • x) = c ^ 1 * kraftΦ x := by
  intro c hc x
  unfold kraftΦ
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, pow_one]
  calc (c * x.1) ^ 2 / (c * x.2) = c * (c * c⁻¹) * (x.1 ^ 2 / x.2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
    _ = c * (x.1 ^ 2 / x.2) := by
        rw [mul_inv_cancel₀ hc.ne']
        ring

/-- **N2c.** So the KraftMeasure weight gives a matched pair no interference. -/
theorem kraft_matched_no_interference (v : ι → ℝ × ℝ) {A B : Finset ι} (hd : Disjoint A B)
    (hm : tally v A = tally v B) : I₂ (readout kraftΦ v) A B = 0 :=
  degree_one_matched_no_interference kraftΦ kraftΦ_degree_one v hd hm

/-- **N2c, cross-check (P2).** `QLF_KraftMeasure`'s own equality case says the same: a matched pair
`(a, p) = (b, q)` has equal mean phase, so its merged weight is exactly the sum. -/
theorem kraft_matched_agrees {a p : ℚ} (hp : 0 < p) :
    (a + a) ^ 2 / (p + p) = a ^ 2 / p + a ^ 2 / p :=
  (QLF.merge_eq_sum_iff hp hp).mpr rfl

/-! ## N3 — sublinear readouts never interfere constructively -/

section Sublinear

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- **N3.** A readout that is convex on `C` and doubles under doubling there is sub-additive on `C`. -/
theorem sublinear_subadditive {C : Set V} {Φ : V → ℝ} (hconv : ConvexOn ℝ C Φ)
    (h2 : ∀ x ∈ C, (2 : ℝ) • x ∈ C) (hhom : ∀ x ∈ C, Φ ((2 : ℝ) • x) = 2 * Φ x)
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) : Φ (x + y) ≤ Φ x + Φ y := by
  have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ C :=
    hconv.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hxy : x + y = (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
    rw [smul_add, smul_smul, smul_smul]
    norm_num
  have hc := hconv.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [hxy, hhom _ hm]
  linarith

/-- **N3, for events.** Under a convex degree-1 readout, two disjoint events whose tallies lie in
`C` never interfere constructively: `I₂ ≤ 0`. -/
theorem sublinear_no_constructive_interference {C : Set V} {Φ : V → ℝ}
    (hconv : ConvexOn ℝ C Φ) (h2 : ∀ x ∈ C, (2 : ℝ) • x ∈ C)
    (hhom : ∀ x ∈ C, Φ ((2 : ℝ) • x) = 2 * Φ x)
    (v : ι → V) {A B : Finset ι} (hd : Disjoint A B)
    (hA : tally v A ∈ C) (hB : tally v B ∈ C) :
    I₂ (readout Φ v) A B ≤ 0 := by
  unfold I₂ readout
  rw [tally_union v hd]
  linarith [sublinear_subadditive hconv h2 hhom hA hB]

end Sublinear

/-! ## N4 — complete cancellation needs signed tallies -/

/-- **N4.** With non-negative tallies and a readout vanishing only at `0`, an event of non-zero
weight cannot be cancelled by any disjoint event: **no dark fringe from unsigned counts.** -/
theorem unsigned_no_dark_fringe {n : ℕ} (Φ : (Fin n → ℝ) → ℝ) (hΦ0 : Φ 0 = 0)
    (hΦpos : ∀ x, Φ x = 0 → x = 0) (v : ι → Fin n → ℝ) (hv : ∀ h, 0 ≤ v h)
    {A B : Finset ι} (hd : Disjoint A B) (hA : readout Φ v A ≠ 0) :
    readout Φ v (A ∪ B) ≠ 0 := by
  intro h0
  unfold readout at h0 hA
  rw [tally_union v hd] at h0
  have hsum := hΦpos _ h0
  have hA0 : 0 ≤ tally v A := by
    unfold tally
    exact Finset.sum_nonneg (fun h _ => hv h)
  have hB0 : 0 ≤ tally v B := by
    unfold tally
    exact Finset.sum_nonneg (fun h _ => hv h)
  have hzero : tally v A = 0 := by
    funext i
    have h1 := congrFun hsum i
    have h2 := Pi.le_def.mp hA0 i
    have h3 := Pi.le_def.mp hB0 i
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 ⊢
    linarith
  exact hA (by rw [hzero, hΦ0])

/-! ## N5 — the squared complex tally interferes both ways, and only pairwise -/

/-- The Born readout: squared modulus of a complex tally. -/
noncomputable def normSqΦ (z : ℂ) : ℝ := Complex.normSq z

/-- The Born event weight. -/
noncomputable def born (v : ι → ℂ) : Finset ι → ℝ := readout normSqΦ v

/-- **N5.** The Born interference term is the real part of the cross term. -/
theorem born_I₂ (v : ι → ℂ) {A B : Finset ι} (hd : Disjoint A B) :
    I₂ (born v) A B = 2 * (tally v A * (starRingEnd ℂ) (tally v B)).re := by
  unfold I₂ born readout normSqΦ
  rw [tally_union v hd, Complex.normSq_add]
  ring

/-- **N5.** The Born readout is homogeneous of degree two. -/
theorem born_degree_two : ∀ c : ℝ, 0 < c → ∀ z : ℂ, normSqΦ (c • z) = c ^ 2 * normSqΦ z := by
  intro c hc z
  unfold normSqΦ
  rw [Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- **N5.** So a matched pair gets exactly the quantum factor two (from N2b). -/
theorem born_matched_factor (v : ι → ℂ) {A B : Finset ι} (hd : Disjoint A B)
    (hm : tally v A = tally v B) :
    born v (A ∪ B) = 2 * (born v A + born v B) := by
  unfold born
  rw [matched_pair_factor normSqΦ 2 (by norm_num) born_degree_two v hd hm]
  norm_num

/-- **N5.** Opposite tallies cancel completely: the dark fringe N4 forbids for unsigned counts. -/
theorem born_dark_fringe (v : ι → ℂ) {A B : Finset ι} (hd : Disjoint A B)
    (hneg : tally v B = -tally v A) : born v (A ∪ B) = 0 := by
  unfold born readout normSqΦ
  rw [tally_union v hd, hneg]
  simp

/-- **N5.** Born interference is purely pairwise: Sorkin's third-order term vanishes. -/
theorem born_I₃ (v : ι → ℂ) {A B C : Finset ι} (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) : I₃ (born v) A B C = 0 := by
  unfold I₃ born readout normSqΦ
  rw [tally_union v (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩), tally_union v hAB,
    tally_union v hAC, tally_union v hBC]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

end QLF.InterferenceNoGo
