import Mathlib
import QLF_FreeEnergy

/-!
# QLF_MrEUpdate — the maximum-relative-entropy update for one binary observation (issue #221)

The specification is [`MrE_Update.md`](../MrE_Update.md). This module fixes the model that
issue #221 asked for and proves the properties that hold in it.

**The model (stated, so every implementation agrees on it).**

* Hypothesis space `{H, ¬H}`; **prior** `P(H) = p`, any `p` with `0 < p < 1` (not only the uniform
  prior).
* One **binary observation** `E` with likelihoods `a = P(E | H)` and `b = P(E | ¬H)` in `[0, 1]`.
* **Evidence** `m = P(E) = p·a + (1−p)·b`; **posterior** `P(H | E) = p·a / m`, and
  `P(H | ¬E) = p·(1−a) / (1−m)`.
* **Information measure:** the Kullback–Leibler divergence in nats, `binary_kl` from
  [`QLF_FreeEnergy`](QLF_FreeEnergy.lean), with Mathlib's `Real.log` (so `0·log 0 = 0`).

**What is proved.**

1. `eig_le_log_two` — the **expected** information gain of one binary observation,
   `m·D(P(H|E) ‖ p) + (1−m)·D(P(H|¬E) ‖ p)` (`eig_eq_expected_kl`), is at most `log 2`, for
   **every** prior and every likelihood pair. It is the mutual information `I(H; E)`, which
   equals `h(m) − p·h(a) − (1−p)·h(b)` (`eig_eq_entropy`), and `h ≤ log 2`.
2. `eig_nonneg` — it is never negative (concavity of the binary entropy).
3. `eig_eq_log_two_iff` — it reaches `log 2` exactly when the prior is uniform and the
   observation is perfectly discriminating: the half-spin closure case of `QLF_FreeEnergy`.
4. `pointwise_bound_false` — the **pointwise** bound is false: one outcome can move the posterior
   by more than `log 2`. Aria's counterexample on #221: prior `0.01`, `P(E|H) = 1`,
   `P(E|¬H) = 1/9801`, posterior `0.99`, divergence `0.98·log 99 ≈ 4.50 > log 2`.
5. `mre_update_unique` — Caticha's MrE: among joint distributions that put all mass on the
   observed outcome, the one closest to the prior joint in relative entropy is **unique** and is
   the Bayes posterior (`mre_eq_kl_posterior`).
6. `prior_unique_minimizer`, `uninformative_posterior`, `uninformative_eig` — with no constraint
   the update returns the prior, and an observation with `a = b` changes nothing.
7. `sequential_update` — two **conditionally independent** observations compose: updating on
   one and then the other equals one update with the product likelihoods. In odds form the
   log-likelihood ratios add. Information gains do **not** add in general, and nothing here
   claims that they do.

No axioms beyond Lean's own.
-/

namespace QLF.MrEUpdate

open QLF

/-! ## The model -/

/-- `P(E) = p·a + (1−p)·b`: the probability of the observation under the prior. -/
noncomputable def evidence (p a b : ℝ) : ℝ := p * a + (1 - p) * b

/-- The Bayes posterior `P(H | E) = p·a / P(E)`. -/
noncomputable def posterior (p a b : ℝ) : ℝ := p * a / evidence p a b

/-- The posterior after the other outcome, `P(H | ¬E)`. -/
noncomputable def posteriorNot (p a b : ℝ) : ℝ := posterior p (1 - a) (1 - b)

/-- Expected information gain of the observation, written as the mutual information
`I(H; E) = Σ P(h) P(e|h) log (P(e|h) / P(e))`. -/
noncomputable def eig (p a b : ℝ) : ℝ :=
  p * a * Real.log (a / evidence p a b) + (1 - p) * b * Real.log (b / evidence p a b)
  + p * (1 - a) * Real.log ((1 - a) / (1 - evidence p a b))
  + (1 - p) * (1 - b) * Real.log ((1 - b) / (1 - evidence p a b))

/-- `QLF_FreeEnergy`'s `binary_entropy` is Mathlib's `Real.binEntropy`. -/
theorem binary_entropy_eq_binEntropy (q : ℝ) : binary_entropy q = Real.binEntropy q := by
  simp only [binary_entropy, Real.binEntropy, Real.log_inv]
  ring

/-! ## Basic algebra of the update -/

theorem evidence_mul_posterior {p a b : ℝ} (hm : evidence p a b ≠ 0) :
    evidence p a b * posterior p a b = p * a := by
  unfold posterior
  rw [mul_div_assoc', mul_comm (evidence p a b) (p * a), mul_div_assoc, div_self hm, mul_one]

theorem one_sub_posterior {p a b : ℝ} (hm : evidence p a b ≠ 0) :
    1 - posterior p a b = (1 - p) * b / evidence p a b := by
  have h : (1 - p) * b = evidence p a b - p * a := by unfold evidence; ring
  unfold posterior
  rw [h, sub_div, div_self hm]

theorem evidence_mul_one_sub_posterior {p a b : ℝ} (hm : evidence p a b ≠ 0) :
    evidence p a b * (1 - posterior p a b) = (1 - p) * b := by
  rw [one_sub_posterior hm, mul_div_assoc', mul_comm (evidence p a b) ((1 - p) * b),
    mul_div_assoc, div_self hm, mul_one]

/-- The two outcomes' evidences sum to one. -/
theorem evidence_not (p a b : ℝ) : evidence p (1 - a) (1 - b) = 1 - evidence p a b := by
  unfold evidence; ring

/-- With `0 < p < 1` and positive likelihoods, the posterior is strictly inside `(0, 1)`. -/
theorem posterior_mem {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : 0 < b) :
    0 < evidence p a b ∧ 0 < posterior p a b ∧ 0 < 1 - posterior p a b := by
  have h1 : 0 < p * a := mul_pos hp0 ha
  have h2 : 0 < (1 - p) * b := mul_pos (sub_pos.2 hp1) hb
  have hm : 0 < evidence p a b := by unfold evidence; linarith
  have e1 := evidence_mul_posterior (ne_of_gt hm)
  have e2 := evidence_mul_one_sub_posterior (ne_of_gt hm)
  refine ⟨hm, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    nlinarith
  · by_contra hc
    push_neg at hc
    nlinarith

/-! ## Expected information gain = mutual information -/

private theorem log_term_split (w y m : ℝ) (h : w * y ≠ 0 → 0 < m) :
    w * y * Real.log (y / m) = w * (y * Real.log y) - w * y * Real.log m := by
  by_cases hz : w * y = 0
  · rcases mul_eq_zero.mp hz with hw | hy
    · rw [hw]; ring
    · rw [hy]; ring
  · have hy : y ≠ 0 := right_ne_zero_of_mul hz
    rw [Real.log_div hy (ne_of_gt (h hz))]
    ring

/-- **The entropy form.** `I(H; E) = h(P(E)) − p·h(a) − (1−p)·h(b)`, for all `p, a, b ∈ [0, 1]`,
boundary cases included. -/
theorem eig_eq_entropy {p a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    eig p a b = binary_entropy (evidence p a b) - p * binary_entropy a
      - (1 - p) * binary_entropy b := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hpa : 0 ≤ p * a := mul_nonneg hp0 ha0
  have hpb : 0 ≤ (1 - p) * b := mul_nonneg hq0 hb0
  have hpa' : 0 ≤ p * (1 - a) := mul_nonneg hp0 (by linarith)
  have hpb' : 0 ≤ (1 - p) * (1 - b) := mul_nonneg hq0 (by linarith)
  have hE : evidence p a b = p * a + (1 - p) * b := rfl
  have hE' : 1 - evidence p a b = p * (1 - a) + (1 - p) * (1 - b) := by unfold evidence; ring
  have c1 : p * a ≠ 0 → 0 < evidence p a b := fun h => by
    have : 0 < p * a := lt_of_le_of_ne hpa (Ne.symm h)
    rw [hE]; linarith
  have c2 : (1 - p) * b ≠ 0 → 0 < evidence p a b := fun h => by
    have : 0 < (1 - p) * b := lt_of_le_of_ne hpb (Ne.symm h)
    rw [hE]; linarith
  have c3 : p * (1 - a) ≠ 0 → 0 < 1 - evidence p a b := fun h => by
    have : 0 < p * (1 - a) := lt_of_le_of_ne hpa' (Ne.symm h)
    rw [hE']; linarith
  have c4 : (1 - p) * (1 - b) ≠ 0 → 0 < 1 - evidence p a b := fun h => by
    have : 0 < (1 - p) * (1 - b) := lt_of_le_of_ne hpb' (Ne.symm h)
    rw [hE']; linarith
  unfold eig
  rw [log_term_split p a _ c1, log_term_split (1 - p) b _ c2,
    log_term_split p (1 - a) _ c3, log_term_split (1 - p) (1 - b) _ c4]
  unfold binary_entropy
  rw [hE]
  ring

/-- One outcome's contribution: `P(E)·D(P(H|E) ‖ p)` in the mutual-information form. -/
theorem kl_branch {p a b : ℝ} (hp : p ≠ 0) (hp' : 1 - p ≠ 0) (hm : evidence p a b ≠ 0) :
    evidence p a b * binary_kl (posterior p a b) p
      = p * a * Real.log (a / evidence p a b)
        + (1 - p) * b * Real.log (b / evidence p a b) := by
  have h1 : posterior p a b / p = a / evidence p a b := by
    unfold posterior
    rw [div_div, div_eq_div_iff (mul_ne_zero hm hp) hm]
    ring
  have h2 : (1 - posterior p a b) / (1 - p) = b / evidence p a b := by
    rw [one_sub_posterior hm, div_div, div_eq_div_iff (mul_ne_zero hm hp') hm]
    ring
  have hmq := evidence_mul_posterior hm
  have hmq' := evidence_mul_one_sub_posterior hm
  unfold binary_kl
  rw [h1, h2]
  linear_combination (Real.log (a / evidence p a b)) * hmq
    + (Real.log (b / evidence p a b)) * hmq'

/-- **The KL form.** The expected information gain is the evidence-weighted divergence of the
two possible posteriors from the prior — the quantity Aria's question on #221 is about. -/
theorem eig_eq_expected_kl {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hm0 : 0 < evidence p a b) (hm1 : evidence p a b < 1) :
    eig p a b = evidence p a b * binary_kl (posterior p a b) p
      + (1 - evidence p a b) * binary_kl (posteriorNot p a b) p := by
  have hp : p ≠ 0 := ne_of_gt hp0
  have hp' : 1 - p ≠ 0 := ne_of_gt (sub_pos.2 hp1)
  have hb1 := kl_branch (a := a) (b := b) hp hp' (ne_of_gt hm0)
  have hn : evidence p (1 - a) (1 - b) ≠ 0 := by
    rw [evidence_not]; exact ne_of_gt (sub_pos.2 hm1)
  have hb2 := kl_branch (a := 1 - a) (b := 1 - b) hp hp' hn
  rw [evidence_not] at hb2
  unfold eig posteriorNot
  linear_combination -hb1 - hb2

/-! ## The bound, its sharpness, and the failure of the pointwise version -/

/-- **The bound (#221).** The expected information gain of one binary observation is at most
`log 2` nats, whatever the prior and the likelihoods. -/
theorem eig_le_log_two {p a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    eig p a b ≤ Real.log 2 := by
  rw [eig_eq_entropy hp0 hp1 ha0 ha1 hb0 hb1]
  have h1 : binary_entropy (evidence p a b) ≤ Real.log 2 := by
    rw [binary_entropy_eq_binEntropy]; exact Real.binEntropy_le_log_two
  have h2 : 0 ≤ p * binary_entropy a := mul_nonneg hp0 (binary_entropy_nonneg ha0 ha1)
  have h3 : 0 ≤ (1 - p) * binary_entropy b :=
    mul_nonneg (by linarith) (binary_entropy_nonneg hb0 hb1)
  linarith

/-- Expected information gain is never negative. -/
theorem eig_nonneg {p a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ eig p a b := by
  rw [eig_eq_entropy hp0 hp1 ha0 ha1 hb0 hb1]
  have hc := Real.strictConcave_binEntropy.concaveOn.2 (Set.mem_Icc.2 ⟨ha0, ha1⟩)
    (Set.mem_Icc.2 ⟨hb0, hb1⟩) hp0 (sub_nonneg.2 hp1) (by ring)
  simp only [smul_eq_mul] at hc
  simp only [binary_entropy_eq_binEntropy]
  unfold evidence
  linarith

/-- **Saturation.** For a non-degenerate prior, the bound is reached exactly when the prior is
uniform and the observation is perfectly discriminating — the half-spin closure of
`QLF_FreeEnergy` (`binary_kl_delta_uniform`). -/
theorem eig_eq_log_two_iff {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    eig p a b = Real.log 2 ↔ p = 1 / 2 ∧ ((a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)) := by
  constructor
  · intro h
    rw [eig_eq_entropy hp0.le hp1.le ha0 ha1 hb0 hb1] at h
    have h1 : binary_entropy (evidence p a b) ≤ Real.log 2 := by
      rw [binary_entropy_eq_binEntropy]; exact Real.binEntropy_le_log_two
    have h2 : 0 ≤ p * binary_entropy a := mul_nonneg hp0.le (binary_entropy_nonneg ha0 ha1)
    have h3 : 0 ≤ (1 - p) * binary_entropy b :=
      mul_nonneg (by linarith) (binary_entropy_nonneg hb0 hb1)
    have hm : binary_entropy (evidence p a b) = Real.log 2 := by linarith
    have hpa : p * binary_entropy a = 0 := by linarith
    have hpb : (1 - p) * binary_entropy b = 0 := by linarith
    have ha := (mul_eq_zero.mp hpa).resolve_left (ne_of_gt hp0)
    have hb := (mul_eq_zero.mp hpb).resolve_left (ne_of_gt (sub_pos.2 hp1))
    simp only [binary_entropy_eq_binEntropy] at hm ha hb
    have hm' := Real.binEntropy_eq_log_two.mp hm
    have ha' := Real.binEntropy_eq_zero.mp ha
    have hb' := Real.binEntropy_eq_zero.mp hb
    unfold evidence at hm'
    have h2inv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exfalso; linarith
    · exact ⟨by linarith, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨by linarith, Or.inl ⟨rfl, rfl⟩⟩
    · exfalso; linarith
  · rintro ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rw [eig_eq_entropy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)]
      have he : evidence (1 / 2) 1 0 = 2⁻¹ := by unfold evidence; norm_num
      rw [he]
      simp only [binary_entropy_eq_binEntropy, Real.binEntropy_two_inv, Real.binEntropy_one,
        Real.binEntropy_zero]
      ring
    · rw [eig_eq_entropy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)]
      have he : evidence (1 / 2) 0 1 = 2⁻¹ := by unfold evidence; norm_num
      rw [he]
      simp only [binary_entropy_eq_binEntropy, Real.binEntropy_two_inv, Real.binEntropy_one,
        Real.binEntropy_zero]
      ring

/-- **The pointwise bound is false** (Aria's counterexample on #221). With prior `0.01`,
`P(E|H) = 1` and `P(E|¬H) = 1/9801`, observing `E` gives posterior `0.99`, and the divergence of
that posterior from the prior, `0.98·log 99 ≈ 4.50`, exceeds `log 2`. So the bound holds for the
expected gain, not for each outcome. -/
theorem pointwise_bound_false :
    posterior (1 / 100) 1 (1 / 9801) = 99 / 100 ∧
      Real.log 2 < binary_kl (99 / 100) (1 / 100) := by
  constructor
  · unfold posterior evidence; norm_num
  · have e1 : (99 / 100 : ℝ) / (1 / 100) = 99 := by norm_num
    have e2 : (1 - 99 / 100 : ℝ) / (1 - 1 / 100) = 99⁻¹ := by norm_num
    unfold binary_kl
    rw [e1, e2, Real.log_inv]
    have h4 : Real.log (2 * 2) < Real.log 99 := Real.log_lt_log (by norm_num) (by norm_num)
    have h22 : Real.log (2 * 2) = Real.log 2 + Real.log 2 :=
      Real.log_mul two_ne_zero two_ne_zero
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith

/-! ## Gibbs' inequality for two outcomes -/

private theorem kl_term_gt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    x - y < x * Real.log (x / y) := by
  have hyx : y / x ≠ 1 := fun h => hne ((div_eq_one_iff_eq (ne_of_gt hx)).mp h).symm
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hy hx) hyx
  have hneg : Real.log (x / y) = -Real.log (y / x) := by
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy), Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
    ring
  have hxy : x * (y / x) = y := by
    rw [mul_div_assoc', mul_comm x y, mul_div_assoc, div_self (ne_of_gt hx), mul_one]
  rw [hneg]
  nlinarith [mul_lt_mul_of_pos_left hlog hx, hxy]

private theorem kl_term_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, zero_mul]; linarith
  · by_cases hxy : x = y
    · rw [hxy, div_self (ne_of_gt hy), Real.log_one]; linarith
    · exact (kl_term_gt h hy hxy).le

/-- Relative entropy is non-negative (two outcomes). -/
theorem binary_kl_nonneg {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ binary_kl q r := by
  have h1 := kl_term_ge hq0 hr0
  have h2 := kl_term_ge (sub_nonneg.2 hq1) (sub_pos.2 hr1)
  unfold binary_kl
  linarith

/-- Relative entropy is strictly positive away from the reference. -/
theorem binary_kl_pos {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hne : q ≠ r) : 0 < binary_kl q r := by
  unfold binary_kl
  rcases hq0.eq_or_lt with h | h
  · have h1 := kl_term_ge hq0 hr0
    have h2 := kl_term_gt (x := 1 - q) (y := 1 - r) (by linarith) (by linarith)
      (fun e => hne (by linarith))
    linarith
  · have h1 := kl_term_gt h hr0 hne
    have h2 := kl_term_ge (sub_nonneg.2 hq1) (sub_pos.2 hr1)
    linarith

theorem binary_kl_self {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : binary_kl r r = 0 := by
  unfold binary_kl
  rw [div_self (ne_of_gt hr0), div_self (ne_of_gt (sub_pos.2 hr1)), Real.log_one]
  ring

theorem binary_kl_eq_zero_iff {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r)
    (hr1 : r < 1) : binary_kl q r = 0 ↔ q = r := by
  constructor
  · intro h
    by_contra hne
    have := binary_kl_pos hq0 hq1 hr0 hr1 hne
    linarith
  · rintro rfl
    exact binary_kl_self hr0 hr1

/-- **No constraint returns the prior.** Minimising relative entropy to the prior with no
evidence-constraint is solved by the prior itself, and by nothing else. -/
theorem prior_unique_minimizer {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    binary_kl p p ≤ binary_kl q p ∧ (binary_kl q p = binary_kl p p ↔ q = p) := by
  rw [binary_kl_self hp0 hp1]
  exact ⟨binary_kl_nonneg hq0 hq1 hp0 hp1, binary_kl_eq_zero_iff hq0 hq1 hp0 hp1⟩

/-- An observation that is equally likely under both hypotheses leaves the prior unchanged. -/
theorem uninformative_posterior {p a : ℝ} (ha : a ≠ 0) : posterior p a a = p := by
  have h : evidence p a a = a := by unfold evidence; ring
  unfold posterior
  rw [h, mul_div_assoc, div_self ha, mul_one]

/-- …and carries no information. -/
theorem uninformative_eig {p a : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    eig p a a = 0 := by
  have h : evidence p a a = a := by unfold evidence; ring
  rw [eig_eq_entropy hp0 hp1 ha0 ha1 ha0 ha1, h]
  ring

/-! ## The MrE update is the Bayes update, uniquely -/

/-- Relative entropy, from the prior joint `(p·a, (1−p)·b, p·(1−a), (1−p)·(1−b))`, of the
candidate joint that puts mass `s` on `H ∧ E`, `1 − s` on `¬H ∧ E` and nothing on `¬E` — the
distributions allowed by the constraint "E was observed". -/
noncomputable def mreDivergence (s p a b : ℝ) : ℝ :=
  s * Real.log (s / (p * a)) + (1 - s) * Real.log ((1 - s) / ((1 - p) * b))

private theorem log_term_div (x m y : ℝ) (hm : 0 < m) (hy : 0 < y) :
    x * Real.log (x / (m * y)) = x * Real.log (x / y) - x * Real.log m := by
  by_cases hx : x = 0
  · rw [hx]; ring
  · rw [Real.log_div hx (mul_ne_zero (ne_of_gt hm) (ne_of_gt hy)),
      Real.log_mul (ne_of_gt hm) (ne_of_gt hy), Real.log_div hx (ne_of_gt hy)]
    ring

/-- The constrained divergence is the divergence from the Bayes posterior, shifted by the
constant `−log P(E)`. -/
theorem mre_eq_kl_posterior {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : 0 < b)
    (s : ℝ) :
    mreDivergence s p a b = binary_kl s (posterior p a b) - Real.log (evidence p a b) := by
  obtain ⟨hm, hq0, hq1⟩ := posterior_mem hp0 hp1 ha hb
  have e1 := (evidence_mul_posterior (ne_of_gt hm)).symm
  have e2 := (evidence_mul_one_sub_posterior (ne_of_gt hm)).symm
  unfold mreDivergence
  rw [e1, e2, log_term_div s _ _ hm hq0, log_term_div (1 - s) _ _ hm hq1]
  unfold binary_kl
  ring

/-- **MrE uniqueness (Caticha).** Under the constraint "E was observed", the distribution of
least relative entropy to the prior is the Bayes posterior, and it is the only minimiser. -/
theorem mre_update_unique {p a b s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : 0 < b)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    mreDivergence (posterior p a b) p a b ≤ mreDivergence s p a b ∧
      (mreDivergence s p a b = mreDivergence (posterior p a b) p a b ↔
        s = posterior p a b) := by
  obtain ⟨_, hq0, hq1⟩ := posterior_mem hp0 hp1 ha hb
  have hq1' : posterior p a b < 1 := by linarith
  rw [mre_eq_kl_posterior hp0 hp1 ha hb s,
    mre_eq_kl_posterior hp0 hp1 ha hb (posterior p a b), binary_kl_self hq0 hq1']
  have hn := binary_kl_nonneg hs0 hs1 hq0 hq1'
  have hz := binary_kl_eq_zero_iff hs0 hs1 hq0 hq1'
  constructor
  · linarith
  · constructor
    · intro h; exact hz.1 (by linarith)
    · intro h; rw [hz.2 h]

/-! ## Composition -/

/-- **Conditionally independent observations compose.** Updating on `E₁` and then on `E₂` gives
the same posterior as one update on the pair with likelihoods `a₁a₂` and `b₁b₂`. Equivalently,
posterior odds = prior odds × `(a₁/b₁)·(a₂/b₂)`: log-likelihood ratios add. -/
theorem sequential_update {p a₁ b₁ a₂ b₂ : ℝ} (hm1 : evidence p a₁ b₁ ≠ 0)
    (hm12 : evidence p (a₁ * a₂) (b₁ * b₂) ≠ 0) :
    posterior (posterior p a₁ b₁) a₂ b₂ = posterior p (a₁ * a₂) (b₁ * b₂) := by
  have hmq := evidence_mul_posterior hm1
  have hmq' := evidence_mul_one_sub_posterior hm1
  have h1 : evidence (posterior p a₁ b₁) a₂ b₂ * evidence p a₁ b₁
      = evidence p (a₁ * a₂) (b₁ * b₂) := by
    have u := hmq
    have v := hmq'
    simp only [evidence] at u v ⊢
    linear_combination a₂ * u + b₂ * v
  have he : evidence (posterior p a₁ b₁) a₂ b₂ ≠ 0 := by
    have : evidence (posterior p a₁ b₁) a₂ b₂ * evidence p a₁ b₁ ≠ 0 := by rw [h1]; exact hm12
    exact left_ne_zero_of_mul this
  show posterior p a₁ b₁ * a₂ / evidence (posterior p a₁ b₁) a₂ b₂
    = p * (a₁ * a₂) / evidence p (a₁ * a₂) (b₁ * b₂)
  rw [div_eq_div_iff he hm12]
  linear_combination (-(posterior p a₁ b₁ * a₂)) * h1
    + (a₂ * evidence (posterior p a₁ b₁) a₂ b₂) * hmq

end QLF.MrEUpdate
