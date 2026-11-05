import QLF_BornProbability

/-!
# QLF_BornFromWays — the Born rule is the count of equal ways

Issue #207, the measurement postulate. [`QLF_BornCounting`](QLF_BornCounting.lean) showed that the
Born weight `‖a‖²` is a pair count, and [`QLF_BornProbability`](QLF_BornProbability.lean) that the
count ratio is a probability measure. Neither shows that a probability *must* be that ratio. This
module does, from two rules about probability and one fact about states.

The setting is an outcome register `ψ : Fin n → ℤ[i]` (unnormalized, as in
[`QLF_StateSpace`](QLF_StateSpace.lean)). A *probability assignment* `P` gives each outcome a rational
number, and is asked to obey:

* **`perm` (no outcome is privileged by its label).** Relabeling the outcomes relabels the
  probabilities. This is the only symmetry used, and it is used only on the register whose
  amplitudes are all `1`.
* **`normalized`.** The probabilities of a non-degenerate register sum to `1`.
* **`refine` (probability adds over ways).** An outcome of norm `m` is `m` unit ways: when a record
  (an environment, an apparatus) tells the ways apart, the outcome splits into `m` orthogonal unit
  outcomes, and its probability is the sum of theirs. The input here is the norm, which is unitarity's
  Pythagoras (the squared length of an orthogonal sum is the sum of the squared lengths) together
  with `pairCount = ways` from `QLF_BornCounting`. It is not a probability rule.

**Theorem (`born_from_ways`).** Every such assignment is the Born rule: `P ψ i = ‖ψᵢ‖² / Σⱼ ‖ψⱼ‖²`.

The proof is counting. Refining to unit ways turns every register into the all-ones register on
`N = Σ ‖ψⱼ‖²` outcomes; relabeling symmetry makes that uniform, so each unit way has probability
`1/N`; and outcome `i` owns `‖ψᵢ‖²` of them.

**R6a check.** The interface is satisfiable (`bornAssignment`) and `born_from_ways` shows it pins `P`
completely, so it is neither empty nor free: it excludes every other rule, including the modulus
`|ψᵢ|` and every `|ψᵢ|^q` with `q ≠ 2` (`modulus_rule_excluded` is the worked case).

**Classical credit.** This is Zurek's envariance argument (*Phys. Rev. A* **71**, 052105 (2005)) in
finite form; Deutsch's decision-theoretic derivation (*Proc. R. Soc. A* **455**, 3129 (1999)) reaches
the same rule.
Zurek's argument needs a continuity step to reach irrational weights. Here none is needed, and that
is the QLF contribution: amplitudes are Gaussian integers, so every Born weight is a ratio of whole
counts, and the rational case is the only case. No continuum enters at any step.

No axioms.
-/

namespace QLF.BornFromWays

open QLF.StateSpace

/-- The fibre of outcome `i` under a refinement map `f`: the unit ways that belong to `i`. -/
def fibre {n N : ℕ} (f : Fin N → Fin n) (i : Fin n) : Finset (Fin N) :=
  Finset.univ.filter (fun j => f j = i)

/-- The register whose every amplitude is `1`: `N` equal unit ways. -/
def units (N : ℕ) : Fin N → GaussianInt := fun _ => 1

/-- A probability assignment on outcome registers, obeying relabeling symmetry, normalization and
    additivity over unit ways. -/
structure ProbAssignment where
  /-- The probability of outcome `i` in register `ψ`. -/
  P : {n : ℕ} → (Fin n → GaussianInt) → Fin n → ℚ
  /-- Relabeling the outcomes relabels the probabilities. -/
  perm : ∀ {n : ℕ} (ψ : Fin n → GaussianInt) (σ : Equiv.Perm (Fin n)) (i : Fin n),
    P (ψ ∘ σ) i = P ψ (σ i)
  /-- A non-degenerate register's probabilities sum to `1`. -/
  normalized : ∀ {n : ℕ} (ψ : Fin n → GaussianInt),
    (∑ j, (Zsqrtd.norm (ψ j) : ℚ)) ≠ 0 → ∑ i, P ψ i = 1
  /-- An outcome of norm `m` is `m` unit ways, and its probability is the sum of theirs. -/
  refine : ∀ {n N : ℕ} (ψ : Fin n → GaussianInt) (f : Fin N → Fin n),
    (∀ i, ((fibre f i).card : ℤ) = Zsqrtd.norm (ψ i)) →
    ∀ i, P ψ i = ∑ j ∈ fibre f i, P (units N) j

lemma norm_one : Zsqrtd.norm (1 : GaussianInt) = 1 := by decide

lemma norm_nonneg' (a : GaussianInt) : 0 ≤ Zsqrtd.norm a :=
  Zsqrtd.norm_nonneg (by norm_num) a

/-- **Equal ways are equally likely.** On the all-ones register, relabeling symmetry and
    normalization force every unit way to have probability `1/N`. -/
theorem uniform (A : ProbAssignment) {N : ℕ} (j : Fin N) : A.P (units N) j = 1 / N := by
  have hN : (N : ℚ) ≠ 0 := by
    have : 0 < N := Fin.pos j
    exact_mod_cast this.ne'
  have hconst : ∀ k, A.P (units N) k = A.P (units N) j := by
    intro k
    have h := A.perm (units N) (Equiv.swap j k) j
    have hu : units N ∘ (Equiv.swap j k) = units N := rfl
    rw [hu, Equiv.swap_apply_left] at h
    exact h.symm
  have hsum := A.normalized (units N) (by
    simp only [units, norm_one, Int.cast_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact hN)
  rw [Finset.sum_congr rfl (fun k _ => hconst k), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  field_simp
  linarith

/-- The fibres of a refinement partition its unit ways, so their sizes add up to `N`. -/
lemma sum_fibre_card {n N : ℕ} (f : Fin N → Fin n) : ∑ i, ((fibre f i).card : ℚ) = N := by
  have h := (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin N)))
    (t := (Finset.univ : Finset (Fin n))) (f := f) (fun _ _ => Finset.mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at h
  unfold fibre
  exact_mod_cast h.symm

/-- **Born from a refinement.** Given any refinement of `ψ` into unit ways, the assignment is the
    Born rule. -/
theorem born_of_refinement (A : ProbAssignment) {n N : ℕ} (ψ : Fin n → GaussianInt)
    (f : Fin N → Fin n) (hf : ∀ i, ((fibre f i).card : ℤ) = Zsqrtd.norm (ψ i)) (i : Fin n) :
    A.P ψ i = bornProb ψ i := by
  rw [A.refine ψ f hf i, Finset.sum_congr rfl (fun j _ => uniform A j), Finset.sum_const,
    nsmul_eq_mul]
  have hc : ∀ k, ((fibre f k).card : ℚ) = (Zsqrtd.norm (ψ k) : ℚ) := by
    intro k; exact_mod_cast hf k
  have hN : (N : ℚ) = ∑ j, (Zsqrtd.norm (ψ j) : ℚ) := by
    rw [← sum_fibre_card f]; exact Finset.sum_congr rfl (fun k _ => hc k)
  unfold bornProb
  rw [hc i, ← hN]
  ring

/-- **Every register can be refined into unit ways**: outcome `i` gets `‖ψᵢ‖²` of them. -/
theorem exists_refinement {n : ℕ} (ψ : Fin n → GaussianInt) :
    ∃ N, ∃ f : Fin N → Fin n, ∀ i, ((fibre f i).card : ℤ) = Zsqrtd.norm (ψ i) := by
  let m : Fin n → ℕ := fun i => (Zsqrtd.norm (ψ i)).toNat
  let e : ((k : Fin n) × Fin (m k)) ≃ Fin (∑ k, m k) := finSigmaFinEquiv
  refine ⟨∑ k, m k, fun j => (e.symm j).1, fun i => ?_⟩
  have hcard : (fibre (fun j => (e.symm j).1) i).card = m i := by
    unfold fibre
    rw [Finset.card_filter, ← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_sigma]
    simp [apply_ite Finset.card]
  rw [hcard]
  exact Int.toNat_of_nonneg (norm_nonneg' _)

/-- **The Born rule is the count of equal ways.** Any assignment obeying relabeling symmetry,
    normalization and additivity over unit ways is `‖ψᵢ‖² / Σⱼ ‖ψⱼ‖²`. -/
theorem born_from_ways (A : ProbAssignment) {n : ℕ} (ψ : Fin n → GaussianInt) (i : Fin n) :
    A.P ψ i = bornProb ψ i := by
  obtain ⟨N, f, hf⟩ := exists_refinement ψ
  exact born_of_refinement A ψ f hf i

/-! ## The interface is satisfiable (R6a), so it is a characterization, not an empty claim -/

/-- The Born rule obeys all three rules. -/
def bornAssignment : ProbAssignment where
  P := fun ψ i => bornProb ψ i
  perm := by
    intro n ψ σ i
    unfold bornProb
    congr 1
    exact Equiv.sum_comp σ (fun j => (Zsqrtd.norm (ψ j) : ℚ))
  normalized := by
    intro n ψ h
    exact QLF.BornProbability.bornProb_sum_eq_one ψ h
  refine := by
    intro n N ψ f hf i
    have hc : ∀ k, ((fibre f k).card : ℚ) = (Zsqrtd.norm (ψ k) : ℚ) := by
      intro k; exact_mod_cast hf k
    have hN : (N : ℚ) = ∑ j, (Zsqrtd.norm (ψ j) : ℚ) := by
      rw [← sum_fibre_card f]; exact Finset.sum_congr rfl (fun k _ => hc k)
    have hu : ∀ j : Fin N, bornProb (units N) j = 1 / N := by
      intro j
      simp only [bornProb, units, norm_one, Int.cast_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl (fun j _ => hu j), Finset.sum_const, nsmul_eq_mul]
    unfold bornProb
    rw [hc i, ← hN]
    ring

/-- The assignment is unique: any two assignments obeying the rules agree everywhere. -/
theorem assignment_unique (A B : ProbAssignment) {n : ℕ} (ψ : Fin n → GaussianInt) (i : Fin n) :
    A.P ψ i = B.P ψ i := by
  rw [born_from_ways A, born_from_ways B]

/-- Worked case: the register `(1 + i, 1)`. Its first outcome has two unit ways and the second one,
    so every admissible assignment gives `2/3`. -/
theorem two_thirds (A : ProbAssignment) :
    A.P (![⟨1, 1⟩, 1] : Fin 2 → GaussianInt) 0 = 2 / 3 := by
  rw [born_from_ways]
  have h1 : Zsqrtd.norm (⟨1, 1⟩ : GaussianInt) = 2 := by decide
  simp only [bornProb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    h1, norm_one]
  norm_num

/-- **The modulus rule is excluded.** Reading probability as `|ψᵢ|` rather than `|ψᵢ|²` would give
    the register `(1 + i, 1)` the ratio `√2 : 1`, which is not even rational; the rules give `2 : 1`. -/
theorem modulus_rule_excluded (A : ProbAssignment) :
    A.P (![⟨1, 1⟩, 1] : Fin 2 → GaussianInt) 0 = 2 * A.P (![⟨1, 1⟩, 1] : Fin 2 → GaussianInt) 1 := by
  rw [born_from_ways, born_from_ways]
  have h1 : Zsqrtd.norm (⟨1, 1⟩ : GaussianInt) = 2 := by decide
  simp only [bornProb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    h1, norm_one]
  norm_num

end QLF.BornFromWays
