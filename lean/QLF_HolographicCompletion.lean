import QLF_HolographicBoundary
import QLF_JointClosure

/-!
# QLF_HolographicCompletion — the cut-pair entropy, and what ZFA is as a code

Two gaps named in [`Holography_Audit.md`](../Holography_Audit.md) §3.

**§1 From cut pairs to von Neumann entropy (gap 2).** `cutEntropy` counts `log 2` per shared pair
cut by a region's boundary. That is the von Neumann entropy of the region's reduced state when the
cut pairs are singlets:

* `singlet_reduced`: tracing either half out of the normalized singlet leaves `I/2`.
* `entropy_half_half`: the spectrum `(½, ½)` has Shannon entropy `log 2`, the per-event quantum.
* `entropy_product`: the entropy of a product spectrum is the sum of the entropies.
* `half_id_kronecker`: a Kronecker product of `I/2` factors is a scalar multiple of the
  identity, so the reduced state of `M` cut singlets has the uniform spectrum on `2^M` points.
* `entropy_uniform_pow`, `cutEntropy_eq_vonNeumann`: that spectrum has entropy `M log 2`, which
  is `cutEntropy`.

The one standard step used and not reproved is that the reduced state of a tensor product is the
tensor product of the reduced states (partial trace is multiplicative). The area law itself still
rests on the locality premise of `QLF_LocalAreaLaw`.

**§2 ZFA as a code (gap 5).** The prose reading "`full_zeno_prune` is the boundary decoder" asks
for a code property. Treating the closures as the codewords among all twist words:

* `insertion_detected`, `deletion_detected`, `substitution_detected`: every single insertion,
  deletion or substitution of a twist turns a closure into a non-closure. ZFA **detects** every
  single error.
* `conjugate_pair_undetected`: inserting a conjugate pair keeps a closure a closure, so the
  insertion–deletion distance is exactly 2.
* `single_error_not_correctable`: two distinct closures reach the same word by one deletion each,
  so a single error cannot be **corrected**.

So ZFA is an error-detecting code of distance 2, not an error-correcting code. That is the precise
form of the holographic-QEC reading: no recovery map exists for single errors, so ZFA closure alone
is not a HaPPY-type code. No axioms.

Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

noncomputable section

namespace QLF.HolographicCompletion

open Matrix QLF QLF.HolographicBoundary
open scoped Kronecker

/-! ## §1 Cut pairs and von Neumann entropy -/

/-- Partial trace over the second factor. -/
def reducedA (ρ : QLF.Tsirelson.Q) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑ k, ρ (i, k) (j, k)

/-- The normalized singlet density matrix `|s⟩⟨s| / 2`. -/
def singletState : QLF.Tsirelson.Q :=
  fun a b => (1 / 2 : ℂ) * QLF.JointClosure.s a * star (QLF.JointClosure.s b)

/-- **Tracing out half a singlet leaves the maximally mixed state.** -/
theorem singlet_reduced : reducedA singletState = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reducedA, singletState, QLF.JointClosure.s]

/-- The Shannon entropy of a spectrum. -/
def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- **The reduced singlet's spectrum carries one `log 2`.** -/
theorem entropy_half_half : entropy (fun _ : Fin 2 => (1 / 2 : ℝ)) = per_event_entropy := by
  unfold entropy per_event_entropy Real.negMulLog
  simp [Real.log_inv]

/-- **Entropy adds over product spectra.** -/
theorem entropy_product {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → ℝ) (q : κ → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    entropy (fun x : ι × κ => p x.1 * q x.2) = entropy p + entropy q := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  simp only [Real.negMulLog_mul]
  rw [Finset.sum_comm.symm.symm]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp, hq]
  ring

/-- **A Kronecker product of `I/2` with a scalar identity is a scalar identity.** So the reduced
    state of `M` cut singlets, `(I/2)^{⊗M}`, is `2^{-M}` times the identity. -/
theorem half_id_kronecker {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) :
    ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ (c • (1 : Matrix n n ℂ)) =
      ((1 / 2 : ℂ) * c) • (1 : Matrix (Fin 2 × n) (Fin 2 × n) ℂ) := by
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]

/-- **The uniform spectrum on `2^M` points has entropy `M log 2`.** -/
theorem entropy_uniform_pow (M : ℕ) :
    entropy (fun _ : Fin (2 ^ M) => (1 / 2 ^ M : ℝ)) = M * per_event_entropy := by
  unfold entropy per_event_entropy Real.negMulLog
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (2 : ℝ) ^ M ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [one_div, Real.log_inv, Real.log_pow]
  push_cast
  field_simp

/-- **`cutEntropy` is the von Neumann entropy of the reduced state of the cut singlets.** With
    `M` cut pairs, each a singlet, the reduced state has the uniform spectrum on `2^M` points, whose
    entropy is `cutEntropy`. -/
theorem cutEntropy_eq_vonNeumann {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (V × V)) (A : Finset V) :
    cutEntropy P A =
      entropy (fun _ : Fin (2 ^ (cutPairs P A).card) => (1 / 2 ^ (cutPairs P A).card : ℝ)) := by
  rw [entropy_uniform_pow]
  rfl

/-! ## §2 ZFA as an error-detecting code -/

/-- **A single insertion breaks a closure.** -/
theorem insertion_detected (p q : List Twist) (t : Twist) (h : countBalanced (p ++ q)) :
    ¬ countBalanced (p ++ t :: q) := by
  unfold countBalanced at h ⊢
  simp only [List.count_append, List.count_cons] at h ⊢
  cases t <;> simp (config := { decide := true }) <;> omega

/-- **A single deletion breaks a closure.** -/
theorem deletion_detected (p q : List Twist) (t : Twist) (h : countBalanced (p ++ t :: q)) :
    ¬ countBalanced (p ++ q) := fun h' => insertion_detected p q t h' h

/-- **A single substitution breaks a closure.** -/
theorem substitution_detected (p q : List Twist) (t t' : Twist) (hne : t ≠ t')
    (h : countBalanced (p ++ t :: q)) : ¬ countBalanced (p ++ t' :: q) := by
  unfold countBalanced at h ⊢
  simp only [List.count_append, List.count_cons] at h ⊢
  cases t <;> cases t' <;> simp (config := { decide := true }) at hne h ⊢ <;> omega

/-- **A conjugate pair is invisible:** the distance is exactly 2. -/
theorem conjugate_pair_undetected (p q : List Twist) (t : Twist) (h : countBalanced (p ++ q)) :
    countBalanced (p ++ t :: t.conj :: q) := by
  unfold countBalanced at h ⊢
  simp only [List.count_append, List.count_cons] at h ⊢
  cases t <;> simp (config := { decide := true }) <;> omega

/-- **A single error cannot be corrected.** `^v` and `v^` are distinct closures, and deleting `^`
    from either gives `v`. -/
theorem single_error_not_correctable :
    countBalanced [Twist.up, Twist.down] ∧ countBalanced [Twist.down, Twist.up] ∧
      [Twist.up, Twist.down] ≠ [Twist.down, Twist.up] ∧
      [Twist.up, Twist.down].erase Twist.up = [Twist.down, Twist.up].erase Twist.up := by
  refine ⟨?_, ?_, by decide, by decide⟩ <;>
    (unfold countBalanced; decide)

end QLF.HolographicCompletion
