import QLF_PoleFactorization

/-!
# QLF_Resonance — resonance poles: the decay rate is the leakage

Issue #207, Phase D, *resonance/decay pole demonstration*. Take a unitary step `U` on a finite
channel space, and a closed sector given by a Hermitian projector `P` (the channels kept). The
step seen inside the sector is the compression `K = P U P`, and its resolvent `(1 − zK)⁻¹` has its
poles at `z = 1/μ` for the eigenvalues `μ` of `K` (`QLF_PoleFactorization`).

* **`norm_unitary`, `norm_split`.** A unitary step keeps `‖·‖²`, and `‖w‖² = ‖P w‖² + ‖(1 − P) w‖²`.
* **`resonance_balance`.** For an eigenvector `v` of `K` inside the sector, `K v = μ v`:
  `|μ|² ‖v‖² + ‖(1 − P) U v‖² = ‖v‖²`. **The norm the mode keeps per step plus the norm it leaks
  out of the sector is the norm it had.** This is the leakage identity of #208 (U3) for one mode.
* **`resonance_le_one`.** So `|μ| ≤ 1`: every pole of the sector's resolvent lies on or outside the
  unit circle, `|z| ≥ 1`.
* **`stable_iff_no_leak`.** `|μ| = 1` exactly when the mode does not leak: an on-shell, stable
  state (a pole on the circle, as for the realizable walk in `QLF_PoleFactorization`). Otherwise
  `|μ| < 1` and the pole moves off the circle: a resonance, surviving each step with probability
  `|μ|² = 1 − (leaked fraction)`, a width `Γ = −log |μ|²` per step.

So resonance poles are closures that leak: a closed sector of a unitary process whose modes
escape into open channels. No axioms.

**Credit.** The compression of a unitary is a contraction, and the decay rate of a resonance is
the norm lost to open channels, as in Gamow (1928) and Weisskopf–Wigner (1930); the finite
statement is the Feshbach projection picture (Feshbach, *Ann. Phys.* **5**, 357 (1958)). Part of
the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.Resonance

open Matrix Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖w‖² = Σ |wᵢ|²`, as a real number. -/
noncomputable def nrm (w : ι → ℂ) : ℝ := (star w ⬝ᵥ w).re

omit [DecidableEq ι] in
lemma nrm_nonneg (w : ι → ℂ) : 0 ≤ nrm w := by
  unfold nrm
  rw [dotProduct, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    simp [Pi.star_apply, Complex.mul_re]; nlinarith [sq_nonneg (w i).re, sq_nonneg (w i).im]

omit [DecidableEq ι] in
lemma nrm_eq_zero (w : ι → ℂ) (h : nrm w = 0) : w = 0 := by
  unfold nrm at h
  rw [dotProduct, Complex.re_sum] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
    simp [Pi.star_apply, Complex.mul_re]; nlinarith [sq_nonneg (w i).re, sq_nonneg (w i).im])).mp h
  funext i
  have := hz i (Finset.mem_univ _)
  simp [Pi.star_apply, Complex.mul_re] at this
  apply Complex.ext <;> simp <;> nlinarith [sq_nonneg (w i).re, sq_nonneg (w i).im]

omit [DecidableEq ι] in
lemma star_mulVec' (A : Matrix ι ι ℂ) (w : ι → ℂ) : star (A *ᵥ w) = star w ᵥ* Aᴴ := by
  rw [star_mulVec]

omit [DecidableEq ι] in
/-- `star (A w) ⬝ (B w) = star w ⬝ (Aᴴ B w)`. -/
lemma dot_mulVec (A B : Matrix ι ι ℂ) (w : ι → ℂ) :
    star (A *ᵥ w) ⬝ᵥ (B *ᵥ w) = star w ⬝ᵥ ((Aᴴ * B) *ᵥ w) := by
  rw [star_mulVec', ← dotProduct_mulVec, mulVec_mulVec]

/-- **A unitary step keeps the norm.** -/
theorem norm_unitary (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (w : ι → ℂ) : nrm (U *ᵥ w) = nrm w := by
  unfold nrm; rw [dot_mulVec, hU, one_mulVec]

/-- **The norm splits across a Hermitian projector.** -/
theorem norm_split (P : Matrix ι ι ℂ) (hP : Pᴴ = P) (hP2 : P * P = P) (w : ι → ℂ) :
    nrm w = nrm (P *ᵥ w) + nrm ((1 - P) *ᵥ w) := by
  unfold nrm
  rw [dot_mulVec, dot_mulVec, hP, hP2, conjTranspose_sub, conjTranspose_one, hP]
  have : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hP2]; abel
  rw [this, ← Complex.add_re, ← dotProduct_add, ← add_mulVec, add_sub_cancel, one_mulVec]

/-- **The resonance balance**: kept norm plus leaked norm is the original norm. -/
theorem resonance_balance (U P : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (hP : Pᴴ = P) (hP2 : P * P = P)
    (v : ι → ℂ) (μ : ℂ) (hv : P *ᵥ v = v) (he : (P * U * P) *ᵥ v = μ • v) :
    normSq μ * nrm v + nrm ((1 - P) *ᵥ (U *ᵥ v)) = nrm v := by
  have hk : P *ᵥ (U *ᵥ v) = μ • v := by
    rw [← he, ← mulVec_mulVec, ← mulVec_mulVec, hv]
  have hs := norm_split P hP hP2 (U *ᵥ v)
  rw [norm_unitary U hU, hk] at hs
  have hμ : nrm (μ • v) = normSq μ * nrm v := by
    unfold nrm
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]
  rw [hμ] at hs
  linarith

/-- **Every pole of the sector's resolvent lies on or outside the unit circle.** -/
theorem resonance_le_one (U P : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (hP : Pᴴ = P) (hP2 : P * P = P)
    (v : ι → ℂ) (μ : ℂ) (hv : P *ᵥ v = v) (he : (P * U * P) *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    normSq μ ≤ 1 := by
  have hb := resonance_balance U P hU hP hP2 v μ hv he
  have hl := nrm_nonneg ((1 - P) *ᵥ (U *ᵥ v))
  have hpos : 0 < nrm v := lt_of_le_of_ne (nrm_nonneg v) (fun h => hv0 (nrm_eq_zero v h.symm))
  by_contra h
  have h' := not_le.mp h
  nlinarith

/-- **A pole is on the circle exactly when its mode does not leak.** -/
theorem stable_iff_no_leak (U P : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (hP : Pᴴ = P)
    (hP2 : P * P = P) (v : ι → ℂ) (μ : ℂ) (hv : P *ᵥ v = v) (he : (P * U * P) *ᵥ v = μ • v)
    (hv0 : v ≠ 0) : normSq μ = 1 ↔ (1 - P) *ᵥ (U *ᵥ v) = 0 := by
  have hb := resonance_balance U P hU hP hP2 v μ hv he
  have hpos : 0 < nrm v := lt_of_le_of_ne (nrm_nonneg v) (fun h => hv0 (nrm_eq_zero v h.symm))
  constructor
  · intro h
    rw [h, one_mul] at hb
    exact nrm_eq_zero _ (by linarith)
  · intro h
    rw [h] at hb
    have h0 : nrm (0 : ι → ℂ) = 0 := by simp [nrm]
    rw [h0, add_zero] at hb
    have : (normSq μ - 1) * nrm v = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · linarith

end QLF.Resonance
