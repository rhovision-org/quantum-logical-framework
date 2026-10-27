import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_GlobalConstraint — Lombriser's global constraint, read as "closed so far"

Lombriser (*On the cosmological constant problem*, Phys. Lett. B 2019, arXiv:1901.08588) varies the
action with respect to the Planck mass as a global variable. That gives `∫√−g (R − 2Λ) = 0`, and with
the trace of Einstein's equations `M_p²Λ = ½⟨T⟩`, the four-volume average of the matter trace. It is a
global zero-action condition, so `Cosmological_Constant.md` §5.9 asks whether ZFA can supply it. The
statements G1–G3 were pre-registered there (commit `c03bd76`) before this module was written.

* G1 `lombriser_relation`, `lombriser_relation_avg`: over finitely many cells, the trace relation and the
  constraint give `M²Λ = ½ Σ wᵢTᵢ / Σ wᵢ`. Algebra (bookkeeping by `CLAUDE.md` rule 4), stated as the
  anchor of Lombriser's relation.
* G2 `closedAvg_matter_era`: closure is irrevocable and the future is not yet synthesized, so the average
  QLF can use runs over what has closed so far. In a matter era (`a³ = k t²`, comoving matter
  `ρ_m a³ = ρ₀`) that average is exactly `3 ρ_m(t)`.
* G3 `omegaLambda_matter_era`, `omegaLambda_exceeds_bound`: so `ρ_Λ = (3/2)ρ_m` and `Ω_Λ = 3/5` at every
  matter-era epoch, above the early-dark-energy bound `0.06`.

## Scope

The identification of QLF's free action with the Einstein–Hilbert density (step 1 of §5.9) is **not**
attempted here: QLF has no gravitational action density. G2–G3 show the closed-so-far reading fails
whatever that identification turns out to be: it is a matter-like term (`ρ_Λ ∝ a⁻³`), the same failure as
§5.7's reading A. A constant `Λ` from the constraint needs Lombriser's future-including average.
Numerical history with radiation: `global_constraint_epochs.py`. No new axioms.
-/

namespace QLF.GlobalConstraint

open Finset

/-- **G1.** Cells `i ∈ s` with four-volumes `w i`. The trace of Einstein's equations is
`M²(4Λ − Rᵢ) = Tᵢ` (Lombriser's convention, `T = ρ` for dust), and the constraint is
`Σ wᵢ(Rᵢ − 2Λ) = 0`. Then `2 M² Λ Σ wᵢ = Σ wᵢTᵢ`. -/
theorem lombriser_relation {ι : Type*} (s : Finset ι) (w R T : ι → ℝ) (Λ M2 : ℝ)
    (htrace : ∀ i ∈ s, M2 * R i = 4 * M2 * Λ - T i)
    (hcon : ∑ i ∈ s, w i * (R i - 2 * Λ) = 0) :
    2 * M2 * Λ * (∑ i ∈ s, w i) = ∑ i ∈ s, w i * T i := by
  have h1 : ∑ i ∈ s, w i * (M2 * R i - 2 * M2 * Λ) = M2 * ∑ i ∈ s, w i * (R i - 2 * Λ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : ∑ i ∈ s, w i * (M2 * R i - 2 * M2 * Λ)
      = ∑ i ∈ s, (2 * M2 * Λ * w i - w i * T i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [htrace i hi]
    ring
  have h3 : ∑ i ∈ s, (2 * M2 * Λ * w i - w i * T i)
      = 2 * M2 * Λ * (∑ i ∈ s, w i) - ∑ i ∈ s, w i * T i := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hcon, mul_zero] at h1
  linear_combination h3.symm.trans (h2.symm.trans h1)

/-- **G1**, as an average: `M²Λ = ½ ⟨T⟩` when the total four-volume is positive. -/
theorem lombriser_relation_avg {ι : Type*} (s : Finset ι) (w R T : ι → ℝ) (Λ M2 : ℝ)
    (hw : 0 < ∑ i ∈ s, w i)
    (htrace : ∀ i ∈ s, M2 * R i = 4 * M2 * Λ - T i)
    (hcon : ∑ i ∈ s, w i * (R i - 2 * Λ) = 0) :
    M2 * Λ = (∑ i ∈ s, w i * T i) / (∑ i ∈ s, w i) / 2 := by
  have key := lombriser_relation s w R T Λ M2 htrace hcon
  rw [eq_div_iff two_ne_zero, eq_div_iff (ne_of_gt hw)]
  linear_combination key

/-- Matter density in a matter era: `ρ_m = ρ₀ / a³` with `a³ = k t²`. -/
noncomputable def matterDensity (ρ0 k t : ℝ) : ℝ := ρ0 / (k * t ^ 2)

/-- The closed-so-far average of the matter trace: `∫₀ᵗ ρ_m a³ / ∫₀ᵗ a³`, with `ρ_m a³ = ρ₀`
(comoving matter conserved) and `a³ = k t²`. -/
noncomputable def closedAvg (ρ0 k t : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..t, ρ0) / (∫ x in (0 : ℝ)..t, k * x ^ 2)

/-- **G2.** In a matter era the closed-so-far average is three times the current matter density. -/
theorem closedAvg_matter_era (ρ0 k t : ℝ) (hk : 0 < k) (ht : 0 < t) :
    closedAvg ρ0 k t = 3 * matterDensity ρ0 k t := by
  have hn : ∫ x in (0 : ℝ)..t, ρ0 = t * ρ0 := by simp
  have hd : ∫ x in (0 : ℝ)..t, k * x ^ 2 = k * (t ^ 3 / 3) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  have hb : k * (t ^ 3 / 3) ≠ 0 := (mul_pos hk (div_pos (pow_pos ht 3) three_pos)).ne'
  have hc : k * t ^ 2 ≠ 0 := (mul_pos hk (pow_pos ht 2)).ne'
  unfold closedAvg matterDensity
  rw [hn, hd]
  conv_rhs => rw [← mul_div_assoc]
  rw [div_eq_div_iff hb hc]
  ring

/-- **G3.** With `ρ_Λ = ½ ⟨ρ_m⟩` (Lombriser's relation, `ρ_Λ = M²Λ`), the dark-energy fraction of a
matter era is `3/5` at every epoch. -/
theorem omegaLambda_matter_era (ρ0 k t : ℝ) (hρ : 0 < ρ0) (hk : 0 < k) (ht : 0 < t) :
    (closedAvg ρ0 k t / 2) / (closedAvg ρ0 k t / 2 + matterDensity ρ0 k t) = 3 / 5 := by
  rw [closedAvg_matter_era ρ0 k t hk ht]
  have hm : 0 < matterDensity ρ0 k t := by
    unfold matterDensity
    exact div_pos hρ (mul_pos hk (pow_pos ht 2))
  generalize matterDensity ρ0 k t = m at hm ⊢
  have hden : 3 * m / 2 + m ≠ 0 := (by linarith : (0 : ℝ) < 3 * m / 2 + m).ne'
  rw [div_eq_div_iff hden (by norm_num : (5 : ℝ) ≠ 0)]
  ring

/-- **G3**, the kill: `3/5` exceeds the early-dark-energy bound `Ω_early < 0.06`
(Doran & Robbers 2006), so the closed-so-far reading is excluded at recombination. -/
theorem omegaLambda_exceeds_bound : (6 : ℝ) / 100 < 3 / 5 := by norm_num

end QLF.GlobalConstraint
