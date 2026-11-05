import QLF_VacuumPolarizationTower

/-!
# QLF_VacuumResolvent — vacuum polarization resummed through renewal

Issue #207, §10.1 (*QED vacuum-polarization resolvent*). A photon line with one vacuum-polarization
insertion is `D₀ Π D₀`; with `k` insertions in a chain it is `(D₀ Π)^k D₀`. This module sums the
chain through the same renewal that dresses every closure channel (`vacuum_renewal`,
[`QLF_ClosureKernel`](QLF_ClosureKernel.lean)), and reads the running coupling of
[`QLF_VacuumPolarizationTower`](QLF_VacuumPolarizationTower.lean) as its resolvent.

**Operator level, in any ring.**

* **`chain_succ`.** The chain of up to `n` insertions obeys the renewal
  `D_{n+1} = D₀ + D₀ Π D_n`: one more insertion is one more step of the same recursion.
* **`chain_telescope`.** `(1 − D₀Π) D_n = D₀ − (D₀Π)^n D₀`: the chain is a truncated resolvent.
* **`dyson_exists`, `dyson_unique`.** When `1 − D₀Π` is invertible, `D = (1 − D₀Π)⁻¹ D₀` solves
  Dyson's equation `D = D₀ + D₀ Π D`, and it is the only solution.
* **`dyson_of_nilpotent`.** If the insertion chain stops (`(D₀Π)^n = 0`), the finite chain is
  already the exact dressed propagator: no series, no limit.

**Scalar coupling.**

* **`dressed_inv`.** The resummed coupling `g = g₀ / (1 − g₀ Π)` has `1/g = 1/g₀ − Π`: the inverse
  coupling subtracts the polarization, linearly.
* **`chain_tendsto`.** For `|g₀ Π| < 1` the chain partial sums converge to it.
* **`resummed_is_tower`.** With `Π` the octave-tower sum over active closures, the resummed inverse
  coupling **is** `towerRunning`: the running `α⁻¹(Q²)` of `QLF_VacuumPolarizationTower` is the
  resolvent of the insertion chain.
* **`counterterm_finite`.** Raising the capacity by one octave changes `Π` by exactly the per-octave
  increment, a finite number, the same at every octave. Renormalization here is a finite
  difference between two finite sums; there is no divergent subtraction.
* **`landau_capacity`, `dressed_pos`.** A charged closure's tower grows without bound in the octave
  count, so for any IR coupling there is a finite capacity where `1 − g₀Π` reaches zero (the
  Landau pole of the resummed propagator); below it the dressed coupling is finite and positive.
  This module does not say where that capacity lies relative to the Planck floor.

**Not here.** The prime electromagnetic closure kernel itself (which closures are the insertions,
with their charges and thresholds): the tower takes them as input. No axioms.

**Credit.** Resumming self-energy insertions is Dyson's (*Phys. Rev.* **75**, 1736 (1949)); the
geometric chain and the Landau pole of the resummed QED coupling are Landau, Abrikosov and
Khalatnikov's (*Dokl. Akad. Nauk SSSR* **95**, 497 (1954)). Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.VacuumResolvent

open Filter Topology

section Ring

variable {R : Type*} [Ring R] (D₀ S : R)

/-- The chain of up to `n` vacuum-polarization insertions: `Σ_{k<n} (D₀S)^k D₀`. -/
def chain (n : ℕ) : R := ∑ k ∈ Finset.range n, (D₀ * S) ^ k * D₀

/-- **Renewal**: one more insertion is one more step, `D_{n+1} = D₀ + D₀ S D_n`. -/
theorem chain_succ (n : ℕ) : chain D₀ S (n + 1) = D₀ + D₀ * S * chain D₀ S n := by
  rw [chain, Finset.sum_range_succ', pow_zero, one_mul, chain, Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ', mul_assoc]

/-- **The chain is a truncated resolvent**: `(1 − D₀S) D_n = D₀ − (D₀S)^n D₀`. -/
theorem chain_telescope (n : ℕ) :
    (1 - D₀ * S) * chain D₀ S n = D₀ - (D₀ * S) ^ n * D₀ := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    rw [chain, Finset.sum_range_succ, ← chain, mul_add, ih, sub_mul, one_mul, pow_succ',
      mul_assoc]
    noncomm_ring

/-- **Dyson's equation is solved by the resolvent.** -/
theorem dyson_exists (u : Rˣ) (hu : (u : R) = 1 - D₀ * S) :
    (↑u⁻¹ * D₀ : R) = D₀ + D₀ * S * (↑u⁻¹ * D₀) := by
  have h : (1 - D₀ * S) * (↑u⁻¹ * D₀) = D₀ := by
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  rw [sub_mul, one_mul, sub_eq_iff_eq_add] at h
  rw [← h]

/-- **And it is the only solution.** -/
theorem dyson_unique (u : Rˣ) (hu : (u : R) = 1 - D₀ * S) (D : R)
    (hD : D = D₀ + D₀ * S * D) : D = ↑u⁻¹ * D₀ := by
  have h : (u : R) * D = D₀ := by
    rw [hu, sub_mul, one_mul, sub_eq_iff_eq_add]
    exact hD
  rw [← h, ← mul_assoc, Units.inv_mul, one_mul]

/-- **A chain that stops is exact**: if `(D₀S)^n = 0`, the `n`-insertion chain solves Dyson's
    equation. -/
theorem dyson_of_nilpotent (n : ℕ) (h : (D₀ * S) ^ n = 0) :
    chain D₀ S n = D₀ + D₀ * S * chain D₀ S n := by
  have t := chain_telescope D₀ S n
  rw [h, zero_mul, sub_zero, sub_mul, one_mul, sub_eq_iff_eq_add] at t
  rw [← t]

end Ring

/-! ## The scalar coupling -/

/-- The resummed coupling `g₀ / (1 − g₀ S)`. -/
noncomputable def dressed (g₀ P : ℝ) : ℝ := g₀ / (1 - g₀ * P)

/-- **The inverse coupling subtracts the polarization**: `1/g = 1/g₀ − S`. -/
theorem dressed_inv (g₀ P : ℝ) (hg : g₀ ≠ 0) (hd : 1 - g₀ * P ≠ 0) :
    (dressed g₀ P)⁻¹ = g₀⁻¹ - P := by
  unfold dressed
  rw [inv_div]
  field_simp

/-- **The chain converges to the resummed coupling** when `|g₀ S| < 1`. -/
theorem chain_tendsto (g₀ P : ℝ) (h : |g₀ * P| < 1) :
    Tendsto (fun n => chain g₀ P n) atTop (𝓝 (dressed g₀ P)) := by
  have hs := (hasSum_geometric_of_abs_lt_one h).mul_right g₀
  rw [dressed, div_eq_inv_mul]
  exact hs.tendsto_sum_nat

/-- **The resummed inverse coupling is the octave tower's running.** -/
theorem resummed_is_tower (a : ℝ) (ha : a ≠ 0) (species : List (ℝ × ℕ)) (RQ : ℕ)
    (hd : 1 - a⁻¹ * (species.map (fun p => octaveTower p.1 (RQ - p.2))).sum ≠ 0) :
    (dressed a⁻¹ (species.map (fun p => octaveTower p.1 (RQ - p.2))).sum)⁻¹ =
      towerRunning a species RQ := by
  rw [dressed_inv _ _ (inv_ne_zero ha) hd, inv_inv, towerRunning]

/-- **The counterterm is finite**: one more octave adds exactly the per-octave increment. -/
theorem counterterm_finite (Qf : ℝ) (k : ℕ) :
    octaveTower Qf (k + 1) - octaveTower Qf k = perOctaveIncrement Qf := by
  rw [octaveTower, Finset.sum_range_succ, ← octaveTower]
  ring

/-- **The Landau capacity is finite**: a charged closure's tower passes any bound. -/
theorem landau_capacity (Qf : ℝ) (hQ : Qf ≠ 0) (a : ℝ) : ∃ k : ℕ, a ≤ octaveTower Qf k := by
  have hp := perOctaveIncrement_pos Qf hQ
  obtain ⟨k, hk⟩ := exists_nat_ge (a / perOctaveIncrement Qf)
  refine ⟨k, ?_⟩
  rw [octaveTower_eq]
  rw [div_le_iff₀ hp] at hk
  exact hk

/-- **Below the Landau capacity the dressed coupling is finite and positive**. -/
theorem dressed_pos (a P : ℝ) (ha : 0 < a) (hP : P < a) : 0 < dressed a⁻¹ P := by
  have hd : 1 - a⁻¹ * P ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : a⁻¹ * P < a⁻¹ * a := mul_lt_mul_of_pos_left hP (inv_pos.mpr ha)
    rw [inv_mul_cancel₀ ha.ne'] at this; linarith
  have e := dressed_inv a⁻¹ P (inv_ne_zero ha.ne') hd
  rw [inv_inv] at e
  have : 0 < (dressed a⁻¹ P)⁻¹ := by rw [e]; linarith
  exact inv_pos.mp this

end QLF.VacuumResolvent
