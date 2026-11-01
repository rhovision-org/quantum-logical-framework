import Mathlib
import QLF_PolyaTransience
import QLF_FirstReturn

/-!
# QLF_CensusTemperature — the census temperature, and why closure makes it normalizable

`QLF_FreeEnergy` proves `log 2` nats per half-spin closure, a dimensionless quantity. Landauer's
`k_B T ln 2` is an energy, and comparing the two needs a temperature. At a horizon the temperature is
supplied (`QLF_HorizonFirstLaw.bh_entropy_first_law`). This module derives one from the census, using
the definition of thermodynamic temperature, `1/T = dS/dE`.

Statements L1–L4 (and later L5) were pre-registered in `Information_Physics.md` §5b before this proof
was written; L6 and the renamed/strengthened L2, L4 were added after review (PR #199).
Units: `k_B = 1`, so a temperature is an energy. **`ε` is the energy per twist step** (one symbol
choice, a distinction), an input; a physical QLF event is a closure, which may contain many steps.
Physical domain: `K > 1`, `ε > 0`, `T > 0`. Lean's totalized division makes some identities below
hold at degenerate values too; those have no thermodynamic meaning.

* L1 `historyEntropy_hasDerivAt`: `S(E) = E · (log K / ε)` (`n = E/ε` steps, `Kⁿ` words) has
  `dS/dE = log K / ε`; so the census temperature is `T_c = ε / log K` (`inv_censusTemperature`).
* L2 `landauer_scale_eq_energyPerBit`: `T_c · log 2 = ε / log₂ K`. At the census temperature the
  Landauer energy **scale** equals the census energy per bit of symbol-choice entropy. This is an
  energy-scale identity; it is **not** a proof that any erasure protocol dissipates that amount.
* L3 `log_eight`, `landauer_eight`: on the 8-twist alphabet a step carries 3 bits of symbol-choice
  entropy (`log 8 = 3 log 2`), so `T_c · log 2 = ε / 3`, a mass-equivalent `ε/(3c²)` per bit.
* L4 `closureEntropy_hasDerivAt`, `closure_inverseTemperature_lower`, `closure_runs_hotter`: closed
  histories number `≈ C · 8^L / L²` (the `d = 4` Pólya factor), so `β_cl = log 8 / ε − 2/E < β_c`, and
  where `β_cl > 0` the closed census is strictly hotter than `T_c`.
* L5 `zipf_rank_frequency`, `zipf_one_iff`: with Boltzmann weight `e^{−ε/T}` per step, frequency
  against rank is `r^{−B}`, `B = ε/(T log K)`, and `B = 1` exactly at `T_c`.
* L6 `free_shell_weight_one`, `free_census_not_normalizable`, `closed_census_normalizable`: at `T_c`
  every length shell of the free census weighs exactly `1`, so the free census is **critical and not
  normalizable** (a pure `B = 1` Zipf law has no normalization), while the closed census's weight
  `W_L · 8^{−L}` is summable (`QLF_PolyaTransience.returnWeight_summable`). **ZFA closure makes the
  ensemble normalizable at its own census temperature.** Unlike L2, this is not generic bookkeeping:
  it rests on the `L^{−2}` suppression of the four-dimensional closure walk, which a recurrent
  (`d ≤ 2`) walk would not supply.
* L7 `closed_partition_le_four`, `event_partition_le_three_quarters`, `event_partition_lt_one`,
  `zfa_regularizes_critical_census`: the closed critical partition function is at most `4`, and the
  event (first-closure) partition function at `T_c` is the prime Kraft mass, at most `3/4` and below
  `1`. At `T_c` the Boltzmann weight is exactly the uniform cylinder weight `8^{−L}`, so L6–L7 are
  Pólya transience and the first-return bound (`QLF_PolyaTransience`, `QLF_FirstReturn`) read as
  statements about partition functions: the mathematics is reused, the thermodynamic reading is new.

## R6a, and what stays open

L2 holds for every uniform alphabet, so it is bookkeeping, not evidence. What is QLF's is `K = 8`
(`QLF_AlphabetNecessity`), the closure correction L4 and the normalization contrast L6. L4 uses the
asymptotic form of `W_L` as its model; L6 uses the exact count (`walkCount`). Open: `ε`, which is the
energy per step of whichever ensemble is counting (the Planck reading `ε = E_P` gives
`T_c ≈ T_P/(3 log 2) ≈ 10³¹ K`, the logical bang; a room-temperature bath has `ε = 3 log 2 · k_B T`),
and the identification of `T_c` with a thermometer's temperature. No axioms.
-/

namespace QLF.CensusTemperature

/-- The census entropy of words of energy `E` over a `K`-letter alphabet at energy `ε` per step:
    `n = E/ε` steps and `Kⁿ` words, so `S = n log K = E · (log K / ε)`. -/
noncomputable def historyEntropy (K ε : ℝ) (E : ℝ) : ℝ := E * (Real.log K / ε)

/-- The census temperature `T_c = ε / log K` (`k_B = 1`). -/
noncomputable def censusTemperature (K ε : ℝ) : ℝ := ε / Real.log K

/-- The energy per bit of symbol-choice entropy when a step of energy `ε` carries `log₂ K` bits. -/
noncomputable def energyPerBit (K ε : ℝ) : ℝ := ε / Real.logb 2 K

/-- **L1.** `dS/dE = log K / ε`. -/
theorem historyEntropy_hasDerivAt (K ε E : ℝ) :
    HasDerivAt (historyEntropy K ε) (Real.log K / ε) E := by
  have h : HasDerivAt (fun x : ℝ => x * (Real.log K / ε)) (1 * (Real.log K / ε)) E :=
    (hasDerivAt_id E).mul_const (Real.log K / ε)
  rw [one_mul] at h
  exact h

/-- **L1, read as a temperature.** `1/T_c = log K / ε`, the derivative of L1. -/
theorem inv_censusTemperature (K ε : ℝ) :
    1 / censusTemperature K ε = Real.log K / ε := by
  unfold censusTemperature
  rw [one_div_div]

/-- **L2 — an energy-scale identity, for any alphabet.** At the census temperature the Landauer energy
    scale `T_c · log 2` equals the census energy per bit, `ε / log₂ K`. Bookkeeping (R6a): it holds for
    every uniform alphabet, and it says nothing about what an erasure protocol dissipates. -/
theorem landauer_scale_eq_energyPerBit (K ε : ℝ) :
    censusTemperature K ε * Real.log 2 = energyPerBit K ε := by
  unfold censusTemperature energyPerBit Real.logb
  rw [div_div_eq_mul_div, div_mul_eq_mul_div]

/-- `log 8 = 3 log 2`: a step on the 8-twist alphabet carries three bits of symbol-choice entropy. -/
theorem log_eight : Real.log 8 = 3 * Real.log 2 := by
  have h : (8 : ℝ) = 2 ^ 3 := by norm_num
  rw [h, Real.log_pow] <;> norm_num

/-- **L3 — the substrate value.** On the 8-twist alphabet `T_c · log 2 = ε / 3`: the Landauer scale at
    the census temperature is a third of the energy per step. -/
theorem landauer_eight (ε : ℝ) : censusTemperature 8 ε * Real.log 2 = ε / 3 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  unfold censusTemperature
  rw [log_eight, div_mul_eq_mul_div, mul_div_mul_right ε 3 h2]

/-- **L3, as a temperature.** `T_c = ε / (3 log 2)` on the 8-twist alphabet. -/
theorem censusTemperature_eight (ε : ℝ) : censusTemperature 8 ε = ε / (3 * Real.log 2) := by
  unfold censusTemperature
  rw [log_eight]

/-- The census entropy of *closed* histories, from `W ≈ C · 8^n / n²` with `n = E/ε`, up to the
    constant `log C`: `n log 8 − 2 log n = E · (log 8 / ε) − 2 log E + 2 log ε`. -/
noncomputable def closureEntropy (ε : ℝ) (E : ℝ) : ℝ :=
  E * (Real.log 8 / ε) - 2 * Real.log E + 2 * Real.log ε

/-- **L4.** `dS_cl/dE = log 8 / ε − 2/E`. -/
theorem closureEntropy_hasDerivAt (ε : ℝ) {E : ℝ} (hE : E ≠ 0) :
    HasDerivAt (closureEntropy ε) (Real.log 8 / ε - 2 * E⁻¹) E := by
  have h1 : HasDerivAt (fun x : ℝ => x * (Real.log 8 / ε)) (1 * (Real.log 8 / ε)) E :=
    (hasDerivAt_id E).mul_const (Real.log 8 / ε)
  have h2 : HasDerivAt (fun x : ℝ => 2 * Real.log x) (2 * E⁻¹) E :=
    (Real.hasDerivAt_log hE).const_mul 2
  have h3 := (h1.sub h2).add_const (2 * Real.log ε)
  rw [one_mul] at h3
  exact h3

/-- **L4 — the closed census's inverse temperature is lower.** For `E > 0`,
    `β_cl = log 8 / ε − 2/E < β_c`. -/
theorem closure_inverseTemperature_lower (ε : ℝ) {E : ℝ} (hE : 0 < E) :
    Real.log 8 / ε - 2 * E⁻¹ < 1 / censusTemperature 8 ε := by
  rw [inv_censusTemperature]
  have : 0 < 2 * E⁻¹ := by positivity
  linarith

/-- The temperature of the closed census, `T_cl = 1/β_cl`. -/
noncomputable def closureTemperature (ε E : ℝ) : ℝ := 1 / (Real.log 8 / ε - 2 * E⁻¹)

/-- **L4 — requiring closure raises the temperature.** Where both inverse temperatures are positive
    (`E > 0` and `β_cl > 0`, i.e. `E log 8 > 2ε` for `ε > 0`), `T_c < T_cl`. -/
theorem closure_runs_hotter {ε E : ℝ} (hE : 0 < E)
    (hβ : 0 < Real.log 8 / ε - 2 * E⁻¹) :
    censusTemperature 8 ε < closureTemperature ε E := by
  have hlt : Real.log 8 / ε - 2 * E⁻¹ < Real.log 8 / ε := by
    have : 0 < 2 * E⁻¹ := by positivity
    linarith
  have h := one_div_lt_one_div_of_lt hβ hlt
  have hc : censusTemperature 8 ε = 1 / (Real.log 8 / ε) := by
    unfold censusTemperature
    rw [one_div_div]
  unfold closureTemperature
  rw [hc]
  exact h

/-- The Zipf exponent of a `K`-letter census whose steps carry Boltzmann weight `e^{−ε/T}`:
    `B = ε / (T log K)`. -/
noncomputable def zipfExponent (K ε T : ℝ) : ℝ := ε / (T * Real.log K)

/-- **L5 — the rank–frequency law.** A word of `n` steps has frequency `e^{−nε/T}` and rank
    `r = Kⁿ = e^{n log K}`; then `f = r^{−B}`, written `e^{−B · log r}`. -/
theorem zipf_rank_frequency {K ε T n : ℝ} (hT : T ≠ 0) (hK : Real.log K ≠ 0) :
    Real.exp (-(n * ε / T))
      = Real.exp (-(zipfExponent K ε T) * Real.log (Real.exp (n * Real.log K))) := by
  rw [Real.log_exp]
  unfold zipfExponent
  congr 1
  field_simp <;> ring

/-- **L5 — Zipf's exponent is 1 exactly at the census temperature.** -/
theorem zipf_one_iff {K ε T : ℝ} (hT : T ≠ 0) (hK : Real.log K ≠ 0) :
    zipfExponent K ε T = 1 ↔ T = censusTemperature K ε := by
  unfold zipfExponent censusTemperature
  rw [div_eq_one_iff_eq (mul_ne_zero hT hK), eq_div_iff hK]
  exact eq_comm

/-- **L6 — at `T_c` every shell of the free census weighs exactly `1`.** `Kⁿ` words, each with
    Boltzmann weight `e^{−n ε/T_c} = e^{−n log K}`. -/
theorem free_shell_weight_one {K : ℝ} (hK : 0 < K) (n : ℕ) :
    K ^ n * Real.exp (-((n : ℝ) * Real.log K)) = 1 := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hK n)]
  exact mul_inv_cancel₀ (pow_ne_zero n hK.ne')

/-- **L6 — the free census is not normalizable at its own census temperature.** Its partition function
    `Σₙ Kⁿ e^{−n log K} = Σₙ 1` diverges: the free census is critical, and a pure `B = 1` Zipf law has
    no normalization. -/
theorem free_census_not_normalizable {K : ℝ} (hK : 0 < K) :
    ¬ Summable (fun n : ℕ => K ^ n * Real.exp (-((n : ℝ) * Real.log K))) := by
  intro h
  have h1 : (fun n : ℕ => K ^ n * Real.exp (-((n : ℝ) * Real.log K))) = fun _ => (1 : ℝ) :=
    funext (free_shell_weight_one hK)
  rw [h1] at h
  have h2 := h.tendsto_atTop_zero
  rw [tendsto_const_nhds_iff] at h2
  exact one_ne_zero h2

/-- At `T_c` the closed census weighs `W_L / 8^L` per shell, the `ℤ⁴` return weight. -/
theorem closedWeight_eq_returnWeight :
    (fun L : ℕ =>
      (QLF.PolyaTransience.walkCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8)))
      = QLF.PolyaTransience.returnWeight := by
  funext L
  unfold QLF.PolyaTransience.returnWeight
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), div_eq_mul_inv]

/-- **L6 — ZFA closure makes the census normalizable at the same temperature.** The closed census
    weighs `W_L · e^{−L log 8} = W_L / 8^L` per shell, which is summable by Pólya transience in `d = 4`
    (`QLF_PolyaTransience.returnWeight_summable`). -/
theorem closed_census_normalizable :
    Summable (fun L : ℕ =>
      (QLF.PolyaTransience.walkCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8))) := by
  have h := QLF.PolyaTransience.returnWeight_summable
  rw [← closedWeight_eq_returnWeight] at h
  exact h

/-- **L7 — the closed critical partition function is bounded:** `Z_ZFA(T_c) ≤ 4`. -/
theorem closed_partition_le_four :
    ∑' L : ℕ, (QLF.PolyaTransience.walkCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8)) ≤ 4 := by
  have h := QLF.PolyaTransience.returnWeight_tsum_le_four
  rw [← closedWeight_eq_returnWeight] at h
  exact h

/-- At `T_c` an event (a first closure, a prime history) of length `L` weighs `I_L / 8^L`, the prime
    Kraft weight. -/
theorem eventWeight_eq_primeKraft :
    (fun L : ℕ =>
      (QLF.FirstReturn.primeCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8)))
      = QLF.FirstReturn.a := by
  funext L
  unfold QLF.FirstReturn.a
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), div_eq_mul_inv]

/-- **L7 — the event partition function at `T_c` is the Kraft event mass, at most `3/4`.** -/
theorem event_partition_le_three_quarters :
    ∑' L : ℕ, (QLF.FirstReturn.primeCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8)) ≤ 3 / 4 := by
  have h := QLF.FirstReturn.at_least_quarter_never_closes
  rw [← eventWeight_eq_primeKraft] at h
  exact h

/-- **L7 — and strictly below one.** -/
theorem event_partition_lt_one :
    ∑' L : ℕ, (QLF.FirstReturn.primeCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8)) < 1 := by
  have h := QLF.PolyaTransience.polya_transience_lt_one QLF.FirstReturn.a_zero
    QLF.FirstReturn.a_nonneg QLF.FirstReturn.renewal_relation
  rw [← eventWeight_eq_primeKraft] at h
  exact h

/-- **L7 — ZFA closure regularizes the census at its own critical temperature.** At `T_c` the free
    census does not normalize, the closed census does with `Z ≤ 4`, and the event (first-closure)
    census has `Z < 1`, the Kraft event mass. -/
theorem zfa_regularizes_critical_census :
    ¬ Summable (fun n : ℕ => (8 : ℝ) ^ n * Real.exp (-((n : ℝ) * Real.log 8))) ∧
    Summable (fun L : ℕ =>
      (QLF.PolyaTransience.walkCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8))) ∧
    ∑' L : ℕ, (QLF.PolyaTransience.walkCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8)) ≤ 4 ∧
    ∑' L : ℕ, (QLF.FirstReturn.primeCount L : ℝ) * Real.exp (-((L : ℝ) * Real.log 8)) < 1 :=
  ⟨free_census_not_normalizable (by norm_num), closed_census_normalizable,
    closed_partition_le_four, event_partition_lt_one⟩

end QLF.CensusTemperature
