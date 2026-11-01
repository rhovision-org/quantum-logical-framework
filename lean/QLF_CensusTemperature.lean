import Mathlib

/-!
# QLF_CensusTemperature — Landauer at the substrate's own temperature

`QLF_FreeEnergy` proves `log 2` nats per half-spin closure, a dimensionless quantity. Landauer's
`k_B T ln 2` is an energy, and turning one into the other needs a temperature. At a horizon the
temperature is supplied (`QLF_HorizonFirstLaw.bh_entropy_first_law`). This module derives one in
general from the census, using the definition of thermodynamic temperature, `1/T = dS/dE`.

Statements L1–L4 (and later L5) were pre-registered in `Information_Physics.md` §5b before this proof was written.
Units: `k_B = 1`, so a temperature is an energy. `ε` is the energy per substrate event, an input.

* L1 `historyEntropy_hasDerivAt`: `S(E) = E · (log K / ε)` (that is, `n = E/ε` events, `Kⁿ` ways) has
  `dS/dE = log K / ε`; so the census temperature is `T = ε / log K` (`inv_censusTemperature`).
* L2 `landauer_saturated`: for any alphabet, `T · log 2 = ε / log₂ K`, the event energy divided by the
  bits per event. Landauer's bound is met with equality.
* L3 `log_eight`, `landauer_eight`: on the 8-twist alphabet `log 8 = 3 log 2`, so `T · log 2 = ε / 3`.
  A bit costs a third of an event quantum.
* L4 `closureEntropy_hasDerivAt`, `closure_runs_hotter`: closed histories number `≈ C · 8^L / L²`
  (the `d = 4` Pólya factor, `Closure_Walk.md`), so `S_cl(E) = E · (log 8/ε) − 2 log E + 2 log ε` and
  `dS_cl/dE = log 8 / ε − 2/E`, strictly below `1/T`. Requiring closure raises the temperature.
* L5 `zipf_rank_frequency`, `zipf_one_iff` (pre-registered after L1–L4): with Boltzmann weight
  `e^{−ε/T}` per event, frequency against rank is `r^{−B}` with `B = ε/(T log K)`, and `B = 1` exactly
  at the census temperature. A Zipf exponent is a thermometer for `ε/T` (Mandelbrot 1953), never for
  `ε` alone.

## R6a, and what stays open

L2 holds for every uniform alphabet, so the saturation is bookkeeping, not evidence. What is QLF's is
the input `K = 8` (`QLF_AlphabetNecessity`) and the closure correction of L4. L4 takes the asymptotic
form of `W_L` as its model; the exact count is computed in `Closure_Walk.md`, and Lean has the upper
bound (`QLF_PolyaTransience`). Open: the energy per event `ε`, and the identification of this census
temperature with a thermometer's. `ε` is the energy per elementary distinction of whichever ensemble
is counting, not one constant: the Planck reading `ε = E_P` gives `T = T_P/(3 log 2) ≈ 10³¹ K`, the
logical bang, while a room-temperature bath has `ε = 3 log 2 · k_B T`. So the result does not predict
today's temperature; it says one bit costs a third of the energy of one eight-way event at any
temperature.
No axioms.
-/

namespace QLF.CensusTemperature

/-- The census entropy of histories of energy `E` over a `K`-letter alphabet at energy `ε` per event:
    `n = E/ε` events and `Kⁿ` ways, so `S = n log K = E · (log K / ε)`. -/
noncomputable def historyEntropy (K ε : ℝ) (E : ℝ) : ℝ := E * (Real.log K / ε)

/-- The census temperature `T = ε / log K` (`k_B = 1`). -/
noncomputable def censusTemperature (K ε : ℝ) : ℝ := ε / Real.log K

/-- The energy one bit carries when an event of energy `ε` carries `log₂ K` bits. -/
noncomputable def energyPerBit (K ε : ℝ) : ℝ := ε / Real.logb 2 K

/-- **L1.** `dS/dE = log K / ε`. -/
theorem historyEntropy_hasDerivAt (K ε E : ℝ) :
    HasDerivAt (historyEntropy K ε) (Real.log K / ε) E := by
  have h : HasDerivAt (fun x : ℝ => x * (Real.log K / ε)) (1 * (Real.log K / ε)) E :=
    (hasDerivAt_id E).mul_const (Real.log K / ε)
  rw [one_mul] at h
  exact h

/-- **L1, read as a temperature.** `1/T = log K / ε`, the derivative of L1. -/
theorem inv_censusTemperature (K ε : ℝ) :
    1 / censusTemperature K ε = Real.log K / ε := by
  unfold censusTemperature
  rw [one_div_div]

/-- **L2 — Landauer saturated, for any alphabet.** `T · log 2 = ε / log₂ K`. Bookkeeping (R6a): it holds
    for every uniform alphabet. -/
theorem landauer_saturated (K ε : ℝ) :
    censusTemperature K ε * Real.log 2 = energyPerBit K ε := by
  unfold censusTemperature energyPerBit Real.logb
  rw [div_div_eq_mul_div, div_mul_eq_mul_div]

/-- `log 8 = 3 log 2`: an event on the 8-twist alphabet carries three bits. -/
theorem log_eight : Real.log 8 = 3 * Real.log 2 := by
  have h : (8 : ℝ) = 2 ^ 3 := by norm_num
  rw [h, Real.log_pow] <;> norm_num

/-- **L3 — the substrate value.** On the 8-twist alphabet `T · log 2 = ε / 3`: a bit costs a third of
    an event quantum. -/
theorem landauer_eight (ε : ℝ) : censusTemperature 8 ε * Real.log 2 = ε / 3 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  unfold censusTemperature
  rw [log_eight, div_mul_eq_mul_div, mul_div_mul_right ε 3 h2]

/-- **L3, as a temperature.** `T = ε / (3 log 2)` on the 8-twist alphabet. -/
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

/-- **L4 — requiring closure raises the temperature.** For `E > 0` the closed census's inverse
    temperature is strictly below the free census's. -/
theorem closure_runs_hotter (ε : ℝ) {E : ℝ} (hE : 0 < E) :
    Real.log 8 / ε - 2 * E⁻¹ < 1 / censusTemperature 8 ε := by
  rw [inv_censusTemperature]
  have : 0 < 2 * E⁻¹ := by positivity
  linarith

/-- The Zipf exponent of a `K`-letter census whose events carry Boltzmann weight `e^{−ε/T}`:
    `B = ε / (T log K)`. -/
noncomputable def zipfExponent (K ε T : ℝ) : ℝ := ε / (T * Real.log K)

/-- **L5 — the rank–frequency law.** A word of `n` events has frequency `e^{−nε/T}` and rank
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

end QLF.CensusTemperature
