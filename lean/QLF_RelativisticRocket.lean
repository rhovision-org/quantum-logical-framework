import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_RelativisticRocket — accelerating away from Earth at constant proper acceleration

Companion to [`Rocket_To_The_Horizon.md`](../Rocket_To_The_Horizon.md); the flat-space half of the
question (the expanding-universe half is numerical, [`rocket_horizon.py`](../rocket_horizon.py)).
Units `c = 1`; proper acceleration `g > 0`; the ship starts at rest at Earth (`x = 0`, `t = 0`).
Standard special relativity, so what this module settles is the exact numbers and which statements
are about the ship's perspective.

The hyperbolic worldline (`earthTime`, `earthDist`): `t = sinh(gτ)/g`, `x = (cosh(gτ) − 1)/g`.

* `earthTime_hasDerivAt`, `earthDist_hasDerivAt`: `dt/dτ = cosh(gτ) = γ` and the **proper velocity**
  `dx/dτ = sinh(gτ)` (`properVelocity`), which grows without bound.
* `properVelocity_eq_one_iff`: the proper velocity reaches light speed exactly at
  `gτ = arsinh 1 = log(1 + √2)` (`arsinh_one`) — about `0.854` years of ship time at `1 g`.
  Then Earth time is `1/g` (`earthTime_at_light`) and the coordinate speed is `1/√2`
  (`coordSpeed_at_light`).
* `shipTime_to_reach` / `earthDist_shipTime_to_reach`: the ship time to reach distance `D` is
  `log(y + √(y² − 1))/g` with `y = 1 + gD` — logarithmic in `D` (`shipTime_to_reach_le`).
* **The ship's horizon** (`earth_signal_reaches_iff`): a light signal sent from Earth at Earth time
  `tₑ ≥ 0` ever reaches the ship iff `tₑ < 1/g`. The accelerating ship has a horizon a distance
  `1/g` (about `0.97` light-years at `1 g`) behind it, and Earth falls behind it. This is the
  flat-space twin of the static observer's horizon in [`QLF_BlackHoleInfall`](QLF_BlackHoleInfall.lean).
* **Every perspective has a horizon** (`arrivalTime_hasDerivAt`, `mutual_redshift`,
  `inertial_redshift_horizon`): with a finite redshift limit `N`, Earth loses the ship at the same
  ship time `log N / g` at which the ship loses Earth, and any two inertial observers at relative
  rapidity `η ≥ log N` are beyond each other's horizons. Horizons are relations between
  perspectives.

No axioms.
-/

namespace QLF.RelativisticRocket

open Real

/-- Earth time at ship proper time `τ`. -/
noncomputable def earthTime (g τ : ℝ) : ℝ := Real.sinh (g * τ) / g

/-- Distance from Earth at ship proper time `τ`. -/
noncomputable def earthDist (g τ : ℝ) : ℝ := (Real.cosh (g * τ) - 1) / g

/-- Proper velocity `dx/dτ`. -/
noncomputable def properVelocity (g τ : ℝ) : ℝ := Real.sinh (g * τ)

theorem earthTime_hasDerivAt {g : ℝ} (hg : 0 < g) (τ : ℝ) :
    HasDerivAt (earthTime g) (Real.cosh (g * τ)) τ := by
  have h := ((hasDerivAt_id' τ).const_mul g).sinh.div_const g
  have e : Real.cosh (g * τ) * (g * 1) / g = Real.cosh (g * τ) := by field_simp
  rw [e] at h; exact h

theorem earthDist_hasDerivAt {g : ℝ} (hg : 0 < g) (τ : ℝ) :
    HasDerivAt (earthDist g) (properVelocity g τ) τ := by
  have h := ((((hasDerivAt_id' τ).const_mul g).cosh).sub_const 1).div_const g
  have e : Real.sinh (g * τ) * (g * 1) / g = Real.sinh (g * τ) := by field_simp
  rw [e] at h; exact h

/-- The worldline is timelike with unit proper-time rate: `cosh² − sinh² = 1`. -/
theorem worldline_unit (g τ : ℝ) :
    Real.cosh (g * τ) ^ 2 - properVelocity g τ ^ 2 = 1 := by
  unfold properVelocity; rw [Real.cosh_sq]; ring

theorem arsinh_one : Real.arsinh 1 = Real.log (1 + Real.sqrt 2) := by
  rw [Real.arsinh]; norm_num

/-- **Proper velocity reaches `c`** exactly at `gτ = arsinh 1 = log(1 + √2)`. -/
theorem properVelocity_eq_one_iff {g τ : ℝ} (hg : 0 < g) :
    properVelocity g τ = 1 ↔ τ = Real.log (1 + Real.sqrt 2) / g := by
  have key : Real.sinh (g * τ) = 1 ↔ g * τ = Real.arsinh 1 := by
    constructor
    · intro h; rw [← h, Real.arsinh_sinh]
    · intro h; rw [h, Real.sinh_arsinh]
  unfold properVelocity
  rw [key, arsinh_one, eq_div_iff hg.ne', mul_comm]

theorem cosh_at_light (g : ℝ) (hg : 0 < g) :
    Real.cosh (g * (Real.log (1 + Real.sqrt 2) / g)) = Real.sqrt 2 := by
  have e : g * (Real.log (1 + Real.sqrt 2) / g) = Real.arsinh 1 := by
    rw [arsinh_one]; field_simp
  rw [e, Real.cosh_arsinh]; norm_num

/-- At that moment Earth has aged `1/g`. -/
theorem earthTime_at_light {g : ℝ} (hg : 0 < g) :
    earthTime g (Real.log (1 + Real.sqrt 2) / g) = 1 / g := by
  have e : g * (Real.log (1 + Real.sqrt 2) / g) = Real.arsinh 1 := by
    rw [arsinh_one]; field_simp
  unfold earthTime; rw [e, Real.sinh_arsinh]

/-- …and the ship's speed relative to Earth is `c/√2`. -/
theorem coordSpeed_at_light {g : ℝ} (hg : 0 < g) :
    properVelocity g (Real.log (1 + Real.sqrt 2) / g) /
      Real.cosh (g * (Real.log (1 + Real.sqrt 2) / g)) = 1 / Real.sqrt 2 := by
  rw [cosh_at_light g hg, (properVelocity_eq_one_iff hg).mpr rfl]

/-- Ship time to reach distance `D ≥ 0`. -/
noncomputable def shipTime_to_reach (g D : ℝ) : ℝ :=
  Real.log ((1 + g * D) + Real.sqrt ((1 + g * D) ^ 2 - 1)) / g

theorem cosh_log_inv {y : ℝ} (hy : 1 ≤ y) :
    Real.cosh (Real.log (y + Real.sqrt (y ^ 2 - 1))) = y := by
  have hs : 0 ≤ Real.sqrt (y ^ 2 - 1) := Real.sqrt_nonneg _
  have hpos : 0 < y + Real.sqrt (y ^ 2 - 1) := by linarith
  have hsq : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hpos]
  have hinv : (y + Real.sqrt (y ^ 2 - 1))⁻¹ = y - Real.sqrt (y ^ 2 - 1) := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith [hsq]
  rw [hinv]; ring

/-- **Reaching distance `D`** takes ship time `shipTime_to_reach g D`. -/
theorem earthDist_shipTime_to_reach {g D : ℝ} (hg : 0 < g) (hD : 0 ≤ D) :
    earthDist g (shipTime_to_reach g D) = D := by
  have hy : 1 ≤ 1 + g * D := by nlinarith
  unfold earthDist shipTime_to_reach
  rw [show g * (Real.log ((1 + g * D) + Real.sqrt ((1 + g * D) ^ 2 - 1)) / g)
      = Real.log ((1 + g * D) + Real.sqrt ((1 + g * D) ^ 2 - 1)) by field_simp,
    cosh_log_inv hy]
  field_simp; ring

/-- The ship time grows only logarithmically with distance: `τ ≤ log(2(1 + gD))/g`. -/
theorem shipTime_to_reach_le {g D : ℝ} (hg : 0 < g) (hD : 0 ≤ D) :
    shipTime_to_reach g D ≤ Real.log (2 * (1 + g * D)) / g := by
  have hy : 1 ≤ 1 + g * D := by nlinarith
  unfold shipTime_to_reach
  apply div_le_div_of_nonneg_right _ hg.le
  apply Real.log_le_log
  · have := Real.sqrt_nonneg ((1 + g * D) ^ 2 - 1); linarith
  · have : Real.sqrt ((1 + g * D) ^ 2 - 1) ≤ 1 + g * D := by
      rw [Real.sqrt_le_left (by linarith)]; linarith
    linarith

/-- The light-cone coordinate `t − x` of the ship: `(1 − e^{−gτ})/g`. -/
theorem earthTime_sub_earthDist (g τ : ℝ) (hg : 0 < g) :
    earthTime g τ - earthDist g τ = (1 - Real.exp (-(g * τ))) / g := by
  unfold earthTime earthDist
  rw [Real.sinh_eq, Real.cosh_eq]
  field_simp; ring

/-- **The ship's horizon.** A light signal sent from Earth at Earth time `tₑ ≥ 0` meets the ship
    (at some proper time) iff `tₑ < 1/g`. The signal travels on `t − x = tₑ`. -/
theorem earth_signal_reaches_iff {g tₑ : ℝ} (hg : 0 < g) (ht : 0 ≤ tₑ) :
    (∃ τ, earthTime g τ - earthDist g τ = tₑ) ↔ tₑ < 1 / g := by
  constructor
  · rintro ⟨τ, h⟩
    rw [earthTime_sub_earthDist g τ hg] at h
    rw [← h]
    apply div_lt_div_of_pos_right _ hg
    linarith [Real.exp_pos (-(g * τ))]
  · intro h
    have h1 : 0 < 1 - g * tₑ := by
      rw [lt_div_iff₀ hg] at h; linarith
    refine ⟨-Real.log (1 - g * tₑ) / g, ?_⟩
    rw [earthTime_sub_earthDist _ _ hg]
    have : -(g * (-Real.log (1 - g * tₑ) / g)) = Real.log (1 - g * tₑ) := by field_simp
    rw [this, Real.exp_log h1]
    field_simp; ring

/-! ## The redshift of Earth, and the redshift limit -/

/-- The Earth time at which the signal the ship receives at proper time `τ` was sent:
    `tₑ(τ) = (1 − e^{−gτ})/g`. -/
noncomputable def emitTime (g τ : ℝ) : ℝ := (1 - Real.exp (-(g * τ))) / g

theorem emitTime_eq (g τ : ℝ) (hg : 0 < g) : emitTime g τ = earthTime g τ - earthDist g τ :=
  (earthTime_sub_earthDist g τ hg).symm

/-- **Earth's redshift**: `dtₑ/dτ = e^{−gτ}`. Earth's clock, as received, runs slow by the factor
    `e^{−gτ}`, and every frequency sent from Earth arrives multiplied by it. -/
theorem emitTime_hasDerivAt {g : ℝ} (hg : 0 < g) (τ : ℝ) :
    HasDerivAt (emitTime g) (Real.exp (-(g * τ))) τ := by
  have h := ((((hasDerivAt_id' τ).const_mul (-g)).exp).const_sub 1).div_const g
  have hf : emitTime g = fun x => (1 - Real.exp (-g * x)) / g := by
    funext x; simp [emitTime, neg_mul]
  rw [hf]
  refine h.congr_deriv ?_
  rw [neg_mul]
  field_simp

theorem emitTime_lt {g : ℝ} (hg : 0 < g) (τ : ℝ) : emitTime g τ < 1 / g := by
  unfold emitTime
  apply div_lt_div_of_pos_right _ hg
  linarith [Real.exp_pos (-(g * τ))]

/-- **The redshift limit.** If no frequency ratio larger than `N > 1` can be realized (for QLF, the
    Planck frequency over the background frequency, below which nothing can be seen), Earth drops below it at
    ship time `log N / g` and not before: `e^{−gτ} ≤ 1/N ↔ log N / g ≤ τ`. Finite, not infinite. -/
theorem redshift_limit_iff {g N τ : ℝ} (hg : 0 < g) (hN : 0 < N) :
    Real.exp (-(g * τ)) ≤ 1 / N ↔ Real.log N / g ≤ τ := by
  rw [show (1 : ℝ) / N = Real.exp (-Real.log N) by rw [Real.exp_neg, Real.exp_log hN, one_div],
    Real.exp_le_exp, div_le_iff₀ hg]
  constructor <;> intro h <;> linarith [mul_comm g τ]

/-! ## Every perspective has a horizon

With a finite redshift limit, horizons are mutual. Earth, an inertial observer, sees the ship's
signals arrive redshifted by the same factor `e^{−gτ}`, so it loses the ship at the same ship time
`log N / g` at which the ship loses Earth. And any two inertial observers with relative rapidity `η`
see each other redshifted by `e^{−η}`, so each is beyond the other's horizon once `η ≥ log N`. -/

/-- The Earth time at which a signal the ship sends at proper time `τ` arrives at Earth:
    `t + x = (e^{gτ} − 1)/g`. -/
noncomputable def arrivalTime (g τ : ℝ) : ℝ := (Real.exp (g * τ) - 1) / g

theorem arrivalTime_eq (g τ : ℝ) : arrivalTime g τ = earthTime g τ + earthDist g τ := by
  unfold arrivalTime earthTime earthDist
  rw [Real.sinh_eq, Real.cosh_eq]
  ring

/-- Earth time per ship second, as Earth receives it: `e^{gτ}`, so the ship's frequencies arrive at
    Earth multiplied by `e^{−gτ}`, the same factor the ship sees on Earth's (`emitTime_hasDerivAt`). -/
theorem arrivalTime_hasDerivAt {g : ℝ} (hg : 0 < g) (τ : ℝ) :
    HasDerivAt (arrivalTime g) (Real.exp (g * τ)) τ := by
  have h := (((hasDerivAt_id' τ).const_mul g).exp.sub_const 1).div_const g
  have e : Real.exp (g * τ) * (g * 1) / g = Real.exp (g * τ) := by field_simp
  rw [e] at h; exact h

/-- **The redshifts are mutual**: the factor Earth sees on the ship is the factor the ship sees on
    Earth, `(e^{gτ})⁻¹ = e^{−gτ}`. -/
theorem mutual_redshift (g τ : ℝ) : (Real.exp (g * τ))⁻¹ = Real.exp (-(g * τ)) :=
  (Real.exp_neg _).symm

/-- **Inertial observers have horizons too**: two inertial observers at relative rapidity `η` see
    each other's frequencies multiplied by `e^{−η}` (the relativistic Doppler factor
    `√((1−β)/(1+β))`), so each is past the other's redshift limit iff `log N ≤ η`. -/
theorem inertial_redshift_horizon {N η : ℝ} (hN : 0 < N) :
    Real.exp (-η) ≤ 1 / N ↔ Real.log N ≤ η := by
  rw [show (1 : ℝ) / N = Real.exp (-Real.log N) by rw [Real.exp_neg, Real.exp_log hN, one_div],
    Real.exp_le_exp]
  constructor <;> intro h <;> linarith

end QLF.RelativisticRocket
