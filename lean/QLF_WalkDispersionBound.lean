import QLF_BoostCovariance

/-!
# QLF_WalkDispersionBound — **the Dirac walk's speed of light is exact on the axes and slower off them**

The substrate theorem behind the first registered prediction for issue #11
([`Planck_Dispersion_Prediction.md`](../Planck_Dispersion_Prediction.md)).

The unitary Dirac walk of [`QLF_DiracWalk`](QLF_DiracWalk.lean) has the exact dispersion
`cos E = cos m · cos k_y · cos k_x · cos k_z` (`diracWalk_dispersion`), and
[`QLF_BoostCovariance`](QLF_BoostCovariance.lean) shows it is the Minkowski shell up to a relative
error of order `S ≈ (L_P/λ)²` (`onShell_minkowski`), so there is no correction linear in `L_P`.
This module fixes the **sign and direction pattern** of the quadratic correction for a massless mode:

> **`walk_axis_exact`** — along a lattice axis the walk's speed is exactly `c`: `E = k`.
>
> **`walk_face_subluminal`** — along a face diagonal `(κ, κ, 0)` the phase is strictly below `|k|`.
>
> **`walk_body_subluminal`** — along a body diagonal `(κ, κ, κ)`, `E < √3 κ = |k|`.
>
> **`walk_body_deficit_bounded`** — and the deficit is at most quadratic:
> `√3 κ (1 − κ²/2) < E`, so the phase velocity lies in `(1 − |k|²/6, 1)`.

`diracWalk_body_bracket` states the last two for an actual eigenvalue of the walk. The exact series
coefficient, `v_g = 1 − (1 − Σ n_a⁴)|k|²/4`, is computed in
[`planck_dispersion_prediction.py`](../planck_dispersion_prediction.py); the theorems here bound it
and fix its sign. No axioms.
-/

namespace QLF.WalkDispersionBound

open QLF.BoostCovariance Matrix

/-- `cos κ ≤ 1 − κ²/2 + 5κ⁴/96` for `|κ| ≤ 1`. -/
theorem cos_upper {x : ℝ} (hx : |x| ≤ 1) : Real.cos x ≤ 1 - x ^ 2 / 2 + 5 / 96 * x ^ 4 := by
  have h := cos_quad hx
  have := (abs_le.mp h).2
  linarith

/-- `1 − x²/2 + 5x⁴/96 ≤ cos x` fails in general; the lower bound used is `1 − x²/2 ≤ cos x`. -/
theorem cos_lower (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos

/-- **Along an axis the walk is exactly light-like.** For a massless mode with momentum `(k, 0, 0)`
the dispersion `cos E = cos k` forces `E = k` in the first band. -/
theorem walk_axis_exact {E k : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ Real.pi) (hk0 : 0 ≤ k)
    (hk1 : k ≤ Real.pi)
    (h : Real.cos E = Real.cos 0 * (Real.cos k * Real.cos 0 * Real.cos 0)) : E = k := by
  simp only [Real.cos_zero, one_mul, mul_one] at h
  exact Real.injOn_cos ⟨hE0, hE1⟩ ⟨hk0, hk1⟩ h

/-- `cos (√2 κ) < cos² κ` for `0 < κ ≤ 1/2`. -/
theorem face_gap {κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2) :
    Real.cos (Real.sqrt 2 * κ) < Real.cos κ ^ 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hslt : Real.sqrt 2 < 2 := by nlinarith
  have hx : |Real.sqrt 2 * κ| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have hu := cos_upper hx
  have hx2 : (Real.sqrt 2 * κ) ^ 2 = 2 * κ ^ 2 := by rw [mul_pow, hs2]
  have hx4 : (Real.sqrt 2 * κ) ^ 4 = 4 * κ ^ 4 := by
    have : (Real.sqrt 2 * κ) ^ 4 = ((Real.sqrt 2 * κ) ^ 2) ^ 2 := by ring
    rw [this, hx2]; ring
  rw [hx2, hx4] at hu
  have hl := cos_lower κ
  have ha : 0 ≤ 1 - κ ^ 2 / 2 := by nlinarith
  have hsq : (1 - κ ^ 2 / 2) ^ 2 ≤ Real.cos κ ^ 2 := pow_le_pow_left₀ ha hl 2
  have hk4 : 0 < κ ^ 4 := by positivity
  nlinarith

/-- **Along a face diagonal the walk is slower than light.** A massless mode with momentum
`(κ, κ, 0)`, `0 < κ ≤ 1/2`, has `E < √2 κ = |k|`. -/
theorem walk_face_subluminal {E κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2)
    (hE1 : E ≤ Real.pi)
    (h : Real.cos E = Real.cos 0 * (Real.cos κ * Real.cos κ * Real.cos 0)) :
    E < Real.sqrt 2 * κ := by
  simp only [Real.cos_zero, one_mul, mul_one] at h
  have gap := face_gap h0 h1
  by_contra hle
  rw [not_lt] at hle
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hE1 hle
  rw [h] at hmono
  nlinarith

/-- `cos (√3 κ) < cos³ κ` for `0 < κ ≤ 1/2`. -/
theorem body_gap {κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2) :
    Real.cos (Real.sqrt 3 * κ) < Real.cos κ ^ 3 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hslt : Real.sqrt 3 < 2 := by nlinarith
  have hx : |Real.sqrt 3 * κ| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have hu := cos_upper hx
  have hx2 : (Real.sqrt 3 * κ) ^ 2 = 3 * κ ^ 2 := by rw [mul_pow, hs3]
  have hx4 : (Real.sqrt 3 * κ) ^ 4 = 9 * κ ^ 4 := by
    have : (Real.sqrt 3 * κ) ^ 4 = ((Real.sqrt 3 * κ) ^ 2) ^ 2 := by ring
    rw [this, hx2]; ring
  rw [hx2, hx4] at hu
  have hl := cos_lower κ
  have ha : 0 ≤ 1 - κ ^ 2 / 2 := by nlinarith
  have hcube : (1 - κ ^ 2 / 2) ^ 3 ≤ Real.cos κ ^ 3 := pow_le_pow_left₀ ha hl 3
  -- (1 − κ²/2)³ − (1 − 3κ²/2 + 15κ⁴/32) = κ⁴ (9 − 4κ²)/32 > 0
  have hk4 : 0 < κ ^ 4 := by positivity
  have hpoly : 1 - 3 * κ ^ 2 / 2 + 15 / 32 * κ ^ 4 < (1 - κ ^ 2 / 2) ^ 3 := by
    have hk2 : κ ^ 2 ≤ 1 / 4 := by nlinarith
    have : (1 - κ ^ 2 / 2) ^ 3 - (1 - 3 * κ ^ 2 / 2 + 15 / 32 * κ ^ 4)
        = κ ^ 4 * (9 - 4 * κ ^ 2) / 32 := by ring
    have hpos : 0 < κ ^ 4 * (9 - 4 * κ ^ 2) / 32 := by
      apply div_pos _ (by norm_num); apply mul_pos hk4; nlinarith
    linarith
  have : 5 / 96 * (9 * κ ^ 4) = 15 / 32 * κ ^ 4 := by ring
  linarith

/-- **Along a body diagonal the walk is slower than light.** A massless mode with momentum
`(κ, κ, κ)`, `0 < κ ≤ 1/2`, has `E < √3 κ = |k|`. -/
theorem walk_body_subluminal {E κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2)
    (hE1 : E ≤ Real.pi)
    (h : Real.cos E = Real.cos 0 * (Real.cos κ * Real.cos κ * Real.cos κ)) :
    E < Real.sqrt 3 * κ := by
  simp only [Real.cos_zero, one_mul] at h
  have gap := body_gap h0 h1
  by_contra hle
  rw [not_lt] at hle
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hE1 hle
  rw [h] at hmono
  nlinarith

/-- `cos³ κ < cos (√3 κ (1 − κ²/2))` for `0 < κ ≤ 1/2`: the deficit is no larger than `κ²/2`. -/
theorem body_gap_lower {κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2) :
    Real.cos κ ^ 3 < Real.cos (Real.sqrt 3 * κ * (1 - κ ^ 2 / 2)) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hκ : |κ| ≤ 1 := by rw [abs_of_pos h0]; linarith
  have hu := cos_upper hκ
  have hc0 : 0 ≤ Real.cos κ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hcube : Real.cos κ ^ 3 ≤ (1 - κ ^ 2 / 2 + 5 / 96 * κ ^ 4) ^ 3 :=
    pow_le_pow_left₀ hc0 hu 3
  have hl := cos_lower (Real.sqrt 3 * κ * (1 - κ ^ 2 / 2))
  have hy2 : (Real.sqrt 3 * κ * (1 - κ ^ 2 / 2)) ^ 2 = 3 * κ ^ 2 * (1 - κ ^ 2 / 2) ^ 2 := by
    rw [mul_pow, mul_pow, hs3]
  rw [hy2] at hl
  -- (1 − y²/2) − (1 − κ²/2 + 5κ⁴/96)³ = κ⁴ q(κ²) / 884736 with q > 0 for κ² ≤ 1/4
  set u := κ ^ 2 with hu_def
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 4 := by rw [hu_def]; nlinarith
  have hpoly : (1 - κ ^ 2 / 2 + 5 / 96 * κ ^ 4) ^ 3 < 1 - 3 * κ ^ 2 * (1 - κ ^ 2 / 2) ^ 2 / 2 := by
    have hk4 : κ ^ 4 = u ^ 2 := by rw [hu_def]; ring
    rw [hk4, ← hu_def]
    have e : 1 - 3 * u * (1 - u / 2) ^ 2 / 2 - (1 - u / 2 + 5 / 96 * u ^ 2) ^ 3
        = u ^ 2 * (525312 - 82944 * u - 41760 * u ^ 2 + 3600 * u ^ 3 - 125 * u ^ 4) / 884736 := by
      ring
    have hq : 0 < 525312 - 82944 * u - 41760 * u ^ 2 + 3600 * u ^ 3 - 125 * u ^ 4 := by
      have h2 : u ^ 2 ≤ 1 / 16 := by nlinarith
      have h3 : 0 ≤ u ^ 3 := by positivity
      have h4 : u ^ 4 ≤ 1 / 256 := by nlinarith
      nlinarith
    have : 0 < u ^ 2 * (525312 - 82944 * u - 41760 * u ^ 2 + 3600 * u ^ 3 - 125 * u ^ 4) / 884736 :=
      div_pos (mul_pos (by positivity) hq) (by norm_num)
    linarith
  linarith

/-- **The body-diagonal deficit is at most quadratic.** With `cos E = cos³ κ`,
`√3 κ (1 − κ²/2) < E`. -/
theorem walk_body_deficit_bounded {E κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2) (hE0 : 0 ≤ E)
    (h : Real.cos E = Real.cos 0 * (Real.cos κ * Real.cos κ * Real.cos κ)) :
    Real.sqrt 3 * κ * (1 - κ ^ 2 / 2) < E := by
  simp only [Real.cos_zero, one_mul] at h
  have gap := body_gap_lower h0 h1
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hslt : Real.sqrt 3 < 2 := by nlinarith
  have hy0 : 0 ≤ Real.sqrt 3 * κ * (1 - κ ^ 2 / 2) := by
    apply mul_nonneg (by positivity); nlinarith
  have hy1 : Real.sqrt 3 * κ * (1 - κ ^ 2 / 2) ≤ Real.pi := by
    have : Real.sqrt 3 * κ * (1 - κ ^ 2 / 2) ≤ Real.sqrt 3 * κ := by
      have : 0 ≤ Real.sqrt 3 * κ := by positivity
      nlinarith
    nlinarith [Real.pi_gt_three]
  by_contra hle
  rw [not_lt] at hle
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hE0 hy1 hle
  rw [h] at hmono
  nlinarith

/-- **For an actual eigenvalue of the massless walk on the body diagonal**, the quasi-energy is
bracketed: `√3 κ (1 − κ²/2) < E < √3 κ`. The phase velocity `E/|k|` lies in `(1 − κ²/2, 1)`:
slower than `c`, by at most a quadratic amount, and never faster. -/
theorem diracWalk_body_bracket {κ E : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2) (hE0 : 0 ≤ E)
    (hE1 : E ≤ Real.pi) (v : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0)
    (hev : QLF.DiracWalk.diracWalk κ κ κ 0 *ᵥ v = Complex.exp (E * Complex.I) • v) :
    Real.sqrt 3 * κ * (1 - κ ^ 2 / 2) < E ∧ E < Real.sqrt 3 * κ := by
  have hd := QLF.DiracWalk.diracWalk_dispersion κ κ κ 0 E v hv hev
  have hd' : Real.cos E = Real.cos 0 * (Real.cos κ * Real.cos κ * Real.cos κ) := by
    rw [hd]
  exact ⟨walk_body_deficit_bounded h0 h1 hE0 hd', walk_body_subluminal h0 h1 hE1 hd'⟩

/-- **For an actual eigenvalue on a lattice axis**, the walk is exactly light-like: `E = k`. -/
theorem diracWalk_axis_exact {k E : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ Real.pi) (hE0 : 0 ≤ E)
    (hE1 : E ≤ Real.pi) (v : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0)
    (hev : QLF.DiracWalk.diracWalk 0 k 0 0 *ᵥ v = Complex.exp (E * Complex.I) • v) :
    E = k := by
  have hd := QLF.DiracWalk.diracWalk_dispersion 0 k 0 0 E v hv hev
  apply walk_axis_exact hE0 hE1 hk0 hk1
  rw [hd]; ring

end QLF.WalkDispersionBound
