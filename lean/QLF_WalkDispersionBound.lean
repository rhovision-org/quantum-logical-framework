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

/-! ## Group velocity in every direction

The prediction concerns wave packets, so the group velocity `∇E` matters, not only the phase
velocity `E/|k|`. For the massless walk `E = arccos (cos k₁ cos k₂ cos k₃)`; its partial derivatives
are `sin kᵢ ∏_{j≠i} cos kⱼ / √(1 − P²)` with `P = ∏ cos kᵢ`. Writing `aᵢ = sin² kᵢ`, the squared
speed is (weight of exactly one active axis) / (weight of at least one active axis), which is at most
`1`. So the walk's group velocity never exceeds `c`, in every direction and at every in-band
momentum where the dispersion is differentiable (`P ≠ ±1`). -/

/-- The census inequality: one active axis weighs no more than at least one. -/
theorem one_axis_le_some_axis (k₁ k₂ k₃ : ℝ) :
    (Real.sin k₁ * Real.cos k₂ * Real.cos k₃) ^ 2 + (Real.cos k₁ * Real.sin k₂ * Real.cos k₃) ^ 2
      + (Real.cos k₁ * Real.cos k₂ * Real.sin k₃) ^ 2
      ≤ 1 - (Real.cos k₁ * Real.cos k₂ * Real.cos k₃) ^ 2 := by
  have e1 := Real.sin_sq_add_cos_sq k₁
  have e2 := Real.sin_sq_add_cos_sq k₂
  have e3 := Real.sin_sq_add_cos_sq k₃
  set a₁ := Real.sin k₁ ^ 2
  set a₂ := Real.sin k₂ ^ 2
  set a₃ := Real.sin k₃ ^ 2
  set b₁ := Real.cos k₁ ^ 2
  set b₂ := Real.cos k₂ ^ 2
  set b₃ := Real.cos k₃ ^ 2
  have h : 1 - (Real.cos k₁ * Real.cos k₂ * Real.cos k₃) ^ 2
      - ((Real.sin k₁ * Real.cos k₂ * Real.cos k₃) ^ 2 + (Real.cos k₁ * Real.sin k₂ * Real.cos k₃) ^ 2
        + (Real.cos k₁ * Real.cos k₂ * Real.sin k₃) ^ 2)
      = a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃ + a₁ * a₂ * a₃ := by
    have hb1 : b₁ = 1 - a₁ := by linarith
    have hb2 : b₂ = 1 - a₂ := by linarith
    have hb3 : b₃ = 1 - a₃ := by linarith
    have : (Real.cos k₁ * Real.cos k₂ * Real.cos k₃) ^ 2 = b₁ * b₂ * b₃ := by ring
    have h1 : (Real.sin k₁ * Real.cos k₂ * Real.cos k₃) ^ 2 = a₁ * b₂ * b₃ := by ring
    have h2 : (Real.cos k₁ * Real.sin k₂ * Real.cos k₃) ^ 2 = b₁ * a₂ * b₃ := by ring
    have h3 : (Real.cos k₁ * Real.cos k₂ * Real.sin k₃) ^ 2 = b₁ * b₂ * a₃ := by ring
    rw [this, h1, h2, h3, hb1, hb2, hb3]; ring
  have ha1 : 0 ≤ a₁ := sq_nonneg _
  have ha2 : 0 ≤ a₂ := sq_nonneg _
  have ha3 : 0 ≤ a₃ := sq_nonneg _
  have hb1 : 0 ≤ b₁ := sq_nonneg _
  have hb2 : 0 ≤ b₂ := sq_nonneg _
  have hb3 : 0 ≤ b₃ := sq_nonneg _
  have : 0 ≤ a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃ + a₁ * a₂ * a₃ := by positivity
  linarith

/-- The partial derivative of `arccos (cos x · c)` in `x`. -/
theorem hasDerivAt_arccos_cos_mul (x c : ℝ) (h1 : Real.cos x * c ≠ -1) (h2 : Real.cos x * c ≠ 1) :
    HasDerivAt (fun y => Real.arccos (Real.cos y * c))
      (Real.sin x * c / Real.sqrt (1 - (Real.cos x * c) ^ 2)) x := by
  have hin : HasDerivAt (fun y => Real.cos y * c) (-Real.sin x * c) x :=
    (Real.hasDerivAt_cos x).mul_const c
  have := (Real.hasDerivAt_arccos h1 h2).comp x hin
  show HasDerivAt (Real.arccos ∘ fun y => Real.cos y * c) _ x
  exact this.congr_deriv (by ring)

/-- **The walk's group velocity never exceeds `c`.** At any momentum `(k₁, k₂, k₃)` where
`P = cos k₁ cos k₂ cos k₃ ≠ ±1`, the massless walk's quasi-energy `E = arccos P` has partial
derivatives `g₁, g₂, g₃` with `g₁² + g₂² + g₃² ≤ 1`. -/
theorem walk_group_velocity_le_one (k₁ k₂ k₃ : ℝ)
    (h1 : Real.cos k₁ * Real.cos k₂ * Real.cos k₃ ≠ -1)
    (h2 : Real.cos k₁ * Real.cos k₂ * Real.cos k₃ ≠ 1) :
    ∃ g₁ g₂ g₃ : ℝ,
      HasDerivAt (fun x => Real.arccos (Real.cos x * Real.cos k₂ * Real.cos k₃)) g₁ k₁ ∧
      HasDerivAt (fun y => Real.arccos (Real.cos k₁ * Real.cos y * Real.cos k₃)) g₂ k₂ ∧
      HasDerivAt (fun z => Real.arccos (Real.cos k₁ * Real.cos k₂ * Real.cos z)) g₃ k₃ ∧
      g₁ ^ 2 + g₂ ^ 2 + g₃ ^ 2 ≤ 1 := by
  set P := Real.cos k₁ * Real.cos k₂ * Real.cos k₃ with hP
  set D := Real.sqrt (1 - P ^ 2)
  have hP2 : P ^ 2 < 1 := by
    have hle : P ^ 2 ≤ 1 := by
      have a := Real.cos_sq_le_one k₁
      have b := Real.cos_sq_le_one k₂
      have c := Real.cos_sq_le_one k₃
      have : P ^ 2 = Real.cos k₁ ^ 2 * Real.cos k₂ ^ 2 * Real.cos k₃ ^ 2 := by rw [hP]; ring
      rw [this]
      have h0a : 0 ≤ Real.cos k₁ ^ 2 := sq_nonneg _
      have h0b : 0 ≤ Real.cos k₂ ^ 2 := sq_nonneg _
      have h0c : 0 ≤ Real.cos k₃ ^ 2 := sq_nonneg _
      calc Real.cos k₁ ^ 2 * Real.cos k₂ ^ 2 * Real.cos k₃ ^ 2 ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by norm_num
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have : (P - 1) * (P + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact h2 (by linarith)
      · exact h1 (by linarith)
  have hD2 : D ^ 2 = 1 - P ^ 2 := Real.sq_sqrt (by linarith)
  have hDpos : 0 < D ^ 2 := by rw [hD2]; linarith
  -- the three partial derivatives
  have d1 := hasDerivAt_arccos_cos_mul k₁ (Real.cos k₂ * Real.cos k₃)
    (by rw [← mul_assoc]; exact h1) (by rw [← mul_assoc]; exact h2)
  have d2 := hasDerivAt_arccos_cos_mul k₂ (Real.cos k₁ * Real.cos k₃)
    (by rw [hP] at h1; intro h; apply h1; rw [← h]; ring)
    (by rw [hP] at h2; intro h; apply h2; rw [← h]; ring)
  have d3 := hasDerivAt_arccos_cos_mul k₃ (Real.cos k₁ * Real.cos k₂)
    (by rw [hP] at h1; intro h; apply h1; rw [← h]; ring)
    (by rw [hP] at h2; intro h; apply h2; rw [← h]; ring)
  refine ⟨Real.sin k₁ * (Real.cos k₂ * Real.cos k₃) / D,
    Real.sin k₂ * (Real.cos k₁ * Real.cos k₃) / D,
    Real.sin k₃ * (Real.cos k₁ * Real.cos k₂) / D, ?_, ?_, ?_, ?_⟩
  · have e : (fun x => Real.arccos (Real.cos x * Real.cos k₂ * Real.cos k₃))
        = (fun y => Real.arccos (Real.cos y * (Real.cos k₂ * Real.cos k₃))) := by
      funext x; rw [mul_assoc]
    rw [e]
    have : (Real.cos k₁ * (Real.cos k₂ * Real.cos k₃)) ^ 2 = P ^ 2 := by rw [hP]; ring
    simpa [D, this] using d1
  · have e : (fun y => Real.arccos (Real.cos k₁ * Real.cos y * Real.cos k₃))
        = (fun y => Real.arccos (Real.cos y * (Real.cos k₁ * Real.cos k₃))) := by
      funext y; congr 1; ring
    rw [e]
    have : (Real.cos k₂ * (Real.cos k₁ * Real.cos k₃)) ^ 2 = P ^ 2 := by rw [hP]; ring
    simpa [D, this] using d2
  · have e : (fun z => Real.arccos (Real.cos k₁ * Real.cos k₂ * Real.cos z))
        = (fun z => Real.arccos (Real.cos z * (Real.cos k₁ * Real.cos k₂))) := by
      funext z; congr 1; ring
    rw [e]
    have : (Real.cos k₃ * (Real.cos k₁ * Real.cos k₂)) ^ 2 = P ^ 2 := by rw [hP]; ring
    simpa [D, this] using d3
  · have key := one_axis_le_some_axis k₁ k₂ k₃
    rw [← hP] at key
    rw [div_pow, div_pow, div_pow, hD2, ← add_div, ← add_div,
      div_le_one (by linarith)]
    nlinarith [key]

end QLF.WalkDispersionBound
