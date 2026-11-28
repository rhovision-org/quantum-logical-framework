import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_BlackHoleInfall — whose horizon? Falling into large, spinning and small black holes

Companion to [`Falling_Into_Black_Holes.md`](../Falling_Into_Black_Holes.md). Units `c = 1`; the
Schwarzschild radius is `rs = 2GM/c²`. Everything here is algebra on standard general relativity
(Painlevé–Gullstrand / river coordinates, Kerr horizons, the Hawking `M³` lifetime). What it settles
is **which statements are frame statements**, so the doc can say precisely what "the horizon recedes
and you never reach it" means and where QLF goes further than GR.

## 1. The river (Painlevé–Gullstrand) picture of a non-spinning hole

Space flows inward at `v(r) = √(rs/r)` (Hamilton & Lisle, *Am. J. Phys.* 76, 519 (2008)). The radial
line element is `ds² = −dt² + (dr + v dt)²`, so per `dt²` an observer with coordinate velocity
`u = dr/dt` has interval `−1 + (u + v)²` (`pgInterval`).

* `freefall_proper_time`: an observer carried by the river (`u = −v`) has `dτ = dt` **at every
  radius, inside the horizon included**. Nothing in the infaller's own clock marks `r = rs`.
* `static_timelike_iff`, `static_exists_iff`: an observer who *stays put* (`u = 0`) is timelike iff
  `rs < r`. The Schwarzschild horizon is where **holding still** becomes impossible — a property of the
  static perspective, not of the infaller's path.
* `null_iff`: light moves at `±1` relative to the river everywhere: `u = 1 − v` or `u = −1 − v`.

## 2. The perspective horizon recedes ahead of the infaller

For an observer with coordinate velocity `u < 1`, outgoing light keeps exact pace with them where
`1 − v(r) = u`, i.e. at `perspectiveHorizon rs u = rs/(1−u)²` (`river_perspectiveHorizon`,
`river_eq_iff`). The static observer's (`u = 0`) is the event-horizon radius `rs`
(`perspectiveHorizon_static`). For the infaller at `r` (`u = −v(r)`):

* `infaller_horizon_lt_position`: it is **always strictly below them**;
* `infaller_horizon_lt_rs`: it lies inside `rs`;
* `infaller_horizon_strictMono`: it **falls as they fall**;
* `infaller_horizon_tendsto_zero`: it reaches `0` only as `r → 0`;
* `infaller_horizon_tendsto_rs`: at large distance it tends to `rs` — the far observers' horizon is the
  limit of the family.

An observer climbing out (`0 < u`) has a horizon **outside** `rs` (`outward_horizon_gt_rs`). So the
surface called "the horizon" depends on the motion of the perspective, which is the precise content of
"motion is only relative — even falling into a black hole". Scope: this is an instantaneous surface in
river coordinates, not the global event horizon, and GR still says the infaller passes the radius
`rs` in finite proper time (`fall_time_hasDerivAt`, `fall_time_finite`), where far observers see them
slow to a stop (`farVelocity_at_horizon`).

**Thrust and escape.** Thrust works at every radius: every local velocity below `c` relative to the
river is available (`thrust_works`), and every timelike observer, thrusting or not, inside or outside,
has their own perspective horizon strictly below them (`own_horizon_below`). What thrust cannot change
inside is the static perspective's radius: an outward path in `r` exists exactly where `rs < r`
(`escape_possible_iff_radius`, `inside_all_inward`).

## 3. "Large enough": the horizon is locally invisible

The radial tidal stretch on a body of length `ℓ` is `rs·ℓ/r³` (exact for radial geodesics in
Schwarzschild). At the horizon it is `ℓ/rs²` (`tidal_at_horizon`) and tends to `0` as the hole grows
(`tidal_at_horizon_tendsto_zero`, explicit threshold `tidal_at_horizon_lt`).

## 4. Spinning (Kerr) holes

`rPlus = M + √(M² − a²)`, `Ω_H = a/(r₊² + a²)` (`horizonOmega`). `rPlus_sq_add_sq` gives
`r₊² + a² = 2M r₊`; `horizonOmega_le` bounds the dragging rate by `1/(2M)`; `horizonOmega_scale`
shows it scales as `1/M` at fixed spin, so `horizonOmega_tendsto_zero`: being dragged around a large
hole is slow. Free fall is geodesic whether or not the frame is dragged, so no accelerometer reads the
dragging. Where Kerr genuinely differs is the **inner horizon** (`kerr_two_horizons`), the
Cauchy horizon at which GR's mass inflation occurs.

## 5. Small holes evaporate, and finish fast

With Hawking's lifetime `t = K·M³` (`lifetime`): `lifetime_strictMono`, `evaporated_iff` (a hole
younger than its lifetime survives exactly when it is heavier than the threshold mass), and
`lifetime_fraction` / `last_half_eighth`: the time left when a fraction `f` of the mass remains is
`f³` of the whole — the last half of the mass goes in the last eighth of the lifetime.

No axioms.
-/

namespace QLF.BlackHoleInfall

open Real Filter Topology

/-! ## 1. The river picture -/

/-- The inflow speed of space, `v(r) = √(rs/r)` (units `c = 1`). -/
noncomputable def river (rs r : ℝ) : ℝ := Real.sqrt (rs / r)

theorem river_pos {rs r : ℝ} (hrs : 0 < rs) (hr : 0 < r) : 0 < river rs r :=
  Real.sqrt_pos.mpr (div_pos hrs hr)

theorem river_sq {rs r : ℝ} (hrs : 0 ≤ rs) (hr : 0 < r) : river rs r ^ 2 = rs / r :=
  Real.sq_sqrt (div_nonneg hrs hr.le)

/-- The radial Painlevé–Gullstrand interval per `dt²` for coordinate velocity `u` in a river of
    speed `v`: `ds²/dt² = −1 + (u + v)²`. -/
def pgInterval (v u : ℝ) : ℝ := -1 + (u + v) ^ 2

/-- **The infaller's clock is the river's clock**: carried by the river, `dτ = dt` at every radius. -/
theorem freefall_proper_time (v : ℝ) : pgInterval v (-v) = -1 := by
  simp [pgInterval]

/-- Light moves at `±1` relative to the river. -/
theorem null_iff (v u : ℝ) : pgInterval v u = 0 ↔ u = 1 - v ∨ u = -1 - v := by
  unfold pgInterval
  constructor
  · intro h
    have : (u + v - 1) * (u + v + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> ring

/-- A static observer (`u = 0`) is timelike iff the river is slower than light there. -/
theorem static_timelike_iff {v : ℝ} (hv : 0 ≤ v) : pgInterval v 0 < 0 ↔ v < 1 := by
  unfold pgInterval
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem river_lt_one_iff {rs r : ℝ} (hrs : 0 ≤ rs) (hr : 0 < r) : river rs r < 1 ↔ rs < r := by
  unfold river
  rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one hr]

/-- **Holding still is possible exactly outside `rs`**: the horizon is the static perspective's
    boundary. -/
theorem static_exists_iff {rs r : ℝ} (hrs : 0 ≤ rs) (hr : 0 < r) :
    pgInterval (river rs r) 0 < 0 ↔ rs < r := by
  have hv : 0 ≤ river rs r := Real.sqrt_nonneg _
  rw [static_timelike_iff hv, river_lt_one_iff hrs hr]

/-- The infaller's coordinate velocity in Schwarzschild time, `dr/dt_S = −(1 − rs/r)·v`. -/
noncomputable def farVelocity (rs r : ℝ) : ℝ := -(1 - rs / r) * river rs r

/-- Far observers see the infaller stop at the horizon. -/
theorem farVelocity_at_horizon {rs : ℝ} (hrs : 0 < rs) : farVelocity rs rs = 0 := by
  simp [farVelocity, div_self hrs.ne']

/-- Outside the horizon the far observers still see the infaller moving inward. -/
theorem farVelocity_neg {rs r : ℝ} (hrs : 0 < rs) (h : rs < r) : farVelocity rs r < 0 := by
  have hr : 0 < r := hrs.trans h
  have h1 : 0 < 1 - rs / r := by rw [sub_pos, div_lt_one hr]; exact h
  have h2 := river_pos hrs hr
  unfold farVelocity; nlinarith

/-- The infaller's proper time as a function of radius, `τ(r) = (2/3)·r^{3/2}/√rs`. -/
noncomputable def fallTime (rs r : ℝ) : ℝ := 2 / 3 * (r * Real.sqrt r) / Real.sqrt rs

/-- `dτ/dr = √r/√rs = 1/v(r)`: the proper time is the integral of `1/v` (see `river_mul_inv`). -/
theorem fall_time_hasDerivAt {rs r : ℝ} (hr : 0 < r) :
    HasDerivAt (fallTime rs) (Real.sqrt r / Real.sqrt rs) r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have h : HasDerivAt (fun x => x * Real.sqrt x) (1 * Real.sqrt r + r * (1 / (2 * Real.sqrt r))) r :=
    (hasDerivAt_id' r).mul (Real.hasDerivAt_sqrt hr.ne')
  have e : 2 / 3 * (1 * Real.sqrt r + r * (1 / (2 * Real.sqrt r))) = Real.sqrt r := by
    have : r * (1 / (2 * Real.sqrt r)) = Real.sqrt r / 2 := by
      field_simp
      linarith [hsq]
    rw [this]; ring
  have h3 := (h.const_mul (2 / 3 : ℝ)).div_const (Real.sqrt rs)
  rw [e] at h3
  exact h3

theorem river_mul_inv {rs r : ℝ} (hrs : 0 < rs) (hr : 0 < r) :
    river rs r * (Real.sqrt r / Real.sqrt rs) = 1 := by
  unfold river
  rw [Real.sqrt_div' rs hr.le]
  have : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have : 0 < Real.sqrt rs := Real.sqrt_pos.mpr hrs
  field_simp

/-- **GR's crossing is finite**: from `r₀ > rs` to `rs` takes positive, finite proper time. -/
theorem fall_time_finite {rs r₀ : ℝ} (hrs : 0 < rs) (h : rs < r₀) :
    0 < fallTime rs r₀ - fallTime rs rs := by
  unfold fallTime
  have hq : 0 < Real.sqrt rs := Real.sqrt_pos.mpr hrs
  have hle : Real.sqrt rs < Real.sqrt r₀ := Real.sqrt_lt_sqrt hrs.le h
  rw [← sub_div]
  apply div_pos _ hq
  have : rs * Real.sqrt rs < r₀ * Real.sqrt r₀ := by nlinarith
  linarith

/-! ## 2. The perspective horizon -/

/-- Where outgoing light keeps pace with an observer of coordinate velocity `u < 1`:
    `1 − v(r) = u`, i.e. `r = rs/(1 − u)²`. -/
noncomputable def perspectiveHorizon (rs u : ℝ) : ℝ := rs / (1 - u) ^ 2

theorem perspectiveHorizon_pos {rs u : ℝ} (hrs : 0 < rs) (hu : u < 1) :
    0 < perspectiveHorizon rs u := by
  unfold perspectiveHorizon; have : 0 < 1 - u := by linarith
  positivity

theorem river_perspectiveHorizon {rs u : ℝ} (hrs : 0 < rs) (hu : u < 1) :
    river rs (perspectiveHorizon rs u) = 1 - u := by
  have hu' : 0 < 1 - u := by linarith
  unfold river perspectiveHorizon
  have : rs / (rs / (1 - u) ^ 2) = (1 - u) ^ 2 := by field_simp
  rw [this, Real.sqrt_sq hu'.le]

/-- The perspective horizon is the unique radius where outgoing light keeps pace. -/
theorem river_eq_iff {rs u r : ℝ} (hrs : 0 < rs) (hu : u < 1) (hr : 0 < r) :
    1 - river rs r = u ↔ r = perspectiveHorizon rs u := by
  constructor
  · intro h
    have hv : river rs r = 1 - u := by linarith
    have hsq := river_sq hrs.le hr
    rw [hv] at hsq
    have hu' : 0 < 1 - u := by linarith
    unfold perspectiveHorizon
    rw [hsq]; field_simp
  · rintro rfl; rw [river_perspectiveHorizon hrs hu]; ring

/-- The static observer's perspective horizon is the event-horizon radius. -/
theorem perspectiveHorizon_static (rs : ℝ) : perspectiveHorizon rs 0 = rs := by
  simp [perspectiveHorizon]

/-- An infaller with any inward speed has a perspective horizon inside `rs`. -/
theorem infaller_horizon_lt_rs {rs w : ℝ} (hrs : 0 < rs) (hw : 0 < w) :
    perspectiveHorizon rs (-w) < rs := by
  unfold perspectiveHorizon
  apply div_lt_self hrs
  nlinarith

/-- **The horizon is always ahead**: the infaller's perspective horizon is strictly below them. -/
theorem infaller_horizon_lt_position {rs r : ℝ} (hrs : 0 < rs) (hr : 0 < r) :
    perspectiveHorizon rs (-river rs r) < r := by
  have hw := river_pos hrs hr
  have hsq := river_sq hrs.le hr
  have hrs_eq : rs = river rs r ^ 2 * r := by
    rw [hsq]; field_simp
  unfold perspectiveHorizon
  set w := river rs r
  rw [div_lt_iff₀ (by nlinarith), hrs_eq]
  nlinarith [mul_pos hw hr]

theorem river_strictAnti {rs r₁ r₂ : ℝ} (hrs : 0 < rs) (h1 : 0 < r₁) (h : r₁ < r₂) :
    river rs r₂ < river rs r₁ := by
  unfold river
  apply Real.sqrt_lt_sqrt (div_nonneg hrs.le (h1.trans h).le)
  exact div_lt_div_of_pos_left hrs h1 h

/-- **The horizon recedes as you fall**: a deeper infaller has a deeper perspective horizon. -/
theorem infaller_horizon_strictMono {rs r₁ r₂ : ℝ} (hrs : 0 < rs) (h1 : 0 < r₁) (h : r₁ < r₂) :
    perspectiveHorizon rs (-river rs r₁) < perspectiveHorizon rs (-river rs r₂) := by
  have hlt := river_strictAnti hrs h1 h
  have hw2 := river_pos hrs (h1.trans h)
  have hp : 0 < 1 - -river rs r₂ := by linarith
  unfold perspectiveHorizon
  apply div_lt_div_of_pos_left hrs (by positivity)
  nlinarith

/-- It reaches the centre only together with the infaller. -/
theorem infaller_horizon_tendsto_zero {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (fun r => perspectiveHorizon rs (-river rs r)) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hw := river_pos hrs hr
    exact (perspectiveHorizon_pos hrs (by linarith)).le
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (infaller_horizon_lt_position hrs hr).le

theorem river_tendsto_zero {rs : ℝ} : Tendsto (river rs) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => rs / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have := (Real.continuous_sqrt.tendsto 0).comp h
  show Tendsto (fun r => Real.sqrt (rs / r)) atTop (𝓝 0)
  simpa [Function.comp_def] using this

/-- Far away, the infaller's horizon tends to the static one, `rs`. -/
theorem infaller_horizon_tendsto_rs {rs : ℝ} :
    Tendsto (fun r => perspectiveHorizon rs (-river rs r)) atTop (𝓝 rs) := by
  have hden : Tendsto (fun r => (1 - -river rs r) ^ 2) atTop (𝓝 ((1 - -0) ^ 2)) :=
    ((tendsto_const_nhds.sub river_tendsto_zero.neg).pow 2)
  have := (tendsto_const_nhds (x := rs)).div hden (by norm_num)
  unfold perspectiveHorizon
  convert this using 2 <;> norm_num

/-- An observer climbing out has a horizon outside `rs`. -/
theorem outward_horizon_gt_rs {rs u : ℝ} (hrs : 0 < rs) (hu0 : 0 < u) (hu1 : u < 1) :
    rs < perspectiveHorizon rs u := by
  unfold perspectiveHorizon
  have h : (1 - u) ^ 2 < 1 := by nlinarith
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith [mul_lt_mul_of_pos_left h hrs]

/-! ## 2a. Escaping -/

/-- **Climbing out is possible exactly where the river is slower than light**: some outward
    coordinate velocity `u > 0` is timelike iff `v < 1`. -/
theorem escape_possible_iff {v : ℝ} (hv : 0 ≤ v) : (∃ u, 0 < u ∧ pgInterval v u < 0) ↔ v < 1 := by
  unfold pgInterval
  constructor
  · rintro ⟨u, hu, h⟩
    nlinarith
  · intro h
    refine ⟨(1 - v) / 2, by linarith, ?_⟩
    nlinarith

/-- **Inside, every timelike path moves inward**: where `v > 1`, any timelike coordinate velocity is
    negative, whatever the thrust. -/
theorem inside_all_inward {v u : ℝ} (hv : 1 < v) (h : pgInterval v u < 0) : u < 0 := by
  unfold pgInterval at h
  nlinarith

/-- **Thrust works everywhere**: at every radius, inside the horizon included, every local velocity
    `w` with `|w| < 1` relative to the river is a timelike motion. -/
theorem thrust_works (v : ℝ) {w : ℝ} (hw : |w| < 1) : pgInterval v (w - v) < 0 := by
  unfold pgInterval
  have : w ^ 2 < 1 := by
    have := sq_abs w ▸ (pow_lt_one₀ (abs_nonneg w) hw two_ne_zero); simpa using this
  nlinarith

/-- **Nobody ever reaches their own horizon**: every timelike observer at `r`, thrusting or not,
    inside `rs` or outside, has their perspective horizon strictly below them. -/
theorem own_horizon_below {rs r u : ℝ} (hrs : 0 < rs) (hr : 0 < r)
    (htl : pgInterval (river rs r) u < 0) : perspectiveHorizon rs u < r := by
  unfold pgInterval at htl
  have hv := river_pos hrs hr
  have h1 : u + river rs r < 1 := by nlinarith
  have hu : u < 1 := by linarith
  have hph := perspectiveHorizon_pos hrs hu
  by_contra hle'
  have hle := not_lt.mp hle'
  rcases hle.lt_or_eq with hlt | heq
  · have := river_strictAnti hrs hr hlt
    rw [river_perspectiveHorizon hrs hu] at this
    linarith
  · have := river_perspectiveHorizon hrs hu
    rw [← heq] at this
    linarith

/-- In terms of radius: some outward path exists at `r` iff `rs < r`. -/
theorem escape_possible_iff_radius {rs r : ℝ} (hrs : 0 ≤ rs) (hr : 0 < r) :
    (∃ u, 0 < u ∧ pgInterval (river rs r) u < 0) ↔ rs < r := by
  have hv : 0 ≤ river rs r := Real.sqrt_nonneg _
  rw [escape_possible_iff hv, river_lt_one_iff hrs hr]

/-! ## 2b. The interior grows with the hole's age

Inside (`r < rs`) the Schwarzschild metric is `ds² = −dr²/(rs/r − 1) + (rs/r − 1) dt² + r² dΩ²`: the
exterior time `t` is a spatial direction. A stretch of it spanning the hole's age `T` has proper length
`√(rs/r − 1)·T` (`interiorStretch`), exactly `c·T` at `r = rs/2` (`interiorStretch_half`). The
spheres shrink meanwhile, so the growth is along one axis. The volume per unit time,
`4π r²·√(rs/r − 1)`, is largest at `r = 3rs/4`, where it is `3√3·π·M²`
(`interiorVolumeRate_sq_le`, `interiorVolumeRate_sq_max`): the Christodoulou–Rovelli linear growth
of the maximal interior volume (Phys. Rev. D 91, 064046 (2015)). -/

/-- The proper-length factor of the interior's long direction at radius `r < rs`. -/
noncomputable def interiorStretch (rs r : ℝ) : ℝ := Real.sqrt (rs / r - 1)

/-- At half the Schwarzschild radius the interior length is exactly `c × (the hole's age)`. -/
theorem interiorStretch_half {rs : ℝ} (hrs : 0 < rs) : interiorStretch rs (rs / 2) = 1 := by
  unfold interiorStretch
  rw [show rs / (rs / 2) - 1 = 1 by field_simp; ring, Real.sqrt_one]

/-- The squared volume rate per unit time, divided by `(4π)²`: `r⁴(rs/r − 1) = rs r³ − r⁴`. -/
def interiorVolumeRateSq (rs r : ℝ) : ℝ := rs * r ^ 3 - r ^ 4

/-- **The interior volume grows at most at `3√3·π·M²` per unit time**: `rs r³ − r⁴ ≤ 27 rs⁴/256`
    for `r > 0` (so `4π√(…) ≤ (3√3/4)π rs² = 3√3 π M²`). -/
theorem interiorVolumeRate_sq_le {rs r : ℝ} (hrs : 0 < rs) (hr : 0 < r) :
    interiorVolumeRateSq rs r ≤ 27 / 256 * rs ^ 4 := by
  unfold interiorVolumeRateSq
  have hq : 0 < r ^ 2 + rs / 2 * r + 3 / 16 * rs ^ 2 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (r - 3 * rs / 4)) hq.le]

/-- …attained at `r = 3rs/4`. -/
theorem interiorVolumeRate_sq_max (rs : ℝ) :
    interiorVolumeRateSq rs (3 * rs / 4) = 27 / 256 * rs ^ 4 := by
  unfold interiorVolumeRateSq; ring

/-! ## 3. Tidal stretch at the horizon -/

/-- Radial tidal acceleration across a body of length `ℓ` at radius `r`: `rs·ℓ/r³`. -/
noncomputable def tidal (rs r ℓ : ℝ) : ℝ := rs * ℓ / r ^ 3

theorem tidal_at_horizon {rs : ℝ} (ℓ : ℝ) (hrs : 0 < rs) : tidal rs rs ℓ = ℓ / rs ^ 2 := by
  unfold tidal; field_simp

/-- **Large enough means locally invisible**: the tidal stretch at the horizon vanishes as the hole
    grows. -/
theorem tidal_at_horizon_tendsto_zero (ℓ : ℝ) :
    Tendsto (fun rs : ℝ => ℓ / rs ^ 2) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)

theorem tidal_at_horizon_lt {rs ℓ ε : ℝ} (hrs : 0 < rs) (hε : 0 < ε) (h : ℓ < ε * rs ^ 2) :
    tidal rs rs ℓ < ε := by
  rw [tidal_at_horizon ℓ hrs, div_lt_iff₀ (by positivity)]; exact h

/-! ## 4. Kerr -/

/-- Outer Kerr horizon, `r₊ = M + √(M² − a²)` (units `G = c = 1`). -/
noncomputable def rPlus (M a : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2)

/-- Inner (Cauchy) Kerr horizon, `r₋ = M − √(M² − a²)`. -/
noncomputable def rMinus (M a : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - a ^ 2)

/-- Angular velocity of the outer horizon (the frame-dragging rate there). -/
noncomputable def horizonOmega (M a : ℝ) : ℝ := a / (rPlus M a ^ 2 + a ^ 2)

theorem rPlus_sq_add_sq {M a : ℝ} (h : a ^ 2 ≤ M ^ 2) :
    rPlus M a ^ 2 + a ^ 2 = 2 * M * rPlus M a := by
  unfold rPlus
  have hs := Real.sq_sqrt (sub_nonneg.mpr h)
  nlinarith [hs]

theorem M_le_rPlus (M a : ℝ) : M ≤ rPlus M a := by
  unfold rPlus; linarith [Real.sqrt_nonneg (M ^ 2 - a ^ 2)]

/-- **The dragging rate at a horizon is at most `1/(2M)`**. -/
theorem horizonOmega_le {M a : ℝ} (hM : 0 < M) (ha : 0 ≤ a) (haM : a ≤ M) :
    horizonOmega M a ≤ 1 / (2 * M) := by
  have h2 : a ^ 2 ≤ M ^ 2 := by nlinarith
  have hr := M_le_rPlus M a
  unfold horizonOmega
  rw [rPlus_sq_add_sq h2, div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

theorem horizonOmega_nonneg {M a : ℝ} (hM : 0 < M) (ha : 0 ≤ a) : 0 ≤ horizonOmega M a := by
  unfold horizonOmega; positivity

/-- At fixed spin parameter `χ = a/M`, the dragging rate scales as `1/M`. -/
theorem horizonOmega_scale {M a l : ℝ} (hM : 0 < M) (ha : 0 ≤ a) (haM : a ≤ M) (hl : 0 < l) :
    horizonOmega (l * M) (l * a) = horizonOmega M a / l := by
  have h2 : a ^ 2 ≤ M ^ 2 := by nlinarith
  have hs : Real.sqrt ((l * M) ^ 2 - (l * a) ^ 2) = l * Real.sqrt (M ^ 2 - a ^ 2) := by
    rw [show (l * M) ^ 2 - (l * a) ^ 2 = l ^ 2 * (M ^ 2 - a ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq hl.le]
  have hr : rPlus (l * M) (l * a) = l * rPlus M a := by
    unfold rPlus; rw [hs]; ring
  have hpos : 0 < rPlus M a ^ 2 + a ^ 2 := by
    have := M_le_rPlus M a; nlinarith
  unfold horizonOmega
  rw [hr]
  field_simp

/-- **Being dragged around a large hole is slow**: at fixed spin, `Ω_H → 0` as `M → ∞`. -/
theorem horizonOmega_tendsto_zero {χ : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    Tendsto (fun M => horizonOmega M (χ * M)) atTop (𝓝 0) := by
  have hup : Tendsto (fun M : ℝ => 1 / (2 * M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_gt_atTop 0] with M hM
    exact horizonOmega_nonneg hM (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with M hM
    exact horizonOmega_le hM (by positivity) (by nlinarith)

/-- A non-spinning hole: `r₊ = 2M`, no dragging. -/
theorem schwarzschild_limit {M : ℝ} (hM : 0 < M) : rPlus M 0 = 2 * M ∧ horizonOmega M 0 = 0 := by
  refine ⟨?_, by simp [horizonOmega]⟩
  unfold rPlus
  rw [show M ^ 2 - (0 : ℝ) ^ 2 = M ^ 2 by ring, Real.sqrt_sq hM.le]; ring

/-- **Where Kerr genuinely differs**: a spinning hole has a second, inner horizon. -/
theorem kerr_two_horizons {M a : ℝ} (ha : 0 < a) (haM : a < M) :
    0 < rMinus M a ∧ rMinus M a < rPlus M a := by
  have hM : 0 < M := ha.trans haM
  have hpos : 0 < M ^ 2 - a ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (M ^ 2 - a ^ 2) := Real.sqrt_pos.mpr hpos
  have hsM : Real.sqrt (M ^ 2 - a ^ 2) < M := by
    rw [Real.sqrt_lt' hM]; nlinarith
  unfold rMinus rPlus
  constructor <;> linarith

/-! ## 5. Evaporation -/

/-- Hawking lifetime `t = K·M³` (`K = 5120πG²/(ħc⁴)` for photon emission only; more species lower
    `K`, Page 1976). -/
def lifetime (K M : ℝ) : ℝ := K * M ^ 3

theorem lifetime_strictMono {K : ℝ} (hK : 0 < K) {M₁ M₂ : ℝ} (h0 : 0 ≤ M₁) (h : M₁ < M₂) :
    lifetime K M₁ < lifetime K M₂ := by
  unfold lifetime
  have : M₁ ^ 3 < M₂ ^ 3 := pow_lt_pow_left₀ h h0 (by norm_num)
  nlinarith

/-- **Which holes are gone**: with `K·M*³ = T` (the age), a hole of mass `M` has evaporated by `T`
    iff `M ≤ M*`. -/
theorem evaporated_iff {K T Mstar M : ℝ} (hK : 0 < K) (hs : 0 ≤ Mstar) (hM : 0 ≤ M)
    (hT : lifetime K Mstar = T) : lifetime K M ≤ T ↔ M ≤ Mstar := by
  rw [← hT]
  constructor
  · intro h
    rcases le_or_gt M Mstar with h' | hlt
    · exact h'
    · exact absurd h (not_le.mpr (lifetime_strictMono hK hs hlt))
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (lifetime_strictMono hK hM h).le
    · rw [h]

/-- The time left when a fraction `f` of the mass remains is `f³` of the lifetime. -/
theorem lifetime_fraction (K f M : ℝ) : lifetime K (f * M) = f ^ 3 * lifetime K M := by
  unfold lifetime; ring

/-- **The last half of the mass goes in the last eighth of the lifetime.** -/
theorem last_half_eighth (K M : ℝ) : lifetime K (M / 2) = lifetime K M / 8 := by
  unfold lifetime; ring

end QLF.BlackHoleInfall
