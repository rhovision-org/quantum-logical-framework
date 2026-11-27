# Falling into black holes: whose horizon?

Part of the [Quantum Logical Framework (QLF)](README.md). Lean companion:
[`lean/QLF_BlackHoleInfall.lean`](lean/QLF_BlackHoleInfall.lean) (no axioms). Background:
[`BLACK-HOLES.md`](BLACK-HOLES.md), [`GR_Schwarzschild.md`](GR_Schwarzschild.md),
[`Hadron_BlackHoles.md`](Hadron_BlackHoles.md).

Jim's father taught him that *motion is only relative, even falling into a black hole*
([`MyStory.md`](MyStory.md)). This doc makes that precise for three cases: a large stationary hole, a
spinning hole, and small holes. For each it separates three layers: what standard general relativity
says, what is proved in Lean here, and where QLF goes further (labelled as conjecture where it is one).

Every Lean statement below is algebra on standard GR, in units `c = 1` with Schwarzschild radius
`rs = 2GM/c²`. What the proofs settle is **which statements are statements about a perspective**.

---

## 1. A large stationary hole: the horizon recedes ahead of you

### 1a. The river picture

In Painlevé–Gullstrand coordinates the Schwarzschild geometry is space flowing inward through flat
space at `v(r) = √(rs/r)`, with light and matter moving through the flow by special relativity
(Hamilton & Lisle 2008, the "river model"). This is the GR form of the picture in
[`BLACK-HOLES.md`](BLACK-HOLES.md)'s Personal Origin: *"as if spacetime itself were falling into
masses."* The radial interval per `dt²`, for an observer with coordinate velocity `u = dr/dt`, is
`−1 + (u + v)²` (`pgInterval`). Three facts follow:

| Fact | Lean |
|---|---|
| An observer carried by the river (`u = −v`) has `dτ = dt` at **every** radius, inside `rs` too. Their clock records no event at the horizon. | `freefall_proper_time` |
| Light moves at `±c` relative to the river everywhere. | `null_iff` |
| An observer who **holds still** (`u = 0`) is possible exactly where `rs < r`. | `static_timelike_iff`, `static_exists_iff` |

So `r = rs` is where **standing still** stops being possible. It is the boundary of the static
observers' perspective, not a place marked on the infaller's own path.

### 1b. The perspective horizon

Take any observer moving with coordinate velocity `u < 1`. Outgoing light keeps exact pace with them
where `1 − v(r) = u`, which is the radius

`r_h(u) = rs / (1 − u)²`     (`perspectiveHorizon`, `river_perspectiveHorizon`, `river_eq_iff`).

Below `r_h`, outgoing light loses ground to that observer at that instant; above it, light gains. For
the static observer (`u = 0`) this is exactly `rs` (`perspectiveHorizon_static`). For an infaller
carried by the river at radius `r` (`u = −v(r)`) it is `rs/(1 + √(rs/r))²`, and:

| Property of the infaller's horizon | Lean |
|---|---|
| it is always strictly **below** the infaller | `infaller_horizon_lt_position` |
| it lies inside `rs` | `infaller_horizon_lt_rs` |
| it **falls as they fall** (strictly monotone in `r`) | `infaller_horizon_strictMono` |
| it reaches `0` only as the infaller does | `infaller_horizon_tendsto_zero` |
| far away it tends to `rs`, so the far observers' horizon is the limit of the family | `infaller_horizon_tendsto_rs` |
| an observer climbing out (`0 < u < 1`) has a horizon **outside** `rs` | `outward_horizon_gt_rs` |

That is the precise content of *"the horizon recedes from you and you never reach it."* The surface
called "the horizon" depends on the motion of the one who asks. The far observers' horizon `rs` is
one member of the family, the one that belongs to holding still.

**Scope.** `r_h` is an instantaneous surface in river coordinates, not the global event horizon (which
is defined by the whole future of the spacetime). It is the same construction applied to each
perspective, which is the point.

### 1c. What GR says about crossing `rs`, honestly

GR does not say the infaller is stopped at `rs`:

* **In the infaller's own time the radius `rs` is passed in finite proper time.**
  `τ(r) = (2/3) r^{3/2}/√rs` has `dτ/dr = 1/v(r)` (`fall_time_hasDerivAt`, `river_mul_inv`), and
  the trip from any `r₀ > rs` to `rs` is finite and positive (`fall_time_finite`). From rest at
  infinity, falling from `10 rs` to `rs` takes `(2/3)(10^{3/2} − 1) rs/c ≈ 20 rs/c`: about 14 minutes
  for Sgr A* (`rs/c ≈ 42 s`).
* **Far observers see the infaller slow to a stop.** The infaller's velocity in Schwarzschild time,
  `−(1 − rs/r)·v`, is negative outside and exactly zero at `rs` (`farVelocity_neg`,
  `farVelocity_at_horizon`). The "frozen at the horizon" picture is the static perspective.

The two readings do not contradict each other, and Jim's statement is consistent with both: the
infaller passes the radius `rs` with no event, because `rs` is not *their* horizon; the horizon that
belongs to them is always ahead.

### 1d. Why "large enough" matters

The radial tidal stretch across a body of length `ℓ` is `rs·ℓ/r³` (exact for radial geodesics in
Schwarzschild), so at the horizon it is `ℓ/rs²` (`tidal_at_horizon`) and goes to zero as the hole
grows (`tidal_at_horizon_tendsto_zero`, explicit threshold `tidal_at_horizon_lt`). In SI units it is
`c²ℓ/rs²`. For a 2 m body:

| Hole | `rs` | tidal stretch at horizon |
|---|---:|---:|
| 10 solar masses | 30 km | about 2×10⁸ m/s² (spaghettified well outside) |
| about 4.6×10⁴ solar masses | 1.4×10⁵ km | 9.8 m/s² (one Earth gravity) |
| Sgr A*, 4.3×10⁶ solar masses | 1.3×10⁷ km | about 1×10⁻³ m/s² |

Above roughly 10⁵ solar masses nothing local marks the horizon at all. The equivalence principle
then does all the work: a freely falling body is locally inertial, and "locally nothing changes"
([`MyStory.md`](MyStory.md)).

### 1e. Where QLF departs (conjecture)

In GR the infaller's own horizon in 1b and the infaller both reach `r = 0`, and the worldline ends at
the singularity after at most `π GM/c³` of proper time inside `rs`. QLF has no point of infinite
density: curvature is bounded by finite event density
([`Curvature.md`](Curvature.md) §3, [`Quantum_Gravity.md`](Quantum_Gravity.md)). **Conjecture:** with
no `r = 0` endpoint, the infaller's horizon is never reached at all, and the interior continues as the
time-dependent interior cosmology that GR already describes inside `rs` and that
[`BLACK-HOLES.md`](BLACK-HOLES.md) §4a reads as a nested domain. This is not proved here; what is
proved is that, up to wherever the geometry holds, the infaller's horizon is strictly ahead of them.

### 1g. The inside is huge, and grows with the hole's age

Inside the horizon the exterior time `t` becomes a direction in space, so the interior is a long
cylinder: a shrinking sphere times a line. The stretch of that line laid down while the hole has
existed for a time `T` has proper length `√(rs/r − 1)·c·T` (`interiorStretch`). At `r = rs/2` the
factor is exactly 1 (`interiorStretch_half`): **the interior is `c × (the hole's age)` long**, and it
gets longer at `c` for as long as the hole exists. The spheres shrink meanwhile, so the growth is
along one axis, not an isotropic expansion.

The volume of the largest interior slice grows at a constant rate, `3√3·π·(GM/c²)²·c` per unit
time (Christodoulou & Rovelli 2015), reached at `r = 3rs/4`; in Lean, `interiorVolumeRate_sq_le` and
`interiorVolumeRate_sq_max` prove that this is the maximum over all `r`. If Sgr A* has existed for
about 10 Gyr, its interior volume in this sense is about 6×10⁴⁶ m³, about 10¹⁶ times the
`(4/3)π rs³` a naive outside view suggests. This is the GR content of the Personal Origin's
*"black holes must be huge inside"*. In GR the growth ends for each infaller at the singularity; with
QLF's bounded density the shrinking of the spheres must stop instead, which leaves an interior that
keeps lengthening (**conjecture**).

### 1f. Seeing later infallers, older than "our" universe (conjecture and test)

**GR:** an observer inside a Schwarzschild hole still receives light from matter that falls in
*after* them. It arrives from above, behind them, until the observer meets the singularity. That
matter aged outside before it fell, so its own clock can show any age, unrelated to the time since
the observer crossed. Nothing forbids an infaller seeing objects whose ages exceed the age of the
interior measured from the horizon crossing.

**Nested reading (conjecture):** if our domain is the interior of a parent hole
([`BLACK-HOLES.md`](BLACK-HOLES.md) §4a), its 13.8 Gyr is the age of *our* clock measured from our
birth surface. Matter falling into the parent after our domain formed would enter through that
surface carrying the age of its parent history, and with QLF's bounded density there is no
singularity to cut the view short, so the reception would continue indefinitely. So the nested
picture permits, and on this reading predicts, **objects that appear older than the universe**. This
is a test it can fail: ΛCDM forbids such objects, and the nested reading allows them.

**Observed so far: none confirmed.** The oldest well-measured star, HD 140283, was dated at
`14.46 ± 0.8` Gyr (Bond et al. 2013), consistent with `13.77 ± 0.06` within errors. Models with
abundances tailored to the star give 12.3 Gyr (Guillaume et al. 2024). So present data neither
support nor exclude the prediction. What is open: where in our sky such matter would appear (the
identification "parent horizon = birth surface" does not fix it), and how many such objects to
expect. Without those the prediction is qualitative, not yet pre-registered.

---

## 2. A spinning (Kerr) hole: being dragged around is not much different

A rotating hole drags the local frames around it. The outer horizon is at `r₊ = M + √(M² − a²)` and
rotates at `Ω_H = a/(r₊² + a²)` (units `G = c = 1`, `a = J/M`). Hamilton & Lisle extend the river
picture to Kerr: the river then carries a twist as well as an inflow.

| Fact | Lean |
|---|---|
| `r₊² + a² = 2M r₊` | `rPlus_sq_add_sq` |
| the dragging rate at the horizon is at most `1/(2M)`, i.e. one turn takes at least `4πGM/c³` | `horizonOmega_le` |
| at fixed spin `χ = a/M` it scales as `1/M` | `horizonOmega_scale` |
| so being dragged around a large hole is slow: `Ω_H → 0` as `M → ∞` | `horizonOmega_tendsto_zero` |
| no spin: `r₊ = 2M`, no dragging | `schwarzschild_limit` |

The one-turn bound is about 4.4 minutes for Sgr A* and about 4.7 days for M87* (6.5×10⁹ solar
masses). The tidal field at the horizon scales as `1/M²` at fixed spin, as in 1d (by dimensional
analysis; not in Lean here).

The physical point is that **a freely falling body is on a geodesic whether or not the frame is
dragged**, so no accelerometer reads the dragging. Being swept around a large Kerr hole is locally the
same as falling into a Schwarzschild one: the swirl, like the inflow, is a property of how distant
observers slice the geometry. So Jim's "not much different" holds at the **outer** horizon.

**Where Kerr genuinely differs.** A spinning hole has a second, inner horizon
`0 < r₋ < r₊` (`kerr_two_horizons`). In GR this inner (Cauchy) horizon is unstable: infalling and
outgoing streams pile up there and the interior mass parameter blows up, "mass inflation" (Poisson &
Israel 1990). That is the hard part of the Kerr problem, and it is inside the hole, not at its outer
edge. **Conjecture (QLF):** mass inflation is an unbounded density growth, which QLF's bounded event
density forbids, so it must saturate at the Planck scale. Nothing here derives the saturated state.

---

## 3. Small holes: they condense into matter and evaporate, so none are left

### 3a. Standard physics

Hawking's lifetime scales as `t = K·M³` (photon-only: `K = 5120πG²/(ħc⁴)`; emitting more particle
species shortens it, Page 1976). In Lean (`lifetime`):

| Fact | Lean |
|---|---|
| lighter holes die sooner | `lifetime_strictMono` |
| a hole has evaporated by age `T` iff it is lighter than `M*` with `K·M*³ = T` | `evaporated_iff` |
| with fraction `f` of the mass left, `f³` of the lifetime is left | `lifetime_fraction` |
| the last half of the mass goes in the last eighth of the lifetime | `last_half_eighth` |

The photon-only formula gives `M* ≈ 2×10¹¹ kg` for an age of 13.8 Gyr; with all emitted species the
threshold is about `5×10¹¹ kg` (5×10¹⁴ g; Carr, Kohri, Sato & Yokoyama 2021). So **every primordial
hole born lighter than about 5×10¹¹ kg is gone**, and each finished in a final burst, since the
`f³` law puts the end of the evaporation into a vanishing share of the lifetime.

Holes heavier than `M*` evaporate too slowly to be gone. The asteroid-mass range (roughly 10¹⁷ to
10²² g) is not excluded observationally as a dark-matter component (Carr et al. 2021). So "none exist
anymore" is established for the light ones and is a QLF claim, not an observation, for the heavier
small ones.

### 3b. The QLF reading: small holes become matter

In QLF a particle *is* a primordial quantum black hole, and the difference between a hole and a
particle is a matter of scale ([`BLACK-HOLES.md`](BLACK-HOLES.md) §1,
[`Hadron_BlackHoles.md`](Hadron_BlackHoles.md)). Two proved pieces carry this:

* `compton_eq_schwarzschild_iff` and `sub_planck_compton_gt_schwarzschild`
  ([`QLF_QuantumBlackHole`](lean/QLF_QuantumBlackHole.lean)): below the Planck mass the Compton radius
  exceeds the Schwarzschild radius, so a sub-Planck "hole" is not a Schwarzschild hole at all; its
  horizon is the Planck-scale blanket of a particle.
* `planck_length_floor` ([`QLF_PlanckScale`](lean/QLF_PlanckScale.lean)): no coherent closure is
  smaller than the Planck length.

**Reading (well supported, not proved):** small holes formed near the Planck temperature condense
possibilistically into matter (every closure that can form does, and the light ones evaporate into
hadrons and leptons), and the ones with exposed chirality keep evaporating while hidden-chirality
ones (the proton) are stable horizons ([`Hadron_BlackHoles.md`](Hadron_BlackHoles.md)). On that
reading the small holes that survive today are not holes we could find in the sky; they are the
matter we are made of. What is open: a census count of how much Planck-epoch mass ends up in which
species, and whether any heavier small holes formed at all.

---

## 3c. How to escape a black hole

The same perspective view answers the escape question, in four parts.

1. **Outside `rs`: accelerate.** Some outward velocity is available exactly where the river is
   slower than light, i.e. exactly where `rs < r` (`escape_possible_iff`,
   `escape_possible_iff_radius`). An escaping rocket also carries its own horizon, and it lies
   *outside* `rs` (`outward_horizon_gt_rs`): the harder you climb, the more of the hole falls behind
   your own horizon. That is the rocket of [`Rocket_To_The_Horizon.md`](Rocket_To_The_Horizon.md),
   which escapes Earth by letting Earth fall behind its horizon.
2. **Inside `rs`: thrust still works.** Locally nothing is different: at every radius, inside
   the horizon included, every velocity below `c` relative to the surrounding space is available
   (`thrust_works`). And every observer, thrusting or not, inside or outside, has their own horizon
   strictly below them (`own_horizon_below`). So wherever you are, you are in ordinary space with
   your horizon ahead of you; there is nowhere else to be. What thrust does not do inside is
   increase the radius `r` (`inside_all_inward`, standard GR): `r` is the label of the static
   outside observers, and inside you are past *their* limit, not yours. The rocket shows the same
   thing from the other side: Earth is behind the ship's horizon
   ([`Rocket_To_The_Horizon.md`](Rocket_To_The_Horizon.md) §4), and everything on Earth, rockets
   included, works as usual. "Inside" is a relation between two perspectives, not a place where
   physics stops.
3. **But the hole does not keep you.** Every hole evaporates in finite time, `t ∝ M³`
   (`lifetime_strictMono`, §3a), and in QLF a horizon is a Markov blanket whose Hawking unwind
   returns the closure's information to the outside ([`BLACK-HOLES.md`](BLACK-HOLES.md) §3, §3a).
   **Reading:** you do not climb out; the hole comes apart around you, and what you were leaves as
   radiation. For a large hole this takes far longer than the age of the universe.
4. **Or the inside becomes a cosmos.** In the nested picture ([`BLACK-HOLES.md`](BLACK-HOLES.md)
   §4a) the interior re-closes as a child domain whose birth surface is the parent's horizon.
   **Speculative reading:** the infaller never reaches their own horizon (§1e) and finds themselves
   in a new expanding interior, which is "escape" only in the sense that the hole was never a trap
   from inside. Nothing inside a hole, or inside ours if we are in one, can cross the parent's horizon
   outward: it lies in the interior's past.

## 4. See it in the constructor

The [Spectral Spacetime Constructor](https://rhovision-org.github.io/quantum-logical-framework/spacetime_constructor.html)
([notes](Spacetime_Constructor.md)) is drawn from one movable observer's frame, which is the
perspective point of §1: what any picture shows is one observer's cut. Its black holes are
Planck-scale, so it shows §3, not the large-hole infall of §1–§2. Everything it shows is a reading
of the closure census, not a cause.

* [▶ A small hole evaporates](https://rhovision-org.github.io/quantum-logical-framework/spacetime_constructor.html#qc=blackhole%20m%202%20%40%200%2C0%2C0):
  it loses mass at a rate `∝ 1/M²` (the `M³` lifetime of §3a), radiates hotter as it shrinks, and
  ends in a burst of hadrons and leptons. It keeps most of its mass for most of its life and then
  goes quickly (`last_half_eighth`).
* [▶ The logical bang](https://rhovision-org.github.io/quantum-logical-framework/spacetime_constructor.html#t=1):
  at the Planck temperature small holes form where Compton = Schwarzschild and cascade into hadrons
  that cool into atoms. This is §3b's "small holes condense into matter". Lower the temperature slider
  and the remaining holes evaporate while no new ones form, so none are left.
* [▶ Matter drifting into a well](https://rhovision-org.github.io/quantum-logical-framework/spacetime_constructor.html#qc=blackhole%20m%204%20%40%200%2C0%2C0%0AH%20%40%204%2C0%2C0):
  an atom drifts down the latency gradient toward the hole, with no force, which is the discrete
  counterpart of the river in §1a.

---

## 4a. The rocket twin

A ship accelerating away from Earth at constant `g` is the flat-space version of the same story: the
accelerated perspective has a horizon, the free one does not, and with QLF's finite redshift limit the
far side fades out in finite time. Worked out in
[`Rocket_To_The_Horizon.md`](Rocket_To_The_Horizon.md) ([`QLF_RelativisticRocket`](lean/QLF_RelativisticRocket.lean)).

## 5. Status

| Claim | Status |
|---|---|
| The static horizon `rs` is where holding still becomes impossible; the infaller's clock marks nothing there | **proved** (standard GR, in Lean) |
| The infaller's own perspective horizon is always strictly ahead, recedes as they fall, and reaches `0` only with them | **proved** (in river coordinates; an instantaneous surface, not the event horizon) |
| GR: the radius `rs` is passed in finite proper time; far observers see the infaller stop | **proved** (standard GR) |
| Large holes have locally invisible horizons (tidal `∝ 1/M²`) | **proved** for Schwarzschild |
| Kerr dragging at the outer horizon is slow for large holes and not felt in free fall | **proved** (`Ω_H ≤ 1/(2M)`, `∝ 1/M`); "not felt" is the geodesic property |
| No singularity, so the infaller's horizon is never reached | **conjecture** (QLF bounded density) |
| Kerr mass inflation saturates at the Planck scale | **conjecture** |
| The interior is `c × (age)` long at `r = rs/2`; its maximal volume grows at `3√3πM²c` per unit time | **proved** (standard GR) |
| In the nested reading, later infallers into a parent hole appear older than our universe | **conjecture**; no confirmed object yet (HD 140283 consistent with 13.8 Gyr) |
| Thrust works at every radius; everyone's own horizon is strictly below them | **proved** (`thrust_works`, `own_horizon_below`) |
| The static radius `r` can increase only outside `rs` | **proved** (standard GR) |
| Primordial holes lighter than about 5×10¹¹ kg are gone | **standard physics**, `M³` law proved |
| Small holes became matter; none of any small size remain | **QLF reading**, supported by `QLF_QuantumBlackHole` and `QLF_PlanckScale`; open for asteroid-mass holes |

## References

* A. J. S. Hamilton & J. P. Lisle, "The river model of black holes", *Am. J. Phys.* **76**, 519
  (2008), [arXiv:gr-qc/0411060](https://arxiv.org/abs/gr-qc/0411060).
* A. J. S. Hamilton, "Illusory horizons, thermodynamics, and holography inside black holes",
  [arXiv:1210.4541](https://arxiv.org/abs/1210.4541).
* E. Poisson & W. Israel, "Internal structure of black holes", *Phys. Rev. D* **41**, 1796 (1990).
* H. E. Bond et al., "HD 140283: A star in the solar neighborhood that formed shortly after the
  Big Bang", *ApJL* **765**, L12 (2013), [arXiv:1302.3180](https://arxiv.org/abs/1302.3180).
* C. Guillaume et al., "The age of the Methuselah star in light of stellar evolution models with
  tailored abundances", *A&A* **692**, L3 (2024), [arXiv:2411.12343](https://arxiv.org/abs/2411.12343).
* M. Christodoulou & C. Rovelli, "How big is a black hole?", *Phys. Rev. D* **91**, 064046 (2015),
  [arXiv:1411.2854](https://arxiv.org/abs/1411.2854).
* D. N. Page, "Particle emission rates from a black hole", *Phys. Rev. D* **13**, 198 (1976).
* B. Carr, K. Kohri, Y. Sato & J. Yokoyama, "Constraints on primordial black holes", *Rep. Prog.
  Phys.* **84**, 116902 (2021), [arXiv:2002.12778](https://arxiv.org/abs/2002.12778).
