# Accelerating away from Earth at 1 g: the rocket's horizon

Part of the [Quantum Logical Framework (QLF)](README.md). Lean companion:
[`lean/QLF_RelativisticRocket.lean`](lean/QLF_RelativisticRocket.lean) (no axioms). Twin problem:
[`Falling_Into_Black_Holes.md`](Falling_Into_Black_Holes.md).

A ship leaves Earth and keeps a constant proper acceleration of `1 g` forever. How long, on the
ship's clock, until its proper velocity reaches light speed relative to Earth? How long to reach the
stars and galaxies? When does it leave the cosmic horizon? The answers are flat-space special
relativity plus one QLF ingredient: **a finite redshift limit**. Expansion of the universe is left
out on purpose. The question is about horizons of perspective, and expansion would add a second,
unrelated horizon.

At `1 g` the natural scales are `c/g = 0.9687` years and `c²/g = 0.9687` light-years.

---

## 1. The worldline

With proper time `τ`, Earth time and distance are `t = (c/g) sinh(gτ/c)` and
`x = (c²/g)(cosh(gτ/c) − 1)` (`earthTime`, `earthDist`). Differentiating gives `dt/dτ = cosh = γ`
and the **proper velocity** `dx/dτ = c·sinh(gτ/c)` (`earthTime_hasDerivAt`, `earthDist_hasDerivAt`,
`worldline_unit`). Proper velocity is distance on Earth's ruler per second of ship time, and it grows
without bound. The ordinary speed `dx/dt = c·tanh` never reaches `c`.

## 2. Proper velocity reaches light speed

`dx/dτ = c` exactly when `gτ/c = arsinh 1 = ln(1 + √2)` (`properVelocity_eq_one_iff`,
`arsinh_one`):

| At that moment | Value at 1 g | Lean |
|---|---|---|
| ship time | `0.854` yr (about 10.2 months) | `properVelocity_eq_one_iff` |
| Earth time | `c/g = 0.969` yr | `earthTime_at_light` |
| speed relative to Earth | `c/√2 = 0.707c` | `coordSpeed_at_light` |
| distance from Earth | `0.401` ly | (`(√2 − 1)c²/g`) |

So after ten months you cover a light-year of Earth's ruler per year of your own time.

## 3. Reaching the stars and galaxies

Distance `D` is reached at ship time `τ = (c/g)·arcosh(1 + gD/c²)` (`shipTime_to_reach`,
`earthDist_shipTime_to_reach`), which grows only as `ln D` (`shipTime_to_reach_le`). Flying past
without slowing:

| Destination | Distance | Ship time at 1 g |
|---|---:|---:|
| Proxima Centauri | 4.25 ly | 2.3 yr |
| Galactic centre | 26,000 ly | 10.6 yr |
| Andromeda | 2.5 million ly | 15.0 yr |
| Hubble distance `c/H₀` (`H₀ = 67.7` km/s/Mpc) | 14.4 billion ly | 23.4 yr |

(To stop at the destination, flip halfway and decelerate: the time is twice the time to reach
`D/2`.)

## 4. The ship's horizon: Earth falls behind it

A light signal sent from Earth at Earth time `tₑ ≥ 0` ever reaches the ship **iff `tₑ < c/g`**
(`earth_signal_reaches_iff`). At `1 g` everything Earth does after its first 0.969 years never
reaches the ship. The ship has a horizon a distance `c²/g ≈ 0.97` ly behind it, and Earth crosses it.
Earth's last signal that will ever arrive is the one it
sends at the Earth time when the ship's proper velocity reaches `c` (`earthTime_at_light`; both are
exactly `c/g`).

This is the flat-space version of the black-hole case in
[`Falling_Into_Black_Holes.md`](Falling_Into_Black_Holes.md):

| | Black hole | Rocket |
|---|---|---|
| the accelerated perspective | the observer who **holds still** outside the hole | the ship accelerating away from Earth |
| the free perspective | the infaller | Earth |
| what the accelerated one sees | the infaller slows, reddens and freezes at `rs` | Earth slows, reddens and freezes behind the ship |
| what the free one experiences | nothing happens at `rs` | nothing happens on Earth |

By the equivalence principle these are the same thing.

### 4a. Every perspective has a horizon

The free perspective has one too. The infaller's own horizon is always just below them
(`own_horizon_below` in [`QLF_BlackHoleInfall`](lean/QLF_BlackHoleInfall.lean)). Earth sees the
ship's signals arrive redshifted by the same factor `e^{−gτ/c}` that the ship sees on Earth's
(`arrivalTime_hasDerivAt`, `mutual_redshift`). So, with the redshift limit of §5, Earth loses the
ship at exactly the ship time at which the ship loses Earth. Even two inertial observers see each
other redshifted by `e^{−η}` at relative rapidity `η`, and each is past the other's horizon once
`η ≥ ln N` (`inertial_redshift_horizon`). **Horizons are relations between perspectives, not
properties of one observer.** What acceleration adds in special relativity is a sharp causal cutoff
(§4's `c/g`); the redshift horizon belongs to every pair.

## 5. The redshift limit: leaving the cosmic horizon

The signal the ship receives at proper time `τ` left Earth at `tₑ(τ) = (c/g)(1 − e^{−gτ/c})`
(`emitTime`, `emitTime_lt`), and `dtₑ/dτ = e^{−gτ/c}` (`emitTime_hasDerivAt`). So **every frequency
from Earth arrives multiplied by `e^{−gτ/c}`**. In special relativity this goes to zero only as
`τ → ∞`: Earth never quite disappears, it fades forever.

But nothing can be seen below the background. A signal redshifted down into the background radiation
is indistinguishable from it, so the usable frequency range has a floor (the background) as well as
a ceiling (the Planck frequency: a finite-information universe realizes only a finite range of
frequencies, [`QLF_Realizability`](lean/QLF_Realizability.lean), with the Planck scale at the top,
[`QLF_PlanckScale`](lean/QLF_PlanckScale.lean) `planck_length_floor`). Call the ratio of ceiling to
floor `N`. Then even the most energetic signal Earth could send drops into the background at ship
time

`τ = (c/g) ln N`, exactly, and not before (`redshift_limit_iff`).

That is finite. With the cosmic microwave background as the floor, `N = E_P/(k T_CMB) ≈ 5.2×10³¹`
and `ln N ≈ 73`:

**At 1 g the ship leaves Earth's horizon after about 71 years of ship time.** After that, even a
Planck-energy signal from Earth arrives below the background, so nothing Earth sends can be seen by
the ship. (Measuring the floor at the CMB peak instead, `2.82 kT`, changes this by one year. Taking
the far lower floor of the Hubble rate, `N = 1/(H₀ t_P)`, `ln N ≈ 140`, would give 136 years: an
upper bound for a background-free universe.)

| Milestone | Ship time at 1 g |
|---|---:|
| proper velocity reaches `c`; Earth's last arriving signal is sent | 0.85 yr |
| passes the Hubble distance | 23 yr |
| Earth's brightest possible signal sinks into the background (`ln N ≈ 73`) | 71 yr |

The same limit applies to the black hole. Far observers see the infaller's signals redden as
`e^{−κt}`, with `κ = c/(2 rs)` the surface gravity (the standard late-time law). With the limit, the
infaller sinks into the background for the far observers after `t = (2 rs/c) ln N`: about 1.7 hours
for Sgr A* and 14 ms for a 10-solar-mass hole, not "never".

**Is the ship leaving our black hole?** In the nested picture of [`BLACK-HOLES.md`](BLACK-HOLES.md)
§4a, no. There our universe is the interior of a parent hole, and the parent's horizon is our
*birth surface*: inside a hole the inward radial direction is the future, so the parent horizon lies
in our past, like the Big Bang, not at a place in space a rocket can fly to. Nothing inside can cross
it outward, in GR or in QLF's causal-sealing reading. What the ship crosses is different: its own
horizon, relative to Earth. From the ship's perspective it is **Earth** that falls behind a horizon,
exactly as the infaller falls behind the static observers' horizon. The ship carries its own horizon
along, and the redshift limit is a fact about the ship–Earth pair, not about the parent. Like the
infaller of [`Falling_Into_Black_Holes.md`](Falling_Into_Black_Holes.md), the ship itself never
meets a horizon.

**Status and scope.** §1–§4 and the formula `τ = (c/g) ln N` are proved. The choice of `N` is a
premise: the ceiling is QLF's Planck scale and the floor is the observed background, and a different
floor changes `ln N` and so the 71 years proportionally. The background floor is ordinary physics
(signal below noise); the ceiling is the QLF ingredient. That
crossing the redshift limit is physically "leaving the universe" of Earth is a QLF **reading**: in
SR the signals still arrive, ever redder; in QLF they stop being realizable. The `e^{−κt}` black-hole
law is standard GR and is not proved in Lean here. Note also that the substrate's step census has a
preferred frame ([`Relativity_Principle.md`](Relativity_Principle.md)); a ship boosted far enough
relative to the cosmic rest frame would meet oncoming background radiation at Planck energies, which
is where any lattice departure from SR would show. That is a separate, open question.
