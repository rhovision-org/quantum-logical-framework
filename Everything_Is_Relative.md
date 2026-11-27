# Everything is relative

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

*"Motion is only relative — even falling into a black hole."* Jim's father ([`MyStory.md`](MyStory.md)).

QLF maintains that **everything is relative**: every description of the world is a perspective's
description, and no perspective is the world's own. This page states that principle in one place and
lists what is proved about it. The long-form account is [`UniversalRelativity.md`](UniversalRelativity.md);
this page is the summary to cite.

The principle has three parts, and each needs the others:

1. **What a perspective sees is relative.** Times, orders, horizons, what is open or closed, what is
   known: all depend on whose view it is.
2. **What closes is shared.** Every perspective agrees on whether a history closes and on the phase it
   carries. This is what keeps relativity from being arbitrary: the views differ, the closures do not.
3. **Nothing is assumed beyond logic.** Relativity is not posited; each item below is either proved
   from the construction, which is one model of logic (see [`CLAUDE.md`](CLAUDE.md), "Only logic is
   assumed"), or labelled as a reading.

---

## 1. What is relative

| What | Relative to | Proved by |
|---|---|---|
| How an interval splits into time and space | the observer's motion | `split_by_perspective`, `boost_interval` ([`QLF_TimeReversalPerspective`](lean/QLF_TimeReversalPerspective.lean)) |
| The order of spacelike-separated events | the observer's motion | `spacelike_order_by_perspective` (same module) |
| Which way time is read | the selection among 16 readings, all of which are the census | `every_reading_is_the_census`, `sixteen_reversed_readings` (same module; [`Time_Reversed_Universe.md`](Time_Reversed_Universe.md)) |
| Whether a process is open or closed | the observer's capacity (horizon depth) | `horizon_relative`, `closedAtHorizon_mono` ([`QLF_HorizonClosure`](lean/QLF_HorizonClosure.lean)) |
| What a body can know | its own record | `perspective_locality` ([`QLF_PerspectiveLocality`](lean/QLF_PerspectiveLocality.lean)); `single_body_perspectives_share_only_constants` ([`QLF_PerspectiveHolography`](lean/QLF_PerspectiveHolography.lean)) |
| Where the horizon is | the observer's motion: every timelike observer has one strictly below them | `own_horizon_below`, `river_perspectiveHorizon`, `static_exists_iff` ([`QLF_BlackHoleInfall`](lean/QLF_BlackHoleInfall.lean); [`Falling_Into_Black_Holes.md`](Falling_Into_Black_Holes.md)) |
| Who is beyond whose horizon | the pair: redshifts are mutual, and even inertial observers pass beyond each other's redshift limit | `mutual_redshift`, `arrivalTime_hasDerivAt`, `inertial_redshift_horizon` ([`QLF_RelativisticRocket`](lean/QLF_RelativisticRocket.lean); [`Rocket_To_The_Horizon.md`](Rocket_To_The_Horizon.md)) |
| Whether you are "inside" a black hole, or Earth is "in your universe" | the pair of perspectives, not a place | `thrust_works`, `own_horizon_below`, `earth_signal_reaches_iff` (same two modules) |
| Who triggered whom at a primitive event | which side you read it from; the closure is the invariant | reading, `B-OPEN` ([`UniversalRelativity.md`](UniversalRelativity.md) §3a‴) |
| The four forces | the projection the one closure is viewed through | reading ([`UniversalRelativity.md`](UniversalRelativity.md) §4a) |

## 2. What every perspective shares

Relativity is a statement about views of something. These are the things every view agrees on:

| Shared | Proved by |
|---|---|
| Whether a history closes, and its phase | `observers_agree` ([`QLF_MultiObserver`](lean/QLF_MultiObserver.lean)) |
| The value of the interval | `boost_interval` ([`QLF_TimeReversalPerspective`](lean/QLF_TimeReversalPerspective.lean)) |
| The light cone | `boost_null_iff` (same module) |
| The order of timelike- and null-separated events | `timelike_order_invariant`, `null_order_invariant` (same module) |
| No signalling: one side's statistics never depend on the other's choice | `no_signalling_typed` ([`QLF_PerspectiveLocality`](lean/QLF_PerspectiveLocality.lean)) |
| The count of ways a closure happens | the census itself ([`census_inventory.py`](census_inventory.py)) |

In one line: **what a perspective sees is relative; what closes is not.**

## 3. The step census: relative, or a preferred frame?

One substrate step reaches the rest observer's tick, while its image under a boost needs at least
seven steps, so two inertial observers disagree on how many ways an event is reached
(`step_census_frame_dependent`, [`QLF_RelativityScale`](lean/QLF_RelativityScale.lean)). In the large
the census becomes isotropic, but that isotropy is Euclidean, not boost invariance
(`covariance_isotropic`, `boost_not_euclidean`). What that theorem means depends on whose lattice the
steps are taken in, and that is not settled:

* **Hypothesis P (one lattice).** There is one substrate lattice. Its rest frame is preferred, the
  disagreement is asymmetric, and the relativity of motion is a very close approximation with a
  Planck-scale departure ([`Relativity_Principle.md`](Relativity_Principle.md)). This is the reading
  the repository has used so far.
* **Hypothesis R (every perspective counts in its own frame; Jim, 2026-11-27).** Each perspective
  counts ways in its own frame, with the same counting law. Then each sees the *other's* tick as the
  seven-step one, and the disagreement is symmetric and relative to perspective, like the disagreement
  of two observers on simultaneity. Einstein's principle says the *laws* are the same in every inertial
  frame, not that every frame assigns the same count to a given event, so on this reading the theorem
  breaks only the stronger, usual expectation that counts of ways are frame-invariant. It does not
  break the principle itself.

**What decides it** is the open interacting case: when two bodies in relative motion close jointly,
whose frame does the joint closure count in? Under P it is the lattice's, and an anisotropy tied to one
cosmic frame should show up at Planck scale. Under R it must be fixed by the pair, and no single frame
should ever be singled out by experiment. Boost covariance is proved for free propagation in the large
and is open with interactions ([`Relativity_Principle.md`](Relativity_Principle.md) stages 4–5), which
is exactly where the two come apart. Hypothesis R is a well-motivated conjecture, not yet a result.

## 4. Time goes every way

Time is relative in direction, not only in rate. Every one of the sixteen reversed readings of a closure
is itself the census (`every_reading_is_the_census`, `sixteen_reversed_readings`,
[`QLF_TimeReversalPerspective`](lean/QLF_TimeReversalPerspective.lean)), so time goes every way,
backwards included, by perspective. A reversed reading is a selection among histories, not a boost of
the same observer (`no_congruence_reverses_time`). See
[`Time_Reversed_Universe.md`](Time_Reversed_Universe.md).

**No time loops.** Every way is not every loop. Each perspective's record only grows: under the law of
weakening, construction only adds (`weakening_iff_persistence`, `closedAtHorizon_mono`), and from
that alone no history returns to its own past (`no_time_loops_from_logic`,
[`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean)). Running time backwards is reading a
record the other way, never going round in a circle. (A logic without weakening can model a loop,
`loopWorld_has_time_loop`; that is a statement about such a logic, not about any record.) In one line:
**time goes every way, and never in a loop.**
