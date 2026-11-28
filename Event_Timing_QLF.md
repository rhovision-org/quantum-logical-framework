# Event Timing — listening delay, atomic closure, and frequency/priority separation

**Status:** pre-registration plus a finite reference implementation. Tracking issue:
[#280](https://github.com/rhovision-org/quantum-logical-framework/issues/280).

**The one rule.** *Listening takes time; closure does not.*

```
open possibility --tau_listen > 0--> trigger --ZFA, tau_event = 0--> new state
```

This is the shared timing semantics for the uncertainty, affect, listener, cosmic, and conscious
layers. It does not add a force or a new dynamics.

---

## 1. Definitions

- `T_i^(B)` — characteristic listening/retrigger period of candidate `i` under listener `B`;
- `f_i^(B) = 1 / T_i^(B)` — recurrence frequency;
- `d_i^(B)` — remaining distance to the next trigger;
- `S_t` — eligible, self-relevant, integrated closures;
- `i_next = argmin_{i ∈ S_t} d_i^(B)` — event priority;
- `d_i = 0` — `Close(i)` with `tau_event = 0` (atomic expression).

The correction is:

```
frequency governs recurring dominance;
trigger distance governs the next event.
```

A faster recurrent mode need not be the next one to fire if a slower mode is already nearer closure.

---

## 2. Relation to existing results

- [`QLF_Consciousness`](lean/QLF_Consciousness.lean) proves `freq R = 1/R`, `freq_lt_of_lt`, and
  `consciousPeriod`. Those are **recurring-dominance** statements; they do not by themselves pick the
  next event.
- [`QLF_HarmonicClosure`](lean/QLF_HarmonicClosure.lean) proves `higher_freq_dominates` and
  `freq_bind_ge_left/right` — again a recurrence/binding result, and the binding half holds by definition (`bind := min`, [Morphogenesis.md](Morphogenesis.md) §2).
- `QLF_LocalClock` supplies the local-clock period `R`.
- [`Manifestation.md`](Manifestation.md) supplies `distance_eq_delay`; this document treats the
  remaining distance as trigger proximity, not event duration.
- `no_time_loops_from_logic` keeps realized event histories acyclic even when the listener/model
  relation is a loop.

[`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean) derives ET1 from `zeno_prune` itself, with
`tau_listen` the first-passage time of a gauge-free balanced history: each pass lowers the remaining
latency by exactly one (`listening_countdown`), the state is open at every earlier pass
(`listening_open_before`), it is one pass from closure at `tau_listen − 1` (`listening_trigger`), and
at `tau_listen` it is the empty history, which has latency `0` and which every later pass leaves
unchanged (`closure_event_atomic`). The theorem counts passes. Reading the fixed closed state as
`tau_event = 0` is this document's interpretation. ET2 and ET3 are still finite checks.

No existing theorem is overturned. The new layer separates two quantities that the static
highest-frequency reading did not distinguish.

---

## 3. Gates

| gate | requirement | status |
|---|---|---|
| **ET0** | `T`, `f`, `d`, eligibility, priority, atomic closure frozen | **done** here |
| **ET1** | `tau_listen > 0`; `tau_event = 0`; no duration assigned to closure | **proved in Lean** for the pruning clock ([`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean) §5); finite check below |
| **ET2** | frequency and event priority are distinct; a faster recurrent mode need not be next | **finite check** |
| **ET3** | event steps increase; no backward causation | **finite check + cited** |
| **ET4** | dependent PRs use the same semantics | **cited**: #271, #272, #275, #277, #279 |

This PR is a foundation, not a domain claim. ET2 is the key check.

---

## 4. Finite model

`event_timing.py` implements:

- candidates with `period`, `distance`, and `eligible`;
- `frequency = 1/period`;
- `next_trigger` = minimum `distance` over eligible candidates;
- `highest_frequency` = maximum `frequency` (the contrast);
- `listening_trace` — each listening step reduces distance by one; at zero, emit `CLOSE` with
  `tau_event = 0`.

The separation case:

| candidate | `T` | `f` | `d` | next? |
|---|---:|---:|---:|---|
| `fast_recurrent` | 1 | 1.0 | 5 | no |
| `slow_near` | 10 | 0.1 | 1 | **yes** |
| `percept` | 2 | 0.5 | 2 | no |

`next_trigger` is `slow_near`; `highest_frequency` is `fast_recurrent`. They differ by construction.

A second trace shows the timing split:

```
listening step 1: d = 2
listening step 2: d = 1
listening step 3: d = 0 -> CLOSE, tau_event = 0
```

`tau_listen = 3`, `tau_event = 0`.

---

## 5. What this does not claim

- No new force or new axiom.
- No duration for a ZFA closure.
- No claim that frequency is event priority; ET2 is the opposite.
- No empirical or qualia claim.
- No backward causation; realized event steps still increase.

---

## 6. Reproduce

```bash
python3 event_timing.py --self-test
python3 event_timing.py --run
python3 -m unittest tests.test_event_timing -v
```

The run writes `data/event_timing_census.json`.
