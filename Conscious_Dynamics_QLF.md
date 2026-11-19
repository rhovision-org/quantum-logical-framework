# Conscious Dynamics — effective frequency, promotion, and the finite strange loop

**Status:** pre-registration plus a finite reference implementation. This is a **functional model**,
not a theory of qualia. Tracking issue: [#278](https://github.com/rhovision-org/quantum-logical-framework/issues/278).

**The rule at the top.** *No shared vocabulary is evidence of a shared mechanism.* A candidate
closure becomes conscious content only if the listener-relative delay, eligibility filter, promotion
rule, and update rule are all declared. The `QLF_Consciousness` frequency layer is reused; it is not
silently upgraded.

---

## 0. The core equations

```
f_i^(B)   = 1 / R_i^(B)
C_t*      = argmax_{i ∈ S_t} f_i^(B_t)
B_{t+1}   = U(B_t, C_t*)
```

- `R_i^(B)` — completion delay of candidate closure `i` relative to blanket/listener `B`;
- `S_t` — sufficiently integrated, self-relevant bound closures;
- `C_t*` — the promoted closure (provisional conscious content);
- `U` — the listener/self-model update.

The three lines are: **listening determines effective frequency; the highest eligible frequency
determines content; content updates the listener.** That is a finite strange loop across levels of
description, not backward causation in event time.

---

## 1. What is new relative to the existing Lean layer

The repository already proves:

- `freq R = 1/R` and `freq_lt_of_lt` — a shorter period is a higher frequency
  ([`QLF_Consciousness`](lean/QLF_Consciousness.lean));
- `higher_freq_dominates`, `freq_bind_ge_left`, `freq_bind_ge_right` — binding raises frequency
  ([`QLF_HarmonicClosure`](lean/QLF_HarmonicClosure.lean));
- `consciousPeriod`, `conscious_internal`, `conscious_external`,
  `quieting_shifts_to_external` — the highest-frequency available closure and the meditative shift
  ([`Consciousness.md`](Consciousness.md) §3–§4).

What is **new** here:

1. the delay is **listener-relative**: `R_i^(B)`, not only intrinsic;
2. the promotion rule is filtered by **self-relevance and integration**, not raw global frequency;
3. the winner **updates the listener**, so the next race is different;
4. the past is fixed but its **listener-relative compression changes**, which is the formal version
   of “that was what I was thinking all along.”

---

## 2. Gates

| gate | requirement | status |
|---|---|---|
| **D0** | candidates, intrinsic delay, listener context, effective delay, eligibility, promotion, update frozen | **done** here |
| **D1** | `f=1/R>0`; listening can shorten or lengthen `R`; no free-quark clock | **finite check**; general theorem open |
| **D2** | winner is the highest-frequency eligible self-relevant integrated closure, not the globally fastest event | **finite check** |
| **D3** | `B_t → listening → C_t* → B_{t+1}` is finite and does not loop event time | **finite check**; `no_time_loops_from_logic` cited |
| **D4** | history fixed, listener compression changes; no past rewrite | **finite check** |
| **D5** | `M_t ~ S_t/~_B_t` remains the correctness target | **cited** from [PR #275](https://github.com/rhovision-org/quantum-logical-framework/pull/275); general theorem open |
| **D6** | attention changes the race, not the contestants; quieting raises internal delays | **finite check** |
| **D7** | no qualia theorem; no empirical claim | **gate** |
| **D8** | feeling changes memory accessibility through a generic compatibility relation; same store; recall is atomic; no target identity in the feeling | **finite check** |

The PR is draft. D1–D4, D6, and D8 are finite checks; D5 and the general dynamic theorem remain open.

---

## 3. Electron and quark: the qualification

An electron is already a persistent closed mode. Listening can synchronize or bind it into a faster
effective closure, so `R_e^(B) < R_e` is meaningful.

A quark is not an independently closed object in QLF (`quark_not_closed`,
`charged_not_closed`). Its meaningful period belongs to the larger hadronic closure. The correct
statement is therefore:

```
the open quark strand is heard only through a slower/deeper composite closure.
```

There is no free-quark clock that subsequently slows. This is a **status qualification**, not a new
confinement theorem.

---

## 4. Why promotion is not “the fastest process wins”

A fast microscopic event can be ineligible. The promotion set `S_t` filters for:

- **integration** — the closure binds enough sub-closures to be a candidate at the self-model level;
- **self-relevance** — it is about the listener's own boundary, body, or goals;
- **bound closure** — it is not an open strand that only exists as part of a deeper composite.

The globally fastest physical process is therefore not automatically conscious. The winner is the
highest-frequency member of the eligible integrated set.

---

## 5. Attention and quieting

Attention is a change of listener context:

```
B → B'  ⇒  R_i^(B) → R_i^(B').
```

It does not create a new contestant. It changes which existing candidate is accelerated enough to
win. In compact form: **attention changes the race, not the contestants.**

Quieting is the inverse move. It raises the effective delay of the currently dominant internal
closures, so a normally subdominant external/joint closure can become the maximum among the remaining
eligible modes. This is the finite-model reading of `quieting_shifts_to_external`.

---

## 6. Retrospective compression

Let the realized history be fixed:

```
h_1, h_2, ..., h_N.
```

Before promotion, the self-model may not have a single organizing closure. After `C*` wins, it
compresses the precursor microhistories by their closure-relevant equivalence:

```
h_j ↦ [h_j]_{C*}.
```

The history is unchanged; what changes is

```
C_{B_t}(history).
```

That is the precise sense in which “conscious closure makes its own precursor history intelligible”
without changing the past. The compression is the listener quotient of
[PR #275](https://github.com/rhovision-org/quantum-logical-framework/pull/275); the general
correctness condition remains `M ~ S/~_B`.

---

## 7. Affective recollection (D8)

A feeling is a listener context `F`. For a fixed memory store `M_i`, define a generic
listener-relative distance:

```
d_i(B, F) = max(0, base_distance_i - gain(M_i, F) * t)
gain(M_i, F) = 1 + 2 * |features(M_i) ∩ features(F)|
```

`t` is the listening history. When `d_k(B,F)=0`, the memory closes:

```
RECALL(M_k),  tau_recall = 0.
```

Retrieval takes time; recollection does not. The finite model uses one fixed store and four feeling
contexts:

| feeling context | generic features | recalled memory | trigger step |
|---|---|---|---:|
| `neutral` | `{}` | `M_A` | 4 |
| `F_blue_room` | `{blue, room}` | `M_A` | 1 |
| `F_song_summer` | `{song, summer}` | `M_B` | 1 |
| `F_loss_winter` | `{loss, winter}` | `M_C` | 2 |

The store `{M_A, M_B, M_C}` is identical in every row. What changes is accessibility, not history.

**Kill condition.** The feeling must not contain the target memory's identity. `Feeling` carries only
generic features; the recall target is computed from feature overlap. If a model only recalls the
right memory when the feeling is told which memory to retrieve, D8 fails.

This is the memory analogue of QKB:

```
ask(q_F) → listen → solve → M_k.
```

A **feeling** is an active self-relevant listening trajectory `F_t`; a **mood** is a slower change in
the listener `B_t` itself. The architecture predicts that mood biases which memories are accessible,
not that it rewrites them.

---

## 8. Finite model

`conscious_dynamics.py` implements:

- a candidate set with intrinsic delays, integration, and self-relevance;
- a listener with per-candidate delay bonuses;
- `effective_delay`, `frequency`, `eligible`, `promote`;
- attention (bonus to one candidate) and quieting (penalty to internal candidates);
- a dynamic loop with winner refractory and successor acceleration;
- a fixed-history / changing-compression toy.

The default race promotes the fast self-relevant perception; a fast but ineligible micro-event is
excluded. Attention promotes a slower thought; quieting lets the external joint closure win. The
dynamic loop produces a finite promotion sequence and does not advance event time backward.

---

## 9. Non-goals

- No claim that the model explains qualia.
- No claim that the globally fastest physical process is conscious.
- No free-quark clock.
- No empirical prediction without a measured delay/eligibility protocol.
- No backward causation; every realized step still advances the event record
  (`no_time_loops_from_logic`).
- No general bisimulation theorem; `M ~ S/~_B` is the target, not a result.
- No claim that the D8 feature-overlap metric is the final affective measure; it is a
  kill-condition-satisfying toy, not a validated memory model.

---

## 10. Reproduce

```bash
python3 conscious_dynamics.py --self-test
python3 conscious_dynamics.py --run
python3 -m unittest tests.test_conscious_dynamics -v
```

The run writes `data/conscious_dynamics_census.json`. The definitions are frozen at the commit that
adds this file; a different eligibility filter or update rule is a new pre-registration.
