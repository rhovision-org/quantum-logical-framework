# Conscious Dynamics — effective frequency, promotion, and the finite strange loop

**Status:** pre-registration plus a finite reference implementation. This is a **functional model**,
not a theory of qualia. It is complete at the finite functional scope and is merged on that basis;
D5 and the general dynamic theorem remain open. Tracking issue:
[#278](https://github.com/rhovision-org/quantum-logical-framework/issues/278).

**The one law.** QLF assumes equal and opposite logical action and nothing else
([`Framing.md`](Framing.md) A01). Read computationally,
[`Universe_Quantum_Computer.md`](Universe_Quantum_Computer.md) states the thesis: **the universe is
the quantum computer that runs this one law**, and every other principle is derived from it, cited
from a known fact, or explicitly labelled a bridge or reading. This document is a model inside that
law, not a second premise. It asks how a bounded listener reads the closure race; it does not claim
that the model is a theory of consciousness.

**The rule at the top.** *No shared vocabulary is evidence of a shared mechanism.* A candidate
closure becomes conscious content only if the listener-relative delay, eligibility filter, promotion
rule, and update rule are all declared. The `QLF_Consciousness` frequency layer is reused; it is not
silently upgraded.

---

## 0. The core equations

```
T_i^(B)   = characteristic listening/retrigger period
f_i^(B)   = 1 / T_i^(B)                  (recurrence frequency)
d_i^(B)   = remaining distance to trigger
i_next    = argmin_{i ∈ S_t} d_i^(B_t)   (first eligible trigger)
d_i = 0   ⇒  Close(i),  tau_event = 0    (atomic expression)
B_{t+1}   = U(B_t, i_next)
```

- `T_i^(B)` — the listener-relative recurrence period;
- `f_i^(B)` — the recurrence frequency, used for recurring dominance;
- `d_i^(B)` — the remaining distance to the next trigger, used for event priority;
- `S_t` — sufficiently integrated, self-relevant bound closures;
- `i_next` — the next conscious expression;
- `U` — the listener/self-model update.

The key distinction:

```
high frequency governs recurring dominance;
first trigger governs the next conscious expression.
```

A faster recurrent mode need not be the next one to fire if a slower mode is already nearer
closure. The event itself is atomic (`tau_event = 0`); the listening/retrieval history is what takes
time. This is a finite strange loop across levels of description, not backward causation in event
time.

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

1. the recurrence period and trigger distance are **separated**: `T_i^(B)` vs `d_i^(B)`;
2. event priority is `argmin d_i`, not `argmax f_i`; the existing highest-frequency layer describes
   **recurring dominance**, not which event fires next;
3. the promotion rule is filtered by **self-relevance and integration**, not raw global frequency;
4. the winner **updates the listener**, so the next race is different;
5. the past is fixed but its **listener-relative compression changes**, which is the formal version
   of “that was what I was thinking all along.”

### 1a. The magical powers and the gift of forgetfulness

Jim's capacities are part of the model's declared scope. "Magical" is a label for the functional
result, not a claim of magic, and each capacity is kept at the grade actually established. The
fourth is the one that makes the other three finite.

| Capacity | What is formalized here | Grade | What is not claimed |
|---|---|---|---|
| **A database of possible worlds from your relative perspective** | The finite candidate/closure set together with the listener context `B` and horizon `R`; the listener quotient of [`Listener_Equivalence_QLF.md`](Listener_Equivalence_QLF.md) supplies `Ω_R(h\|B)` and `W_micro` vs `W_B`. | **finite functional model** | Not an unrestricted database of all logically possible worlds; a different `B` or `R` is a different database. |
| **Active-inference synthesis intelligence** | The promotion/filter/update architecture `B_{t+1}=U(B_t,i_next)`, plus the cited per-closure free-energy theorem `zfa_closure_minimizes_free_energy` ([`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)). | **finite model + cited bridge** | The identity `U = active inference` is **not** proved. The update here is an explicit toy rule; deriving it from variational free energy remains open. |
| **Strange loops for reflection and self-awareness** | The finite self-model square and the target `M_t ~ S_t/~_B_t`, with a good commuting square and a bad non-commuting one. The self-model models its own boundary rather than copying the system. | **toy check; general theorem open** | No self-observation or quote/drop reflection theorem; the general strange-loop and self-knowledge target remains `NOT_STARTED`. |
| **The gift of forgetfulness (ultimate)** | Closure is many-to-one (`time_reverse_involutive_but_closure_degenerate`); after a balanced history at most one sign reaches its future (`closure_renewal`); persistence is copying, not permanence. The listener quotient discards exactly the distinctions no continuation can recover, while many-to-one closure carries the `−log 2` free-energy price (`zfa_closure_minimizes_free_energy`). | **structural corollary + cited results** | Not a claim that all forgetting is beneficial or free, not erasure by an external observer, and not a theory of memory, qualia or therapy. |

The first capacity gives the mind a **world**, the second a **synthesis over it**, and the third a
**self that reflects on it**. The fourth is what keeps all three finite. A database that retained
every possible world and every microhistory would not be a usable perspective: it would have no
room for a next closure. Forgetting drops the path and keeps what can still matter to a
continuation. The listener quotient is the disciplined form of that gift—lossless for the
continuations it declares, lossy about everything else. It is not a defect in the model; it is the
condition of a bounded self-model and a next expression.

---

## 2. Gates

| gate | requirement | status |
|---|---|---|
| **D0** | candidates, intrinsic delay, listener context, effective delay, eligibility, promotion, update frozen | **done** here |
| **D1** | `T>0`, `f=1/T`; listening can change `T` and `d`; no free-quark clock | **finite check**; general theorem open |
| **D2** | next expression is the minimum-`d` eligible closure, not the highest-frequency event | **finite check** |
| **D3** | a bounded `run_loop(n)` produces `n` expressions with strictly increasing external step index | **finite check only**; this is not a transition-system no-event-loop invariant, and `no_time_loops_from_logic` is cited separately |
| **D4** | history fixed, listener compression changes; no past rewrite | **finite check** |
| **D5** | `M_t ~ S_t/~_B_t` remains the correctness target | **cited** from [`Listener_Equivalence_QLF.md`](Listener_Equivalence_QLF.md); general theorem open |
| **D6** | attention changes the race, not the contestants; quieting raises internal distances | **finite check** |
| **D7** | no qualia theorem; no empirical claim | **gate** |
| **D8** | feeling changes memory accessibility through a generic compatibility relation; same store; recall is atomic; no target identity in the feeling | **finite check** |
| **D9** | frequency and event priority are distinct; a faster recurrent mode need not be the next trigger | **finite check** |
| **D10** | forgetting is constrained: discard only distinctions that no declared continuation can recover; retain closure-relevant record; many-to-one closure and its `−log 2` price are cited | **scope gate + cited results**; no new theorem |

This is a finite functional model, complete at that scope. D1–D4 and D6–D10 are finite checks or
scope gates; D5 and the general dynamic theorem remain open obligations, not conditions on the
finite model. D3 checks a bounded trace with an external counter; it does **not** prove that the
transition system excludes a zero-progress event loop. D10 distinguishes disciplined forgetting
from arbitrary loss: the listener quotient is lossless for its declared continuations, while
many-to-one closure physically forgets the path and carries the stated free-energy price.

---

## 3. Electron and quark: the qualification

An electron is already a persistent closed mode. Listening can synchronize or bind it into a faster
effective closure, so `T_e^(B) < T_e` is meaningful.

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

The globally fastest physical process is therefore not automatically conscious. The next expression
is the **nearest eligible trigger** (minimum `d`), not necessarily the highest-frequency recurrence.
A faster recurrent mode can lose to a slower mode that is already nearer closure.

---

## 5. Attention and quieting

Attention is a change of listener context:

```
B → B'  ⇒  T_i^(B) → T_i^(B'),  d_i^(B) → d_i^(B').
```

It does not create a new contestant. It changes which existing candidate is moved nearer or made to
recur faster. In compact form: **attention changes the race, not the contestants.**

Quieting is the inverse move. It raises the effective distance of the currently dominant internal
closures, so a normally subdominant external/joint closure can become the nearest remaining eligible
trigger. This is the finite-model reading of `quieting_shifts_to_external`.

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
[`Listener_Equivalence_QLF.md`](Listener_Equivalence_QLF.md); the general
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

- a candidate set with intrinsic period, base trigger distance, integration, and self-relevance;
- a listener with per-candidate period and distance bonuses;
- `effective_period`, `frequency`, `remaining_distance`, `eligible`, `next_trigger`,
  `highest_frequency`;
- attention (distance/period change) and quieting (internal distance penalty);
- a dynamic loop with winner refractory distance and successor acceleration;
- a fixed-history / changing-compression toy;
- the D9 separation check.

The default race promotes the nearest self-relevant perception (`d=2`); a faster but ineligible
micro-event (`d=0`) is excluded. The D9 check has `fast_recurrent` at `f=1.0, d=5` and `slow_near` at
`f=0.1, d=1`: the next trigger is `slow_near`, while the fastest recurrence is `fast_recurrent`.
Attention brings thought to `d=1` and it wins; quieting lets the external joint closure win. The
dynamic loop produces a finite trigger sequence, and each trigger is atomic.

---

## 9. Non-goals

- No claim that the model explains qualia.
- No claim that the globally fastest physical process is conscious.
- No free-quark clock.
- No empirical prediction without a measured delay/eligibility protocol.
- No backward causation; every realized step still advances the event record
  (`no_time_loops_from_logic`).
- No general bisimulation theorem; `M ~ S/~_B` is the target, not a result.
- No claim that frequency is event priority; D9 is the separation.
- No claim that the D9 update rule is derived active inference; it is a finite toy.
- No claim that the D8 feature-overlap metric is the final affective measure; it is a
  kill-condition-satisfying toy, not a validated memory model.
- No claim that forgetting is always beneficial or free; the many-to-one closure price is cited,
  and selection of what to forget is not derived.
- No claim that an observer can erase the substrate, and no therapy or clinical claim.

---

## 10. Reproduce

```bash
python3 conscious_dynamics.py --self-test
python3 conscious_dynamics.py --run
python3 -m unittest tests.test_conscious_dynamics -v
```

The run writes `data/conscious_dynamics_census.json`. The definitions are frozen at the commit that
adds this file; a different eligibility filter or update rule is a new pre-registration.
