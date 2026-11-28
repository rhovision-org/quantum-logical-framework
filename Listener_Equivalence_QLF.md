# Listener Equivalence — bisimulation, QKB compression, and finite strange loops

**Status:** pre-registration plus a finite reference implementation. This is a **finite
listener-compression model**, not a general theorem. It is complete at that scope and is proposed
for merge on that basis; the N-body quotient and general self-model square remain open. QKB storage
is unchanged. Tracking issue: [#274](https://github.com/rhovision-org/quantum-logical-framework/issues/274).

**Framing.** QLF has one conjecture, equal and opposite logical action
([`Framing.md`](Framing.md) A01), and tests models inside it. This document is one such model: a
listener is a quotient of histories under a fixed observation and continuation system. It is not a
second premise and does not claim that nature uses this quotient. The computational reading is
[`Universe_Quantum_Computer.md`](Universe_Quantum_Computer.md): the universe computes by closure,
and the listener is one bounded way of reading that computation.

**The rule at the top.** *No shared vocabulary is evidence of a shared mechanism.* A listener
quotient is admissible only when its observation function and continuation system are fixed and the
quotient is shown to preserve every closure-relevant continuation.

---

## 0. The shift

> **Knowledge is not the microscopic history. Knowledge is the compression of history that
> preserves everything a listener at a given scale can still distinguish.**

This turns three existing threads into one architecture:

```
raw histories → listener quotient → QKB concept
```

with bisimulation as the correctness condition for the compression, and a finite strange loop as the
update architecture.

---

## 1. Frozen definitions

Fix a finite deterministic transition system with observations:

- `S` — finite states (histories, QKB records, model states);
- `step : S × A → S` — one-token continuation, total on the finite alphabet `A`;
- `obs_B : S → O` — what listener/blanket `B` observes at a state.

Define **listener equivalence**:

```
s ~_B t  ⇔  obs_B(s) = obs_B(t)
            and for every token a, step(s,a) ~_B step(t,a).
```

This is the greatest bisimulation of the observed transition system (Park/Milner), computed by
partition refinement. It is an equivalence relation and a right congruence: equivalent states remain
equivalent after any continuation.

For a start state `h`, horizon `R`, and first-completion set `Ω_R(h)`:

```
W_micro = |Ω_R(h)|
W_B     = |{ [c]_B : c ∈ Ω_R(h) }|
```

`W_micro` is microscopic multiplicity. `W_B` is the number of alternatives the listener can
distinguish. The weights are separate:

```
P([c]_B) = Σ_{c' ∈ [c]_B} μ(c')
```

so **multiplicity determines weight; bisimulation determines distinction**. `W_B` is not a physical
entropy; it becomes one only after a measure and a physical reading are supplied
([`MostWays_First.md`](MostWays_First.md)).

**The uniform default is explicit.** `listener_uncertainty()` uses `μ(c) = 1` only when no measure
is supplied, reports `measure: "uniform"`, and accepts `path_weights` for the general case. The
finite counts below therefore do not silently treat path multiplicity as the listener's
uncertainty. A non-uniform test is part of the regression suite.

---

## 2. Gates

| gate | requirement | status |
|---|---|---|
| **L0** | `S`, `A`, `step`, `obs_B`, `Ω_R`, and the quotient are frozen before applications | **done** in this document |
| **L1** | `~_B` is an equivalence relation and a right congruence | **finite exact check** in `listener_equivalence.py`; general Lean layer open |
| **L2** | the quotient is the coarsest lossless listener compression | **finite brute-force check**; the two-body theorem is already `obsEquiv_iff_exists_bisim` in [`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean); N-body generalisation open |
| **L3** | uncertainty factors into microscopic multiplicity and listener classes, with `W_B ≤ W_micro` | **finite exact check**; the uniform default is explicit and `μ(c)` is parameterized; general theorem open |
| **L4** | QKB concepts can be read over quotient classes without changing the closure gate | **schema proposal + prototype**; QKB storage unchanged |
| **L5** | a finite self-model can be faithful by bisimulating the quotient, not copying `S` | **toy check**; general theorem open |
| **L6** | each checked transition has nondecreasing level; same-level transitions are retained as counterexamples | **finite monotonicity check only**; `no_time_loops_from_logic` is cited separately, and a no-event-loop theorem is **not** claimed |

This is a finite model, complete at that scope. L1/L2 have no general Lean layer and L5 has no
general statement, so the N-body quotient and self-model theorem remain open obligations rather
than conditions on the finite result. The finite checks do not upgrade the existing `B-OPEN`
status of the observer/self-model loop. In particular, `bad_model()` contains `m0 -> m0` at a
constant level and still passes L6; that counterexample is now part of the regression suite.

---

## 3. What the repository already proves

- [`Bridge_Tools.md`](Bridge_Tools.md) §“greatest bisimulation” records that on the **two-body**
  domain the observational equivalence is the greatest bisimulation compatible with continuation and
  joint-closure outcomes, a Myhill–Nerode right congruence.
- [`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean) proves
  `bisim_le_obsEquiv`, `obsEquiv_isBisim`, and `obsEquiv_iff_exists_bisim`; the quotient is the
  tensor quotient on that domain. The entangled sector and the `N`-body version are explicitly open.
- [`Strange_Loops.md`](Strange_Loops.md) §3B already states the self-model target
  `M ~_c S|_c` and the update-square obligation, and marks the bisimulation choice `B-OPEN`.
- [`Quantum_Knowledge_Base.md`](Quantum_Knowledge_Base.md) stores closures, not sentences; a concept
  is currently a named set of closures, and `ask`/`answer`/`solve` are the question/continuation
  operations.

The new layer is therefore **not** a replacement for those results. It adds the listener-relative
quotient `S/~_B`, the `W_micro`/`W_B` split, and the QKB/self-model reading.

---

## 4. QKB as listener-relative compression

The current QKB record is, schematically:

```
K = (closure, ways, redundancy, priority)
```

The proposed extension is:

```
K = (B, f, [h]_B, W_B, W_micro, R, φ)
```

- `B` — the listener/blanket;
- `f` — the resolution/frequency scale;
- `[h]_B` — the listener equivalence class, not a microscopic history;
- `W_B` / `W_micro` — distinguishable alternatives vs total path multiplicity;
- `R` — redundancy (unchanged);
- `φ` — phase/priority metadata (unchanged).

This is a **schema proposal**, not a change to the deployed QKB. The closure gate remains exactly
the existing one; `qkb_reference.py` is untouched in this PR.

The same physical history can support different knowledge at different blankets:

```
[h]_{B1} ≠ [h]_{B2}
```

without three different realities. They are different quotients of the same closure structure. This
is the Universal-Relativity reading of knowledge: listener-relative, not arbitrary.

---

## 5. The finite strange loop

The self-model target is

```
M ~ S/~_B
```

not `M = S`. The model does not contain a microscopic copy of the system; it contains a model
equivalent to the system's closure-relevant quotient.

The update architecture is a square:

```
S_t  --T-->  S_{t+1}
 |             |
C_B           C_B'
 ↓             ↓
M_t  --U-->  M_{t+1}
```

The square need not commute microscopically. It must commute **up to the chosen bisimulation**:

```
C_B ∘ T  ~  U ∘ C_B
```

The intended reading of the loop is across levels of description, not backward through event time.
The global `no_time_loops_from_logic` result says realized event histories do not run backward
([`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean),
[`Strange_Loops.md`](Strange_Loops.md) §3B). That global result is not re-proved by this toy: the
toy's own L6 check is only level monotonicity, and `bad_model()` retains a same-level self-loop.

**Timing convention.** `S_t` and `M_t` are **open listener states** between closures. `T` includes
the listening/delay history and ends in an **atomic closure event** (`tau_event = 0`); `U` is the
compression/update triggered by that event. The square therefore alternates open listening and
instantaneous closure, rather than treating the closure itself as an extended process.

**L6 is monotonicity, not a loop theorem.** The finite check verifies
`level(step(s)) >= level(s)`. A same-level transition, including the self-loop `m0 -> m0` in
`bad_model()`, satisfies it. `no_time_loops_from_logic` remains a separate cited result about
realized event histories; this model does not prove that its update square excludes a
zero-progress cycle. The distinction is now explicit in the code, the result JSON and the tests.

### 5a. Relation to the cooperative-closure stack

The merged cooperative results sharpen what this finite layer does and does not supply. They do
not turn the listener quotient into a general theorem; they locate it.

- **A listener is a compression, not a consensus.** `CC0` proves that agreement without an
  observation cannot discriminate the world (`unobserved_consensus_world_free`), and `CC3` proves
  that copying a source adds no independent support (`support_replicate_le`). A QKB quotient adds
  no provenance. Its `W_B` counts distinctions available to one listener, not corroborating
  witnesses.
- **Synthesis is not quotienting.** `CC2/CC6` prove that parity can be resolved by all holders and
  by no proper subset (`parity_irreducible`, `coalition_parity_iff`). The listener quotient in this
  document merges histories that one listener cannot distinguish; it does not create information
  that no participant holds. The cooperative and listener layers are therefore complementary and
  must not be identified.
- **The analogical listener is a different object.** `CC1` proves local consistency and
  preservation for partial relational correspondences (`consistent_extend_iff`,
  `closed_preserves`, `inconsistent_rejected`). A bisimulation quotient is not an analogy and this
  document proves no bridge between them. `CC1` supplies the operational acceptance rule for a
  Quantum-OS listener; this document supplies a finite compression schema. They can be integrated
  by a later implementation only after that bridge is stated.
- **Order cannot be recovered from balance.** `no_act_encoding_sees_order` proves that a fixed
  per-act encoding checked by count balance cannot distinguish `[need, offer]` from
  `[offer, need]`. Any listener-relative knowledge record must therefore retain ordered histories
  or an equivalent ordered witness when fulfilment, rather than mere balance, is the question.

The finite result here is thus exactly what it says: the coarsest lossless quotient for the
supplied observed transition systems, a separated multiplicity/uncertainty count, and a commuting
toy self-model square. The general N-body quotient, the general self-model theorem and the bridge
to the analogical listener remain open, but none of them is needed to state or use the finite
result.

---

## 6. Feelings as slow self-relevant queries (hypothesis)

A feeling is proposed to be a **long-lived self-relevant open query** updated by the same loop, not
a stored closure:

```
q = (self state, context)
Ω_0 ⊇ Ω_1 ⊇ Ω_2 ⊇ ...
M_t = C_{B_t}(S_t)
```

Fast perceptual closures resolve quickly (“blue”); slow affective queries (“Am I safe?”, “What does
this loss mean for me?”) require many lower-level closures before the higher-level equivalence class
stabilises. On this reading:

- perception = fast closure;
- thought = intermediate-frequency query;
- feeling = slow, deep, self-relevant query;
- mood = a very slow context `B` that changes which closures are admissible.

This is a **bridge hypothesis**, not a theory of qualia. It is gated by L5 and by the existing
affect gate C4 in [PR #272](https://github.com/rhovision-org/quantum-logical-framework/pull/272).

---

## 7. Non-goals

- No general `N`-body listener theorem; the existing Lean result is two-body.
- No change to QKB storage or the closure gate.
- No claim that `W_B` is thermodynamic entropy or physical randomness.
- No claim that `M ~ S/~_B` is proved; it is a target with a toy square.
- No claim that feelings are explained; §6 is a hypothesis.
- No event-loop theorem: L6 checks level monotonicity only, and a same-level self-loop passes it.
- No claim that a bisimulation quotient is an analogical listener; that bridge is not proved here.
- No causal loop or backwards causation.

---

## 8. Reproduce

```bash
python3 listener_equivalence.py --self-test
python3 listener_equivalence.py --run
python3 -m unittest tests.test_listener_equivalence -v
```

The run writes `data/listener_equivalence_census.json`. The definitions are frozen at the commit
that adds this file; a different observable or continuation system is a new pre-registration.
