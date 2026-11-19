# Listener Equivalence — bisimulation, QKB compression, and finite strange loops

**Status:** pre-registration plus a finite reference implementation. This is a **draft** layer, not
a general theorem. QKB storage is unchanged. Tracking issue: [#274](https://github.com/rhovision-org/quantum-logical-framework/issues/274).

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

---

## 2. Gates

| gate | requirement | status |
|---|---|---|
| **L0** | `S`, `A`, `step`, `obs_B`, `Ω_R`, and the quotient are frozen before applications | **done** in this document |
| **L1** | `~_B` is an equivalence relation and a right congruence | **finite exact check** in `listener_equivalence.py`; general Lean layer open |
| **L2** | the quotient is the coarsest lossless listener compression | **finite brute-force check**; the two-body theorem is already `obsEquiv_iff_exists_bisim` in [`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean); N-body generalisation open |
| **L3** | uncertainty factors into microscopic multiplicity and listener classes, with `W_B ≤ W_micro` | **finite exact check**; general theorem open |
| **L4** | QKB concepts can be read over quotient classes without changing the closure gate | **schema proposal + prototype**; QKB storage unchanged |
| **L5** | a finite self-model can be faithful by bisimulating the quotient, not copying `S` | **toy check**; general theorem open |
| **L6** | no causal loop: every physical transition still advances the event record | **cited** `no_time_loops_from_logic`; toy level check |

The PR is draft until L1/L2 have a general Lean layer and L5 has a general statement. The finite
checks do not upgrade the existing `B-OPEN` status of the observer/self-model loop.

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

The loop is across levels of description, not backward through event time. Every `T` still advances
the realized history; the model update `U` does not create a closed timelike curve. This is the
existing `no_time_loops_from_logic` distinction: loops may exist in the possibility/representation
relation while realized history does not run backward
([`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean),
[`Strange_Loops.md`](Strange_Loops.md) §3B).

**Timing convention.** `S_t` and `M_t` are **open listener states** between closures. `T` includes
the listening/delay history and ends in an **atomic closure event** (`tau_event = 0`); `U` is the
compression/update triggered by that event. The square therefore alternates open listening and
instantaneous closure, rather than treating the closure itself as an extended process.

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
