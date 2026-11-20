# Cosmic Closure — logical origin, holographic listening, and potential infinity

**Status:** pre-registration plus a finite reference implementation. This is a **cosmology
instantiation**, not a derivation of the observed universe. Tracking issue:
[#276](https://github.com/rhovision-org/quantum-logical-framework/issues/276).

**The rule at the top.** *No shared vocabulary is evidence of a shared mechanism.* A cosmological
claim joins this layer only when it reuses an existing theorem or passes a declared gate. The
logical origin, the information reading, the blanket hierarchy, and the cosmic clock keep separate
status labels.

**Layers.** The uncertainty kernel and its measure gate are
[PR #271](https://github.com/rhovision-org/quantum-logical-framework/pull/271); the Lean finite-check
layer is [PR #273](https://github.com/rhovision-org/quantum-logical-framework/pull/273); the
cooperative-construction spine and its C0–C4 gates are
[PR #272](https://github.com/rhovision-org/quantum-logical-framework/pull/272); the listener quotient
is [PR #275](https://github.com/rhovision-org/quantum-logical-framework/pull/275).

---

## 0. The chain

```
first distinction
   ↓
logical / information bang
   ↓
nested closures
   ↓
primordial Markov blankets
   ↓
holographic boundary compression
   ↓
cosmic blanket
   ↓
open-ended time
```

The arrow is an **index of existing results and bridges**, not a new derivation. Each row below
keeps its own status.

---

## 1. Gates

| gate | requirement | status |
|---|---|---|
| **G1 — logical origin** | reuse `first_distinction_closes`; no metric singularity claim | **theorem** in [`QLF_LogicalBang`](lean/QLF_LogicalBang.lean) |
| **G2 — information** | explain how a closed binary distinction gets the one-bit/`log 2` reading; do not equate information and energy without the existing bridge | **interpretation**; no new theorem |
| **G3 — holographic compression** | define `C_B : interior histories → boundary classes`; show it preserves the claimed closure observable | **finite toy** in `cosmic_closure.py`; general N-body theorem open |
| **G4 — measure** | replace raw path count with a declared measure before physical probability | **candidate**: cylinder/Kraft `μ(c)=8^(-|c|)`; finite check in PR #271 |
| **G5 — time** | prove finite at every realized horizon + unbounded possible extension | **theorem / cited**; physical eternal universe is interpretation |
| **G6 — cosmic clock** | no numerical age until horizon/closure depth `N` is independently mapped to proper time | **B-OPEN**; [`AgeOfUniverse.md`](AgeOfUniverse.md) already says `N` is not derived |

The PR is draft. G1, G5, and G6 are mostly status discipline; G3 and G4 are the new finite checks.

---

## 2. G1 — logical origin, not a metric singularity

[`QLF_LogicalBang`](lean/QLF_LogicalBang.lean) proves `first_distinction_closes`: the minimal balanced
ZFA word `[+,-]` is the first closed distinction. That is a **logical** origin. It is not a metric
singularity, not a curvature blow-up, and not a claim that the observed Big Bang is that word.

The readable statement is:

```
minimal ZFA closure = theorem
"the first bit of the universe" = information interpretation
```

The second line is G2 and is not proved by the first.

**Timing.** The logical bang is an **event**, not an extended process: `first_distinction_closes` is
an atomic closure (`tau_event = 0`). Any duration belongs to the listening/construction history that
precedes it, not to the closure itself.

---

## 3. G2 — the information reading

A closure resolves a binary distinction, and the information layer assigns the per-event `log 2`
quantum. That is enough for a one-bit reading of the first closed distinction. It is **not** enough
to identify information with energy, entropy, or the cosmological constant. Those require the
existing bridge conditions in [`Cosmological_Constant.md`](Cosmological_Constant.md) and
[`Gravity_From_Delay.md`](Gravity_From_Delay.md); they are not folded into this gate.

---

## 4. G3 — holographic listening as compression

A blanket does not need every interior microhistory. It can respond to a compressed boundary
representation:

```
{many interior histories} --C_B--> {boundary-relevant classes}
```

`C_B` must preserve the closure observable the blanket is said to hear. If two interiors are merged
but a continuation can distinguish their closure outcomes, the compression is lossy and the listener
claim fails.

This is the same correctness condition as the listener quotient in
[PR #275](https://github.com/rhovision-org/quantum-logical-framework/pull/275):

```
s ~_B t  ⇔  same observation and every continuation stays equivalent.
```

The two-body greatest-bisimulation theorem is already
`obsEquiv_iff_exists_bisim` in
[`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean). The N-body/horizon version
is open. The finite toy in `cosmic_closure.py` checks the compression on a small interior set and
shows a safe compression and a deliberately lossy one.

**Holography is the proposed general mechanism, not a proved identity.** The boundary screen,
the cosmic horizon, a cell membrane, and a sensory blanket are different physical implementations of
the same compression schema only if their `C_B` maps pass G3 independently.

---

## 5. G4 — the measure gate

Raw completion counts are not probabilities. Before any cosmological probability claim, declare a
measure. The candidate is the cylinder/Kraft weight

```
μ(c) = 8^(-|c|)
P(c | h, B) = μ(c) / Σ_{c' ∈ Ω_R(h|B)} μ(c').
```

The uncertainty kernel's U5 gate (PR #271) computes this for the flat-ZFA completions. The raw
`W_R` stays a count; `P` is the normalized weight. No cosmological use of `W` is allowed before this
declaration. The cylinder weight is a **candidate**, not the final physical measure.

---

## 6. G5 — finite horizons and potential infinity

Every realized history is finite. QLF also proves that balanced strings always have longer balanced
extensions (`no_terminal_phase`, `order_at_every_scale`; see
[`Open_Eternal_Mind.md`](Open_Eternal_Mind.md) and
[`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean)):

```
∀ n, n < ∞
∀ n, ∃ m > n  with a longer balanced extension.
```

**Timing.** Cosmic time accumulates **between and nested among atomic closures**, not during a
closure. The unbounded extension is a sequence of events with `tau_event = 0`, not a single event of
infinite duration. This is the same listening-vs-event distinction as the D9 gate in
[PR #279](https://github.com/rhovision-org/quantum-logical-framework/pull/279).

That is **potential infinity**. It does not prove that the physical cosmos actualizes an endless
sequence of those extensions. The distinction is:

- **proved:** unbounded possible extension;
- **interpretation/bridge:** a physically eternal universe.

This document keeps the second label. The finite toy checks the constructive witness `(^v)^n` for
small `n`; it does not observe the cosmos.

---

## 7. G6 — the cosmic clock

`t₀ = N·τ_Planck` is a clock reading, not a derivation of `N`. [`AgeOfUniverse.md`](AgeOfUniverse.md)
already states that `N` is not yet derived and that the numerical age is calibrated through the
cosmological clock/expansion history. Any high-level prose that presents `N` as substrate-fixed is
stale and should be corrected to the `AgeOfUniverse.md` status.

No numerical age claim is made here. The Gupta/CCC+TL comparison remains an external comparator, not
a QLF derivation.

---

## 8. Correction: the `^<v` triangle claim

[`Primordial_Markov_Blankets.md`](Primordial_Markov_Blankets.md) §4 previously said that a 3-twist
sequence such as `^<v` is a ZFA-balanced triangle. Under the current count-balance definition it is
**not** balanced: `^` and `v` cancel on the up/down axis, but `<` has no `>` conjugate, so the net
action is one unit on the left/right axis. It is not a ZFA closure.

The correction is:

- the **geometric triangle** remains a blanket-combinatorics object; the Fuller/Euler/face-count
  results (`F_v = 20v²`, the 12 pentamons) are not affected;
- the claim that each geometric triangle is literally the 3-twist word `^<v` is withdrawn;
- a ZFA closure needs the conjugate twist or a longer balanced word; the minimal closure is `^v`,
  and the triangle's three edges are not three independently closed 3-twist words.

The corrected §4 distinguishes **blanket cell** from **ZFA closure**. This is a status correction,
not a change to the Euler count.

---

## 9. What this does and does not establish

**Established / cited.**

- The minimal ZFA closure is `[+,-]` (`first_distinction_closes`).
- Balanced strings have unbounded possible extensions (`no_terminal_phase`,
  `order_at_every_scale`).
- The two-body observational quotient is the greatest bisimulation
  (`obsEquiv_iff_exists_bisim`).
- The raw completion count and the cylinder-normalized weight are distinct (PR #271 U5).
- `N` is not derived (`AgeOfUniverse.md`).

**Bridge / open.**

- A general N-body/horizon holographic compression theorem.
- A physical identification of the boundary screen with a QLF closure observable.
- A derivation of `N` and the cosmic age.
- A physically eternal universe (as opposed to unbounded possible extension).

**Not claimed.**

- No metric singularity, no new force, no information-energy identity.
- No proof that the observed cosmos is the logical bang.
- No numerical age, no `N ~ 10^60` derivation.
- No claim that all blankets are physically the same.

---

## 10. Reproduce

```bash
python3 cosmic_closure.py --self-test
python3 cosmic_closure.py --run
python3 -m unittest tests.test_cosmic_closure -v
```

The run writes `data/cosmic_closure_census.json`. The definitions are frozen at the commit that adds
this file; a different boundary/observable or measure is a new pre-registration.
