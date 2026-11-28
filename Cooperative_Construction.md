# Cooperative Construction — the TOE spine and its gates

**Status:** synthesis/index, not a new physical claim. Every domain below keeps its existing status
label. The index and its domain-status audit are complete at that scope and it is proposed for
merge on that basis. General bridges remain open where they are labelled open. Tracking issue:
[#270](https://github.com/rhovision-org/quantum-logical-framework/issues/270).

**Framing.** QLF has one conjecture, equal and opposite logical action ([`Framing.md`](Framing.md)
A01), and tests models inside it. This document is an **index of existing results**, not a second
premise. Read computationally ([`Universe_Quantum_Computer.md`](Universe_Quantum_Computer.md)), it
asks how separately held closures compose into a larger closure, and which top-down constraints are
admissible. It does not promote any row merely because the row uses cooperative language.

**The rule at the top.** *No shared vocabulary is evidence of a shared mechanism.* A domain joins
this spine only when its existing objects instantiate the common definitions or a pre-registered
operational bridge succeeds. Otherwise it stays a neighbor, not an instance.

**Layers.** The static flat-history assembly index is [`Assembly_Index_QLF.md`](Assembly_Index_QLF.md)
(#264); the tensor-sector index is #266; the transport screen is
[`Cooperative_Assembly_QLF.md`](Cooperative_Assembly_QLF.md) (#267, negative); the finite
uncertainty kernel is [`Closure_Uncertainty_QLF.md`](Closure_Uncertainty_QLF.md) (#269); and the
proved cooperative-closure stack is [`Cooperative_Intelligence.md`](Cooperative_Intelligence.md)
(CC0–CC9). This document is the index over those layers, not a replacement for any of them.

---

## 0. The spine

```
possibility
   ↓
uncertainty
   ↓
entanglement
   ↓
closure
   ↓
information
   ↓
reuse
   ↓
assembly
   ↓
new possibility
```

with two directions at every scale:

```
bottom-up construction   ⇄   top-down contextual constraint
```

The arrow down the left side is construction. The return arrow is not backwards causation: an
enclosing closure restricts which locally possible continuations participate in the whole. It does
not reach back and change what was possible.

---

## 1. What “cooperative” means here

- **Bottom-up `J`.** Closures compose into larger closures. In the flat-history sector this is the
  concatenation/assembly operation of [`Assembly_Index_QLF.md`](Assembly_Index_QLF.md); in the
  tensor sector it is the separate construction controlled by #266.
- **Top-down `S_B`.** An enclosing blanket `B` removes continuations incompatible with itself. It
  supplies no new force and no new primitive; it is a filter on the admissible next closures.
- **Cooperative step.** `X_{k+1} = S_{B_k}(J(X_k, E_k))`, where `X_k` is the persistent library and
  `E_k` is the environment.

**The equation is intentionally schematic.** `J`, `S_B`, `X_k` and `E_k` are not given a new
universal definition here. The flat-history `J` is the concatenation/assembly operation of
[`Assembly_Index_QLF.md`](Assembly_Index_QLF.md); the tensor-sector `J` is #266; the filter `S_B`
and its provenance are the subject of the proved gates below. Reading the notation as a derived
mechanism would violate gate C0.

**A terminology warning.** [`Theory_Of_Everything.md`](Theory_Of_Everything.md) uses “orientation
from the top down” for the fact that an open history's completion is fixed by its own imbalance. That
is a different axis from top-down **constraint**. Orientation is about the completion of one
history; cooperative top-down is about which continuations an enclosing closure admits. Both are
real; they are not the same claim and should not be merged.

### 1a. The proved cooperative-closure stack (CC0–CC9)

The index now sits over proved results, not only a proposal. Full statements, scopes and
counterexamples are in [`Cooperative_Intelligence.md`](Cooperative_Intelligence.md).

| gate | proved content | status |
|---|---|---|
| **CC0 consensus** | agreement whose provenance contains no observation is the same in both worlds (`unobserved_consensus_world_free`); a unanimous consistent false consensus exists for every community size (`consensus_fallacy`) | **impossible** as evidence; **possible** as a social state |
| **CC3 provenance** | copying one source adds no origin or independent support (`origins_replicate`, `support_replicate_le`); replay preserves origins (`replay_invariance`) | **necessary** bookkeeping |
| **CC2/CC6 synthesis** | parity is resolved by all holders and by no proper subset (`parity_irreducible`, `coalition_parity_iff`); an `n`-party irreducible ZFA closure exists | **necessary/possible** in the information and substrate witnesses |
| **CC1 analogical listener** | a local check keeps or refuses an open-slot proposal without rewriting the mapping (`consistent_extend_iff`); a closed analogy carries every source relation (`closed_preserves`); an inconsistent branch stays rejected (`inconsistent_rejected`) | **proved finite contract**; not a general search theorem |
| **CC4 semantic → ZFA** | exact one-for-one needs/offers balance is sound and complete (`encode_closes_iff_met`); count balance cannot distinguish need-then-offer from offer-then-need (`no_act_encoding_sees_order`) | **bridge, scoped**; order-sensitive semantics are outside it |
| **CC5 free energy** | QLF's `log 2` matches one free-energy change in magnitude under a uniform prior (`quantum_matches_iff_uniform`), with the sign fixed by the direction of resolution (`vfe_resolution_signed`) | **magnitude match only**; no constant identity |
| **CC7 first closure** | the final verdict is schedule invariant, but the first closure is not (`first_closure_schedule_dependent`); a first closure stays first in every extension (`isFirst_append`) | **proved**; no schedule-free global now |
| **CC8 hierarchy** | every level of a parity hierarchy is irreducible; no finite group of capacity-bounded listeners hears every closure | **proved**; physical hierarchy remains a reading |
| **CC9 certificates** | verifiers agree (`verifiers_agree`); a certificate carries only its external bit | **proved bookkeeping** |
| **competing listeners** | the race winner changes with the schedule (`race_schedule_dependent`); covering balanced views balance the whole (`listeners_cover_met`) | **proved** |

**What this changes for the spine.** CC0 and CC3 make provenance part of the top-down filter `S_B`:
agreement and repetition do not create independent constraint. CC2/CC6 supply the first exact
information form of irreducible synthesis. CC1 supplies the listener-side acceptance rule. CC4
locates the semantic bridge precisely: exact conservation of needs and offers is encodable, but
count balance alone is blind to order, so a cooperative system that must know whether an offer
answered an earlier need needs ordered histories and fulfilment evidence, not only a balance. CC7
shows that the first closure is schedule-relative even though the final balance is not.

These results **do not upgrade any domain row** in §3. They constrain what a future row can claim.
In particular, "cooperative" is not identified with "consensus", "copying", "agreement" or
"balance"; and the analogical listener is not identified with a bisimulation quotient. The Quantum-OS
instantiation therefore has an explicit obligation: retain ordered, listener-relative histories and
provenance when order or fulfilment matters.

---

## 2. Gate C0 — no analogy by vocabulary

A domain is listed as an **instance** only if one of these holds:

1. its closure predicate is an existing QLF theorem (for example `IsNash ↔ IsClosure`);
2. its states and steps instantiate a `FiniteClosureSystem` of the uncertainty kernel without
   changing the kernel's definitions;
3. a pre-registered operational bridge has been run and recorded.

Otherwise the domain remains **structural**, **open**, or **negative** in the table below. Similar
words — “closure,” “assembly,” “uncertainty,” “information” — do not move a row.

---

## 3. Domain ledger

| Domain | Existing anchor | Status | What is actually established |
|---|---|---|---|
| **Quarks / confinement** | `quark_not_closed`, `charged_not_closed`, `singlet_closure`, `baryon_needs_all_three_axes` (`QLF_Confinement`, `QLF_QuarkStructure`) | **Theorem** | a lone coloured/charged state is not a ZFA closure; only singlets close. The assembly reading (“the quark contributes but is not a reusable node”) is a restatement of this closure obstruction. |
| **Particles** | `prime_closure_irreducible`, `half_spin_is_prime_agent` (`QLF_QuantumTurbulence`) | **Theorem / structural** | prime closures are irreducible; the half-spin agent is the minimal prime. “Persistent prime closure” is a structural reading, not a separate derivation. |
| **Game theory** | `nash_iff_closure` (`QLF_PotentialGames`, `QLF_NPlayerPotential`) | **Theorem** | in a potential game with a free-action functional, Nash equilibrium = ZFA closure. The uncertainty kernel's Stag Hunt instantiation counts first-completion paths to that closure. |
| **Atoms** | `QLF_Unsaturation`, `QLF_Folding` | **Theorem** | valence/closure counting; degree of unsaturation = cycle rank; a folding contact is a ZFA loop. |
| **Chemistry** | [`Chemistry.md`](Chemistry.md), [`Protein_Folding.md`](Protein_Folding.md) | **Structural; molecular-AT bridge open** | bonds are shared closures; the operational Assembly-Theory bridge (mass-spec fragmentation) has not been run. |
| **Turbulence** | `vortex_quantum`, `circulation_integer_quantized`, `flux_scale_invariant`, `kolmogorov_exponents` | **Mixed; negative baseline** | quantized vorticity and the scaling argument are proved/anchored; the raw closure census has **no inertial range**, vacuum or seeded (`intermittency_bridge.py`, `intermittency_seeded.py`). No cascade is claimed. |
| **Motion** | [`Inertia.md`](Inertia.md), [`Gravity_From_Delay.md`](Gravity_From_Delay.md) | **Open** | QLF has latency/inertia readings; the Brownian-plus-drift decomposition needs a measure and has not been derived. |
| **Biology** | [`Evolution.md`](Evolution.md), [`Hierarchical_Control.md`](Hierarchical_Control.md) | **Structural** | generate-and-select and nested Markov blankets; not the uncertainty kernel instantiated. |
| **Consciousness / feelings** | [`Consciousness.md`](Consciousness.md), [`TheQuantumBrain.md`](TheQuantumBrain.md) | **Open; affect hypothesis** | no qualia theorem. A long/slow, deep, integrated, self-relevant listening trajectory ending in an atomic closure is a measurable hypothesis, not a result. |
| **Cosmology** | [`AgeOfUniverse.md`](AgeOfUniverse.md), [`Primordial_Markov_Blankets.md`](Primordial_Markov_Blankets.md), [`Cosmological_Constant.md`](Cosmological_Constant.md) | **Structural / B-OPEN; gates G1–G6 in PR #277** | logical origin, holographic compression, measure, potential infinity, and the clock gate; `N` is not derived. |

This table is deliberately conservative. The fact that a row uses the word “closure” does not make it
an instance of the cooperative step.

---

## 4. Gates C1–C4

| gate | requirement | current status |
|---|---|---|
| **C1 — no backwards causation** | top-down restricts admissible continuations; it is not retrocausation and not a new force | stated; [`Cooperative_Intelligence.md`](Cooperative_Intelligence.md) adds the schedule-relative first-closure result (CC7), not a new force |
| **C2 — negative-result preservation** | the closure-census turbulence kill stands; no Kolmogorov, Zipf, or `1/f` exponent may be inserted into a transport model | preserved in [`Cooperative_Assembly_QLF.md`](Cooperative_Assembly_QLF.md) |
| **C3 — status labels** | every domain is theorem / structural / bridge / open / negative | ledger audit complete here; no row is promoted by this document |
| **C4 — affect gate** | feelings and consciousness enter only as an affect hypothesis with measurable timescales, not as a theorem about qualia | §6; the finite model is [`Conscious_Dynamics_QLF.md`](Conscious_Dynamics_QLF.md) |

If a gate fails, the domain does not move up the ladder. The failure is recorded.

---

## 5. What the spine does and does not show

**Shown (existing results, not new here).**

- Closure is composition and isolation: `isolated_iff_closed`, `closed_insertion_is_phase`.
- Quark confinement is a closure obstruction, not a missing force.
- Nash equilibrium is closure in the potential-game class.
- Atoms and folding have closure-counting theorems.
- Quantum vortices are quantized; the `−5/3` exponent follows from the flux-invariance premise.
- The raw closure census has no inertial range, vacuum or seeded.
- Consensus without an observation in its provenance carries no information (CC0), and copying a
  source adds no support (CC3).
- Parity synthesis is irreducible: the whole resolves it, no proper part does (CC2/CC6).
- The analogical listener's local extension/rejection contract is proved (CC1).
- Exact needs/offers balance is encodable, and fixed per-act count balance is proved order-blind
  (CC4).
- The first closure is schedule-relative while the final balance is not (CC7).
- The cooperative limits: no constant free-energy identity (CC5), no finite capacity hears every
  closure (CC8), and verifiers agree (CC9).

**Bridge / open.**

- A tensor-sector `A_E` (#266).
- A cooperative transport model that produces a non-floor stationary range (#267; the first frozen
  screen was negative).
- A molecular Assembly-Theory bridge with fragmentation data.
- A derivation of motion as biased closure renewal.
- A physical Markov-blanket instantiation of `S_B`, and its Quantum-OS implementation, including
  ordered listener-relative histories for order-sensitive fulfilment.
- CC4 beyond exact needs/offers balance; the semantic bridge there is scoped and does not establish
  ordinary fulfilment, commitment or causal matching.

**Not claimed.**

- That quarks, games, chemistry, turbulence, and consciousness are “the same mechanism.”
- That the cooperative step is a new force or a new axiom.
- That the TOE is complete, or that the ladder is a derivation rather than an index.
- That agreement is evidence, that copying is corroboration, or that balance alone is fulfilment.
- That the analogical listener is a bisimulation quotient, or that either is a general N-body
  theorem.
- That a schedule-free global “now” follows from the final closure verdict.

---

## 6. The affect hypothesis (explicitly a hypothesis)

A feeling is proposed to correspond to a **long/slow, deep, highly integrated, self-relevant
listening or integration trajectory ending in an instantaneous closure**, not to “complexity” in
general. For a blanket `B_k`, record

```
(tau_k, A_k, U_k, D_k, d_k)
```

where `tau_k` is the listening/renewal timescale (not the duration of the closure event), `A_k` the
assembly complexity, `U_k` the unresolved first-completion information from the uncertainty kernel,
`D_k` the nesting depth, and `d_k` the remaining distance to the next trigger. A candidate affective
trajectory lies in the long/slow, deep, high-integration region of that state space; the closure
event itself is atomic (`tau_event = 0`).

A candidate valence is `V_k = -ΔU_k/Δt`: positive when unresolved possibility is being resolved,
negative when it accumulates. This is a **bridge hypothesis with measurable directions**, not a
theory of qualia. It is gated by C4 and is not used anywhere else in this document.

---

## 7. Cosmological instantiation

Cosmology is no longer a one-line placeholder. The chain is gated in
[PR #277](https://github.com/rhovision-org/quantum-logical-framework/pull/277) (issue #276):

```
first distinction → logical/information bang → nested closures
→ primordial Markov blankets → holographic compression
→ cosmic blanket → open-ended time
```

| gate | status |
|---|---|
| G1 logical origin | `first_distinction_closes`; no metric singularity |
| G2 information | one-bit/`log 2` reading; no information-energy identity |
| G3 holographic compression | `C_B` must preserve the closure observable; two-body theorem exists, N-body open |
| G4 measure | cylinder/Kraft `μ(c)=8^(-|c|)`; raw `W` vs normalized `P` |
| G5 time | finite at every realized horizon + unbounded possible extension; physical eternity is interpretation |
| G6 cosmic clock | no numerical age until `N` is independently derived |

The correction matters: `^<v` is **not** a count-balanced ZFA word (the `<` has no `>` conjugate).
[`Primordial_Markov_Blankets.md`](Primordial_Markov_Blankets.md) §4 now distinguishes a triangular
**blanket cell** from a **ZFA closure**; the Euler/Fuller face count is unchanged, but the literal
3-twist ZFA identification is withdrawn.

---

## 8. Relation to the TOE index

[`Theory_Of_Everything.md`](Theory_Of_Everything.md) remains the map. This document supplies one
organizing spine for the map:

```
possibility → uncertainty → entanglement → closure → information → reuse → assembly → new possibility
```

The TOE rows keep their own status labels. The spine does not upgrade them.

---

## 9. References

- [`Cooperative_Intelligence.md`](Cooperative_Intelligence.md) — proved CC0–CC9 stack, scopes and
  counterexamples.
- [`Assembly_Index_QLF.md`](Assembly_Index_QLF.md) — static flat-history assembly.
- [`Closure_Uncertainty_QLF.md`](Closure_Uncertainty_QLF.md) — finite first-completion uncertainty
  kernel.
- [PR #277](https://github.com/rhovision-org/quantum-logical-framework/pull/277) — cosmic closure
  gates G1–G6 (`Cosmic_Closure_QLF.md`), including the `^<v` correction.
- [`Cooperative_Assembly_QLF.md`](Cooperative_Assembly_QLF.md) — pre-registered transport screen,
  negative.
- [`Hierarchical_Control.md`](Hierarchical_Control.md) — bottom-up synthesis / top-down blanket
  constraint.
- [`Turbulence.md`](Turbulence.md), [`Navier_Stokes_Geometry.md`](Navier_Stokes_Geometry.md) —
  quantized vortices, forced `−5/3`, and the census kill.
- [`Game_Theory_QLF.md`](Game_Theory_QLF.md) — Nash = closure in potential games.
- [`Quarks.md`](Quarks.md) — confinement as the singlet-closure obstruction.
- [`MostWays_First.md`](MostWays_First.md) — ways require a measure.
