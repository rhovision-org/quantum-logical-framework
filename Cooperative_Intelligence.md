# Cooperative Intelligence — what closes beyond any one participant

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Status.** Gates CC0, CC3 and CC2/CC6 are **proved** in Lean, with no axioms, in
[`lean/QLF_CooperativeClosure.lean`](lean/QLF_CooperativeClosure.lean). Gate CC1 (the analogical
listener) is **proved** in [`lean/QLF_AnalogicalListener.lean`](lean/QLF_AnalogicalListener.lean), no
axioms. CC4 (semantic-to-ZFA bridge) and CC5 (free action vs Friston free
energy) are **open bridges**. Nothing here claims that QLF closure *is* semantic or empirical truth.

The program is a joint one with [Quantum-OS](https://github.com/rhovision-org/quantum-os): QLF states
and proves the closure conditions; Quantum-OS would instantiate them among humans and agents and test
them. In the framing of [Framing.md](Framing.md), QLF is the quantum computer that tests models, and
ZFA is its one well-supported conjecture. A cooperative protocol is one more model to test. Every
statement below is one of the four kinds of [Framing.md](Framing.md) §2: derived (a Lean theorem), a
known fact (A10–A14 in [Principles.md](Principles.md); none is used here), a bridge, or a reading.
Each verdict is one of the five of [Framing.md](Framing.md) §4: necessary, possible, impossible,
equivalent or undetermined.

| Gate | Kind | Verdict |
|---|---|---|
| CC0 consensus fallacy | Derived | **Impossible**: consensus with no observation among its sources cannot discriminate the world. **Possible**: a unanimous, consistent false consensus, for every `n`. |
| CC3 provenance | Derived | **Necessary**: origins and support are invariant under repetition, replay and copying. |
| CC2/CC6 synthesis | Derived | **Necessary**: parity needs every holder. **Possible**: an `n`-party irreducible ZFA closure. |
| CC1 analogical listener | Derived | **Necessary**: extension keeps mappings, closure carries the relation, inconsistency is permanent. **Impossible**: closing with an obligation open. |
| CC4, CC5 | Bridge | **Undetermined**. |

---

## 1. The target, stated so it can fail

> **Separately held information can resolve a question that no proper part of it resolves, and
> agreement is neither necessary nor sufficient for that resolution.**

Two conditions keep this from being empty.

1. **The parts are fixed before the answer is seen.** Without that, the statement is trivially true of
   every closure: any closed word splits after its first twist into two open pieces (CO0,
   [`QLF_CoincidenceTrivial`](lean/QLF_CoincidenceTrivial.lean) `co0_trivial_split`,
   [Coincidence_QLF.md](Coincidence_QLF.md) §4). Every theorem below fixes the holders first.
2. **"Resolves" is defined independently of closure.** Here it means *determines the answer*: agreement
   on what the coalition holds forces agreement on the answer. That is information, not ZFA. Linking the
   two is CC4 (§6).

Four kinds of closure are kept apart throughout. **Social** closure is agreement. **Logical** closure is
satisfying stated obligations (for QLF, a ZFA verdict). **Empirical** closure is surviving
independently specified observation. **Constructive** closure is realizing a possibility by action.
Mass hysteria is the worked case of the first without the third.

---

## 2. CC0 — consensus is not evidence (proved)

A source is either an **observation**, which reads the world, or an **assertion**, which states a fixed
claim whatever the world is. A record lists the source each participant relays.

| Theorem | Statement |
|---|---|
| `consensus_fallacy` | For every `n` there is a record of `n` participants who all accept `p`, are mutually consistent, share one origin, and `p` is false. |
| `unobserved_consensus_world_free` | If no source in the record is an observation, consensus is the **same in both worlds**: it carries no information about which one holds. |
| `observed_consensus_sound` | If the record contains an observation and everyone accepts `p`, then `p` is true. |

**What this is worth.** The first two are bookkeeping in the sense of [ScientificApproach.md](ScientificApproach.md)
rule 4: consensus is a function of the record, truth is a function of the world, and nothing ties them
unless a source reads the world. That is exactly the content wanted from CC0. It is the formal boundary
between cooperative inference and collective delusion: what makes agreement informative is an
observation in its provenance, not the number of participants or their consistency.

---

## 3. CC3 — provenance is conserved (proved)

Provenance is the set of originating sources (`r.toFinset`), not the identity of the latest
transmitter. Independent support is the number of distinct observation sources (`support`).

| Theorem | Statement |
|---|---|
| `origins_replicate` | `n ≠ 0` copies of one source have exactly one origin. |
| `support_replicate_le` | Repetition never raises support above one. A thousand agents repeating one assertion are not a thousand confirmations. |
| `duplicate_suppression` | Re-transmitting a source already present changes no origin. |
| `replay_invariance` | Reordering the record changes no origin. |
| `origins_append` | A composed claim carries the union of its parts' origins (traceability). |
| `compose_same_origin` | Composing two contributions with the same origin set yields that origin set. |
| `support_append_le`, `copy_adds_no_support` | Support is subadditive, and copying sources already held adds none. |
| `separate_not_independent` | Two distinct observations of one proposition agree in every world: separate provenance is **not** statistical independence. |

These are definitional consequences of choosing *set of origins* as the measure. The choice is the
content: any measure that counts transmissions instead fails `support_replicate_le`.

**Multiplicity versus repetition.** QLF's census multiplicity counts distinct *ways* a closure happens.
Memetic repetition counts copies of one way. The provenance measure above is the one that keeps the two
apart. (Per [MostWays_First.md](MostWays_First.md), multiplicity does not decide priority either; the
first closure does.)

---

## 4. CC2/CC6 — irreducible synthesis (proved)

A set `S` of variables **resolves** a question `Q : (V → ℤ/2) → ℤ/2` when any two assignments that agree
on `S` give the same answer.

| Theorem | Statement |
|---|---|
| `parity_resolves_iff` | A set resolves the parity of all variables **iff** it is all of them. |
| `parity_coalition_blind` | Any proper set, **whatever values it sees**, is compatible with both parities. |
| `parity_irreducible` | Parity is an irreducible synthesis: resolved by the whole, by no proper subset. Holds for any finite number of participants. |
| `xor_synthesis` | Two participants: together they determine `x ⊕ y`; neither alone does. |
| `dictator_not_irreducible` | The ordinary contrast: a question one variable decides is resolved by the whole but is not irreducible. |
| `coalitionResolves_iff` | A coalition of participants, each holding a variable, resolves `Q` iff the **set of variables held** does. Resolution never depends on how many members hold a variable. |
| `coalition_parity_iff` | A coalition resolves parity iff its members together hold every variable. |
| `echo_chamber_blind` | Any number of members who all hold the same variable cannot resolve parity when another variable exists. |
| `irrelevant_member` | **Limit:** a member whose variable the question ignores adds nothing. |
| `missing_variable` | **Limit:** if nobody holds some variable, no coalition resolves parity. |
| `resolves_mono` | Holding more never loses a resolution. |

So the target of §1 is proved in its information form: separately held bits resolve a question no
proper part resolves, and **no participant needs to agree with any other** on anything for that to
hold. Each holds a different bit. Diversity is productive here *because* the question depends on every
variable; `irrelevant_member` and `echo_chamber_blind` are the two ways it fails to be.
Two of CC6's listed limits are not yet proved: that redundancy can raise reliability without adding
information (this needs a noise model), and that contradictions must be resolved rather than averaged
(CC1's rejection predicate now exists, §4b; the cooperative statement is not yet proved).

### 4a. The substrate witness, and how `StrongCoIncides` fits

On the twist alphabet, `n` parties contribute `^` and one contributes `v^n`.

| Theorem | Statement |
|---|---|
| `star_closes` | All `n + 1` parties together are a ZFA closure. |
| `star_irreducible` | No nonempty proper sub-coalition, taken in order, closes. |
| `star_one_is_primordial` | The case `n = 1` is the primordial `^ \| v`: each side open, the pair closed. |

This is an `n`-party irreducible **joint closure**, with the holders fixed before the closure is
checked, so it escapes CO0.

`StrongCoIncides` ([Coincidence_QLF.md](Coincidence_QLF.md) §3) fits as a **stronger, two-origin,
algebraic** condition, not as the representation of cooperative synthesis:

- It is two-origin. The `n`-party analogue above is defined by sub-coalition closure; no `n`-origin
  `StrongCoIncides` exists yet.
- Irreducible closure does not imply it. The gauge pair `+ | −` is irreducible (neither side closes
  alone) but each side folds to a scalar, so it is in the product sector and not strong
  (`gauge_pair_is_product_sector`). For even `n` the last party's `v^n` also folds to a scalar.
- Neither substrate condition is the information condition of §4. `^ | v` is not "about" any question.
  Showing that an encoding of a cooperative history closes **iff** its question is resolved is CC4.

---

## 4b. CC1 — the analogical listener (proved)

An analogy `A : B :: C : ?` is a **partial correspondence** from a source relational structure to a
target one (one binary relation each, finite). Its unmapped source elements are its **open
obligations**. It **closes** when no obligation is open and every source relation is carried exactly
onto the target. It is **rejected** when no extension closes.

| Theorem | Statement |
|---|---|
| `extend_le`, `extend_keeps` | Filling an obligation never rewrites an established mapping. |
| `closed_preserves` | A closed analogy carries every source relation onto the target. |
| `consistent_extend_iff` | Filling one obligation keeps consistency **iff** a local check against the element itself and everything already mapped passes. A listener can grow one contribution at a time, and each contribution is checked against what is there, not re-checked from scratch. |
| `not_consistent_iff` | An invalid correspondence has a concrete counterexample: two mapped elements whose relation is not carried. Consistency is decidable on finite structures. Rejection (no closed extension exists) is not decided by anything in the module. |
| `open_not_closed`, `closed_has_no_obligation` | An analogy with an open obligation is not closed, so it is never promoted to a validated correspondence. |
| `inconsistent_persists`, `inconsistent_rejected` | Inconsistency survives every extension of that branch, so an inconsistent branch is rejected. A failed proposal does not invalidate its consistent parent or other branches. |
| `consistent_not_extendable`, `other_branch_closes` | **Consistency is not extendability.** Source edge `0 → 1`, target edge `1 → 2` with `0` isolated: mapping `0 ↦ 0` passes every local check yet no extension closes, while `0 ↦ 1` completes with `1 ↦ 2`. So `inconsistent_rejected` has no converse, and greedy growth by the local check can stall. |
| `extend_mapped_noop` | Offering a target for an element already mapped is a no-op, whatever is offered. It preserves the established mapping; it does not report a conflict. |
| `rutherford_closes`, `wrong_completion_rejected` | Worked case, a stipulated finite relation model rather than physical validation: sun : planet :: nucleus : ? closes with *electron*; filling it with *nucleus* is rejected (planet orbits sun, nucleus does not orbit itself). |
| `similarity_not_correspondence` | A map that matches every element's label perfectly can still fail to carry the relation. Similarity can guide the search; it is not a proof. |

**What it is worth.** These are properties of finite partial maps, standard in model theory. The
operational contract they give a Quantum-OS listener is narrow, and should be stated as narrowly:

- A proposal to fill an **open** slot of an **already consistent** map is accepted or refused by a
  local, decidable check. Passing it keeps the branch consistent; it does not promise the branch can
  close (`consistent_not_extendable`).
- A refused branch stays refused under extension, but the refusal is **branch-relative**: the parent
  and other branches are untouched.
- A conflicting offer for an already mapped element is silently ignored by `extend`. Detecting and
  reporting it is a separate check, not defined here.
- Nothing with an open obligation is called closed.
- `Closed` is exact agreement of the relation on every source pair under a total map. It imposes no
  injectivity or surjectivity: not an isomorphism, not unique, not covering the target.

CC6's cooperative contradiction policy (resolve rather than average) is **not** established by this;
§4 keeps it open. Not done here: competing analogies listening concurrently, higher-order analogies whose
elements are closed analogies (CC8), and any encoding of a listener as a twist history (CC4).

---

## 5. Gates not yet proved

| Gate | Status | Note |
|---|---|---|
| Constructive closure | Partly addressed | The Need → Offer → Commitment step is closure selection: choose offers so that an obligation closes. [`QLF_ClosureSelection`](lean/QLF_ClosureSelection.lean) `selection_closes_iff` decides it in polynomial time in what is written ([Framing.md](Framing.md) §4a), for conservation of written counts only. Fulfilment and acknowledgement are outside the substrate and stay empirical. |
| CC4 semantic → ZFA | **Open bridge** | Needs `Encode : CooperativeHistory → QLFHistory`, fixed independently of the verdict, with soundness and completeness on a declared domain. An encoding that runs an external verifier and emits a balanced or unbalanced word is an encoding of verification, not a QLF mechanism. Until CC4 holds, Quantum-OS results are QLF-inspired verification, not QLF-derived closure. |
| CC5 free action vs free energy | **Open bridge** | QLF's per-closure `ΔF = −log 2` ([`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)) is not Friston's variational free energy. No identity is claimed. |
| CC7 first cooperative closure | Partly addressed | `coalitionResolves_iff` shows resolution is invariant under repetition, popularity and member count. Ordering relative to a schedule without a global "now" (per [Coincidence_QLF.md](Coincidence_QLF.md) and #281) is open. |
| CC8 hierarchy | Open | `closure_hierarchy_strict` ([`QLF_LawOfExceptions`](lean/QLF_LawOfExceptions.lean)) gives a strict capacity hierarchy; the bridge from a finite cooperative resolver to a finite restrictive closure is the same missing step as CO4 in #283. Failure within a budget is not impossibility. |
| CC9 observer-independent verdict | Bookkeeping | `countBalanced` is decidable, so anyone recomputing a certificate gets the same verdict. That is true of any decidable checker and says nothing QLF-specific. |

Related: [Diversity_Composition_QLF.md](Diversity_Composition_QLF.md) (D8a, cross-type composition)
is the diversity thread on the substrate; CC6 here is its information-theoretic counterpart.

---

## 6. Corrections to the proposal this program started from

The initiating proposal was read as a plan, not a specification. Where it does not hold as stated:

1. **"Separately originating information can participate in a joint closure inaccessible to any
   individual origin."** On the bare substrate this is CO0-trivial. It has content only with holders
   fixed in advance (§1), which `star_irreducible` respects.
2. **CC2 asked whether `StrongCoIncides` is the right representation.** It is not, on its own: it is
   two-origin and algebraic, and irreducible closure can lie in the product sector (§4a).
3. **The XOR witness uses no QLF.** It is information theory. It proves cooperative synthesis in that
   sense; it does not show that QLF closure selects it. That is CC4.
4. **CC0 and CC3 are largely definitional.** That is stated rather than hidden (§2, §3). Their value
   is to fix the measure (origins, observation) against which Quantum-OS claims can be tested.
5. **Agreement on `/solve` is logical closure, not empirical closure.** Quantum-OS rooms that compute
   the same `/solve` on a joint position agree on a computed closure ([QucalcSearch.md](QucalcSearch.md)).
   By CC0 that agreement is not evidence about the world unless an observation is in its provenance.
   Docs that read a room's shared closure as validated truth should say so.

---

## 7. Relation to azoth PR #82

[PatrickMockridge/azoth#82](https://github.com/PatrickMockridge/azoth/pull/82) ("Add the intake
review", merged 2026-11-26) adds an intake dossier of sources, claims and bindings, and a
deterministic checker that splits gaps into **hard** (target refused) and **soft** (a licensed rule or a
lower source rung, flagged and run), with a four-role agent team (reader, clerk, assessor, auditor). Its
auditor is told the review is "clerical, not a proof that the quoted number is the right physics."

It uses none of QLF's vocabulary (no listener, closure, ZFA or consensus). The relation is structural:

- A dossier with source rungs is a **provenance record** (CC3), and refusing a target on a conflicting
  pair of sources is the operational form of "consensus does not override a contradiction" (CC0).
- Hard and soft gaps are **open obligations** with a rejection predicate, close to what CC1's
  listener needs.
- Its own disclaimer is the CC4 distinction: a clerical check of inputs is verification, not a
  derivation of the result.

It is a useful prior example for the Quantum-OS side, specifically the certificate and lifecycle
(QOS4–QOS5 in the proposal). It does not bear on the QLF proofs.

---

## 8. Where to go next

1. CC1 extensions: concurrent competing listeners, multiple relations, and listeners whose elements
   are closed listeners (the CC8 hierarchy).
2. An `n`-origin `StrongCoIncides` and a census of how many irreducible `k`-party closures are strong.
3. CC4 on a toy domain: an encoding of parity-resolution histories into twist words, specified before
   checking, with a stated soundness or completeness verdict (either outcome is a result).
4. The Quantum-OS side, as an issue there: cooperative listener, provenance graph, certificates and the
   five-arm experiment, kept separate from the frozen `quantum-os#322` controller experiment.
