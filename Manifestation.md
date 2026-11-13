# Manifestation — orientation, isolation, unbounded closures, distance = delay, and the proton

**Status:** formal result (**F** at the collaborator assurance tier), not a physical validation.
**Module:** [`lean/QLF_Manifestation.lean`](lean/QLF_Manifestation.lean)
**Audit anchors:** twelve `QLF.Manifestation.*` entries in
[`lean/axiom_footprints.expected.json`](lean/axiom_footprints.expected.json)
(current baseline: 344 anchors). The module also proves
`closures_at_least_eight_pow`; it is part of the module but is not a separate
baseline entry.
**Merged by:** PR #226.

This page is the companion document for the Manifestation module. It says what the
module proves, what it does **not** prove, and how it should be cited. It is a
claim-map entry and a formal result, not evidence for a physical selection
mechanism, a detector model, or an empirical QLF prediction.

## What is proved

The module proves a set of finite statements about ZFA closure histories and the
substrate walk. The exact theorem statements and their dependencies are in the
module and the audit baseline; the groups are:

### 1. Orientation

- `completion_net_determined` — every completion of a history must supply the
  same signed action.
- `completion_not_unique` — there is more than one way to supply it.

The content is structural: the completion condition fixes a net, not a unique
history. It does not assert that nature selects one completion, nor that the
selection is physically observable.

### 2. Isolation is closure

- `isolated_iff_closed` — a part is isolated exactly when it is closed.
- `isolation_interleaved` — the equivalence still holds when its events are
  interleaved with the environment's.
- `closed_insertion_is_phase` — inserting a closed part anywhere changes the
  rest by only a global Pauli phase.

This is a statement about the substrate's closure algebra. It is not a claim
that a laboratory qubit is isolated, nor a derivation of decoherence or error
correction thresholds.

### 3. Unbounded complexity

- `closures_unbounded` — the closure count is unbounded.
- `prime_closure_every_length` — a prime closure exists at every even length.
- `closures_at_least_eight_pow` — at least `8ⁿ` closures of length `2n`.

The result is combinatorial. It does not claim that complexity, life, or minds
follow, and it does not identify the count with a physical entropy or a
probability measure.

### 4. Distance equals delay

- `delay_ge_distance` and `distance_eq_delay` — the shortest completion of a
  history has exactly the ℓ¹ norm of its signed action.

This is an identity in the substrate's distance/delay bookkeeping. It is not a
measurement of a laboratory distance or a derivation of the metric; the
metric-singlet/lattice-Einstein result is a separate representational theorem
under its own premises.

### 5. Selection and rearrangement

- `same_niches_iff_sameNet` — two variants are admitted by the same niches exactly
  when they have the same net.
- `rearrangement_neutral` — reordering within a net does not change the selection.
- `short_closures_unwound` — short closures are unwound in the stated sense.

These are structural selection statements. They do not assert a biological or
cognitive selection mechanism.

### 6. The proton as the simplest isolated imbalance

- `proton_simplest_isolated_imbalance` — no closure shorter than six carries
  baryon winding; the proton word closes at six with winding +1.
- `proton_ways_unbounded` — the proton closes in unboundedly many ways.

Here "proton" names a closure word with baryon winding in the substrate model.
It is **not** a QCD derivation of the physical proton mass, radius, or structure.
The result is a formal structural statement, not a particle-physics measurement.

## What this changes

The module gives the `Theory_Of_Everything.md` index's "two a priori solutions"
and proton ladder a formal backbone. It also gives Paper I v0.3 a second kind of
formal development beyond MO2: the claim map can point to exact named theorems,
and the audit can record their footprints.

## What this does not change

- **G3 (physical bridge):** still open. There is no ZFA-history-to-detector map,
  no operational probability law, and no apparatus model for these results.
- **G5 (empirical adequacy):** still open. No independent or prospective test is
  supplied, and no QLF-specific discriminating prediction follows from the module
  alone.
- **G6 (receipt):** the audit footprint is collaborator-tier project CI; it is not
  an independent third-party certificate.
- **The ToE narrative:** the index remains a map, not evidence. "Orientation,"
  "isolation," "complexity," "distance = delay," and "the proton" are formal
  structural statements here; their physical readings are `B-OPEN`.

## How to cite

Cite the module and the exact theorem names, not the headline words alone:

> `QLF.Manifestation.isolated_iff_closed`, `QLF.Manifestation.distance_eq_delay`,
> and the other twelve anchored theorems in `lean/QLF_Manifestation.lean`
> (reviewed project-CI footprints; 344-anchor baseline).

For a physical claim, cite the bridge record or state the missing map explicitly.
A formal theorem is not a physical result by association.

## Related

- [`Theory_Of_Everything.md`](Theory_Of_Everything.md) — the claim map.
- [`Proof_to_Physics.md`](Proof_to_Physics.md) — the evidence registry.
- [`Claim_Status.md`](Claim_Status.md) — the status ledger.
- [`Paper_I_v0.3_Handoff.md`](Paper_I_v0.3_Handoff.md) — current paper status.
- [`Einstein_Equations.md`](Einstein_Equations.md) §6d–§6e and
  [`lean/QLF_MetricSinglet.lean`](lean/QLF_MetricSinglet.lean),
  [`lean/QLF_LatticeDivergence.lean`](lean/QLF_LatticeDivergence.lean) — the
  separate metric-singlet/lattice-Einstein representational result.
