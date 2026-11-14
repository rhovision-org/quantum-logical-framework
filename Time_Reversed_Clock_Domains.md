# Time-reversed clock domains: a proof program

[QLF](README.md) · [Theory index](Theory_Of_Everything.md) · [Gupta program](Gupta_CCC_TL.md) · [Clock conventions](Gupta_ClockConventions.md)

**Status: proposed physical correspondence, B-OPEN.** Tracked in [issue #236](https://github.com/rhovision-org/quantum-logical-framework/issues/236). Jim proposes that our matter-world time perspective has a reversed antimatter counterpart: each side experiences events through its own local clock, while a joint closure relates the two. A horizon-like boundary would prevent reconstruction of the counterpart's internal history from our records. These physical identifications are research targets, not existing theorems.

This is separate from the external Gupta numerical benchmark. Proving or excluding the correspondence is needed before using it to explain the age difference; reproducing Gupta's equations does not depend on it. No numerical age is selected by this proposal. Pure order reversal preserves duration magnitude, so an age difference also requires a derived clock-rate or origin/count relation.

## Existing finite algebra

In [QLF_ClosureUnitarity](lean/QLF_ClosureUnitarity.lean), `dagger`, `fold_dagger`, `closure_by_dagger` and `countBalanced_append_dagger` give a conjugate-reverse completion of every finite twist history. [QLF_Majorana](lean/QLF_Majorana.lean) defines the same word operation as `antiparticle` and proves `antiparticle_involutive`.

These are concrete starting points. They do not identify the word operation with physical time reversal, establish two universe histories, or prove that dagger completion is the only possible completion. In particular, destructive interference of existing histories is different from absence of histories; the closure module explicitly distinguishes these cases.

## Obligations and falsifiers

| Target | Required result | What would defeat or limit it |
|---|---|---|
| Event-history objects | Finite labeled event orders, local clock records and a joint-closure relation, with nontrivial examples | An unconstrained interface satisfied by every history carries no physical selection |
| Reversal map J | Involution; order reversal across domains; monotone clock readings within each domain's own orientation | Word reversal alone does not establish these properties of physical event orders |
| Antimatter identification | Define the relevant charge/baryon labels; show how J transforms them while preserving the specified closure invariants | Charge conjugation and time reversal must not be identified by naming alone |
| Event pairing | Relate paired events to a joint ZFA closure; state whether pairing is sufficient or necessary, and whether it is unique | Other admissible completions defeat uniqueness; an unpaired closed event defeats an asserted necessity |
| Boundary observation | Define O from paired histories to finite records available on our side | An observation map chosen constant makes information hiding automatic and physically empty |
| Reconstruction obstruction | Exhibit distinct admissible counterpart histories with identical accessible records, hence no exact inverse on that class | Distinguishing records refute that equivalence; noninjectivity alone is not universal computational unconstructibility |
| Causal noninterference | Specify allowed counterpart interventions and prove the accessible-record invariance claimed under them | Inability to reconstruct is weaker than no influence or no signalling; test each claim separately |
| Boundary exchange | Define a candidate horizon-emission/absorption channel and show its compatibility with joint closure | Separate clocks do not imply causal isolation. An “only Hawking-type exchange” claim requires exclusion of every other allowed channel |
| Age bridge | Derive clock normalization, start surface and accumulated event/count relation without fitting either age | J by itself gives opposite orientation, not a factor of roughly two in elapsed age |

## First proof milestones

1. Reuse the finite dagger/involution results to construct a nontrivial paired-history model, keeping physical labels explicit.
2. Prove a finite observational nonidentifiability lemma: if distinct admissible histories have the same O-record, O has no exact left inverse on that class. Then construct a meaningful boundary model that actually satisfies its premise.
3. Separate this from causal noninterference and from the physical horizon interpretation. State assumptions and counterexamples before any physical promotion.
4. Only then connect to the clock-convention program and compare operational ages. Neither 13.8 nor 26.7 Gyr is an input for selecting J or the boundary map.

Formal identities, the physical correspondence and empirical evidence require separate verdicts. A successful toy model establishes one realization; it does not establish that our world realizes it. No new dynamics, framework rule adoption or physical conservative return is asserted by this plan.

## Frozen first implementation target: finite accessible records

The first Lean target is a concrete closure-only boundary model, before imposing a unique reversal partner. Let a history be a pair of finite twist lists `h = (p, q)`, admissible exactly when `countBalanced (p ++ q)`. Freeze the accessible record as `O(p, q) = (p, q.length)`: our full local word and the counterpart's aggregate length are accessible, but the counterpart's internal order is not. This is an explicitly chosen toy interface, not a derived physical horizon. It has no adjustable numerical parameters.

Use the following witnesses, in the alphabet of [QLF_TwistAlphabet](lean/QLF_TwistAlphabet.lean):

- `p = [up]`, `q₁ = [down, left, right]`, `q₂ = [down, right, left]`.
- Both concatenations are count-balanced, `q₁ ≠ q₂`, and both records are `([up], 3)`.
- `([up], [down])` is also admissible, with a different record `([up], 1)`. Thus O is nonconstant even with the local word fixed.

The first proposed statements are admissibility of these witnesses, equality of their records, inequality of their counterpart words, nonconstancy of O, and the absence of an exact reconstruction function `R` satisfying `R(O(p,q)) = q` for every admissible pair. The last result follows because R would have to return both q₁ and q₂ for the same input. These statements are implemented in [QLF_ClockDomains](lean/QLF_ClockDomains.lean), with kernel verification and exact-axiom CI pending. Acceptance requires kernel verification and the repository's exact-axiom audit before adding theorem anchors or changing status to **partial algebra, still B-OPEN**.

This model establishes non-identifiability only for the stated record interface and admissible class. A stricter class could exclude a witness. In particular, imposing `q = dagger p` makes the counterpart reconstructible from p and defeats this example. No no-signalling conclusion follows: O deliberately exposes length, so a permitted length-changing intervention could affect the record. Allowed interventions and their invariances need a separate model.

## Alternative completions and fixed points

For `p = [up]`, the canonical dagger completion is `[down]`, but `[down, left, right]` and `[down, right, left]` also give count-balanced concatenations. Thus count-balance alone neither requires the canonical dagger completion nor selects a unique counterpart. These examples do not refute uniqueness under stronger, independently justified conditions such as a fixed length, fixed central phase or prescribed event pairing; those conditions must be stated and tested separately.

Involution also does not imply fixed-point freedom: [QLF_Majorana](lean/QLF_Majorana.lean) already proves that `[up, down]` is fixed by conjugate reversal. A general two-element-orbit counting theorem therefore needs an explicit fixed-point-free hypothesis or a correction for singleton orbits. Adding domain tags can enforce distinct partners in a toy construction, but does not derive a physical doubling of the event census.

## Two-way age-counting hypothesis

Jim suggests that Gupta may include both temporal directions in the quoted age. Locate an explicit source equation or author intermediate before attributing such a sum to the model: the inspected equation 50 is a single age integral. A signed reversal and a sum of positive elapsed durations are different operations. The rough ratio of the quoted ages alone does not establish either. Preserve this as an unverified source-audit hypothesis and do not alter the frozen benchmark to enforce it.

The candidate is `T_Gupta = T₊ + T₋`, with positive durations `T₊ = T₋`, and our operational age identified with T₊. Conditional on these premises, `T_ours = T_Gupta / 2`; the stored stage-1 present age would give approximately 13.3336059294 Gyr. This is retrospective arithmetic on a known baseline, not an independently selected QLF age. Equal durations for an exact reversal pair do not establish that Gupta's integral counts both members. The correspondence must also distinguish paired events from twice-counted descriptions of one event and justify a common tick normalization.

**Hard age-interpretation gate:** before this proposal may explain the Gupta age difference, derive a clock-rate, start-surface or accumulated-count relation on finite records, with operational units and a stated approximation error, and show how the source integral maps to it. The [stage-2 clock conventions](Gupta_ClockConventions.md) must be reviewed and frozen before applying that map. A free scale, an unsigned derivative or the existence of a reversed copy does not discharge this gate. Outcomes remain derived, permitted-but-underdetermined, or incompatible-within-the-frozen-class.

Gupta's benchmark uses fitted external inputs; its numerical reproduction does not make them QLF-derived. The comparison ΛCDM age is likewise model-dependent and uses a smooth FLRW description. These approximation limitations do not supply an error bound or establish the proposed factor of two. Jim has authorized exploring the hypothesis despite the unresolved Table 1 precision residual; that exploratory decision neither resolves the residual nor adopts the physical map. The frozen artifacts and tolerance remain unchanged.

## Independent review record

[Grok's review and disposition](verification/time-reversed-clock-domains/grok_review.md), relayed by Jim on 14 November 2026, finds the issue appropriately scoped and requests the explicit age gate, alternative completions and a concrete non-identifiability target. Those requirements are specified above. The first finite record implementation is present; kernel verification remains pending; the correspondence remains **B-OPEN**.
