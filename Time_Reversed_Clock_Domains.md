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

## Two-way age-counting hypothesis

Jim suggests that Gupta may include both temporal directions in the quoted age. Locate an explicit source equation or author intermediate before attributing such a sum to the model: the inspected equation 50 is a single age integral. A signed reversal and a sum of positive elapsed durations are different operations. The rough ratio of the quoted ages alone does not establish either. Preserve this as an unverified source-audit hypothesis and do not alter the frozen benchmark to enforce it.
