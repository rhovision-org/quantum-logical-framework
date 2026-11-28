# Perspective Holography — Stage C Audit

Issue: [#296](https://github.com/rhovision-org/quantum-logical-framework/issues/296)  
Implementation: [PR #300](https://github.com/rhovision-org/quantum-logical-framework/pull/300)

## Scope and epistemic status

Stage C extends the Stage B finite surrogate by reporting component-wise reconstruction and concrete collision witnesses. Blanket records still consist only of projections of signed action coordinates. This is **not a physical Markov-blanket model**, does not encode causal accessibility, and is not a physical counterexample to holography.

The first three closure-aware record fields (closure verdict, unnormalized action, ordered Pauli fold) are reuse targets from existing QLF formal/algebraic foundations. This experiment adds no Lean theorem. Lean/Lake are not installed on the current remote (`lean` and `lake` both unavailable), so proof status remains unverified by compilation here.

## Experiment

- Enumerate ZFA leaves of length 4, then their non-empty prefixes: **408 histories** in the sample.
- Two overlapping action-coordinate blankets: `(0,1)` and `(1,2)`; shared coordinate **1**.
- Audit factorization of full action and full Bloch observable, plus each action component and each Bloch component, through each surrogate record.
- Every failure now returns concrete histories, the common boundary record, and the differing observable values.

## Results

| Blanket | Full action | Bloch vector | Reconstructible action components | Reconstructible Bloch components |
|---|---|---|---|---|
| `B_vertical_horizontal` (0,1) | No | No | vertical, horizontal | none |
| `B_horizontal_depth` (1,2) | No | No | horizontal, depth | none |

The shared horizontal action coordinate is reconstructible by both screens on this sample; full action and all three Bloch components are not. Component audits are finite-sample statements only.

### Concrete counterexamples

- Full-action collision for both blankets: histories `+` and `++` share boundary `(0,0)` but actions differ: `(0,0,0,1)` vs `(0,0,0,2)`.
- Bloch collision for both blankets: histories `+` and `++--` share boundary `(0,0)` but Bloch vectors differ: `(0,0,-1)` vs `(0,0,1)`.

The witnesses demonstrate information loss in this chosen action-projection surrogate, not a failure of a derived physical holographic dictionary.

## Lean targets (now proved in [`QLF_PerspectiveHolography`](lean/QLF_PerspectiveHolography.lean))

1. **Factorization criterion:** `reconstructs_iff` proves `D(h₁)=D(h₂) → O(h₁)=O(h₂)` iff a reconstruction map exists, for any types; `not_reconstructs_iff` makes every failure a collision witness, which is what `factor_reconstruction` reports on a finite sample.
2. **Fold closure versus territorial ZFA:** `closure_verdict_reconstructible` proves only that the joint fold determines scalar fold closure. It does not determine the count-balanced ZFA event verdict: [QLF_TerritoryReturn](lean/QLF_TerritoryReturn.lean) proves `zfa_not_from_fold` (the empty history and a single gauge + have the same fold, different ZFA). The integer ledger suffices for territorial ZFA (`ledger_returns_zfa`). The dictionary must preserve that distinction.
3. **Overlapping perspectives:** `shared_respects_chain` is the non-circular shared-observable interface: an observable both records reconstruct is constant along every chain of histories that share a record in either one. On the two-body system, `single_body_perspectives_share_only_constants` shows the two one-body perspectives share only constant observables, while `joint_record_reconstructs` and `joint_record_minimal` show the joint fold is the coarsest record that reconstructs the full joint-closure test. `phase_blind_record_fails` is the collision for a record that drops the phase.

These are statements about record maps. A physical Markov blanket, causal accessibility and metric reconstruction remain open.

## Decision

**Stage C finite surrogate: implemented and locally focused-tested.** The generic factorization and two-body fold-closure Lean results are present after #305; the physical blanket semantics, territorial-ZFA-preserving accessibility, justified physical observable algebra and cosmic bridge remain open. Do not promote this result to a holography claim or cosmic metric reconstruction.
