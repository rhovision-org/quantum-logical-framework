# Perspective Holography — Stage C Audit

Issue: [#296](https://github.com/rhovision-org/quantum-logical-framework/issues/296)  
Implementation: [Draft PR #300](https://github.com/rhovision-org/quantum-logical-framework/pull/300)

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

## Next Lean targets (not yet implemented)

1. **Closure preservation:** boundary/record construction must not identify an open history with a ZFA closure when closure verdict is part of the record.
2. **Factorization criterion:** prove the finite/general factorization criterion `D(h₁)=D(h₂) → O(h₁)=O(h₂)` iff a reconstruction map exists, with a concrete counterexample.
3. **Overlapping blankets:** define a non-circular shared-observable interface and prove compatibility for the existing frame-invariant closure/Pauli observables before assigning physical meaning to blankets.

## Decision

**Stage C finite surrogate: implemented and locally focused-tested.** The physical blanket semantics, justified observable algebra, and Lean formalization remain open. Do not promote this result to a holography claim or cosmic metric reconstruction.
