# SelfKnowledgeBisimulation — theorem target

**Status:** `NOT_STARTED`. This is a specification, not a proof. No `sorry` is added to the repository.

## Why

`Strange_Loops.md` §3A gives the observer as a finite self-model; §3B adds the missing update and
faithfulness criteria:

- active inference supplies a candidate update/policy rule;
- bisimulation supplies a candidate criterion for the model faithfully tracking the system.

Neither is proved for QLF, and the QLF free-energy derivation is currently informal
(`Hierarchical_Control.md` §3 flags the Lean step as open).

## Active-inference update

```
b_t          internal belief/model state
o_t          boundary observation / closure record
a_t          action / capability use
b_{t+1} = U(b_t, o_t, a_t)
a_t ≈ argmin_π G(π; b_t)
```

Obligations:

1. `U` is finite/computable and returns to finite closure records.
2. `o_t` is a boundary record, not a target-derived value.
3. `a_t` is a capability use, not an external command.
4. `G` is specified; if it is the QLF free-energy functional, the derivation must be formalized.
5. Policy selection is internal; there is no external scheduler.
6. The update preserves the closure-relevant invariants (conservative return).

## Self-knowledge as bisimulation

Let `S` be the system transition system with labels for observations, actions and closure events; let
`M` be the internal model transition system. A candidate definition:

```
M  ~_c  S|_c
```

where:

- `~_c` is a chosen bisimulation (strong, weak, branching, or purpose-built);
- `S|_c` is restricted to closure-relevant labels;
- there is an embedding `ι : M → S` preserving the relevant transitions;
- `M` can name/quote its own boundary and query process.

Obligations:

7. **Embedding.** `ι` maps model states to system states and preserves closure-relevant labels.
8. **Bisimulation.** `~_c` is proved, not assumed; the choice of equivalence is stated.
9. **Self-reference.** `M` can quote/name itself (reflection), not merely model an external world.
10. **Update preservation.** If `M_t ~_c S_t`, then `M_{t+1} ~_c S_{t+1}` after `U`/`step`.
11. **Conservativity.** The model adds no closure-relevant facts and loses none.
12. **No event-time loop.** The self-query/update loop is a loop in possibility/representation, not a
    realized event-time cycle.

## Non-goals

- Defining self-knowledge as `M = S`.
- Treating a universal encoding as a faithful self-model.
- Using a bisimulation that is so coarse that any process satisfies it.
- Promoting active inference or QLF's free-energy derivation to a formal theorem without the Lean step.
- Claiming empirical evidence or closing G3.

## Relation to QKB (PR #216)

QKB's `ask`/`answer`/`solve` can be read as one transition system. It is a candidate listener/trigger
layer, not a self-model: its questions are first-order, it has no quote/drop self-query, and it has no
belief-revision layer. PR #216 is an open draft and is not in the 344-anchor baseline.

## Current artifacts

- [`Strange_Loops.md`](../../Strange_Loops.md) §3A–§3B — observer loop, active-inference update and
  bisimulation criterion.
- [`Hierarchical_Control.md`](../../Hierarchical_Control.md) §3 — informal QLF free-energy derivation;
  Lean step open.
- [`Active_Inference_Mathematics.md`](../../Active_Inference_Mathematics.md) — active-inference framing.
- [`rho_correspondence_target.md`](rho_correspondence_target.md) — the ρ-correspondence target and
  self-query obligations.
