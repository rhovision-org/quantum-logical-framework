# RhoCorrespondence — theorem target

**Status:** `NOT_STARTED`. This is a specification, not a proof. No `sorry` is added to the repository.

## Why

`Strange_Loops.md` §2B gives an explicit structural analogy between QLF events and reflective
ρ-calculus/Rholang communication:

- name = capability;
- read/write authority = listener/trigger polarities;
- event = successful capability match producing closure;
- join = multi-resource match;
- quote/drop = behavior → name/capability → behavior.

That analogy is not a formal embedding. This target states what a complete relation would have to prove.

## Fixed sides

**QLF side.** Histories `H`, open actions/histories `A, B`, composition `∘`, free-action functional
`Z : H → ℕ` (or the appropriate algebraic codomain), closure predicate `Z(h) = 0`, and the physical
closure equivalence `~` used by the claim records.

**ρ side.** A fixed presentation of pure reflective higher-order ρ-calculus: processes `P`, names `N`,
nil `0`, parallel `P | Q`, input `for(ptrn <- n).P`, output `n!(Q)`, restriction `new n in P`,
replication `*P`, quote `@P`, drop, and the reduction relation `P → P'`. Rholang bundle syntax is a
programming-language illustration, not the formal target.

## Required maps

```
Φ : QLF.History → Rho.Process
Ψ : Rho.Process → Option QLF.History
```

`Φ` should be structure-preserving on the intended fragment; `Ψ` need not recover raw syntax, only the
closure-relevant equivalence class (compare `TensorConservativeReturn`).

## Obligations

1. **Soundness.** If `Z(h) = 0`, then `Φ(h)` reduces to a completed/nil process (or the specified
   success predicate).
2. **Completeness.** If `Φ(h)` reaches the success predicate, then there is `h' ~ h` with `Z(h') = 0`.
3. **Join.** `Z(Σ_i h_i) = 0` iff the corresponding join context fires with all required resources.
4. **Reflection.** `Φ(@P)` and `Φ(*P)` correspond to quote/drop, with the same level-crossing behavior;
   no event-time loop is introduced.
5. **Capability polarity.** Read and write authority map to listener and trigger roles; a single
   authority alone is not an event.
6. **Conservativity.** The translation adds no closures and loses no closure-relevant facts.
7. **Bisimulation / equivalence.** State the equivalence (strong, weak, or a purpose-built closure
   equivalence) and prove the relevant preservation result.
8. **No scheduler.** The translation has no external scheduler; matching is internal to the process
   configuration.

## Non-goals

- Proving that QLF is *the same as* Rholang or pure ρ-calculus.
- Treating the Rholang bundle syntax as a formal semantics without a fixed presentation.
- Recovering every microscopic history from a process; the return is on closure equivalence classes.
- Claiming empirical support or closing G3.

## Relation to the claim records

This target is formal-only. It does not change any `bridge: B-OPEN` status, `strange_loop.status`, or the
343-anchor baseline. Until the theorem exists and is reviewed, the ρ-calculus relation remains an
explicit structural analogy, not a complete correspondence.

## Current artifacts

- [`lean/RhoQuCalc.lean`](../../lean/RhoQuCalc.lean) — ρ-process algebra, Hermitian structure, ZFA stability.
- [`BraKetRhoQuCalc.md`](../../BraKetRhoQuCalc.md) — action/lift (send/receive) reading.
- [`zfa-catalog-rho-notation.md`](../../zfa-catalog-rho-notation.md) — Rholang-style ZFA notation.
- [`Strange_Loops.md`](../../Strange_Loops.md) §2B — the analogy and its status.
