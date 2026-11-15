# RhoCorrespondence — theorem target

**Status:** `NOT_STARTED`. This is a specification, not a proof. No `sorry` is added to the repository.

## Why

`Strange_Loops.md` §2B gives an explicit structural analogy between QLF events and reflective
ρ-calculus/Rholang communication:

- a protected/unforgeable name can serve as a capability;
- read/write authority = listener/trigger polarities;
- a binary event = successful capability match producing closure;
- join = multi-resource match;
- quote/drop = behavior → name/capability → behavior.

That analogy is not a formal embedding. This target states what a complete relation would have to prove.
The central object is **binary**: a closed history alone is too weak, because a process might reduce for
an unrelated reason. The theorem must connect *two complementary open actions* to one communication.

## Fixed sides

**QLF side.** Histories `H`, open actions/histories `A, B`, composition `∘`, free-action functional
`Z : H → ℕ` (or the appropriate algebraic codomain), and the closure predicate

```
Close(A, B)  :=  Z(A ∘ B) = 0.
```

The physical closure equivalence is `~`.

**ρ side.** A fixed presentation of pure reflective higher-order ρ-calculus: processes `P`, names `N`,
nil `0`, parallel `P | Q`, input `for(ptrn <- n).P`, output `n!(Q)`, restriction `new n in P`,
replication `*P`, quote `@P`, drop, and the reduction relation `P → P'`. Rholang bundle syntax is a
programming-language illustration, not the formal target.

## Required maps

```
Φ : QLF.History → Rho.Process
Ψ : Rho.Process → Option QLF.History        (partial return)
```

`Φ` should be structure-preserving on the intended fragment; `Ψ` need not recover raw syntax, only the
closure-relevant equivalence class (compare `TensorConservativeReturn`).

## Success and `↓`

The target must say exactly what “success” means. Define a predicate `Success(P)` on processes and write

```
P ↓  :=  ∃ P', P →* P' ∧ Success(P')
```

for **eventual** success after a finite number of reductions—not a single reduction, not mere weak
termination, and not “some process anywhere can reduce.” The residual process and `Success` predicate
are part of the specification. A separate one-step theorem is optional and would be stronger.

## Core obligations

1. **Binary soundness.** `Close(A, B) → ∃ P', Φ(A) | Φ(B) →* P' ∧ Success(P')`.
2. **Binary completeness.** If `Φ(A) | Φ(B) →* P'` and `Success(P')`, then there exist `A' ~ A` and
   `B' ~ B` with `Close(A', B')`. This rules out a reduction that succeeds for an unrelated reason.
3. **Return.** `Ψ(P') = [A ∘ B]_~` on the closure-relevant quotient; `Ψ` is well-defined on the chosen
   bisimulation class. The raw pair need not be recovered.
4. **Join.** For open actions `A₁,…,Aₙ`,
   `Close(A₁,…,Aₙ)` iff the corresponding join context fires with all required resources.
5. **Reflection.** `Φ(@P)` and `Φ(*P)` correspond to quote/drop, with the same level-crossing behavior;
   no event-time loop is introduced.
6. **Capability polarity.** A protected name can serve as a capability; read and write authority
   attenuate it into listener and trigger roles. A single authority alone is not a binary event.
7. **Conservativity.** The translation adds no closures and loses no closure-relevant facts.
8. **Bisimulation / equivalence.** State the equivalence (strong, weak, or a purpose-built closure
   equivalence) and prove the relevant preservation result. The binary theorem must be stable under it.
9. **No semantically privileged scheduler.** The reduction rule requires no privileged external
   scheduler; an implementation may still choose a schedule.

## Why a formal connection is plausible

The finite QLF event layer is a good target for a ρ encoding:

- a history is a finite word; names can encode axes and messages can encode twists;
- a per-axis ZFA gate can be represented as a join over axis counters (QKB's `scan` is an executable
  sketch of this);
- `ask`/`answer`/`solve` already has the listener/trigger/reduction shape at the knowledge level;
- reflective ρ supplies quote/drop, the natural candidate for self-query.

This makes a formal connection **plausible**, not automatic.

## Universality is not adequacy

A universal process calculus can encode both faithful and unfaithful translations. The existence of
*some* encoding proves only expressiveness. A correspondence theorem still needs the specified encoding,
soundness/completeness, conservativity, a chosen bisimulation, and the no-scheduler result.

## Self-query obligation

A QKB query is a rendezvous, not automatically a strange loop. For a self-query loop, add:

10. **Self-query.** The question representation can name the KB's own state/query process, and the
    answer can update the listener's future question/capability set under a stated authority.
11. **Conservative self-return.** The self-model returns to the finite records on the closure-relevant
    equivalence class: `R(F(records)) ~ records`.

Both are `NOT_STARTED`. The current QKB design is first-order and does not implement them.

## Non-goals

- Proving that QLF is *the same as* Rholang or pure ρ-calculus.
- Treating the Rholang bundle syntax as a formal semantics without a fixed presentation.
- Recovering every microscopic history from a process; the return is on closure equivalence classes.
- Claiming empirical support or closing G3.

## Relation to the claim records

This target is formal-only. It does not change `evidence_status.bridge = OPEN`, `strange_loop.status =
B-OPEN`, the `G3 = INCOMPLETE` or `G5 = INCOMPLETE` gate outcomes, or the 375-anchor baseline. Until the
theorem exists and is reviewed, the ρ-calculus relation remains an explicit structural analogy, not a
complete correspondence.

## Current artifacts

- [`lean/RhoQuCalc.lean`](../../lean/RhoQuCalc.lean) — ρ-process algebra, Hermitian structure, ZFA stability.
- [`BraKetRhoQuCalc.md`](../../BraKetRhoQuCalc.md) — action/lift (send/receive) reading.
- [`zfa-catalog-rho-notation.md`](../../zfa-catalog-rho-notation.md) — Rholang-style ZFA notation.
- [`Strange_Loops.md`](../../Strange_Loops.md) §2B — the analogy and its status.
