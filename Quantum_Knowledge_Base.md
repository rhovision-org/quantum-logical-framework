# A quantum logical knowledge base in Rholang

**Status:** a design with an executable reference. [`qkb_reference.py`](qkb_reference.py) implements
every rule below and checks them against the repo's canonical engines ([`twist_core.py`](twist_core.py),
[`qucalc_search.py`](qucalc_search.py)); it runs in under a second and passes. The Rholang contract
[`rholang/QKB.rho`](rholang/QKB.rho) is the same design written for
[rholo](https://github.com/rhovision-org/rholo) and its `rho:qucalc:*` natives. **It has not yet been
deployed on a node.** Part of the [Quantum Logical Framework (QLF)](README.md).

ZFA here means what it means everywhere in QLF: equal and opposite quantum logical action, with zero
free energy left over.

---

## 0. In brief

A knowledge base for QLF has to store closures, not sentences. The memetics work
([`Memetics_QLF.md`](Memetics_QLF.md)) already settled what a closure can carry and where its record
must live. This design turns those results into a data model:

1. **A record is admitted only if it is a ZFA closure.** The gate is per-axis count balance, and Pauli
   closure then follows from `count_balanced_pauli_closed`. No opinion, weight or truth value is stored
   beside it. What is in the base is what closes.
2. **A concept is the set of distinct closures filed under one name.** The size of that set is the
   concept's **multiplicity**. In QLF a closure's frequency *is* its multiplicity, so "how often" is a
   count the base holds directly.
3. **Each closure carries the set of independent parties holding it.** Its size is the record's
   **redundancy R**. Memetics §5 found that a closure becomes a meme to the degree that third parties
   hold its record, and R is that degree, measured.
4. **A question is an open strand.** An answer is a continuation that closes it, and `solve` returns the
   first-reached closure among the recorded answers. It uses the same cascade as `qucalc_search.solve`,
   so every peer that reads the base gets the same answer.
5. **Propositions form the orthomodular lattice MO3** over the three spatial axes, and the gauge axis is
   a classical block. Two contexts are compatible exactly when their plaquette `a b a† b†` folds to `+I`.
   The base computes that fold rather than storing a table. It refuses to conjoin incompatible
   propositions instead of answering ⊥.

Multiplicity, redundancy and priority are three different statistics. The base keeps all three and
reports which one an answer is (§4), as the method's rule 3 requires.

**One finding came out of the design work.** rholo's `rho:qucalc:zfa` Bool checks count balance in
aggregate (`#even == #odd`), not per axis. At length 4 it admits **216 histories that do not close**,
for example `^^<<` (y = +2, x = −2), on top of the 168 that do. The contract therefore computes the
gate itself and uses the native call only for the phase (§3).

---

## 1. What already exists

| Piece | Where | What QKB takes from it |
|---|---|---|
| Closure records keep ≤ 1 bit; the which-way record lives in a third party; a meme is a closure held redundantly | [`Memetics_QLF.md`](Memetics_QLF.md) §2, §4, §5; Lean [`QLF_ClosureRenewal`](lean/QLF_ClosureRenewal.lean) | the attester set and R (layer 3); the decision to store no meaning beside the closure |
| Naming game: words = first closures, consensus always, first-reached words win | [`Memetics_QLF.md`](Memetics_QLF.md) §10–§13, [`meme_naming_game.py`](meme_naming_game.py) | `first` as the priority query |
| `/solve` cascade (least excursion → shortest → phase → lexicographic) | [`qucalc_search.py`](qucalc_search.py), [`QucalcSearch.md`](QucalcSearch.md) | `solve` (layer 4), copied exactly and checked |
| RhoQuCalc notation (closures as processes, `\|` and `*`) | [`zfa-catalog-rho-notation.md`](zfa-catalog-rho-notation.md), [`QuCalc.md`](QuCalc.md), [`rho_transpiler.py`](rho_transpiler.py) | nothing directly. That notation is Rholang-*style* and transpiles to Python, so it has no store and no attesters |
| MO2 realized by the substrate, orthomodular and not distributive | Lean [`QLF_QuantumLogic`](lean/QLF_QuantumLogic.lean), [`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md) | the logic layer, extended to the three spatial axes (MO3) |
| `rho:qucalc:zfa`, `grant`, `verify`, `fuse` natives; `qucalc.rho`, `syllogism.rho` | [rholo `rholang/src/system_processes.rs`](https://github.com/rhovision-org/rholo/blob/dev/rholang/src/system_processes.rs), [rholo `qucalc/`](https://github.com/rhovision-org/rholo/tree/dev/qucalc) | `zfa` for the phase, `grant` for content-addressed persistent ids |
| Master dictionary: one linear cell, failure never silent, identity-rooted names | [quantum-os `MasterDictionary.md`](https://github.com/rhovision-org/quantum-os/blob/main/MasterDictionary.md) | the one-cell state and the rule that every refusal is an answer |

The memes thread stalled because "every closure is a meme" is bookkeeping as an identity (Memetics §5).
QKB does not depend on that identity. It stores the quantities the memetics work showed are measurable:
the closure, its multiplicity, its holders and its priority.

---

## 2. Data model

Everything lives in one linear cell, which is consumed and restored on every write:

```
{ "records":   { id: { "twists": [Int], "phase": Int, "excursion": Int, "attesters": Set(name) } },
  "names":     { name: Set(id) },                       // a concept = its ways
  "questions": { q: { "seed": [Int], "context": Int, "answers": Set(id) } } }
```

- **`id`** is the uri `rho:qucalc:grant` mints, a blake2b-256 content address of the twists. The same
  closure asserted by two parties lands on one record. That is what lets R count holders instead of
  copies.
- **`twists`** use rholo's integers: `0 ^ 1 v 2 > 3 < 4 / 5 \ 6 + 7 -`. The axis is `t / 2`
  (y, x, z, gauge), and the sign is `+` iff `t` is even.
- **`phase`** is the Pauli scalar the fold lands on (`1` +I, `−1` −I, `2` +iI, `−2` −iI). On an admitted
  record it is always ±1, because count balance implies the fold is `±I`.
- **`excursion`** is the peak total free action along the history, `max_prefix(|y|+|x|+|z|+|g|)`. That
  is the capacity a horizon needs to hear the closure (`closedAtHorizon_iff_maxExcursion_le`).
- **`attesters`** holds unforgeable names. A caller passes its own (its `deployerId`). Only the holder
  of a name can pass it, so nobody can inflate R by naming someone else.

---

## 3. The gate, and the native that is too weak

`assert` admits a history iff its length is ≥ 4 and its signed action vector is zero on every axis.
Length 2 is excluded because all eight `t t†` fold to −I. They carry no bit to record (Memetics §3),
and `qucalc_search` uses the same minimum.

Self-check (a) in [`qkb_reference.py`](qkb_reference.py) enumerates all 4096 histories of length 4.
Exactly 168 pass the gate, matching [`Fredkin_QLF.md`](Fredkin_QLF.md), and every one folds to ±I.
Check (b) runs rholo's rule (`pauli_closed ∧ #even == #odd`, from
[`qucalc/src/lib.rs`](https://github.com/rhovision-org/rholo/blob/dev/qucalc/src/lib.rs)) over the
same 4096. It admits **216 more** histories that are not closures. `^^<<` is the simplest: both
sides fold to `I`, and two "positive" and two "negative" twists sit on different axes. The repo's
[`CLAUDE.md`](CLAUDE.md) already warns the TypeScript port against exactly this aggregate check.

So [`QKB.rho`](rholang/QKB.rho) computes the per-axis vector in Rholang (the `scan` contract, one pass,
which also yields the excursion). It takes only the phase from `rho:qucalc:zfa`. The native should
probably be fixed upstream. Per this project's rule for other repos, that would be an issue on rholo,
not a change made from here.

---

## 4. Queries, and which statistic each one is

| Query | Returns | Statistic |
|---|---|---|
| `assert(name, twists, attester)` | `{ok, id, ways, redundancy}` or `{ok: false, residual}` | a refusal carries the action vector still owed, so it is never silent |
| `ways(name)` | number of distinct closures under `name` | **multiplicity**, a count that is absolute, not capacity-relative |
| `redundancy(id)` | number of independent holders | **R**, how much of a meme the record is |
| `first(name)` | the closure under `name` reached first | **priority**: least excursion, then shortest, then phase, then lexicographic |
| `ask(q, seed, context)` | the residual action vector | what any answer must supply |
| `answer(q, cont, attester)` | as `assert`, for `seed ++ cont` | |
| `solve(q)` | the continuation of the first-reached recorded answer | priority, the same cascade as `/solve` |
| `compatible(p, q)` / `conjoin(p, q)` | Bool / proposition or `"incompatible"` | the logic layer, §5 |

Three things to keep straight:

- **Most ways is not first.** `ways` and `first` answer different questions, and the base never derives
  one from the other ([`MostWays_First.md`](MostWays_First.md), `depth_one_not_modal`).
- **Most held is a third statistic.** A record held by many parties need not be the first closure or a
  concept with many ways. Memetics §9 (T4) found records follow priority in the census, and the base is
  where that can be measured with real holders.
- **`solve` needs no prefix filter.** If a recorded answer has a recorded closing prefix, that prefix
  has no larger excursion and is shorter, so the cascade ranks it first anyway. Check (e) feeds every
  closure within depth 5, events and non-events alike, for five seeds. It recovers `qucalc_search.solve`
  each time. That check could have failed if the argument were wrong.

Composition is deliberately absent. Two closures concatenated are a closure (balance adds), so a
"compose" query would be true for every input. By rule 4 that is bookkeeping and would add nothing. For
the same reason the design does not use `rho:qucalc:fuse`: the syllogism's "middle term" is a pair
`+-` removed from a concatenation, which is a closure already.

---

## 5. The logic layer

A proposition is `bot`, `top`, or an atom `(axis, sign)`. Over the three spatial axes the atoms and
their complements (the opposite sign, which is the Hermitian conjugate twist) form **MO3**. That is the
orthomodular lattice with three incompatible pairs, the next one up from the MO2 that
[`QLF_QuantumLogic`](lean/QLF_QuantumLogic.lean) proves.

**Compatibility is read from the fold.** Contexts `a` and `b` are compatible iff the plaquette
`a b a† b†` folds to `+I`. For two different spatial axes it folds to `−I`, the π flux of
[`Closure_Walk.md`](Closure_Walk.md) §3, so they are incompatible. The gauge twists are `±I`, so a
gauge plaquette folds to `+I` with any axis and the gauge block is classical. In Rholang this is one
`rho:qucalc:zfa` call. Check (c) confirms it agrees with comparing the two matrix orders directly, for
all 16 axis pairs.

**Incompatible conjunctions are refused.** In MO3 the meet of `x+` and `z+` is ⊥. A client that reads
⊥ as "these contradict each other" draws a classical conclusion the logic does not license, and the
failure of distributivity is where that goes wrong. Check (c) counts 120 of 512 triples where
distributivity fails. So `conjoin` returns `"incompatible"` for spatial atoms on different axes. A
gauge atom with a spatial atom gives the Boolean pair, and two atoms in one context use the lattice
meet.

What is proved and what is not:

- **Proved in Lean:** MO2 is orthomodular and not distributive (`orthomodular`, `not_distributive`), and
  the incompatibility comes from `σz σx − σx σz = 2i σy`.
- **Checked here, not in Lean:** MO3's orthomodularity and complement laws, by brute force over its 8
  elements. A Lean `QLF_QuantumLogic3` would be a short `decide` module and is a natural next step.
- **Not claimed:** that MO3 is the base's full proposition lattice. Questions about histories, rather
  than single axes, need the general representation theorem, which is still the named open bridge
  (`QLF_QuantumLogic` §Scope).

---

## 6. What would make it a result

Rule 4 asks what distribution over ways a claim would be false for. A store that admits only closures
makes no claim by itself. The base earns content when it makes a measured quantity available that the
census cannot supply. The candidate is **redundancy against priority**. Run the closure naming game of
Memetics §10 with real, independent attesters on a rholo devnet, and record which closures accumulate
holders. Memetics T4 predicts R follows priority (`first`), not multiplicity (`ways`). If R tracks
`ways` instead, that prediction fails. Pre-register the test before running it, as §8 there did.

## 7. Next steps

1. Deploy [`QKB.rho`](rholang/QKB.rho) on a local rholo devnet. Port the five self-checks as deploys
   and read their results with the node's exploratory deploy.
2. File an issue on rholo about the aggregate gate in `achieves_zfa` (after Jim agrees to filing it).
3. Add `QLF_QuantumLogic3` (MO3 by `decide`).
4. Pre-register and run the redundancy-against-priority test (§6).

## References

- [`Memetics_QLF.md`](Memetics_QLF.md), [`QucalcSearch.md`](QucalcSearch.md),
  [`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md), [`Closure_Walk.md`](Closure_Walk.md),
  [`MostWays_First.md`](MostWays_First.md), [`ScientificApproach.md`](ScientificApproach.md)
- Birkhoff, G. & von Neumann, J. (1936). The logic of quantum mechanics. *Annals of Mathematics* 37(4), 823–843.
- Meredith, L. G. & Radestock, M. (2005). A reflective higher-order calculus. *Electronic Notes in
  Theoretical Computer Science* 141(5), 49–67.
- Zurek, W. H. (2009). Quantum Darwinism. *Nature Physics* 5, 181–188.
