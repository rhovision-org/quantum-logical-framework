# A quantum logical knowledge base in Rholang

**Status:** a design with an executable reference. [`qkb_reference.py`](qkb_reference.py) implements
every rule below and checks them against the repo's canonical engines ([`twist_core.py`](twist_core.py),
[`qucalc_search.py`](qucalc_search.py)); it runs in under a second and passes. The Rholang contract
[`rholang/QKB.rho`](rholang/QKB.rho) is the same design written for
[rholo](https://github.com/rhovision-org/rholo) and its `rho:qucalc:*` natives. **It has not been
parsed or run by rholo, nor deployed on a node.** Until a pinned parser check and an isolated-node
acceptance run exist, it is a specification, not an accepted implementation. Part of the
[Quantum Logical Framework (QLF)](README.md).

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

6. **It shards without coordination.** All of its state only grows, and every query is a set size or
   a minimum under a fixed order. Record shards keyed by content id and index shards keyed by name then
   accept writes in any order, more than once, with no cross-shard transaction (§6).

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
{ "records":   { id: { "twists": [Int], "phase": Int, "excursion": Int, "attesters": Set(key) } },
  "names":     { name: Set(id) },                       // a concept = its ways
  "answers":   { q: Set(id) },                          // q = (seed, context); never mixed with names
  "asked":     Set(q) }                                 // questions registered for listing
```

**Access.** Deploying [`QKB.rho`](rholang/QKB.rho) registers the service in rholo's registry as
`bundle+{*QKB}`, which callers can send to but nobody can receive on, so no client can intercept
another's requests. The registry uri goes to the deploy's own `rho:rchain:deployId` channel. Any
later deploy reaches the service with `rho:registry:lookup` on that uri, the pattern rholo's own
`rgov/Directory.rho` and `Group.rho` use.

- **`id`** is the uri `rho:qucalc:grant` mints, a blake2b-256 content address of the twists. The same
  closure asserted by two parties lands on one record. That is what lets R count holders instead of
  copies.
- **`twists`** use rholo's integers: `0 ^ 1 v 2 > 3 < 4 / 5 \ 6 + 7 -`. The axis is `t / 2`
  (y, x, z, gauge), and the sign is `+` iff `t` is even.
- **`phase`** is the Pauli scalar the fold lands on (`1` +I, `−1` −I, `2` +iI, `−2` −iI). On an admitted
  record it is always ±1, because count balance implies the fold is `±I`.
- **`excursion`** is the peak total free action along the history, `max_prefix(|y|+|x|+|z|+|g|)`. That
  is the capacity a horizon needs to hear the closure (`closedAtHorizon_iff_maxExcursion_le`).
- **`attesters`** holds signing keys (public-key bytes), not names. §3a explains why.

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

### 3a. Who counts as a holder

R is only worth measuring if it counts independent holders. An unforgeable name does not establish
that: any caller can run `new a, b, c in { … }` and pass three fresh names. The first version of the
contract stored whatever name it was given, and Aria caught that in review. So `assert` now
**authenticates** the attester. The caller passes its own `*deployerId`. rholo's node binds that name
to the deploy's verified secp256k1 key, and client code cannot construct one. The contract asks
`rho:rchain:deployerId:ops` for `"pubKeyBytes"`. It gets the key for a genuine deployerId and `Nil`
for any other name, and a `Nil` is refused with `{ok: false, error: "attester is not a deployerId"}`.
The attester set stores the key bytes, so repeating an attestation adds nothing.

**What R therefore measures:** the number of distinct secp256k1 keys that signed a deploy attesting the
closure. It does not measure persons. One person with several keys counts several times. Every
key-based system has this Sybil limit, and no contract can close it alone. If the statistic must
count people, weight attesters by an external trust measure: rhogov's trust levels are the obvious
one in this ecosystem. That would be a separate, stated assumption, not a property of QKB.

Self-check (h) tests this. Five fresh names are refused and leave the store empty. Five attestations
by one key give R = 1, and a second key makes it 2. The sharded model refuses fresh names too.

---

## 4. Queries, and which statistic each one is

| Query | Returns | Statistic |
|---|---|---|
| `assert(name, twists, attester)` | `{ok, id, ways, redundancy}`, or `{ok: false, residual}`, or `{ok: false, error: "invalid twists"}` | a refusal carries the action vector still owed, so it is never silent |
| `ways(name)` | number of distinct closures under `name` | **multiplicity**, a count that is absolute, not capacity-relative |
| `redundancy(id)` | number of independent holders | **R**, how much of a meme the record is |
| `first(name)` | the closure under `name` reached first | **priority**: least excursion, then shortest, then phase, then lexicographic |
| `ask(seed, context)` | `{ok, q, residual}` with `q = (seed, context)` | what any answer must supply |
| `answer(q, cont, attester)` | `{ok, id, redundancy}` for `seed ++ cont`, or a refusal | filed under `q`'s answers only |
| `solve(q)` | the continuation of the first-reached recorded answer | priority, the same cascade as `/solve` |
| `compatible(p, q)` / `conjoin(p, q)` | Bool / proposition, `"incompatible"` or `"invalid proposition"` | the logic layer, §5 |

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
- **A question is its content.** Its id is the pair `(seed, context)`, which the contract uses directly
  as the map key. Asking it again is a no-op that keeps its answers, and nobody can rebind an existing
  id to a different question, so the question state stays grow-only like everything else. The same seed
  in another context is a different question. Check (g) replays an `ask` after an answer and finds the
  answer still there. The first version keyed questions by a caller-chosen name and overwrote them,
  which Aria caught in review.
- **Answers have their own namespace, and need no prior ask.** An answer is checked against `q`'s own
  seed, so it is valid whether or not `q` was asked. `ask` only registers `q` for listing. That keeps
  answers order-independent across shards, because no answer leg depends on an ask leg having
  arrived. Answers are filed in `answers[q]`, never under `names`. Aria's third review found that the
  sharded model had used one index for both. A valid but unrelated closure asserted *under the name*
  `q` then won `solve` with a continuation that does not close the seed. Check (i) reproduces that
  trace and gets the right answer in both models. It also shows the two models refuse the same
  malformed questions, and that 20 shuffled orders of ask-among-answers all converge.
- **Malformed input fails closed, with an answer.** Every twist list (a record, a seed, a continuation)
  must be a list of integers `0..7` no longer than 64. Anything else gets
  `{ok: false, error: "invalid twists"}` before it reaches `scan` or a native call. Check (g) sends
  eight malformed inputs (out of range, a Boolean, a float, a string, a tuple, `None`, too long)
  through `assert`, `ask` and `answer`. Every one is refused and the state is unchanged.

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

**Conjunctions are propositions too.** The full proposition set is MO3 over the spatial axes, smashed
with the gauge block: a pair (spatial part, gauge part), collapsed to ⊥ if either part is ⊥. So a
proposition is `"bot"`, `"top"`, an atom `(axis, sign)`, or `("and", spatial atom, gauge atom)`, which
is what `conjoin` returns for two compatible atoms in different blocks. `conjoin` takes the meet part
by part and refuses only when the spatial parts clash. Its output is always valid input again. The
first version returned `("and", …)` and then rejected it as input, which Aria caught. Check (i)
enumerates all 22 propositions and confirms closure, commutativity and idempotence for every
defined pair, and associativity wherever both groupings are defined.

**Malformed propositions are refused before any fold.** Anything outside that set, including an axis
outside `0..3`, a sign other than `±1`, or an `"and"` whose parts are in the wrong blocks, gets
`"invalid proposition"`. Without this check an axis of 4 would build twist 8 and the native call would
fail instead of answering. Check (h) tries 12 malformed propositions in either position and in
both, and confirms that every well-formed pair still gets an answer.

What is proved and what is not:

- **Proved in Lean:** MO2 is orthomodular and not distributive (`orthomodular`, `not_distributive`), and
  the incompatibility comes from `σz σx − σx σz = 2i σy`.
- **Checked here, not in Lean:** MO3's orthomodularity and complement laws, by brute force over its 8
  elements. A Lean `QLF_QuantumLogic3` would be a short `decide` module and is a natural next step.
- **Not claimed:** that MO3 is the base's full proposition lattice. Questions about histories, rather
  than single axes, need the general representation theorem, which is still the named open bridge
  (`QLF_QuantumLogic` §Scope).

---

## 6. Decentralizing it: sharding

Everything the base stores only grows. Attester sets, the ways under a name and the answers to a
question are all sets that are only ever added to, and every query is a count of a set or the minimum
of a set under a fixed total order. Union and minimum are commutative, associative and idempotent. So
shards can accept writes independently, in any order and more than once, and still agree. **No
cross-shard transaction is needed**, so rholo's two-phase commit
([`cross-shard-transactions.md`](https://github.com/rhovision-org/rholo/blob/dev/docs/src/formal/cross-shard-transactions.md),
Laws 26–29) is not used. The idempotent single legs of Law 28 are enough.

**Two shard roles, two shard keys.**

| Role | Sharded by | Holds | Answers |
|---|---|---|---|
| record shard | content id (blake2b of the twists) | `id → (twists, attesters)` | `redundancy` |
| index shard | name or question | `name → {(key, id)}` and, separately, `q → {(key, id)}` answers | `ways`, `first`, `solve` |

`key` is the `/solve` cascade key: (excursion, length, phase rank, history). It is computed from the
closure alone, so storing it beside the id makes `ways`, `first` and `solve` local to **one** index
shard. `redundancy` is local to one record shard. No query fans out.

**A write is two legs**, to the record shard and then the name's index shard. Each leg is an ordinary
signed deploy and is idempotent. Re-delivery adds nothing, and the legs commute. If a writer crashes
between them, the result is an orphan record: it is held but has no name, and the next write that
names it heals that. There is never a name pointing at nothing. If the legs arrive out of order, an
index entry can briefly come before its record. Only `redundancy` waits for the record leg.

**Both legs carry one snapshot.** The history is copied once, then validated, and its content id and
cascade key are computed from that copy. Both legs carry only those fixed values. Without this, a
client that changes its own list after building the legs could store one history under another's id,
or pair a record with the wrong index key. Aria found both cases in the reference model. Rholang
values are immutable, so the contract cannot hit this, but a client library written in a mutable
language can. Self-check (j) changes the list before delivery and between the two legs, for both
assertions and answers. It confirms that every stored id matches its history and every index key
matches its record.

**Two properties come from the substrate rather than from engineering:**

- **The gate needs no state.** Per-axis balance is a property of the twists alone, so any shard and any
  reader can check a record, and nobody has to trust the shard that stored it. Content addressing means
  two shards that admit the same closure produce the same id.
- **Redundancy counts keys, not copies.** `deployerId` is the same key on every shard
  ([rholo `shard-invoke.md`](https://github.com/rhovision-org/rholo/blob/dev/docs/src/node/shard-invoke.md)),
  so one party attesting a closure on two shards counts once. A replica's R is the size of the union
  of attester sets, never their sum. Summing them would let one party fake a meme by repeating itself.

Self-check (f) in [`qkb_reference.py`](qkb_reference.py) runs this model with 1 to 7 shards. It uses
717 writes, delivered in shuffled order across shards, with a third of them delivered twice. Every
`ways`, `redundancy`, `first` and `solve` agrees with the single store, and so does a full merge of the
shards. Summed attesters or an order that was not total would fail it.

**Not covered, and why it is not needed yet.** There is no retraction. Deleting would break the
grow-only property and need tombstones (a two-phase set) or a coordinated decision. In QLF a closure
cannot un-close (`closedAtHorizon_mono`), so a base whose records are closures never needs to delete
one. A party that stops holding a record is a different matter: it would need a signed withdrawal set
beside each attester set. Hot names can be split further by `(name, hash(id) mod m)`, at the cost of an
`m`-way fan-out for `ways` and `first`, where `first` is still a minimum of minimums. An alternative
placement for record shards is by excursion band, which would let a capacity-`R` reader query only
the bands `≤ R`. It is listed as an option, not chosen. Hashing balances load, and the index already
makes priority queries local.

In Rholang, each shard runs [`QKB.rho`](rholang/QKB.rho) in one role. A client routes each leg with
the cross-shard invoke primitive, using `$at(shard, …)` as
[`shard_exchange.rho`](https://github.com/rhovision-org/rholo/blob/dev/qucalc/examples/shard_exchange.rho)
does. Splitting the contract into the two roles, and storing `key` in the name index, are the
contract-side changes. They are not written yet. Answers already live in their own map, and the
sharded model keeps a separate answer index next to the name index. **So this section is a design checked in a
simulation. The current `QKB.rho` is a single-cell contract and is not decentralized.**

## 7. What would make it a result

Rule 4 asks what distribution over ways a claim would be false for. A store that admits only closures
makes no claim by itself. The base earns content when it makes a measured quantity available that the
census cannot supply. The candidate is **redundancy against priority**. Run the closure naming game of
Memetics §10 with real, independent attesters on a rholo devnet, and record which closures accumulate
holders. Memetics T4 predicts R follows priority (`first`), not multiplicity (`ways`). If R tracks
`ways` instead, that prediction fails. Pre-register the test before running it, as §8 there did.

## 8. Next steps

1. **The merge gate (from review):** parse [`QKB.rho`](rholang/QKB.rho) with rholo's parser at a
   pinned commit, then run an isolated-node acceptance test. It should cover assert and refusal,
   repeat attestation, duplicate questions, malformed input, solve and compatibility, by porting
   self-checks (a)–(g) as deploys and reading their results with the node's exploratory deploy.
   Running rholo's code was not permitted in this session. Either a session that may build rholo
   or a pinned CI job (it would be this repo's first non-Lean CI job) has to do it.
2. File an issue on rholo about the aggregate gate in `achieves_zfa` (after Jim agrees to filing it).
3. Add `QLF_QuantumLogic3` (MO3 by `decide`).
4. Pre-register and run the redundancy-against-priority test (§7).
5. Split `QKB.rho` into record and index roles (§6) and run two shards on a devnet.

## References

- [`Memetics_QLF.md`](Memetics_QLF.md), [`QucalcSearch.md`](QucalcSearch.md),
  [`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md), [`Closure_Walk.md`](Closure_Walk.md),
  [`MostWays_First.md`](MostWays_First.md), [`ScientificApproach.md`](ScientificApproach.md)
- Birkhoff, G. & von Neumann, J. (1936). The logic of quantum mechanics. *Annals of Mathematics* 37(4), 823–843.
- Meredith, L. G. & Radestock, M. (2005). A reflective higher-order calculus. *Electronic Notes in
  Theoretical Computer Science* 141(5), 49–67.
- Zurek, W. H. (2009). Quantum Darwinism. *Nature Physics* 5, 181–188.
