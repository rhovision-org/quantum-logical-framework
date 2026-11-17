# QKB runtime acceptance — isolated rholo node and playground

**Date:** 2026-11-13 (deploys 1–3, isolated node); 2026-11-16 (deploys 4–5, public playground)

**Result:** the Rholang contract parses, deploys, executes its closure gate and native calls, publishes a registry URI, and answers a separate deploy that resolves that URI. This is **isolated-node and playground acceptance**, not a production deployment. Deploys 4–5 reran the harness on the public rholang playground, adding the attester-refusal probe and a second deployer key.

## Runtime pin

| Item | Value |
|---|---|
| Node source tree | [`quantum-os`](https://github.com/rhovision-org/quantum-os) commit `070d8f8254ab4d39cdf80f8a60eee37c38910588` |
| Binary | `/home/jimscarver/quantum-os/bin/rnode` |
| Binary SHA-256 | `3323e67399fd0d5bf5e91fbcfa4dd157848e2b9ec5e7c0276c71288f675f6400` |
| `rnode --version` | `rchain 0.1.0` |
| Node mode | fresh local genesis, shard `/root`, `--dev-mode`, autopropose |
| Chain | disposable local data directory; no public network |

The quantum-os repository commits `bin/rnode` as a checked-in binary. The SHA-256 above identifies the exact binary used. The binary itself reports `commit # unknown` in its HTTP status, so the tree commit and binary hash are the provenance pins.

## Harness

The production contract sends its registry URI to the deploy's private `rho:rchain:deployId` channel. The acceptance harness is generated from `rholang/QKB.rho` and changes only the test plumbing:

- it sends the URI also to the public `@"qkb-uri"` channel;
- it binds the deploy's own `rho:rchain:deployerId`;
- it appends probes for assert, ways, redundancy, ask, answer, solve, compatibility, conjoin and two refusals.

The QKB contracts, gate, store and query logic are unchanged.

```sh
python3 verification/qkb/make_acceptance_harness.py --output /tmp/QKB_acceptance.rho
```

Deploy command used (the key is a throwaway local-genesis key, supplied by the environment and not committed):

```sh
rnode deploy \
  --phlo-limit 10000000 --phlo-price 1 --shard-id /root \
  --private-key "$QKB_DEPLOY_KEY" \
  /tmp/QKB_acceptance.rho
```

## Deploy 1 — contract plus probes

| Item | Value |
|---|---|
| Deploy signature | `304402200824a9060aa64ef93a8266bcb9686341a43c63a5fe1201e83d39bee6f17a86a902204501116f43e3191fae9de1630b1fa482f781c5b222c41d88f1888caeec7317f5` |
| Block | `8` |
| Block hash | `cc3269af82ecd5cae58e732f35941b4fa24630f0bac7beeee092da3657b61091` |
| Rejected deploys | none |
| Published URI | `rho:id:1dqgybt7nwbewj8qgnmm6g76xpdt5funrjtum7a38n7nj3h7umjo` |

Channel values read with `rnode listen-data-at-name --type pub --content '"<name>"'`:

| Channel | Observed value |
|---|---|
| `qkb-uri` | `rho:id:1dqgybt7nwbewj8qgnmm6g76xpdt5funrjtum7a38n7nj3h7umjo` |
| `qkb-assert` | `{ok: true, id: rho:id:w3ihj8nksaqftkwpuc6o8rtotmxtqjsacaw45qysetcndoydxoay, redundancy: 1, ways: 1}` |
| `qkb-ways` | `1` |
| `qkb-redundancy` | `1` |
| `qkb-ask` | `{ok: true, q: ([0], 0), residual: [-1, 0, 0, 0]}` |
| `qkb-answer` | `{ok: true, id: rho:id:w3ihj8nksaqftkwpuc6o8rtotmxtqjsacaw45qysetcndoydxoay, redundancy: 1}` |
| `qkb-solve` | `[3, 1, 2]` |
| `qkb-compatible` | `true` |
| `qkb-conjoin` | `"incompatible"` for `(0,1) ∧ (1,1)` |
| `qkb-bad` | `{ok: false, error: "invalid twists"}` for `[8]` |
| `qkb-bad-prop` | `"invalid proposition"` for axis `4` |

Interpretation: `[0,3,1,2]` passes the per-axis gate, receives a content id from `rho:qucalc:grant`, and folds to a nonzero phase from `rho:qucalc:zfa`. `[0]` as a question leaves residual `[-1,0,0,0]`; the continuation `[3,1,2]` closes it; `solve` returns exactly that continuation. The malformed inputs are refused before `scan` or a native call.

## Deploy 2 — registry lookup from a separate deploy

Generated with the published URI:

```sh
python3 verification/qkb/make_acceptance_harness.py \
  --lookup-uri rho:id:1dqgybt7nwbewj8qgnmm6g76xpdt5funrjtum7a38n7nj3h7umjo \
  --output /tmp/QKB_lookup.rho
rnode deploy --phlo-limit 1000000 --phlo-price 1 --shard-id /root \
  --private-key "$QKB_DEPLOY_KEY" /tmp/QKB_lookup.rho
```

| Item | Value |
|---|---|
| Deploy signature | `304402203cf959f3b2b8e21c4e39e46069e67aa0f152338dd480fe20bf9eef4925baab6c02201934b51617bb36c33bcfc5786b1962d0d8276807912cbfdfbe25d3b1939324a9` |
| Block | `137` |
| Block hash | `4f13c946648ee926bf65a085952fc71dd1f17ea113c1a5e46430d15b781563a1` |
| Rejected deploys | none |

| Channel | Observed value |
|---|---|
| `qkb-lookup2-stage` | `"start"`, then `"found"` |
| `qkb-lookup2-ways` | `1` |
| `qkb-lookup2-solve` | `[3, 1, 2]` |

The lookup deploy does not import or reuse the first deploy's process. It resolves the `bundle+{*QKB}` through `rho:registry:lookup` and calls the service through the resulting capability.

## Deploy 3 — repeat, order and conjoin probes

| Item | Value |
|---|---|
| Deploy signature | `3045022100837d4be698a2adb6fea1cc3039df220a8c6e3f5fd9a354f5fa447664089e2e9d022044e367b1621a77e3773cc7a80bf073395b120e45b1a829d9b868dba0e9e1712f` |
| Block | `161` |
| Block hash | `c7b6bd5e15b84bb494045ed81d2ad353c987f55a7b42f6e9e749a3903f3aa835` |
| Rejected deploys | none |

| Probe | Observed value |
|---|---|
| repeat assert | same id `rho:id:w3ihj...`; `redundancy: 1` |
| duplicate ask | `{ok: true, q: ([0], 0), residual: [-1,0,0,0]}` |
| answer before ask | `{ok: true, id: rho:id:w3ihj..., redundancy: 1}` for `q = ([0],1)` |
| solve after answer-before-ask | `[3, 1, 2]` |
| compatible `(0,1)` with itself | `true` |
| conjoin `(0,1)` with itself | `(0, 1)` |

The repeat attestation by the same signing key leaves `R = 1`, as designed: R counts distinct keys, not supplied names. The answer-before-ask case shows that the content-addressed question does not require an `ask` leg to have arrived first.

## Deploy 4 — the harness on the public playground (2026-11-16)

The same harness, generated from this branch with `--tag r1794823896` so that its output channels
(`@"qkb-r1794823896-..."`) cannot collide with any other run on a shared chain, was deployed to the
rholang playground (`https://rnodeapi.rhobot.net`, `networkId` `playground`, shard `/playground`,
`rholo node 0.1.0 (a5259969a7c5673ccdfc5dad97981d0a3607fcf0)`, `devMode`). It was signed with the
throwaway `alice` key from quantum-os
[`scripts/localnet/pk.txt`](https://github.com/rhovision-org/quantum-os/blob/main/scripts/localnet/pk.txt)
and read back with `explore-deploy-by-block-hash` peeks (`for (@x <<- @"qkb-r1794823896-NAME")`)
against the block that included it.

| Item | Value |
|---|---|
| Deploy signature | `3044022001ec7db6afab03301e4f8e46919fc2d7487b40137cd485afacdb39cd1464e7980220635c64548164ca2be91d409fb61f062a694930d4b0f336b552d6598a70aeadc6` |
| Block | `4747` |
| Block hash | `e46043c7be1aeeed45b2594bda2679cb300e37831e186e980a840eff0ac26d64` |
| Rejected deploys | none |

| Channel | Observed value |
|---|---|
| `uri` | `rho:id:tqzpbz4w9hazaipn5arp3ke8cuxgyab6nprmtwgc6dmfojg7tzno` |
| `assert` | `{ok: true, id: rho:id:w3ihj8nksaqftkwpuc6o8rtotmxtqjsacaw45qysetcndoydxoay, ways: 1, redundancy: 1}` |
| `ways` / `redundancy` | `1` / `1` |
| `ask` | `{ok: true, q: ([0], 0), residual: [-1,0,0,0]}` |
| `answer` | `{ok: true, id: rho:id:w3ihj..., redundancy: 1}` |
| `solve` | `[3, 1, 2]` |
| `compatible` `(0,1)` with `(0,1)` | `true` |
| `conjoin` `(0,1)` with `(1,1)` | `"incompatible"` (Python reference: `"incompatible"`) |
| `bad` (`[8]`) | `{ok: false, error: "invalid twists"}` |
| `bad-prop` (`(4,1)`) | `"invalid proposition"` |
| **`fake-attester`** (fresh `new` name as attester) | **`{ok: false, error: "attester is not a deployerId"}`** |

Two things are new relative to deploys 1–3. The closure id is the same `rho:id:w3ihj...` on a
different node build and chain, so content addressing does not depend on the node. And the native key
check refuses a name that is not a `deployerId`, which the single-key isolated run could not show.

A first lookup deploy against this URI (block `4748`, throwaway `bob` key) was processed without
error but wrote nothing: on this build `rho:registry:lookup` answers with the bare `bundle+` value,
not a `(uri, value)` pair, so the generator's `for (@(_, QKB) <- ch)` never matched. The generator now
accepts either shape.

## Deploy 5 — registry lookup and a second key on the playground (2026-11-16)

The corrected lookup deploy, generated with the same `--tag` and signed with the throwaway `bob` key,
so it comes from a **different deployer** than deploy 4.

| Item | Value |
|---|---|
| Deploy signature | `304402207ffa0aa1b4c3fe203979c3f8da68cf45abb26fc31218cdd84c0cf55a3326911802204b30bd21508a6813be6aeb18db993f602e42911676f1c31db4ff5c6fcaa81b68` |
| Block | `4749` |
| Block hash | `7bd94886fee82ffc45462301a5a4e9527e5af3e69c208dc79c2a0ce9cca91b2d` |
| Rejected deploys | none |

| Channel | Observed value |
|---|---|
| `repeat-assert` (bob's first assert of `[0,3,1,2]`) | `{ok: true, id: rho:id:w3ihj..., ways: 1, redundancy: 2}` |
| `repeat-redundancy` (bob asserts it again) | `{ok: true, id: rho:id:w3ihj..., ways: 1, redundancy: 2}` |
| `repeat-ask` | `{ok: true, q: ([0], 0), residual: [-1,0,0,0]}` |
| `answer-before-ask` (`q = ([0],1)`) | `{ok: true, id: rho:id:w3ihj..., redundancy: 2}` |
| `answer-before-solve` | `[3, 1, 2]` |
| `conjoin-compatible` / `conjoin-result` | `true` / `(0, 1)` |

This is the redundancy-versus-multiplicity distinction on a live chain. A second, distinct key raises
`R` from 1 to 2 while `ways` stays 1, and a repeat by that same key leaves `R = 2`. A separate
exploratory deploy that looked the URI up and called `redundancy` on the id also returned `2`.

## What this establishes and what it does not

**Established here**

- the contract is accepted by rholo's parser/normalizer, not just Python-simulated;
- the `rho:qucalc:zfa`, `rho:qucalc:grant`, deployer-key and registry natives are called on an actual node;
- a valid closure is recorded and a malformed twist list/proposition is refused with an answer;
- a name that is not a `deployerId` is refused as attester (`"attester is not a deployerId"`, deploy 4 on the playground);
- the closure id is the same on two node builds (deploys 1 and 4);
- `R` counts distinct deployer keys: a second key raises it to 2 while `ways` stays 1, and a repeat by the same key does not (deploy 5);
- the service is reachable through the registry on the playground too (deploy 5);
- the service can be reached by a separate deploy through the registry;
- on the vectors probed above, the node returns what the Python reference returns: the gate on one valid and one malformed twist list, `ways`/`redundancy`, ask/answer/solve, a repeat attestation, a duplicate ask, answer-before-ask, `compatible`, `conjoin` and a malformed proposition. That is a subset of the behaviours behind checks (a)–(j), not all of them: (a)–(c) are exhaustive enumerations, and (f) sharding and (j) mutation of captured lists are Python-only by nature.

**Not established here**

- production deployment or adversarial-network security;
- independent human attesters (deploys 4–5 used two throwaway keys held by one operator, so R = 2 shows the counting, not independence; the Sybil limit in §3a remains);
- the sharded two-role contract (§6 remains a design checked in simulation);
- a public-chain registry lifetime or cross-shard behavior;
- any change to QLF claim status. QKB remains an infrastructure/design artifact, not an `E` claim or a closed physical bridge.

The PR stays a design/implementation artifact. This acceptance run removes the "never parsed or run" blocker; it does not make the single-cell contract decentralized or production-ready.
