# QKB runtime acceptance — isolated rholo node

**Date:** 2026-11-13

**Result:** the Rholang contract parses, deploys, executes its closure gate and native calls, publishes a registry URI, and answers a separate deploy that resolves that URI. This is **isolated-node acceptance**, not a production deployment.

## Runtime pin

| Item | Value |
|---|---|
| Node source tree | [`quantum-os`](https://github.com/rchain-community/quantum-os) commit `070d8f8254ab4d39cdf80f8a60eee37c38910588` |
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

## What this establishes and what it does not

**Established here**

- the contract is accepted by rholo's parser/normalizer, not just Python-simulated;
- the `rho:qucalc:zfa`, `rho:qucalc:grant`, deployer-key and registry natives are called on an actual node;
- a valid closure is recorded and a malformed twist list/proposition is refused with an answer;
- the service can be reached by a separate deploy through the registry;
- the basic Python-reference behaviors tested by (a)–(j) agree on the same vectors.

**Not established here**

- production deployment or adversarial-network security;
- independent human attesters (this run uses one deploy key; the Sybil limit in §3a remains);
- the sharded two-role contract (§6 remains a design checked in simulation);
- a public-chain registry lifetime or cross-shard behavior;
- any change to QLF claim status. QKB remains an infrastructure/design artifact, not an `E` claim or a closed physical bridge.

The PR stays a design/implementation artifact. This acceptance run removes the "never parsed or run" blocker; it does not make the single-cell contract decentralized or production-ready.
