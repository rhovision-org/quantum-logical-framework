# QKB verification

This directory holds the runtime-acceptance record for
[`rholang/QKB.rho`](../../rholang/QKB.rho), the Rholang contract described in
[`Quantum_Knowledge_Base.md`](../../Quantum_Knowledge_Base.md).

| Artifact | What it is |
|---|---|
| [`rholo_acceptance.md`](rholo_acceptance.md) | Isolated-node acceptance run: parser, deploy, native calls, refusals, registry publication and separate-deploy lookup. |
| [`make_acceptance_harness.py`](make_acceptance_harness.py) | Generates the test harness from the production contract; `--lookup-uri` generates the separate-deploy lookup probe. |

The acceptance run used the checked-in `rnode` from
[`quantum-os`](https://github.com/rchain-community/quantum-os) at commit
`070d8f8254ab4d39cdf80f8a60eee37c38910588`, binary SHA-256
`3323e67399fd0d5bf5e91fbcfa4dd157848e2b9ec5e7c0276c71288f675f6400`.

It establishes that the contract is parsed and executed against rholo's
natives, and that a separate deploy can resolve and call the published service.
It does not establish production security, independent attesters, sharding, or
any change to QLF claim status. See the "What this establishes and what it does
not" section.
