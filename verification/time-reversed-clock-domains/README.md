# Finite clock-record verification

[Problem definition](../../Time_Reversed_Clock_Domains.md) · [Lean source](../../lean/QLF_ClockDomains.lean) · [Issue #236](https://github.com/rhovision-org/quantum-logical-framework/issues/236) · [PR #237](https://github.com/rhovision-org/quantum-logical-framework/pull/237) · [Independent issue review](grok_review.md)

**Partial finite algebra, physical correspondence still B-OPEN.**

Verified source revision: `55a1be8b4667abdb3a55475c5b224e2be9c9727b`. [GitHub Actions run 43613029731](https://github.com/rhovision-org/quantum-logical-framework/actions/runs/43613029731) passed on 14 November 2026 (16m30s). The full Lake build and separately re-elaborated exact-footprint audit passed. All 395 registered anchors matched the manifest; each of the eleven new `QLF.ClockDomains` statements has an empty kernel axiom footprint. No project axiom was added. Lean was not built locally, per repository instructions.

The module verifies admissibility of three concrete histories; nonunique count-balanced completions; two distinct counterpart words with identical accessible records; nonconstancy of the record map; a general collision-based obstruction to exact counterpart reconstruction and its concrete instance; and reconstruction on a prescribed-partner class. Definitions and assumptions match the frozen closure-only target. The exact footprints are registered in [the manifest](../../lean/axiom_footprints.expected.json) and printed by [the audit module](../../lean/QLF_AxiomAudit.lean).

Local checks passed: document-network validation, declared-axiom audit, proof-placeholder scan, ten proof-trust regression tests, whitespace validation, and both existing Gupta checksum manifests. Those manifests and their covered artifacts are unchanged.

These results establish no physical time-reversal map, matter/antimatter identification, no-signalling law, Hawking-only exchange, two-domain count theorem or Gupta half-age correspondence. Imposing a prescribed counterpart can remove the collision; admissible classes and observation interfaces cannot be changed while silently retaining the obstruction. The age-interpretation gate remains open.

## Second and third stages

[QLF_ClockPairing](../../lean/QLF_ClockPairing.lean) (29 registered statements) was verified at `4b33ce0` by [GitHub Actions run 43755290234](https://github.com/rhovision-org/quantum-logical-framework/actions/runs/43755290234) on 15 November 2026: full Lake build and exact-footprint gate passed, no project axiom. @aixaria0 reviewed and approved that revision on [PR #246](https://github.com/rhovision-org/quantum-logical-framework/pull/246) for the finite algebraic stage, noting that the counts are claims about the stated toy alphabet and counting rule, not evidence for a physical antimatter sector or a Gupta age map.

[QLF_ClockIntervention](../../lean/QLF_ClockIntervention.lean) (17 registered statements) was added afterwards and is not covered by that approval. Its footprints are Lean's own or empty. Both modules were also built in a cloud session container on the pinned toolchain before pushing; CI on the pull request is the verification of record.

QLF_ClockIntervention was verified at `a0d0b82` by [GitHub Actions run 43778588272](https://github.com/rhovision-org/quantum-logical-framework/actions/runs/43778588272) on 16 November 2026. The first attempt of that run failed in the build step without a step result and its log is no longer retrievable; the rerun of the same commit passed the full build and the exact-footprint gate. @aixaria0 then reviewed that revision and reported no remaining verification blocker for the declared finite scope.

The branch was afterwards merged with main, which had gained four modules, and the module list and audit anchors were reconciled to keep both sides (477 registered footprints). That merged state at `6d49212` passed [run 43848265493](https://github.com/rhovision-org/quantum-logical-framework/actions/runs/43848265493). Any later merge of main is verified by the pull request's own run at its final head.
