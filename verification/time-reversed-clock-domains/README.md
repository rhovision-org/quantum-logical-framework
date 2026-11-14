# Finite clock-record verification

[Problem definition](../../Time_Reversed_Clock_Domains.md) · [Lean source](../../lean/QLF_ClockDomains.lean) · [Issue #236](https://github.com/rhovision-org/quantum-logical-framework/issues/236) · [PR #237](https://github.com/rhovision-org/quantum-logical-framework/pull/237) · [Independent issue review](grok_review.md)

**Partial finite algebra, physical correspondence still B-OPEN.**

Verified source revision: `55a1be8b4667abdb3a55475c5b224e2be9c9727b`. [GitHub Actions run 43613029731](https://github.com/rhovision-org/quantum-logical-framework/actions/runs/43613029731) passed on 14 November 2026 (16m30s). The full Lake build and separately re-elaborated exact-footprint audit passed. All 395 registered anchors matched the manifest; each of the eleven new `QLF.ClockDomains` statements has an empty kernel axiom footprint. No project axiom was added. Lean was not built locally, per repository instructions.

The module verifies admissibility of three concrete histories; nonunique count-balanced completions; two distinct counterpart words with identical accessible records; nonconstancy of the record map; a general collision-based obstruction to exact counterpart reconstruction and its concrete instance; and reconstruction on a prescribed-partner class. Definitions and assumptions match the frozen closure-only target. The exact footprints are registered in [the manifest](../../lean/axiom_footprints.expected.json) and printed by [the audit module](../../lean/QLF_AxiomAudit.lean).

Local checks passed: document-network validation, declared-axiom audit, proof-placeholder scan, ten proof-trust regression tests, whitespace validation, and both existing Gupta checksum manifests. Those manifests and their covered artifacts are unchanged.

These results establish no physical time-reversal map, matter/antimatter identification, no-signalling law, Hawking-only exchange, two-domain count theorem or Gupta half-age correspondence. Imposing a prescribed counterpart can remove the collision; admissible classes and observation interfaces cannot be changed while silently retaining the obstruction. The age-interpretation gate remains open.
