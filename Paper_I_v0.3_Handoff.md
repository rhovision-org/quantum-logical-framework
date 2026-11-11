# Paper I v0.3 — current handoff

This supersedes the executable task lists in the earlier review archive, whose
229/240-anchor counts and open/merged PR descriptions are historical snapshots.
The repository changes are collected in [PR #224](https://github.com/rhovision-org/quantum-logical-framework/pull/224).

## Implemented on this branch

- Eight lattice-law obligations in both Lean namespaces; 35 MO2/QuantumLogic
  anchors plus 27 further additions; a reviewed 302-entry baseline with no changed
  old sets. The two BornFromWays anchors already existed and are not duplicated.
- Recursive typed-record validation, nested content checks, applicable gate paths,
  comparison/execution tiers, local receipt integrity and negative regression tests.
- Validation on JSON, relevant receipt and SPARC changes, plus existing Python checks.
- α, SPARC, migrated three-polarizer and scoped Born records; a draft test ledger.
- Correct electron-anomaly notation and input provenance; precise SPARC information
  access, descriptive statistics and fixed-external-comparator accounting.
- Proposed review routing includes the baseline and enforcement files. Actual required
  approvals depend on repository rules; CODEOWNERS does not itself grant governance rights.

## Evidence to inspect

Read [`verification/paper-i-v0.3/`](verification/paper-i-v0.3/). It names the audited
source, original CI test merge, unmodified formal build inputs, exact baseline delta
and new numerical executions. The original Lean execution was project CI, not a local
independent rebuild. A new CI run on this PR is required before final approval.

## Manuscript and release work

The full Paper I v0.3 manuscript is separate. Its positive claims table must preserve
these distinctions: model identity versus measured quantity, reported agreement versus
executed reproduction, conditional characterization versus physical derivation, and
draft test specification versus preregistration. Keep MO2/three-polarizer as the primary
worked case; add α and SPARC as separately scoped records.

Choose an immutable release head after checking CI. Cite the audited source and
execution receipts explicitly; do not silently replace old evidence with moving main.
Confirm the human author list, CRediT roles, conflicts and license before circulation.
Then perform a short delta review and generate the final document/PDF with real tables.
No new physical experiment is required just to finish the methods case study, and no
physical confirmation is established by the present checks.

— Ω-WITNESS
