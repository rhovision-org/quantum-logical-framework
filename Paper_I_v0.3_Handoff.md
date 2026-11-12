# Paper I v0.3 — current handoff

This supersedes the executable task lists in the earlier review archive, whose
229/240-anchor counts and open/merged PR descriptions are historical snapshots.
The repository changes are collected in [PR #224](https://github.com/rhovision-org/quantum-logical-framework/pull/224)
(the claim-record/G1 PR), with two subsequent reviewed extensions:
[PR #225](https://github.com/rhovision-org/quantum-logical-framework/pull/225)
(metric-singlet/lattice-Einstein) and
[PR #226](https://github.com/rhovision-org/quantum-logical-framework/pull/226)
(Manifestation). All three are merged.

## Current merged state

- PR #224: eight lattice-law obligations in both Lean namespaces; 35
  MO2/QuantumLogic anchors plus 27 further additions; a reviewed 302-entry
  baseline with no changed old sets. The two BornFromWays anchors already
  existed and are not duplicated.
- PR #225: five anchors (three `QLF.MetricSinglet`, two
  `QLF.LatticeDivergence`), baseline **307**; metric = singlet and a lattice
  divergence/Einstein-field-equation result under explicit premises.
- PR #226: twelve `QLF.Manifestation` anchors, baseline **319**; orientation,
  isolation-is-closure, unbounded closures, distance = delay, and the proton as
  the simplest isolated imbalance.
- All 319 anchors have reviewed project-CI footprints; no old footprint was
  changed by #225 or #226. The `verification/paper-i-v0.3/` receipt remains
  scoped to the 302-anchor #224 closure; the later deltas are in the #225/#226
  PRs and the current baseline file.
- Recursive typed-record validation, nested content checks, applicable gate paths,
  comparison/execution tiers, local receipt integrity and negative regression tests.
- Validation on JSON, relevant receipt and SPARC changes, plus existing Python checks.
- α, SPARC, migrated three-polarizer and scoped Born records; a draft test ledger.
- Correct electron-anomaly notation and input provenance; precise SPARC information
  access, descriptive statistics and fixed-external-comparator accounting.
- Proposed review routing includes the baseline and enforcement files. Actual required
  approvals depend on repository rules; CODEOWNERS does not itself grant governance rights.

## Evidence to inspect

Read [`verification/paper-i-v0.3/`](verification/paper-i-v0.3/) for the #224
receipt, then inspect the #225 and #226 PR diffs and the current
[`lean/axiom_footprints.expected.json`](lean/axiom_footprints.expected.json)
(319 entries). The original Lean execution was project CI, not a local
independent rebuild. The current exact-footprint gate is the authoritative
formal check; the metric/Einstein and Manifestation results remain formal
theorems under their stated premises, not physical bridge closures.

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
