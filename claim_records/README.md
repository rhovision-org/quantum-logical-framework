# Claim records and draft test ledger

Every JSON file below this directory is discovered recursively. A record must
identify itself as `record_type: claim` or `record_type: test_ledger`; unknown
record types, duplicate record IDs, duplicate JSON keys and non-JSON numeric
constants fail validation. Future records are checked without editing a filename
allowlist. JSON-only changes trigger the Python workflow.

## Current records

| File | Scope |
|---|---|
| `alpha.json` | Defined counting/coupling identities, reported retrodiction and open measured-coupling bridge |
| `sparc_rar.json` | Algebraic RAR model and reproducible retrospective public-data benchmark |
| `three_polarizer.json` | Finite MO2 properties and imported ideal-optics comparator |
| `born_rule.json` | Characterization under `ProbAssignment` assumptions; physical realization remains open |
| `strange_loop` fields | Typed two-phase/return specification in the four bridge records; all four are `B-OPEN` |
| `kill_conditions.json` | Draft falsification/test ledger, not a completed preregistration |

## Structural requirements

Claim records contain typed, non-empty approximation, formal statement/object,
input provenance, interpretation, observable, measurement protocol, comparison,
evidence, defeater, gate, reviewer and provenance fields. Source and receipt
revisions use full lowercase Git identifiers and must agree within a record.
The validator checks identifier syntax and internal agreement, not Git existence.

Inputs name their value, source and provenance (`derived`, `declared`, `fitted`,
`external`). Comparison types are `prospective`, `retrospective blind`,
`retrodiction`, `consistency` or `not_applicable`. A measurement execution status
separately records whether any protocol was completed.

Claims may also carry a `strange_loop` object: a name, at least two typed
levels, a `return_level`, a `conservative_return` statement, a
`noncircularity_witness`, a status (`B-OPEN`, `SPECIFIED` or `TESTED`) and a
defeater. The loop is a review shape, not a new evidence type. A record cannot
mark `bridge: CLOSED` unless its loop is `TESTED`; otherwise the bridge stays
`B-OPEN`.

## Component promotion policy

All listed gates must be PASS; FAIL, INCONCLUSIVE and NOT_APPLICABLE cannot bypass
a mandatory gate. Components have separate statuses: verifying a finite theorem
does not promote its physical identification.

| Promoted component | Mandatory gates | Additional condition |
|---|---|---|
| Formal VERIFIED | G0, G1, G2, G6 | Receipt includes `kernel_audit` scope |
| Numerical REPRODUCED | G0, G4, G6 | Receipt includes `numerical_reproduction` scope |
| Bridge CLOSED | G0, G2, G3, G6 | Explicit noncircular map; G3 PASS cannot coexist with bridge OPEN; `strange_loop.status` must be `TESTED` |
| Empirical ESTABLISHED | G0, G3, G4, G5, G6 | Closed bridge and empirical receipt; completed prospective comparison, or independently replicated blind analysis at independent reviewer tier |

A retrospective reproduction or retrodiction cannot become empirical evidence
merely by flipping G3/G5 to PASS. Reviewer tiers are `self`, `collaborator` and
`independent`. A self-run record cannot mark G6 PASS. G6 is relative to the declared receipt scope/tier: a collaborator
computational receipt is not an independent physical replication. Receipts name
the reviewer, audited source revision, evidence scopes and digest-addressed
artifacts. The directory check verifies that referenced local artifact bytes match their
digests and stay inside the repository. It does not authenticate the issuer,
execution history or signatures. The reproduction tests additionally check the
execution receipt's artifact manifest.

## Registration policy

Test entries use a list of exact qualified anchors (empty when none is claimed),
a separate statement of formal scope, and DRAFT/REGISTERED/RETIRED status.
REGISTERED requires a complete operational specification, full frozen revision,
timezone-bearing timestamp, observable, dataset/experiment, analysis rule,
uncertainty, rejection rule and documented pre-exposure chronology. The validator
checks this structure; chronology and prior access still need inspection.
Unfinished mass windows or generic suggestions remain DRAFT.

## Commands and limits

```bash
python3 scripts/validate_claim_records.py
python3 -m unittest discover -s tests -p 'test_*.py' -v
python3 scripts/mo2_finite_audit.py
```

The validator is not a Lean runner, truth checker, signing service, or blind-data
custodian. A matching hash does not establish preregistration. Current technical
review is within the collaboration; author roles, conflicts and publication
approval require separate agreement.
