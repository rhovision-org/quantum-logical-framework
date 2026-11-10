# Claim records

This directory holds the machine-readable claim records for Paper I v0.3 and the
pre-registered kill-condition ledger. The records are schema-checked by
`scripts/validate_claim_records.py`; they are not a truth checker.

## Files

| File | Purpose |
|---|---|
| `alpha.json` | Fine-structure α claim record (draft). |
| `sparc_rar.json` | SPARC radial-acceleration relation claim record (draft). |
| `kill_conditions.json` | Pre-registered null predictions and kill conditions. |
| `three_polarizer.json` | To be migrated from Paper I v0.2; ideal-polarizer bridge record. |

## Required claim-record fields

```
record_id, version, source_revision, informal_statement,
approximation_or_regime, formal_statement, formal_object, dependencies,
inputs, interpretation, observable, measurement_protocol,
reported_agreement, evidence, defeaters, gate_outcomes, evidence_status,
reviewer_independence, provenance
```

The new fields relative to v0.2 are:

- `approximation_or_regime` — leading order, one-loop, ideal optics,
  non-relativistic equilibrium, local H₀, retrospective blind, prospective
  null, etc.
- `inputs` — each with `name`, `value`, `provenance` in
  `{derived, declared, fitted, external}`, and `source`.
- `reported_agreement` — value, comparator, uncertainty, and
  `comparison_type` in `{prospective, retrospective blind, retrodiction,
  consistency}`.

## Non-promotion rules

- `evidence_status.formal = VERIFIED` requires G1 `PASS`.
- `evidence_status.empirical = ESTABLISHED` requires G3 and G5 `PASS`.
- `evidence_status.bridge = CLOSED` requires G3 `PASS`.
- A record without `approximation_or_regime` is invalid.

## Validation

```bash
python3 scripts/validate_claim_records.py
python3 -m unittest discover -s tests -p 'test_claim_records.py' -v
```

## Reviewer

Aria is the technical reviewer for these records; see `.github/CODEOWNERS`.
The authors are QLF developers, so the review is a collaborator technical
review, not an independent external audit.
