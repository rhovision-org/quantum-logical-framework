#!/usr/bin/env python3
"""Validate QLF claim records and the pre-registered kill-condition record.

This is a schema / non-promotion checker, not a truth checker. It enforces:
  * required fields are present;
  * gate outcomes are well formed;
  * evidence statuses are in the allowed vocabulary;
  * no empirical promotion without G3 and G5 PASS;
  * no formal promotion without G1 PASS;
  * no closed bridge without G3 PASS;
  * every input has a provenance in {derived, declared, fitted, external};
  * kill-condition entries name a claim, comparator, kill condition, and status.

Run from the repository root:
    python3 scripts/validate_claim_records.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIM_FILES = [
    ROOT / "claim_records" / "alpha.json",
    ROOT / "claim_records" / "sparc_rar.json",
]
KILL_FILE = ROOT / "claim_records" / "kill_conditions.json"

CLAIM_FIELDS = {
    "record_id",
    "version",
    "source_revision",
    "informal_statement",
    "approximation_or_regime",
    "formal_statement",
    "formal_object",
    "dependencies",
    "inputs",
    "interpretation",
    "observable",
    "measurement_protocol",
    "reported_agreement",
    "evidence",
    "defeaters",
    "gate_outcomes",
    "evidence_status",
    "reviewer_independence",
    "provenance",
}
GATE_NAMES = {f"G{i}" for i in range(7)}
GATE_STATUSES = {"PASS", "FAIL", "INCONCLUSIVE", "NOT_APPLICABLE"}
FORMAL_STATUSES = {"VERIFIED", "CANDIDATE", "NOT_ESTABLISHED"}
NUMERICAL_STATUSES = {"REPRODUCED", "CANDIDATE", "NOT_ESTABLISHED"}
EMPIRICAL_STATUSES = {"ESTABLISHED", "CANDIDATE", "NOT_ESTABLISHED"}
BRIDGE_STATUSES = {"CLOSED", "OPEN", "NOT_APPLICABLE"}
INPUT_PROVENANCE = {"derived", "declared", "fitted", "external"}


class ValidationError(ValueError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def validate_claim_record(data: dict, path: Path) -> None:
    _require(isinstance(data, dict), f"{path}: top level must be an object")
    missing = CLAIM_FIELDS - set(data)
    extra = set(data) - CLAIM_FIELDS
    _require(not missing, f"{path}: missing fields: {sorted(missing)}")
    _require(not extra, f"{path}: unexpected fields: {sorted(extra)}")
    _require(data["version"].startswith("0.3"), f"{path}: expected version 0.3*")
    _require(data["source_revision"], f"{path}: empty source_revision")

    gates = data["gate_outcomes"]
    _require(set(gates) == GATE_NAMES, f"{path}: gates must be G0..G6")
    for name, gate in gates.items():
        _require(set(gate) == {"status", "reason"}, f"{path}: bad gate {name}")
        _require(gate["status"] in GATE_STATUSES, f"{path}: bad gate status {name}")
        _require(bool(gate["reason"]), f"{path}: empty gate reason {name}")

    status = data["evidence_status"]
    _require(set(status) == {"formal", "numerical", "empirical", "bridge"},
             f"{path}: evidence_status must have formal/numerical/empirical/bridge")
    _require(status["formal"] in FORMAL_STATUSES, f"{path}: bad formal status")
    _require(status["numerical"] in NUMERICAL_STATUSES, f"{path}: bad numerical status")
    _require(status["empirical"] in EMPIRICAL_STATUSES, f"{path}: bad empirical status")
    _require(status["bridge"] in BRIDGE_STATUSES, f"{path}: bad bridge status")

    if status["formal"] == "VERIFIED":
        _require(gates["G1"]["status"] == "PASS", f"{path}: formal VERIFIED without G1 PASS")
    if status["empirical"] == "ESTABLISHED":
        _require(gates["G3"]["status"] == "PASS", f"{path}: empirical ESTABLISHED without G3 PASS")
        _require(gates["G5"]["status"] == "PASS", f"{path}: empirical ESTABLISHED without G5 PASS")
    if status["bridge"] == "CLOSED":
        _require(gates["G3"]["status"] == "PASS", f"{path}: bridge CLOSED without G3 PASS")

    inputs = data["inputs"]
    _require(isinstance(inputs, list) and inputs, f"{path}: inputs must be a non-empty list")
    for entry in inputs:
        _require(isinstance(entry, dict), f"{path}: input entry must be an object")
        _require({"name", "value", "provenance", "source"} <= set(entry),
                 f"{path}: input entry missing name/value/provenance/source")
        _require(entry["provenance"] in INPUT_PROVENANCE,
                 f"{path}: bad input provenance {entry.get('provenance')}")

    agreement = data["reported_agreement"]
    _require({"value", "comparator", "uncertainty", "comparison_type"} <= set(agreement),
             f"{path}: reported_agreement missing fields")


def validate_kill_conditions(data: dict, path: Path) -> None:
    _require(isinstance(data, dict), f"{path}: top level must be an object")
    _require({"record_id", "version", "source_revision", "reviewer", "purpose", "entries"} <= set(data),
             f"{path}: missing top-level kill-condition fields")
    entries = data["entries"]
    _require(isinstance(entries, list) and entries, f"{path}: entries must be non-empty")
    seen = set()
    for entry in entries:
        _require(isinstance(entry, dict), f"{path}: entry must be an object")
        required = {"id", "claim", "anchor", "comparator", "kill_condition", "status", "source"}
        _require(required <= set(entry), f"{path}: entry missing fields: {sorted(required - set(entry))}")
        _require(entry["id"] not in seen, f"{path}: duplicate entry id {entry['id']}")
        seen.add(entry["id"])
        _require(isinstance(entry["claim"], str) and entry["claim"], f"{path}: empty claim")
        _require(isinstance(entry["comparator"], str) and entry["comparator"], f"{path}: empty comparator")
        _require(isinstance(entry["kill_condition"], str) and entry["kill_condition"],
                 f"{path}: empty kill_condition")
        _require(isinstance(entry["status"], str) and entry["status"], f"{path}: empty status")
        _require(entry["anchor"] is None or isinstance(entry["anchor"], str),
                 f"{path}: anchor must be a string or null")


def main() -> int:
    failures = []
    for path in CLAIM_FILES:
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            validate_claim_record(data, path)
            print(f"PASS claim record: {path.relative_to(ROOT)}")
        except Exception as exc:  # noqa: BLE001 - report all validation failures
            failures.append(f"{path}: {exc}")
    try:
        data = json.loads(KILL_FILE.read_text(encoding="utf-8"))
        validate_kill_conditions(data, KILL_FILE)
        print(f"PASS kill-condition record: {KILL_FILE.relative_to(ROOT)}")
    except Exception as exc:  # noqa: BLE001
        failures.append(f"{KILL_FILE}: {exc}")

    if failures:
        print("\nFAIL")
        for failure in failures:
            print(" -", failure)
        return 1
    print("\nPASS: claim records and kill-condition record are schema-valid and non-promoting.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
