#!/usr/bin/env python3
"""Validate typed QLF claim records and draft/registered falsification ledgers.

This checks structural completeness and declared gate consistency. It does not
execute Lean, authenticate receipts, establish blinding, or decide physical truth.
"""
from __future__ import annotations

import json
import hashlib
import re
import sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIM_FIELDS = {
    "record_type", "record_id", "version", "source_revision", "informal_statement",
    "approximation_or_regime", "formal_statement", "formal_object", "dependencies",
    "inputs", "interpretation", "strange_loop", "observable", "measurement_protocol",
    "reported_agreement", "evidence", "defeaters", "gate_outcomes",
    "evidence_status", "reviewer_independence", "provenance",
}
GATE_NAMES = {f"G{i}" for i in range(7)}
GATE_STATUSES = {"PASS", "FAIL", "INCONCLUSIVE", "INCOMPLETE", "NOT_APPLICABLE"}
STRANGE_LOOP_FIELDS = {
    "name", "levels", "return_level", "conservative_return",
    "noncircularity_witness", "status", "first_order_evidence",
    "first_order_note", "defeater", "proof_obligation",
}
STRANGE_LOOP_STATUSES = {"B-OPEN", "SPECIFIED", "TESTED"}
FIRST_ORDER_EVIDENCE = {"F", "N", "F+N", "NONE"}
PROOF_OBLIGATION_FIELDS = {
    "domain", "codomain", "forward_map", "return_map",
    "composite_identity_on", "conservative_return_status",
    "proof_artifact", "imported_axioms", "falsifier",
}
PROOF_OBLIGATION_STATUSES = {"NOT_STARTED", "PARTIAL", "PROVED"}
COMPARISON_TYPES = {"prospective", "retrospective blind", "retrodiction", "consistency", "not_applicable"}
EXECUTION_STATUSES = {"not_performed", "retrospective_reproduction", "prospective_completed", "independently_replicated"}
INPUT_PROVENANCE = {"derived", "declared", "fitted", "external"}
TIERS = {"self", "collaborator", "independent"}
RECEIPT_SCOPES = {"source_review", "numerical_reproduction", "kernel_audit", "empirical_replication"}
SHA1 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
ANCHOR = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)+\Z")
VERSION = re.compile(r"0\.3(?:\.\d+)?(?:-[a-z0-9][a-z0-9.-]*)?\Z")
PROMOTION_GATES = {
    "formal": {"G0", "G1", "G2", "G6"},
    "numerical": {"G0", "G4", "G6"},
    "empirical": {"G0", "G3", "G4", "G5", "G6"},
    "bridge": {"G0", "G2", "G3", "G6"},
}


class ValidationError(ValueError):
    """A record fails the documented schema or a promotion invariant."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def _text(value: object, label: str) -> None:
    _require(isinstance(value, str) and bool(value.strip()), f"{label}: expected non-empty text")


def _object(value: object, label: str, required: set[str], *, exact: bool = False) -> dict:
    _require(isinstance(value, dict), f"{label}: expected an object")
    _require(required <= set(value), f"{label}: missing fields {sorted(required - set(value))}")
    if exact:
        _require(set(value) == required, f"{label}: unexpected fields {sorted(set(value) - required)}")
    return value


def _texts(value: object, label: str) -> list:
    _require(isinstance(value, list) and bool(value), f"{label}: expected a non-empty list")
    for i, entry in enumerate(value):
        _text(entry, f"{label}[{i}]")
    _require(len(value) == len(set(value)), f"{label}: duplicate values")
    return value


def _revision(value: object, label: str) -> None:
    _require(isinstance(value, str) and SHA1.fullmatch(value) is not None,
             f"{label}: expected a full lowercase 40-digit Git revision")


def _metadata(data: dict, path: Path) -> None:
    for field in ("record_id", "version", "source_revision"):
        _text(data[field], f"{path}.{field}")
    _require(VERSION.fullmatch(data["version"]) is not None, f"{path}: expected version 0.3[.patch][-suffix]")
    _revision(data["source_revision"], f"{path}.source_revision")


def _gates(gates: object, path: Path) -> dict:
    gates = _object(gates, f"{path}.gate_outcomes", GATE_NAMES, exact=True)
    for name, gate in gates.items():
        _object(gate, f"{path}.{name}", {"status", "reason"}, exact=True)
        _text(gate["status"], f"{path}.{name}.status")
        _require(gate["status"] in GATE_STATUSES, f"{path}: bad gate status {name}")
        _text(gate["reason"], f"{path}.{name}.reason")
    return gates


def _receipt(data: dict, gates: dict, path: Path) -> dict | None:
    review = _object(data["reviewer_independence"], f"{path}.reviewer_independence", {
        "source_inspection", "enumeration", "original_lean_kernel", "measurement",
        "independence_tier", "receipt",
    })
    for field in ("source_inspection", "enumeration", "original_lean_kernel", "measurement", "independence_tier"):
        _text(review[field], f"{path}.reviewer_independence.{field}")
    _require(review["independence_tier"] in TIERS, f"{path}: invalid independence tier")
    if gates["G6"]["status"] == "PASS":
        _require(review["independence_tier"] != "self", f"{path}: a self-run record is not a completed external/collaborator receipt")
    receipt = review["receipt"]
    if receipt is None:
        _require(gates["G6"]["status"] != "PASS", f"{path}: G6 PASS requires a receipt")
        return None
    _object(receipt, f"{path}.receipt", {"reviewer", "source_revision", "scopes", "artifacts"}, exact=True)
    _text(receipt["reviewer"], f"{path}.receipt.reviewer")
    _revision(receipt["source_revision"], f"{path}.receipt.source_revision")
    _require(receipt["source_revision"] == data["source_revision"], f"{path}: receipt revision differs from claim revision")
    scopes = _texts(receipt["scopes"], f"{path}.receipt.scopes")
    _require(set(scopes) <= RECEIPT_SCOPES, f"{path}: unknown receipt scope")
    artifacts = receipt["artifacts"]
    _require(isinstance(artifacts, list) and bool(artifacts), f"{path}: receipt artifacts required")
    for artifact in artifacts:
        _object(artifact, f"{path}.receipt.artifact", {"path", "sha256"}, exact=True)
        _text(artifact["path"], f"{path}.receipt.artifact.path")
        _require(isinstance(artifact["sha256"], str) and SHA256.fullmatch(artifact["sha256"]) is not None,
                 f"{path}: invalid receipt artifact digest")
    return receipt


def validate_claim_record(data: dict, path: Path) -> None:
    _object(data, str(path), CLAIM_FIELDS, exact=True)
    _require(data["record_type"] == "claim", f"{path}: record_type must be claim")
    _metadata(data, path)
    _text(data["informal_statement"], f"{path}.informal_statement")
    required_text_objects = {
        "approximation_or_regime": {"name", "description", "validity_limits"},
        "dependencies": {"lean_toolchain", "mathlib", "audit_baseline", "qlf_bridge_axioms"},
        "interpretation": {"map", "formal_status", "noncircularity_test"},
        "observable": {"symbol", "baseline", "uncertainties"},
        "measurement_protocol": {"status", "design", "failure_condition", "execution_status"},
        "reported_agreement": {"value", "comparator", "uncertainty", "comparison_type"},
        "evidence": {"F", "N", "E", "reviewer"},
        "defeaters": {"formal", "interpretation", "numerical", "empirical", "conceptual"},
    }
    for field, required in required_text_objects.items():
        obj = _object(data[field], f"{path}.{field}", required)
        for key in required:
            _text(obj[key], f"{path}.{field}.{key}")
    _revision(data["dependencies"]["mathlib"], f"{path}.dependencies.mathlib")
    statement = _object(data["formal_statement"], f"{path}.formal_statement", {"namespace", "theorems", "statement_scope"})
    _text(statement["namespace"], f"{path}.formal_statement.namespace")
    _text(statement["statement_scope"], f"{path}.formal_statement.statement_scope")
    for theorem in _texts(statement["theorems"], f"{path}.formal_statement.theorems"):
        _require(ANCHOR.fullmatch(theorem) is not None, f"{path}: invalid qualified theorem name {theorem!r}")
    formal = _object(data["formal_object"], f"{path}.formal_object", {"primary_files", "type"})
    _texts(formal["primary_files"], f"{path}.formal_object.primary_files")
    _text(formal["type"], f"{path}.formal_object.type")
    if "analysis_files" in formal:
        _texts(formal["analysis_files"], f"{path}.formal_object.analysis_files")
    if "reported_values" in data["observable"]:
        values = _object(data["observable"]["reported_values"], f"{path}.observable.reported_values", set())
        _require(bool(values), f"{path}: reported_values is empty")
        for name, value in values.items():
            _text(value, f"{path}.observable.reported_values.{name}")
    provenance = _object(data["provenance"], f"{path}.provenance", {"repository", "source_revision", "reference_documents", "status"})
    _text(provenance["repository"], f"{path}.provenance.repository")
    _text(provenance["status"], f"{path}.provenance.status")
    _texts(provenance["reference_documents"], f"{path}.provenance.reference_documents")
    _require(provenance["source_revision"] == data["source_revision"], f"{path}: contradictory provenance revision")
    inputs = data["inputs"]
    _require(isinstance(inputs, list) and bool(inputs), f"{path}: inputs must be a non-empty list")
    names = []
    for entry in inputs:
        _object(entry, f"{path}.input", {"name", "value", "provenance", "source"}, exact=True)
        for key, value in entry.items():
            _text(value, f"{path}.input.{key}")
        _require(entry["provenance"] in INPUT_PROVENANCE, f"{path}: bad input provenance")
        names.append(entry["name"])
    _require(len(names) == len(set(names)), f"{path}: duplicate input names")
    comparison = data["reported_agreement"]["comparison_type"]
    execution = data["measurement_protocol"]["execution_status"]
    _require(comparison in COMPARISON_TYPES, f"{path}: unknown comparison type")
    _require(execution in EXECUTION_STATUSES, f"{path}: unknown measurement execution status")
    gates = _gates(data["gate_outcomes"], path)
    status = _object(data["evidence_status"], f"{path}.evidence_status", set(PROMOTION_GATES), exact=True)
    allowed = {
        "formal": {"VERIFIED", "CANDIDATE", "NOT_ESTABLISHED"},
        "numerical": {"REPRODUCED", "CANDIDATE", "NOT_ESTABLISHED"},
        "empirical": {"ESTABLISHED", "CANDIDATE", "NOT_ESTABLISHED"},
        "bridge": {"CLOSED", "OPEN", "NOT_APPLICABLE"},
    }
    for component, values in allowed.items():
        _text(status[component], f"{path}.evidence_status.{component}")
        _require(status[component] in values, f"{path}: invalid {component} status")
    loop = None
    if "strange_loop" in data:
        loop = _object(data["strange_loop"], f"{path}.strange_loop", STRANGE_LOOP_FIELDS, exact=True)
        for key in ("name", "return_level", "conservative_return", "noncircularity_witness", "status",
                    "first_order_evidence", "first_order_note", "defeater"):
            _text(loop[key], f"{path}.strange_loop.{key}")
        levels = _texts(loop["levels"], f"{path}.strange_loop.levels")
        _require(len(levels) >= 2, f"{path}: strange_loop requires at least two levels")
        _require(loop["status"] in STRANGE_LOOP_STATUSES, f"{path}: invalid strange_loop status")
        _require(loop["first_order_evidence"] in FIRST_ORDER_EVIDENCE,
                 f"{path}: invalid first_order_evidence")
        obligation = _object(
            loop["proof_obligation"], f"{path}.strange_loop.proof_obligation",
            PROOF_OBLIGATION_FIELDS, exact=True,
        )
        for key in PROOF_OBLIGATION_FIELDS:
            _text(obligation[key], f"{path}.strange_loop.proof_obligation.{key}")
        _require(
            obligation["conservative_return_status"] in PROOF_OBLIGATION_STATUSES,
            f"{path}: invalid conservative_return_status",
        )
        if obligation["conservative_return_status"] == "PROVED":
            _require(
                obligation["proof_artifact"].strip().lower() not in {"none", "not yet supplied", "n/a"},
                f"{path}: PROVED return requires a proof artifact",
            )
        if loop["status"] == "TESTED":
            _require(
                obligation["conservative_return_status"] == "PROVED",
                f"{path}: TESTED strange_loop requires a PROVED conservative return",
            )
    if status["bridge"] == "CLOSED":
        _require(loop is not None, f"{path}: a CLOSED bridge requires a strange_loop specification")
        _require(loop["status"] == "TESTED", f"{path}: a CLOSED bridge requires a TESTED strange_loop return")
    receipt = _receipt(data, gates, path)
    for component, promoted in {"formal": "VERIFIED", "numerical": "REPRODUCED", "empirical": "ESTABLISHED", "bridge": "CLOSED"}.items():
        if status[component] == promoted:
            blocked = sorted(g for g in PROMOTION_GATES[component] if gates[g]["status"] != "PASS")
            _require(not blocked, f"{path}: {component} {promoted} blocked by {blocked}")
    if status["formal"] == "VERIFIED":
        _require("kernel_audit" in receipt["scopes"], f"{path}: formal verification requires a kernel-audit receipt")
    if status["numerical"] == "REPRODUCED":
        _require("numerical_reproduction" in receipt["scopes"], f"{path}: numerical reproduction requires a matching receipt scope")
    if gates["G3"]["status"] == "PASS":
        _require(status["bridge"] == "CLOSED", f"{path}: G3 PASS contradicts an open/inapplicable bridge")
    if status["empirical"] == "ESTABLISHED":
        _require(status["bridge"] == "CLOSED", f"{path}: empirical establishment requires a closed bridge")
        _require("empirical_replication" in receipt["scopes"], f"{path}: empirical evidence requires an empirical receipt scope")
        prospective = comparison == "prospective" and execution == "prospective_completed"
        blind = (comparison == "retrospective blind" and execution == "independently_replicated"
                 and data["reviewer_independence"]["independence_tier"] == "independent")
        _require(prospective or blind, f"{path}: empirical establishment requires completed prospective or independently replicated blind evidence")


def validate_kill_conditions(data: dict, path: Path) -> None:
    _object(data, str(path), {"record_type", "record_id", "version", "source_revision", "reviewer", "purpose", "entries"}, exact=True)
    _require(data["record_type"] == "test_ledger", f"{path}: record_type must be test_ledger")
    _metadata(data, path)
    _text(data["reviewer"], f"{path}.reviewer")
    _text(data["purpose"], f"{path}.purpose")
    entries = data["entries"]
    _require(isinstance(entries, list) and bool(entries), f"{path}: entries must be non-empty")
    seen = set()
    registration_fields = {"specification_revision", "registered_at", "data_access", "observable", "analysis_rule", "uncertainty", "rejection_rule", "dataset_or_experiment", "chronology_evidence"}
    for entry in entries:
        _object(entry, f"{path}.entry", {"id", "claim", "anchors", "formal_scope", "comparator", "kill_condition", "status", "source", "registration"}, exact=True)
        for key in ("id", "claim", "formal_scope", "comparator", "kill_condition", "status", "source"):
            _text(entry[key], f"{path}.entry.{key}")
        _require(entry["id"] not in seen, f"{path}: duplicate entry ID {entry['id']}")
        seen.add(entry["id"])
        _require(entry["status"] in {"DRAFT", "REGISTERED", "RETIRED"}, f"{path}: invalid registration status")
        anchors = entry["anchors"]
        _require(isinstance(anchors, list), f"{path}: anchors must be a list (empty if none)")
        for anchor in anchors:
            _require(isinstance(anchor, str) and ANCHOR.fullmatch(anchor) is not None, f"{path}: invalid anchor")
        _require(len(anchors) == len(set(anchors)), f"{path}: duplicate anchors")
        reg = _object(entry["registration"], f"{path}.registration", registration_fields, exact=True)
        _text(reg["data_access"], f"{path}.registration.data_access")
        _require(reg["data_access"] in {"not_established", "prior_public_data", "before_target_access"}, f"{path}: invalid data-access status")
        for key in registration_fields - {"data_access"}:
            if reg[key] is not None:
                _text(reg[key], f"{path}.registration.{key}")
        if entry["status"] == "REGISTERED":
            for key in registration_fields:
                _text(reg[key], f"{path}.registered.{key}")
            _revision(reg["specification_revision"], f"{path}.registration.specification_revision")
            try:
                when = datetime.fromisoformat(reg["registered_at"].replace("Z", "+00:00"))
            except ValueError as exc:
                raise ValidationError(f"{path}: invalid registration timestamp") from exc
            _require(when.utcoffset() is not None, f"{path}: registration timestamp requires timezone")
            _require(reg["data_access"] == "before_target_access", f"{path}: registration requires documented pre-exposure status")


def _pairs(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        _require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _constant(value: str) -> None:
    raise ValidationError(f"non-JSON numeric constant: {value}")


def _artifact_integrity(data: dict, repository_root: Path, path: Path) -> None:
    if data["record_type"] != "claim" or data["gate_outcomes"]["G6"]["status"] != "PASS":
        return
    root = repository_root.resolve()
    for artifact in data["reviewer_independence"]["receipt"]["artifacts"]:
        relative = Path(artifact["path"])
        _require(not relative.is_absolute() and ".." not in relative.parts,
                 f"{path}: receipt artifact must be a repository-relative path")
        target = (root / relative).resolve()
        _require(root in target.parents, f"{path}: receipt artifact escapes the repository")
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        _require(actual == artifact["sha256"], f"{path}: receipt artifact digest mismatch: {relative}")


def validate_directory(directory: Path, *, repository_root: Path = ROOT) -> list[Path]:
    files = sorted(directory.rglob("*.json"))
    _require(bool(files), f"{directory}: no JSON records found")
    errors, seen = [], set()
    for path in files:
        try:
            data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_pairs, parse_constant=_constant)
            _require(isinstance(data, dict), f"{path}: top level must be an object")
            kind = data.get("record_type")
            if kind == "claim":
                validate_claim_record(data, path)
            elif kind == "test_ledger":
                validate_kill_conditions(data, path)
            else:
                raise ValidationError(f"{path}: unknown or missing record_type {kind!r}")
            _artifact_integrity(data, repository_root, path)
            _require(data["record_id"] not in seen, f"{path}: duplicate record ID {data['record_id']}")
            seen.add(data["record_id"])
        except (ValidationError, ValueError, OSError) as exc:
            errors.append(f"{path}: {exc}")
    _require(not errors, "\n".join(errors))
    return files


def main(root: Path | None = None) -> int:
    try:
        files = validate_directory((root or ROOT) / "claim_records", repository_root=root or ROOT)
    except (ValidationError, OSError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    for path in files:
        print(f"PASS record: {path.name}")
    print(f"PASS: {len(files)} typed records satisfy schema and declared promotion rules; truth/authenticity remain external checks.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
