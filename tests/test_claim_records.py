"""Regression tests for evidence-record structure, discovery and promotion paths."""
from __future__ import annotations

import contextlib
import hashlib
import copy
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("validate_claim_records", ROOT / "scripts/validate_claim_records.py")
validator = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(validator)


class ClaimRecordTests(unittest.TestCase):
    def setUp(self) -> None:
        self.alpha = json.loads((ROOT / "claim_records/alpha.json").read_text())
        self.kill = json.loads((ROOT / "claim_records/kill_conditions.json").read_text())

    def rejects(self, data: dict) -> None:
        with self.assertRaises(validator.ValidationError):
            validator.validate_claim_record(data, Path("fixture.json"))

    def promoted(self, component: str) -> dict:
        data = copy.deepcopy(self.alpha)
        for gate in validator.PROMOTION_GATES[component]:
            data["gate_outcomes"][gate]["status"] = "PASS"
        data["evidence_status"][component] = {
            "formal": "VERIFIED", "numerical": "REPRODUCED",
            "empirical": "ESTABLISHED", "bridge": "CLOSED",
        }[component]
        data["reviewer_independence"]["receipt"] = {
            "reviewer": "synthetic unit-test fixture, not an actual receipt",
            "source_revision": data["source_revision"],
            "scopes": ["source_review", "numerical_reproduction", "kernel_audit", "empirical_replication"],
            "artifacts": [{"path": "synthetic.log", "sha256": "a" * 64}],
        }
        if component in {"empirical", "bridge"}:
            data["evidence_status"]["bridge"] = "CLOSED"
            for gate in validator.PROMOTION_GATES["bridge"]:
                data["gate_outcomes"][gate]["status"] = "PASS"
            data["strange_loop"]["status"] = "TESTED"
            data["strange_loop"]["proof_obligation"]["conservative_return_status"] = "PROVED"
            data["strange_loop"]["proof_obligation"]["proof_artifact"] = {
                "path": "lean/QLF_TensorConservativeReturn.lean",
                "anchors": ["QLF.TensorConservativeReturn.tensor_conservative_return"],
            }
        if component == "empirical":
            data["reported_agreement"]["comparison_type"] = "prospective"
            data["measurement_protocol"]["execution_status"] = "prospective_completed"
        return data

    def test_records_validate(self) -> None:
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(validator.main(), 0)

    def test_each_complete_promotion_path_is_accepted(self) -> None:
        for component in validator.PROMOTION_GATES:
            with self.subTest(component=component):
                validator.validate_claim_record(self.promoted(component), Path("synthetic.json"))

    def test_every_mandatory_gate_blocks_every_promotion(self) -> None:
        # The expectation is independently specified by Paper I's gate matrix.
        paths = {"formal": {"G0", "G1", "G2", "G6"}, "numerical": {"G0", "G4", "G6"},
                 "empirical": {"G0", "G3", "G4", "G5", "G6"}, "bridge": {"G0", "G2", "G3", "G6"}}
        for component, gates in paths.items():
            for gate in gates:
                for outcome in ("FAIL", "INCONCLUSIVE", "INCOMPLETE", "NOT_APPLICABLE"):
                    with self.subTest(component=component, gate=gate, outcome=outcome):
                        bad = self.promoted(component)
                        bad["gate_outcomes"][gate]["status"] = outcome
                        self.rejects(bad)

    def test_empty_semantic_objects_are_rejected(self) -> None:
        fields = ("approximation_or_regime", "formal_statement", "formal_object", "dependencies",
                  "interpretation", "observable", "measurement_protocol", "evidence", "defeaters",
                  "reviewer_independence", "provenance", "gate_outcomes", "evidence_status")
        for field in fields:
            for empty in (None, {}, [], "", " "):
                with self.subTest(field=field, empty=empty):
                    bad = copy.deepcopy(self.alpha)
                    bad[field] = empty
                    self.rejects(bad)

    def test_malformed_versions_and_revisions_are_rejected(self) -> None:
        for field, value in (("version", 3), ("version", "0.30"), ("version", "0.3garbage"),
                             ("source_revision", "main"), ("source_revision", "not-a-commit"),
                             ("source_revision", "a" * 39), ("source_revision", None)):
            with self.subTest(field=field, value=value):
                bad = copy.deepcopy(self.alpha)
                bad[field] = value
                self.rejects(bad)

    def test_unknown_comparison_and_execution_types_are_rejected(self) -> None:
        for field, key in (("reported_agreement", "comparison_type"), ("measurement_protocol", "execution_status")):
            bad = copy.deepcopy(self.alpha)
            bad[field][key] = "anything"
            self.rejects(bad)

    def test_retrodiction_cannot_become_empirical_by_flipping_gates(self) -> None:
        for comparison in ("retrodiction", "consistency", "not_applicable"):
            bad = self.promoted("empirical")
            bad["reported_agreement"]["comparison_type"] = comparison
            self.rejects(bad)

    def test_unexecuted_prospective_protocol_cannot_be_established(self) -> None:
        bad = self.promoted("empirical")
        bad["measurement_protocol"]["execution_status"] = "not_performed"
        self.rejects(bad)

    def test_retrospective_blind_promotion_requires_independent_replication(self) -> None:
        good = self.promoted("empirical")
        good["reported_agreement"]["comparison_type"] = "retrospective blind"
        good["measurement_protocol"]["execution_status"] = "independently_replicated"
        good["reviewer_independence"]["independence_tier"] = "independent"
        validator.validate_claim_record(good, Path("synthetic.json"))
        for tier in ("self", "collaborator"):
            bad = copy.deepcopy(good)
            bad["reviewer_independence"]["independence_tier"] = tier
            self.rejects(bad)

    def test_empirical_status_and_g3_cannot_coexist_with_open_bridge(self) -> None:
        bad = self.promoted("empirical")
        bad["evidence_status"]["bridge"] = "OPEN"
        self.rejects(bad)

    def test_reproduced_numerics_require_g4(self) -> None:
        bad = self.promoted("numerical")
        bad["gate_outcomes"]["G4"]["status"] = "FAIL"
        self.rejects(bad)

    def test_receipt_must_match_revision_and_scope(self) -> None:
        for component, scope in (("formal", "kernel_audit"), ("numerical", "numerical_reproduction"),
                                 ("empirical", "empirical_replication")):
            bad = self.promoted(component)
            bad["reviewer_independence"]["receipt"]["scopes"].remove(scope)
            self.rejects(bad)
        bad = self.promoted("formal")
        bad["reviewer_independence"]["receipt"]["source_revision"] = "f" * 40
        self.rejects(bad)
        bad = self.promoted("formal")
        bad["reviewer_independence"]["receipt"] = None
        self.rejects(bad)

    def test_self_run_is_not_a_completed_review_receipt(self) -> None:
        bad = self.promoted("formal")
        bad["reviewer_independence"]["independence_tier"] = "self"
        self.rejects(bad)

    def test_contradictory_source_pins_are_rejected(self) -> None:
        bad = copy.deepcopy(self.alpha)
        bad["provenance"]["source_revision"] = "f" * 40
        self.rejects(bad)

    def test_missing_approximation_field_is_rejected(self) -> None:
        bad = copy.deepcopy(self.alpha)
        del bad["approximation_or_regime"]
        self.rejects(bad)

    def test_input_provenance_and_content_are_checked(self) -> None:
        for key, value in (("provenance", "guessed"), ("name", " "), ("source", None), ("value", [])):
            bad = copy.deepcopy(self.alpha)
            bad["inputs"][0][key] = value
            self.rejects(bad)
        bad = copy.deepcopy(self.alpha)
        bad["inputs"].append(copy.deepcopy(bad["inputs"][0]))
        self.rejects(bad)

    def test_invalid_theorem_reference_is_rejected(self) -> None:
        bad = copy.deepcopy(self.alpha)
        bad["formal_statement"]["theorems"] = ["QLF.one; QLF.two"]
        self.rejects(bad)

    def test_kill_conditions_validate_as_drafts(self) -> None:
        self.assertTrue(all(e["status"] == "DRAFT" for e in self.kill["entries"]))
        validator.validate_kill_conditions(self.kill, Path("kill.json"))

    def registered_ledger(self) -> dict:
        data = copy.deepcopy(self.kill)
        data["entries"] = [data["entries"][0]]
        entry = data["entries"][0]
        entry["status"] = "REGISTERED"
        entry["registration"] = {key: "synthetic specification" for key in entry["registration"]}
        entry["registration"].update(specification_revision="b" * 40,
                                     registered_at="2026-11-10T18:00:00Z", data_access="before_target_access")
        return data

    def test_complete_registration_structure_is_accepted(self) -> None:
        validator.validate_kill_conditions(self.registered_ledger(), Path("synthetic-kill.json"))

    def test_unfinished_registration_is_rejected(self) -> None:
        for field in self.kill["entries"][0]["registration"]:
            bad = self.registered_ledger()
            bad["entries"][0]["registration"][field] = None
            with self.subTest(field=field), self.assertRaises(validator.ValidationError):
                validator.validate_kill_conditions(bad, Path("kill.json"))

    def test_registration_requires_qualified_anchors_and_documented_chronology(self) -> None:
        cases = (("anchors", ["QLF.one; QLF.two"]), ("anchors", None), ("status", "pre-registered"))
        for field, value in cases:
            bad = copy.deepcopy(self.kill)
            bad["entries"][0][field] = value
            with self.assertRaises(validator.ValidationError):
                validator.validate_kill_conditions(bad, Path("kill.json"))
        for field, value in (("registered_at", "2026-11-10"), ("registered_at", "not-a-date"),
                             ("specification_revision", "main"), ("data_access", "prior_public_data")):
            bad = self.registered_ledger()
            bad["entries"][0]["registration"][field] = value
            with self.assertRaises(validator.ValidationError):
                validator.validate_kill_conditions(bad, Path("kill.json"))

    def test_duplicate_kill_ids_are_rejected(self) -> None:
        bad = copy.deepcopy(self.kill)
        bad["entries"].append(copy.deepcopy(bad["entries"][0]))
        with self.assertRaises(validator.ValidationError):
            validator.validate_kill_conditions(bad, Path("kill.json"))

    def test_discovery_checks_new_nested_records_and_duplicate_ids(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory / "alpha.json").write_text(json.dumps(self.alpha))
            validator.validate_directory(directory)
            nested = directory / "nested"
            nested.mkdir()
            future = copy.deepcopy(self.alpha)
            future["record_id"] = "QLF-FUTURE-001"
            (nested / "future.json").write_text(json.dumps(future))
            self.assertEqual(len(validator.validate_directory(directory)), 2)
            future["record_id"] = self.alpha["record_id"]
            (nested / "future.json").write_text(json.dumps(future))
            with self.assertRaises(validator.ValidationError):
                validator.validate_directory(directory)
            (nested / "future.json").write_text('{"record_type":"unknown"}')
            with self.assertRaises(validator.ValidationError):
                validator.validate_directory(directory)

    def test_receipt_artifact_integrity_and_path_confinement(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = root / "claim_records"
            directory.mkdir()
            artifact = root / "synthetic.log"
            artifact.write_text("synthetic fixture, no real verification")
            data = self.promoted("formal")
            data["reviewer_independence"]["receipt"]["artifacts"] = [
                {"path": "synthetic.log", "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest()}]
            record = directory / "fixture.json"
            record.write_text(json.dumps(data))
            validator.validate_directory(directory, repository_root=root)
            artifact.write_text("tampered")
            with self.assertRaises(validator.ValidationError):
                validator.validate_directory(directory, repository_root=root)
            for unsafe in ("../outside.log", str(artifact)):
                data["reviewer_independence"]["receipt"]["artifacts"][0]["path"] = unsafe
                record.write_text(json.dumps(data))
                with self.assertRaises(validator.ValidationError):
                    validator.validate_directory(directory, repository_root=root)

    def test_empty_directory_duplicate_json_keys_and_nan_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            with self.assertRaises(validator.ValidationError):
                validator.validate_directory(directory)
            for text in ('{"record_type":"claim","record_type":"test_ledger"}', '{"x":NaN}'):
                (directory / "bad.json").write_text(text)
                with self.assertRaises(validator.ValidationError):
                    validator.validate_directory(directory)

    def test_closed_bridge_requires_tested_strange_loop(self) -> None:
        good = self.promoted("bridge")
        validator.validate_claim_record(good, Path("synthetic.json"))
        bad = copy.deepcopy(good)
        bad["strange_loop"]["status"] = "B-OPEN"
        self.rejects(bad)
        bad = copy.deepcopy(good)
        del bad["strange_loop"]
        self.rejects(bad)

    def test_strange_loop_requires_typed_levels_and_fields(self) -> None:
        bad = copy.deepcopy(self.alpha)
        bad["strange_loop"]["levels"] = ["only one level"]
        self.rejects(bad)
        for field in ("return_level", "conservative_return", "noncircularity_witness", "defeater"):
            bad = copy.deepcopy(self.alpha)
            del bad["strange_loop"][field]
            self.rejects(bad)
        bad = copy.deepcopy(self.alpha)
        bad["strange_loop"]["status"] = "CLOSED"
        self.rejects(bad)
        bad = copy.deepcopy(self.alpha)
        del bad["strange_loop"]["proof_obligation"]["domain"]
        self.rejects(bad)
        bad = copy.deepcopy(self.alpha)
        bad["strange_loop"]["proof_obligation"]["conservative_return_status"] = "DONE"
        self.rejects(bad)
        bad = copy.deepcopy(self.alpha)
        bad["strange_loop"]["first_order_evidence"] = "ESTABLISHED"
        self.rejects(bad)

    def test_tested_loop_requires_proved_return_obligation(self) -> None:
        good = self.promoted("bridge")
        validator.validate_claim_record(good, Path("synthetic.json"))
        bad = copy.deepcopy(good)
        bad["strange_loop"]["proof_obligation"]["conservative_return_status"] = "NOT_STARTED"
        self.rejects(bad)
        bad = copy.deepcopy(good)
        bad["strange_loop"]["proof_obligation"]["proof_artifact"] = "not yet supplied"
        self.rejects(bad)

    def test_proved_return_rejects_missing_or_unreviewed_artifact(self) -> None:
        good = self.promoted("bridge")
        validator.validate_claim_record(good, Path("synthetic.json"))
        for artifact in (
            "synthetic theorem, not a real proof",
            {"path": "does/not/exist.lean", "anchors": ["QLF.TensorConservativeReturn.tensor_conservative_return"]},
            {"path": "lean/QLF_TensorConservativeReturn.lean", "anchors": ["QLF.Does.not_exist"]},
            {"path": "lean/QLF_TensorConservativeReturn.lean", "anchors": ["QLF.FirstReturn.prime_event_reciprocal_open"]},
        ):
            with self.subTest(artifact=artifact):
                bad = copy.deepcopy(good)
                bad["strange_loop"]["proof_obligation"]["proof_artifact"] = artifact
                self.rejects(bad)


if __name__ == "__main__":
    unittest.main()
