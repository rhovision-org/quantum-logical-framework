"""Tests for the claim-record and kill-condition validator."""
from __future__ import annotations

import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "validate_claim_records.py"
spec = importlib.util.spec_from_file_location("validate_claim_records", SCRIPT)
validator = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(validator)


class ClaimRecordTests(unittest.TestCase):
    def setUp(self) -> None:
        self.alpha = json.loads((ROOT / "claim_records" / "alpha.json").read_text())
        self.kill = json.loads((ROOT / "claim_records" / "kill_conditions.json").read_text())

    def test_records_validate(self) -> None:
        self.assertEqual(validator.main(), 0)

    def test_formal_promotion_without_g1_is_rejected(self) -> None:
        bad = copy.deepcopy(self.alpha)
        bad["evidence_status"]["formal"] = "VERIFIED"
        bad["gate_outcomes"]["G1"]["status"] = "INCONCLUSIVE"
        with self.assertRaises(validator.ValidationError):
            validator.validate_claim_record(bad, Path("alpha.json"))

    def test_empirical_promotion_without_g3_g5_is_rejected(self) -> None:
        bad = copy.deepcopy(self.alpha)
        bad["evidence_status"]["empirical"] = "ESTABLISHED"
        bad["gate_outcomes"]["G3"]["status"] = "INCONCLUSIVE"
        bad["gate_outcomes"]["G5"]["status"] = "INCONCLUSIVE"
        with self.assertRaises(validator.ValidationError):
            validator.validate_claim_record(bad, Path("alpha.json"))

    def test_bad_input_provenance_is_rejected(self) -> None:
        bad = copy.deepcopy(self.alpha)
        bad["inputs"][0]["provenance"] = "guessed"
        with self.assertRaises(validator.ValidationError):
            validator.validate_claim_record(bad, Path("alpha.json"))

    def test_missing_approximation_field_is_rejected(self) -> None:
        bad = copy.deepcopy(self.alpha)
        del bad["approximation_or_regime"]
        with self.assertRaises(validator.ValidationError):
            validator.validate_claim_record(bad, Path("alpha.json"))

    def test_kill_conditions_validate(self) -> None:
        validator.validate_kill_conditions(self.kill, Path("kill_conditions.json"))

    def test_kill_condition_missing_field_is_rejected(self) -> None:
        bad = copy.deepcopy(self.kill)
        del bad["entries"][0]["kill_condition"]
        with self.assertRaises(validator.ValidationError):
            validator.validate_kill_conditions(bad, Path("kill_conditions.json"))


if __name__ == "__main__":
    unittest.main()
