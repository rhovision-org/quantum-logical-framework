"""Tests for the toy strange-loop / Markov-blanket observer model."""
from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location("strange_loop_observer", ROOT / "tools/strange_loop_observer.py")
model = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = model
SPEC.loader.exec_module(model)


class StrangeLoopObserverTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = model.run_model()

    def test_operational_malus_is_one_eighth(self) -> None:
        self.assertAlmostEqual(self.result["outputs"]["operational_malus"], 0.125, places=12)

    def test_pure_meet_blocks_at_the_second_polarizer(self) -> None:
        pure = self.result["details"]["pure_meet"]
        self.assertEqual(pure["transmission"], 0.0)
        self.assertEqual(pure["blocked_at"], 2)
        self.assertEqual(pure["state_before"], "az")
        self.assertEqual(pure["screen_element"], "ax")

    def test_uniform_reprepare_matches_but_is_not_unique(self) -> None:
        self.assertAlmostEqual(self.result["outputs"]["reprepare_uniform"], 0.125, places=12)
        self.assertNotAlmostEqual(
            self.result["outputs"]["reprepare_biased_0_6"],
            self.result["outputs"]["reprepare_uniform"],
            places=12,
        )

    def test_blanket_truncation_changes_the_result(self) -> None:
        self.assertEqual(self.result["outputs"]["blanket_first_two_stages"], 0.25)

    def test_self_reference_is_a_toy_fixed_point(self) -> None:
        self.assertTrue(self.result["details"]["self_reference"]["fixed_point"])
        self.assertEqual(self.result["details"]["self_reference"]["final_state"], "azp")

    def test_model_reports_underdetermination(self) -> None:
        self.assertTrue(self.result["underdetermined"])
        self.assertGreaterEqual(len(self.result["distinct_transmissions"]), 3)

    def test_result_is_json_serializable(self) -> None:
        text = json.dumps(self.result, sort_keys=True)
        self.assertIn("underdetermination", text)
        self.assertIn("not QLF evidence", text)


if __name__ == "__main__":
    unittest.main()
