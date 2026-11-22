"""Regression tests for the spatial-response finite ledger (#287)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import spatial_response as sr  # noqa: E402


class SpatialResponseTests(unittest.TestCase):
    def test_orientation_ledger(self) -> None:
        self.assertEqual(sr.joint_space(True, True), 2)
        self.assertEqual(sr.joint_space(True, False), -2)
        self.assertEqual(sr.net_space([(True, True), (True, True)]), 4)
        self.assertEqual(sr.net_space([(True, False), (True, False)]), -4)
        self.assertEqual(sr.net_space([(True, True), (True, False)]), 0)

    def test_closure_distance_is_separate(self) -> None:
        self.assertEqual(sr.closure_distance((False, False)), 0)
        self.assertEqual(sr.closure_distance((True, False)), 1)
        self.assertEqual(sr.closure_distance((True, True)), 2)

    def test_event_updates_are_independent(self) -> None:
        config = sr.Config(history=(), bits=(False, True))
        like = sr.apply_event(config, sr.Event("like", 1))
        self.assertEqual(sr.net_space(like.history), 2)
        self.assertEqual(sr.closure_distance(like.bits), 0)  # the only True bit flipped off
        opposite = sr.apply_event(config, sr.Event("opposite", None))
        self.assertEqual(sr.net_space(opposite.history), -2)
        self.assertEqual(sr.closure_distance(opposite.bits), 1)  # unchanged

    def test_binding_does_not_imply_contraction(self) -> None:
        ledger = sr.census()
        self.assertGreater(ledger["binding_events"], 0)
        self.assertFalse(ledger["binding_implies_contraction"])
        self.assertGreater(ledger["categories"]["binding_and_contraction"], 0)
        self.assertGreater(ledger["categories"]["binding_and_expansion"], 0)
        self.assertEqual(ledger["categories"]["binding_and_neutral"], 0)

    def test_examples_have_opposite_spatial_signs(self) -> None:
        examples = sr.census()["examples"]
        self.assertLess(examples["binding_contraction"]["delta_s"], 0)
        self.assertGreater(examples["binding_expansion"]["delta_s"], 0)
        self.assertEqual(examples["binding_contraction"]["delta_d"], -1)
        self.assertEqual(examples["binding_expansion"]["delta_d"], -1)

    def test_summary_schema(self) -> None:
        summary = sr.build_summary()
        self.assertEqual(summary["meta"]["issue"], 287)
        self.assertIn("SR0_definition", summary["gates"])
        self.assertIn("SR3_independence", summary["gates"])
        self.assertEqual(
            summary["gates"]["SR4_gravity"],
            "open; no coarse-graining or curvature claim",
        )
        self.assertEqual(
            summary["gates"]["SR7_3d"],
            "open; boolean ledger is not a 3D metric",
        )


if __name__ == "__main__":
    unittest.main()
