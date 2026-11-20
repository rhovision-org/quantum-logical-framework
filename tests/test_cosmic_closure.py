"""Regression tests for cosmic closure (#276)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import cosmic_closure as cc  # noqa: E402


class CosmicClosureTests(unittest.TestCase):
    def test_self_test(self) -> None:
        cc.self_test()

    def test_logical_origin(self) -> None:
        self.assertTrue(cc.is_closed("+-"))
        self.assertTrue(cc.is_closed("^v"))
        self.assertFalse(cc.is_closed("^<v"))
        self.assertEqual(cc.net("^<v"), (0, -1, 0, 0))

    def test_first_completions_and_measure(self) -> None:
        completions = cc.first_completions("^", 4)
        self.assertEqual(len(completions), 14)
        measured = cc.measure(completions)
        self.assertEqual(measured["W_micro"], 14)
        self.assertAlmostEqual(sum(measured["normalized"]), 1.0)
        self.assertGreater(
            measured["by_length"]["2"]["P_total"],
            measured["by_length"]["4"]["P_total"],
        )

    def test_holographic_compression(self) -> None:
        self.assertTrue(cc.compression_preserves(cc.SAFE_BOUNDARY, cc.OBSERVABLE))
        self.assertFalse(cc.compression_preserves(cc.LOSSY_BOUNDARY, cc.OBSERVABLE))
        stats = cc.compression_stats(cc.SAFE_BOUNDARY)
        self.assertEqual(stats["interiors"], 6)
        self.assertEqual(stats["boundary_classes"], 3)

    def test_unbounded_extension(self) -> None:
        time = cc.time_gate()
        self.assertTrue(time["finite_at_every_witness"])
        self.assertEqual(len(time["witnesses"]), 6)
        self.assertEqual(time["physical_eternal"], "interpretation, not proved")

    def test_cosmic_clock(self) -> None:
        clock = cc.clock_gate()
        self.assertFalse(clock["N_derived"])
        self.assertIsNone(clock["numerical_age_claim"])

    def test_summary_schema(self) -> None:
        summary = cc.build_summary()
        self.assertEqual(summary["meta"]["issue"], 276)
        self.assertIn("logical_origin", summary)
        self.assertIn("measure", summary)
        self.assertIn("holography", summary)
        self.assertIn("time", summary)
        self.assertIn("clock", summary)
        self.assertEqual(summary["gates"]["G6_cosmic_clock"].split(";")[0], "N not derived")


if __name__ == "__main__":
    unittest.main()
