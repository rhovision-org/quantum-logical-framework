"""Regression tests for the D8c2b negative revision synthesis (#290)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import diversity_advantage_variants as dv  # noqa: E402


class DiversityAdvantageVariantsTests(unittest.TestCase):
    def test_phase_revision_is_empty(self) -> None:
        result = dv.phase_census()
        self.assertEqual(result["total_bases"], 37376)
        self.assertEqual(result["bases_with_added_classes"], 0)
        self.assertEqual(result["verdict"], "phase_label_adds_no_classes")

    def test_two_interface_is_negative(self) -> None:
        result = dv.two_interface_census()
        self.assertEqual(result["total_bases"], 4608)
        self.assertEqual(result["null_differences"], 0)
        self.assertTrue(result["null_matches_exactly"])
        self.assertEqual(result["verdict"], "negative_no_two_interface_advantage")

    def test_two_interface_means(self) -> None:
        result = dv.two_interface_census()
        self.assertEqual(result["by_length"]["3"]["homogeneous_mean_K2"], 0.21428571428571427)
        self.assertEqual(result["by_length"]["3"]["heterogeneous_mean_K2"], 0.07142857142857142)
        self.assertEqual(result["by_length"]["4"]["homogeneous_mean_K2"], 0.55)
        self.assertEqual(result["by_length"]["4"]["heterogeneous_mean_K2"], 0.2785714285714286)
        for stats in result["by_length"].values():
            self.assertFalse(stats["heterogeneous_advantage"])

    def test_d8c2_remains_unpassed(self) -> None:
        summary = dv.build_summary()
        self.assertIn("fail", summary["gates"]["D8c2b_phase_revision"])
        self.assertIn("fail", summary["gates"]["D8c2b_two_interface"])
        self.assertIn("not passed", summary["gates"]["D8c2"])


if __name__ == "__main__":
    unittest.main()
