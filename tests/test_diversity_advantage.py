"""Regression tests for the D8c2a axis-support screen (#290)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import diversity_advantage as da  # noqa: E402


class DiversityAdvantageTests(unittest.TestCase):
    def test_interface_join(self) -> None:
        self.assertTrue(da.interface_ok("^", "v"))
        self.assertTrue(da.join("^", "v"))
        self.assertFalse(da.join("^", "^"))

    def test_screen_is_negative(self) -> None:
        result = da.screen()
        self.assertEqual(result["total_bases"], 37376)
        self.assertEqual(result["null_differences"], 0)
        self.assertTrue(result["null_matches_exactly"])
        self.assertEqual(result["verdict"], "negative_no_heterogeneous_advantage")

    def test_no_length_shows_advantage(self) -> None:
        result = da.screen()
        for stats in result["by_length"].values():
            self.assertFalse(stats["heterogeneous_advantage"])

    def test_exact_length_three_and_five_means(self) -> None:
        result = da.screen()
        self.assertEqual(result["by_length"]["3"]["homogeneous_support_1"]["mean_K"], 2.5)
        self.assertEqual(result["by_length"]["3"]["heterogeneous_support_2_3"]["mean_K"], 2.2142857142857144)
        self.assertGreater(
            result["by_length"]["5"]["homogeneous_support_1"]["mean_K"],
            result["by_length"]["5"]["heterogeneous_support_2_3"]["mean_K"],
        )

    def test_d8c2_is_blocked_not_passed(self) -> None:
        summary = da.build_summary()
        self.assertIn("fail", summary["gates"]["D8c2a_heterogeneous_advantage"])
        self.assertIn("fail", summary["gates"]["D8c2a_null_separation"])
        self.assertIn("not run", summary["gates"]["D8c2_matched_population"])


if __name__ == "__main__":
    unittest.main()
