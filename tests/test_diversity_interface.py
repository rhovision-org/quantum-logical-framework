"""Regression tests for the D3 conjugate-boundary interface census (#290)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import diversity_interface as di  # noqa: E402


class DiversityInterfaceTests(unittest.TestCase):
    def test_interface_condition(self) -> None:
        self.assertTrue(di.interface_ok("^", "v"))
        self.assertFalse(di.interface_ok("^", "^"))
        self.assertTrue(di.join("^", "v"))
        self.assertFalse(di.join("^", "^"))

    def test_closure_preservation(self) -> None:
        result = di.census()
        self.assertEqual(result["closure_failures"], 0)
        self.assertGreater(result["total_admitted_joins"], 0)

    def test_k_distribution(self) -> None:
        result = di.census()
        self.assertEqual(result["by_length"]["1"]["K_counts"], {"4": 8})
        self.assertEqual(result["by_length"]["2"]["K_counts"], {"1": 64})
        self.assertEqual(
            result["by_length"]["3"]["K_counts"],
            {"1": 64, "2": 384, "4": 16, "6": 48},
        )

    def test_interface_dependence_witnesses(self) -> None:
        result = di.census()
        self.assertTrue(result["interface_dependence"]["pass"])
        self.assertEqual(result["interface_dependence"]["distinct_K_values"], [1, 2, 4, 6])
        self.assertEqual(result["witnesses"]["^v<"]["K"], 6)
        self.assertEqual(result["witnesses"]["^^^"]["K"], 1)
        self.assertEqual(result["witnesses"]["^<^"]["K"], 2)

    def test_d8c2_is_not_run(self) -> None:
        result = di.census()
        self.assertEqual(result["d8c2"], "not run")
        summary = di.build_summary()
        self.assertEqual(summary["gates"]["D8c2_matched_comparison"], "not run")

    def test_no_advantage_claim(self) -> None:
        summary = di.build_summary()
        self.assertIn("pass", summary["gates"]["D3.1_interface_dependence"])
        self.assertIn("pass", summary["gates"]["D3.2_closure_preservation"])
        self.assertNotIn("advantage", summary["census"]["verdict"])


if __name__ == "__main__":
    unittest.main()
