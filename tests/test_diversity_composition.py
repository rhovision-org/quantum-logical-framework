"""Regression tests for the D8a cross-type composition witness (#290)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import diversity_composition as dc  # noqa: E402


class DiversityCompositionTests(unittest.TestCase):
    def test_primitive_witness(self) -> None:
        self.assertTrue(dc.is_zfa("^v"))
        self.assertFalse(dc.is_zfa("^"))
        self.assertFalse(dc.is_zfa("v"))
        self.assertEqual(dc.kind("^"), (1, 0, 0, 0))
        self.assertEqual(dc.kind("v"), (-1, 0, 0, 0))
        self.assertEqual(dc.kind("^v"), (0, 0, 0, 0))

    def test_admissible_cross_composition(self) -> None:
        self.assertTrue(dc.admissible_composition("^", "v"))
        self.assertTrue(dc.has_cross_composition())
        self.assertNotEqual(dc.kind("^"), dc.kind("v"))

    def test_same_type_is_not_admissible_in_this_census(self) -> None:
        self.assertFalse(dc.admissible_composition("^", "^"))
        self.assertFalse(dc.admissible_composition("v", "v"))

    def test_census_witness(self) -> None:
        result = dc.census()
        self.assertGreater(result["cross_type_compositions"], 0)
        self.assertEqual(result["same_type_compositions"], 0)
        witness = result["cross_type_witness"]
        self.assertEqual(witness["a"], "^")
        self.assertEqual(witness["b"], "v")
        self.assertEqual(witness["composite"], "^v")
        self.assertTrue(witness["composite_closed"])

    def test_gate_labels_do_not_overclaim(self) -> None:
        summary = dc.build_summary()
        self.assertIn("pass", summary["gates"]["D8a_cross_composition"])
        self.assertIn("open", summary["gates"]["D8b_novel_outcome"])
        self.assertIn("open", summary["gates"]["D8c_measured_advantage"])


if __name__ == "__main__":
    unittest.main()
