"""Regression tests for the co-incidence first slice (#283)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import coincidence as co  # noqa: E402


class CoincidenceTests(unittest.TestCase):
    def test_is_zfa_examples(self) -> None:
        self.assertTrue(co.is_zfa("^v"))
        self.assertTrue(co.is_zfa("<>"))
        self.assertTrue(co.is_zfa("+-"))
        self.assertFalse(co.is_zfa("^"))
        self.assertFalse(co.is_zfa("^^^^"))  # scalar fold, not count-balanced

    def test_trivial_first_twist_split(self) -> None:
        census = co.triviality_census(max_length=6)
        self.assertTrue(census["all_pass"], census["failures"])
        self.assertGreater(census["closed_words_checked"], 0)

    def test_primordial_strong_coincidence(self) -> None:
        result = co.coincides([co.ProvEvent("A", "^"), co.ProvEvent("B", "v")], "A", "B")
        self.assertIsNotNone(result)
        self.assertEqual(result["first_joint_closure"], 2)
        self.assertEqual(result["a"], "^")
        self.assertEqual(result["b"], "v")
        self.assertTrue(result["strong"])
        self.assertFalse(result["product_sector"])

    def test_gauge_pair_is_product_sector(self) -> None:
        result = co.coincides([co.ProvEvent("A", "+"), co.ProvEvent("B", "-")], "A", "B")
        self.assertIsNotNone(result)
        self.assertTrue(result["product_sector"])
        self.assertFalse(result["strong"])

    def test_same_origin_is_not_coincidence(self) -> None:
        self.assertIsNone(co.coincides([co.ProvEvent("A", "^"), co.ProvEvent("A", "v")], "A", "B"))

    def test_first_joint_closure_is_first(self) -> None:
        run = [
            co.ProvEvent("A", "^"),
            co.ProvEvent("B", "v"),
            co.ProvEvent("A", "v"),
            co.ProvEvent("B", "^"),
        ]
        result = co.coincides(run, "A", "B")
        self.assertIsNotNone(result)
        self.assertEqual(result["first_joint_closure"], 2)

    def test_projection_and_origins(self) -> None:
        run = [co.ProvEvent("A", "^"), co.ProvEvent("B", "v"), co.ProvEvent("A", "<")]
        self.assertEqual(co.origins(run), ("A", "B"))
        self.assertEqual(co.project(run, "A", 2), "^")
        self.assertEqual(co.project(run, "A", 3), "^<")

    def test_bad_event_rejected(self) -> None:
        with self.assertRaises(ValueError):
            co.ProvEvent("", "^")
        with self.assertRaises(ValueError):
            co.ProvEvent("A", "x")

    def test_summary_schema(self) -> None:
        summary = co.build_summary()
        self.assertEqual(summary["meta"]["issue"], 283)
        self.assertTrue(summary["co0"]["all_pass"])
        self.assertEqual(
            summary["gates"]["CO3_universality"],
            "interaction-event census open; not implemented here",
        )
        self.assertIn("open bridge", summary["gates"]["CO4_law_of_exceptions"])
        self.assertTrue(summary["co1_co2"]["primordial"]["strong"])
        self.assertFalse(summary["co1_co2"]["gauge_pair"]["strong"])


if __name__ == "__main__":
    unittest.main()
