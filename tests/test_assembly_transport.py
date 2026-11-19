"""Regression tests for the pre-registered cooperative-assembly transport screen (#267)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import assembly_transport as at  # noqa: E402


class AssemblyTransportTests(unittest.TestCase):
    def test_self_test(self) -> None:
        at.self_test()

    def test_class_counts(self) -> None:
        classes = at.build_classes()
        self.assertEqual(len(classes), 1 + 6 + 70 + 1365)
        self.assertEqual(
            sum(c.orbit for c in classes),
            8 + 168 + 5120 + 190120,
        )

    def test_summary_schema_and_frozen_verdict(self) -> None:
        summary = at.build_summary()
        self.assertEqual(summary["classes"]["count"], 1442)
        self.assertEqual(summary["classes"]["orbit_weight_sum"], 195416)
        for label in ("full", "ordinary", "no_filter", "scalar"):
            with self.subTest(model=label):
                self.assertIn(label, summary["models"])
                self.assertEqual(len(summary["models"][label]["W_L"]), 3)
        self.assertEqual(
            summary["verdict"]["status"],
            "negative_no_candidate_plateau",
        )
        # In this frozen screen the capacity never binds and the ordinary index
        # reproduces the closure-constrained transfer.
        self.assertTrue(summary["verdict"]["full_vs_no_filter_identical"])
        self.assertTrue(summary["verdict"]["full_vs_ordinary_identical"])

    def test_floor_diagnostic(self) -> None:
        summary = at.build_summary()
        floors = [
            h["floor_fraction"]
            for h in summary["models"]["full"]["history"]
        ]
        self.assertGreater(floors[-1], 0.5)
        self.assertFalse(summary["verdict"]["candidate_plateau_full"])


if __name__ == "__main__":
    unittest.main()
