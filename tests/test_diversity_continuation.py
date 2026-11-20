"""Regression tests for the D8c naive-continuation pilot (#290)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import diversity_continuation as dc  # noqa: E402


class DiversityContinuationTests(unittest.TestCase):
    def test_closed_extensions(self) -> None:
        extensions = dc.closed_extensions()
        self.assertEqual(len(extensions), 8)
        self.assertTrue(all(dc.is_zfa(word) for word in extensions))

    def test_raw_continuation_is_invariant(self) -> None:
        result = dc.census()
        self.assertTrue(result["raw_continuation_counts_identical"])
        for stats in result["groups"].values():
            self.assertEqual(list(stats["admitted_counts"].keys()), ["8"])

    def test_support_group_sizes(self) -> None:
        result = dc.census()
        self.assertEqual(result["closed_bases"], 5120)
        self.assertEqual(result["groups"]["0"]["bases"], 20)
        self.assertEqual(result["groups"]["1"]["bases"], 1140)
        self.assertEqual(result["groups"]["2"]["bases"], 3240)
        self.assertEqual(result["groups"]["3"]["bases"], 720)

    def test_canonical_variation_is_exploratory(self) -> None:
        result = dc.census()
        self.assertEqual(result["groups"]["0"]["mean_distinct_types"], 3.0)
        self.assertEqual(result["groups"]["3"]["mean_distinct_types"], 7.0)
        self.assertIn("exploratory", result["verdict"])

    def test_gate_labels_do_not_pass_d8c(self) -> None:
        summary = dc.build_summary()
        self.assertIn("fail", summary["gates"]["D8c0_raw_continuation"])
        self.assertIn("exploratory", summary["gates"]["D8c1_canonical_variety"])
        self.assertIn("open", summary["gates"]["D8c2_matched_measure"])


if __name__ == "__main__":
    unittest.main()
