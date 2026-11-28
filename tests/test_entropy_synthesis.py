"""Regression tests for the finite entropy synthesis."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import entropy_synthesis as es  # noqa: E402


class EntropySynthesisTests(unittest.TestCase):
    def test_self_test(self) -> None:
        es.self_test()

    def test_census_counts(self) -> None:
        self.assertEqual(len(es.zfa_closures(2)), 8)
        self.assertEqual(len(es.zfa_closures(4)), 168)
        self.assertEqual(len(es.zfa_closures(6)), 5120)

    def test_sign_entropy_partition(self) -> None:
        for length in (2, 4, 6):
            row = es.census(length)
            self.assertAlmostEqual(
                row["H_sign_bits"] + row["forgotten_bits"],
                row["H_total_bits"],
                places=12,
            )
            self.assertLessEqual(row["H_sign_bits"], 1.0)
            self.assertEqual(row["plus"] + row["minus"], row["closures"])

    def test_route_erasure_witness(self) -> None:
        witness = es.route_erasure_witness()
        self.assertTrue(witness["distinct"])
        self.assertTrue(witness["both_closed"])
        self.assertTrue(witness["same_fold"])
        self.assertEqual(witness["a"], "^v")
        self.assertEqual(witness["b"], "v^")

    def test_summary_schema(self) -> None:
        summary = es.build_summary()
        self.assertIn("sign_census", summary)
        self.assertIn("pair_account", summary)
        self.assertIn("possibilism", summary)
        self.assertEqual(summary["possibilism"]["grades"][0], "possible")
        self.assertIn("proof_obligations", summary)
        self.assertIn("not_claimed", summary)
        self.assertEqual(summary["pair_account"]["global"], "singlet: pure, S(AB) = 0")
        self.assertIn("not a proof of permanent loss", summary["pair_account"]["scope"])


if __name__ == "__main__":
    unittest.main()
