"""Regression tests for listener equivalence (#274)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import listener_equivalence as le  # noqa: E402


class ListenerEquivalenceTests(unittest.TestCase):
    def test_self_test(self) -> None:
        le.self_test()

    def test_partition_refinement(self) -> None:
        coarse = le.refine(le.uncertainty_system("blue"))
        fine = le.refine(le.uncertainty_system("cyan"))
        self.assertEqual(le.blocks_of(coarse), (
            frozenset({"a"}),
            frozenset({"b"}),
            frozenset({"c1", "c2"}),
            frozenset({"s"}),
        ))
        self.assertEqual(len(le.blocks_of(fine)), 5)

    def test_equivalence_and_right_congruence(self) -> None:
        for system in (le.uncertainty_system("blue"), le.uncertainty_system("cyan")):
            block = le.refine(system)
            self.assertTrue(le.is_equivalence(block, system.states))
            self.assertTrue(le.is_right_congruence(system, block))

    def test_coarsest_matches_bruteforce(self) -> None:
        for system in (le.uncertainty_system("blue"), le.uncertainty_system("cyan")):
            block = le.refine(system)
            self.assertEqual(set(le.blocks_of(block)), set(le.coarsest_bisimulation(system)))

    def test_uncertainty_factorization(self) -> None:
        coarse = le.uncertainty_system("blue")
        fine = le.uncertainty_system("cyan")
        cw = le.listener_uncertainty(coarse, "s", 2, le.refine(coarse))
        fw = le.listener_uncertainty(fine, "s", 2, le.refine(fine))
        self.assertEqual(cw["W_micro"], 4)
        self.assertEqual(cw["W_B"], 1)
        self.assertEqual(fw["W_B"], 2)
        self.assertLessEqual(cw["W_B"], cw["W_micro"])
        self.assertAlmostEqual(sum(cw["weights"].values()), 1.0)

    def test_qkb_concept_quotient(self) -> None:
        demo = le.qkb_concept_demo()
        self.assertEqual(demo["ways"], 4)
        self.assertEqual(demo["listener_ways"], 2)
        self.assertLessEqual(demo["listener_ways"], demo["ways"])

    def test_self_model_square(self) -> None:
        self.assertTrue(le.square_commutes(le.good_model()))
        self.assertFalse(le.square_commutes(le.bad_model()))
        self.assertTrue(le.no_event_loop(le.good_model()))
        self.assertTrue(le.no_event_loop(le.bad_model()))

    def test_summary_schema(self) -> None:
        summary = le.build_summary()
        self.assertEqual(summary["meta"]["issue"], 274)
        self.assertIn("partition", summary)
        self.assertIn("uncertainty", summary)
        self.assertIn("qkb", summary)
        self.assertIn("self_model", summary)
        self.assertEqual(summary["gates"]["L1_equivalence_right_congruence"], "finite pass")


if __name__ == "__main__":
    unittest.main()
