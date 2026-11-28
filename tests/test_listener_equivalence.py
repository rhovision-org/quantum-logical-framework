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
        self.assertEqual(cw["measure"], "uniform")
        self.assertAlmostEqual(sum(cw["weights"].values()), 1.0)

    def test_explicit_measure_is_not_silently_uniform(self) -> None:
        fine = le.uncertainty_system("cyan")
        fw = le.listener_uncertainty(
            fine,
            "s",
            2,
            le.refine(fine),
            {
                ("x", "x"): 1.0,
                ("x", "y"): 0.0,
                ("y", "x"): 1.0,
                ("y", "y"): 3.0,
            },
        )
        self.assertEqual(fw["measure"], "explicit")
        self.assertEqual(fw["W_B"], 2)
        self.assertAlmostEqual(fw["weights"]["c1"], 0.2)
        self.assertAlmostEqual(fw["weights"]["c2"], 0.8)

    def test_qkb_concept_quotient(self) -> None:
        demo = le.qkb_concept_demo()
        self.assertEqual(demo["ways"], 4)
        self.assertEqual(demo["listener_ways"], 2)
        self.assertLessEqual(demo["listener_ways"], demo["ways"])

    def test_self_model_square(self) -> None:
        good = le.good_model()
        bad = le.bad_model()
        self.assertTrue(le.square_commutes(good))
        self.assertFalse(le.square_commutes(bad))
        self.assertTrue(le.levels_nondecreasing(good))
        self.assertTrue(le.levels_nondecreasing(bad))
        self.assertNotIn("m0", le.self_loop_states(good))
        self.assertIn("m0", le.self_loop_states(bad))

    def test_summary_schema(self) -> None:
        summary = le.build_summary()
        self.assertEqual(summary["meta"]["issue"], 274)
        self.assertIn("partition", summary)
        self.assertIn("uncertainty", summary)
        self.assertIn("qkb", summary)
        self.assertIn("self_model", summary)
        self.assertEqual(summary["gates"]["L1_equivalence_right_congruence"], "finite pass")
        self.assertIn("L6_level_monotonicity", summary["gates"])
        self.assertTrue(summary["self_model"]["bad_has_m0_self_loop"])


if __name__ == "__main__":
    unittest.main()
