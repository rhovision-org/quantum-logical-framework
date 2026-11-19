"""Regression tests for the finite closure-uncertainty kernel (#269)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import closure_uncertainty as cu  # noqa: E402


class ClosureUncertaintyTests(unittest.TestCase):
    def test_self_test(self) -> None:
        cu.self_test()

    def test_closed_start_is_unique(self) -> None:
        game = cu.game_system(("S", "S"))
        self.assertEqual(cu.first_completions(game, 3), ((),))
        self.assertEqual(cu.W(game, 3), 1)
        self.assertEqual(cu.U(game, 3), 0.0)

    def test_stag_hunt_completions(self) -> None:
        game = cu.game_system(("S", "H"))
        self.assertEqual(cu.W(game, 0), 0)
        self.assertEqual(cu.W(game, 1), 2)
        self.assertEqual(cu.W(game, 3), 2)
        self.assertEqual(cu.U(game, 1), 1.0)

    def test_tighter_context_cannot_increase_W(self) -> None:
        game = cu.game_system(("S", "H"))
        tight = game.with_context(p for p in cu.PROFILES if p != ("H", "H"))
        self.assertEqual(cu.W(tight, 3), 1)
        self.assertLessEqual(cu.W(tight, 3), cu.W(game, 3))

    def test_charge_toy_first_returns(self) -> None:
        charge = cu.charge_system()
        self.assertEqual([cu.W(charge, r) for r in range(4)], [0, 1, 1, 2])
        band = charge.with_context(q for q in charge.states if -1 <= q <= 1)
        self.assertEqual(cu.W(band, 6), 1)

    def test_joint_closure_pair(self) -> None:
        joint = cu.joint_system()
        self.assertEqual(cu.W(joint, 1), 0)
        self.assertEqual(cu.W(joint, 2), 2)

    def test_flat_zfa_first_completions(self) -> None:
        flat = cu.flat_word_system(4, "^")
        self.assertEqual(len(flat.states), 4681)
        self.assertEqual(len(flat.closed), 177)
        self.assertEqual([cu.W(flat, r) for r in range(5)], [0, 1, 1, 14, 14])

    def test_measure_gate(self) -> None:
        flat = cu.flat_word_system(4, "^")
        measure = cu.completion_measure(flat, 3, start_length=1)
        self.assertEqual(measure["W_micro"], 14)
        self.assertAlmostEqual(sum(measure["normalized"]), 1.0)
        self.assertGreater(
            measure["by_steps"]["1"]["P_total"],
            measure["by_steps"]["3"]["P_total"],
        )

    def test_finiteness(self) -> None:
        for system in (
            cu.game_system(),
            cu.charge_system(),
            cu.joint_system(),
            cu.flat_word_system(4, "^"),
        ):
            paths = cu.first_completions(system, 4)
            self.assertTrue(all(len(path) <= 4 for path in paths))

    def test_summary_schema(self) -> None:
        summary = cu.build_summary()
        self.assertEqual(summary["meta"]["issue"], 269)
        self.assertIn("games", summary)
        self.assertIn("flat_zfa", summary)
        self.assertIn("measure", summary)
        self.assertIn("u1_charge", summary)
        self.assertIn("joint_pair", summary)
        self.assertEqual(summary["gates"]["U1_lean"], "open")
        self.assertIn("flat-history ZFA exact", summary["gates"]["U4_domains"])
        self.assertIn("U5_measure", summary["gates"])


if __name__ == "__main__":
    unittest.main()
