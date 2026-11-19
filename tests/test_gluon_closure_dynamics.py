"""Regression tests for gluon vertex-gluing dynamics (#286)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import gluon_closure_dynamics as g  # noqa: E402


class GluonClosureDynamicsTests(unittest.TestCase):
    def test_colour_labels_and_symplectic_form(self) -> None:
        self.assertEqual(len(g.LABELS), 8)
        self.assertEqual(g.symp((1, 0), (0, 1)), 1)
        self.assertEqual(g.symp((1, 0), (2, 0)), 0)
        self.assertEqual(g.total(((1, 0), (0, 1))), (1, 1))

    def test_vertex_gluing_is_independent_move(self) -> None:
        state = ((1, 0), (0, 1))
        self.assertEqual(g.glue_moves(state), {((2, 2),)})
        # The move is defined by the vertex condition, not by distance.
        self.assertIsNone(g.distance_to_singlet(state))

    def test_gluing_state_reaches_singlet(self) -> None:
        state = ((0, 1), (1, 0), (1, 1))
        self.assertEqual(g.distance_to_singlet(state), 1)
        self.assertTrue(any(g.is_singlet(nxt) for nxt in g.glue_moves(state)))

    def test_two_gluon_singlet(self) -> None:
        state = ((1, 0), (2, 0))
        self.assertTrue(g.is_singlet(state))
        self.assertEqual(g.distance_to_singlet(state), 0)
        self.assertEqual(g.glue_moves(state), set())

    def test_census_has_both_distance_directions(self) -> None:
        result = g.census()
        classes = result["move_classes"]
        self.assertGreater(classes.get("distance_reducing", 0), 0)
        self.assertGreater(classes.get("distance_increasing", 0), 0)
        self.assertGreater(result["first_singlet_moves"].get("distance_reducing", 0), 0)

    def test_harmonic_binding(self) -> None:
        self.assertEqual(g.binding_period([5, 3]), 3)
        self.assertAlmostEqual(g.binding_frequency([5, 3]), 1 / 3)
        self.assertGreaterEqual(g.binding_frequency([5, 3]), 1 / 5)

    def test_summary_schema(self) -> None:
        summary = g.build_summary()
        self.assertEqual(summary["meta"]["issue"], 286)
        self.assertIn("GL2_gluon_move", summary["gates"])
        self.assertIn("GL3_distance_effect", summary["gates"])
        self.assertEqual(
            summary["gates"]["GL7_spatial"],
            "open bridge; no physical distance claim",
        )
        self.assertEqual(
            summary["gates"]["GL8_string_tension"],
            "open; not claimed",
        )


if __name__ == "__main__":
    unittest.main()
