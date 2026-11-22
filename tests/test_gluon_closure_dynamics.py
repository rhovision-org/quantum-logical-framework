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

    def test_vertex_moves_are_independent(self) -> None:
        state = ((1, 0), (0, 1))
        self.assertEqual(g.glue_moves(state), {((2, 2),)})
        self.assertEqual(g.create_moves(state), {((0, 1), (1, 0), (2, 2))})
        # Moves are defined by the vertex condition, not by distance.
        self.assertEqual(g.distance_to_singlet(state), 1)

    def test_gluing_state_reaches_singlet(self) -> None:
        state = ((0, 1), (1, 0), (1, 1))
        self.assertEqual(g.distance_to_singlet(state), 1)
        self.assertTrue(any(g.is_singlet(nxt) for nxt in g.glue_moves(state)))

    def test_two_gluon_singlet(self) -> None:
        state = ((1, 0), (2, 0))
        self.assertTrue(g.is_singlet(state))
        self.assertEqual(g.distance_to_singlet(state), 0)
        self.assertEqual(g.glue_moves(state), set())
        self.assertEqual(g.create_moves(state), set())

    def test_census_has_all_distance_directions(self) -> None:
        result = g.census()
        for kind in ("create", "glue"):
            classes = result["move_classes"][kind]
            self.assertGreater(classes.get("distance_reducing", 0), 0)
            self.assertGreater(classes.get("distance_neutral", 0), 0)
            self.assertGreater(classes.get("distance_increasing", 0), 0)
            self.assertGreater(
                result["first_singlet_moves"][kind].get("distance_reducing", 0), 0
            )

    def test_vertex_witnesses_close(self) -> None:
        for state in (
            ((1, 0), (0, 1)),
            ((0, 1), (1, 0), (1, 1)),
            ((0, 1), (1, 0), (1, 1), (2, 1)),
        ):
            witnesses = g.vertex_witnesses(state)
            self.assertTrue(witnesses)
            for q, r, p in witnesses:
                self.assertEqual(g.add(g.add(q, r), p), (0, 0))
                self.assertNotEqual(g.symp(q, r), 0)

    def test_closure_event_is_atomic(self) -> None:
        event = g.closure_event(((1, 0), (0, 1)))
        self.assertIsNotNone(event)
        self.assertEqual(event["event"], "CLOSE")
        self.assertEqual(event["tau_event"], 0)
        self.assertTrue(event["atomic"])
        self.assertEqual(event["distance"], 1)
        self.assertEqual(event["moves"], ["create"])
        self.assertTrue(g.is_singlet(event["path"][-1]))

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
