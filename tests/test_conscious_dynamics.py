"""Regression tests for conscious dynamics (#278)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import conscious_dynamics as cd  # noqa: E402


class ConsciousDynamicsTests(unittest.TestCase):
    def test_self_test(self) -> None:
        cd.self_test()

    def test_effective_frequency(self) -> None:
        listener = cd.Listener("default")
        percept = next(c for c in cd.CANDIDATES if c.name == "percept")
        self.assertEqual(cd.effective_delay(percept, listener), 2)
        self.assertEqual(cd.frequency(percept, listener), 0.5)
        attended = cd.attention(listener, "thought")
        thought = next(c for c in cd.CANDIDATES if c.name == "thought")
        self.assertLess(cd.effective_delay(thought, attended), thought.intrinsic_delay)
        self.assertGreater(cd.frequency(thought, attended), cd.frequency(thought, listener))

    def test_promotion_filter(self) -> None:
        winner = cd.promote(cd.CANDIDATES, cd.Listener("default"))
        self.assertIsNotNone(winner)
        self.assertEqual(winner["name"], "percept")
        micro = next(c for c in cd.CANDIDATES if c.name == "micro")
        self.assertFalse(cd.eligible(micro))
        self.assertEqual(micro.intrinsic_delay, 1)

    def test_attention_changes_race(self) -> None:
        default = cd.Listener("default")
        attended = cd.attention(default, "thought")
        self.assertEqual(cd.promote(cd.CANDIDATES, default)["name"], "percept")
        self.assertEqual(cd.promote(cd.CANDIDATES, attended)["name"], "thought")

    def test_quieting_shifts_external(self) -> None:
        quiet = cd.quiet_internal(cd.Listener("default"))
        winner = cd.promote(cd.CANDIDATES, quiet)
        self.assertIsNotNone(winner)
        self.assertEqual(winner["name"], "external")

    def test_finite_loop(self) -> None:
        loop = cd.run_loop(4)
        self.assertEqual(
            [row["winner"] for row in loop],
            ["percept", "thought", "feeling", "external"],
        )
        self.assertTrue(all(loop[i]["step"] < loop[i + 1]["step"] for i in range(3)))

    def test_retrospective_compression(self) -> None:
        retro = cd.retrospective_compression()
        self.assertTrue(retro["history_unchanged"])
        self.assertTrue(retro["compression_changed"])
        self.assertNotEqual(retro["compression_before"], retro["compression_after"])

    def test_summary_schema(self) -> None:
        summary = cd.build_summary()
        self.assertEqual(summary["meta"]["issue"], 278)
        self.assertIn("default_race", summary)
        self.assertIn("attention_winner", summary)
        self.assertIn("quieting_winner", summary)
        self.assertIn("loop", summary)
        self.assertIn("retrospective", summary)
        self.assertEqual(summary["gates"]["D7_qualia"], "bracketed; no theorem")


if __name__ == "__main__":
    unittest.main()
