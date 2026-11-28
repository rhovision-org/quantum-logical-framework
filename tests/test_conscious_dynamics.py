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
        percept = next(c for c in cd.CONSCIOUS_CANDIDATES if c.name == "percept")
        thought = next(c for c in cd.CONSCIOUS_CANDIDATES if c.name == "thought")
        self.assertEqual(cd.effective_period(percept, listener), 2)
        self.assertEqual(cd.frequency(percept, listener), 0.5)
        self.assertEqual(cd.remaining_distance(percept, listener), 2)
        attended = cd.attention(listener, "thought", distance_acceleration=0, period_acceleration=2)
        self.assertEqual(cd.effective_period(thought, attended), 3)
        self.assertGreater(cd.frequency(thought, attended), cd.frequency(thought, listener))

    def test_promotion_filter(self) -> None:
        winner = cd.next_trigger(cd.CONSCIOUS_CANDIDATES, cd.Listener("default"))
        self.assertIsNotNone(winner)
        self.assertEqual(winner["name"], "percept")
        micro = next(c for c in cd.CONSCIOUS_CANDIDATES if c.name == "micro")
        self.assertFalse(cd.eligible(micro))
        self.assertEqual(micro.intrinsic_period, 1)
        self.assertEqual(cd.remaining_distance(micro, cd.Listener("default")), 0)

    def test_frequency_priority_separation(self) -> None:
        default = cd.Listener("default")
        priority_next = cd.next_trigger(cd.PRIORITY_CANDIDATES, default)
        priority_fastest = cd.highest_frequency(cd.PRIORITY_CANDIDATES, default)
        self.assertEqual(priority_next["name"], "slow_near")
        self.assertEqual(priority_fastest["name"], "fast_recurrent")
        self.assertNotEqual(priority_next["name"], priority_fastest["name"])
        fast = next(c for c in cd.PRIORITY_CANDIDATES if c.name == "fast_recurrent")
        slow = next(c for c in cd.PRIORITY_CANDIDATES if c.name == "slow_near")
        self.assertGreater(cd.frequency(fast, default), cd.frequency(slow, default))
        self.assertLess(cd.remaining_distance(slow, default), cd.remaining_distance(fast, default))

    def test_attention_changes_race(self) -> None:
        default = cd.Listener("default")
        attended = cd.attention(default, "thought", distance_acceleration=4)
        self.assertEqual(cd.next_trigger(cd.CONSCIOUS_CANDIDATES, default)["name"], "percept")
        self.assertEqual(cd.next_trigger(cd.CONSCIOUS_CANDIDATES, attended)["name"], "thought")

    def test_quieting_shifts_external(self) -> None:
        quiet = cd.quiet_internal(cd.Listener("default"))
        winner = cd.next_trigger(cd.CONSCIOUS_CANDIDATES, quiet)
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

    def test_affective_recollection(self) -> None:
        memory = cd.affective_recollection()
        self.assertEqual(memory["winners"]["neutral"], "M_A")
        self.assertEqual(memory["winners"]["F_blue_room"], "M_A")
        self.assertEqual(memory["winners"]["F_song_summer"], "M_B")
        self.assertEqual(memory["winners"]["F_loss_winter"], "M_C")
        self.assertTrue(memory["store_unchanged_across_feelings"])
        self.assertFalse(memory["target_field_present"])
        for run in memory["runs"]:
            self.assertEqual(run["recall"]["tau_recall"], 0)
            self.assertTrue(run["recall"]["atomic"])
            self.assertEqual(run["trace"][-1]["event"], "RECALL")

    def test_summary_schema(self) -> None:
        summary = cd.build_summary()
        self.assertEqual(summary["meta"]["issue"], 278)
        self.assertIn("default_race", summary)
        self.assertIn("priority_next", summary)
        self.assertIn("priority_fastest", summary)
        self.assertIn("attention_winner", summary)
        self.assertIn("quieting_winner", summary)
        self.assertIn("loop", summary)
        self.assertIn("retrospective", summary)
        self.assertIn("memory", summary)
        self.assertIn("magical_powers", summary)
        self.assertIn("relative_world_database", summary["magical_powers"])
        self.assertIn("active_inference_synthesis", summary["magical_powers"])
        self.assertIn("strange_loop_reflection", summary["magical_powers"])
        self.assertIn("gift_of_forgetfulness", summary["magical_powers"])
        self.assertIn("disciplined", summary["magical_powers"]["gift_of_forgetfulness"])
        self.assertEqual(summary["gates"]["D7_qualia"], "bracketed; no theorem")
        self.assertIn("D3_bounded_trace", summary["gates"])
        self.assertIn("D8_affective_recollection", summary["gates"])
        self.assertIn("D9_frequency_priority_separation", summary["gates"])
        self.assertIn("D10_bounded_forgetting", summary["gates"])
        self.assertIn("D11_thought_effect_separation", summary["gates"])
        self.assertIn("external closure", summary["gates"]["D11_thought_effect_separation"])
        self.assertIn("D12_feeling_deep_closure", summary["gates"])
        self.assertIn("lossy", summary["gates"]["D12_feeling_deep_closure"])


if __name__ == "__main__":
    unittest.main()
