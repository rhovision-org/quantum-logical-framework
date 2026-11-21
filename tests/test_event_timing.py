"""Regression tests for event timing (#280)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import event_timing as et  # noqa: E402


class EventTimingTests(unittest.TestCase):
    def test_self_test(self) -> None:
        et.self_test()

    def test_frequency_priority_separation(self) -> None:
        priority = et.next_trigger(et.CANDIDATES)
        fastest = et.highest_frequency(et.CANDIDATES)
        self.assertEqual(priority["name"], "slow_near")
        self.assertEqual(fastest["name"], "fast_recurrent")
        self.assertNotEqual(priority["name"], fastest["name"])

    def test_fast_recurrent_is_not_next(self) -> None:
        fast = next(c for c in et.CANDIDATES if c.name == "fast_recurrent")
        slow = next(c for c in et.CANDIDATES if c.name == "slow_near")
        self.assertGreater(et.frequency(fast), et.frequency(slow))
        self.assertLess(slow.distance, fast.distance)

    def test_atomic_closure_trace(self) -> None:
        trace = et.listening_trace(et.TRACE_CANDIDATE)
        self.assertEqual(trace["tau_listen"], 3)
        self.assertEqual(trace["tau_event"], 0)
        self.assertTrue(trace["atomic"])
        self.assertEqual(trace["trace"][-1]["event"], "CLOSE")
        self.assertEqual(trace["trace"][-1]["distance"], 0)

    def test_event_steps_increase(self) -> None:
        trace = et.listening_trace(et.TRACE_CANDIDATE)
        steps = [row["step"] for row in trace["trace"]]
        self.assertEqual(steps, sorted(steps))
        self.assertEqual(len(steps), len(set(steps)))

    def test_summary_schema(self) -> None:
        summary = et.build_summary()
        self.assertEqual(summary["meta"]["issue"], 280)
        self.assertTrue(summary["separation"]["distinct"])
        self.assertEqual(summary["priority_next"]["name"], "slow_near")
        self.assertEqual(summary["highest_frequency"]["name"], "fast_recurrent")
        self.assertEqual(summary["trace"]["tau_event"], 0)
        self.assertIn("ET2_separation", summary["gates"])


if __name__ == "__main__":
    unittest.main()
