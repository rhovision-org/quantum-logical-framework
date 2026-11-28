"""Fail-closed gates of shared_pair_sign_check.py (Relativity_Principle.md §6b)."""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest import mock

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("shared_pair_sign_check", ROOT / "shared_pair_sign_check.py")
sps = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(sps)


class SharedPairSignTests(unittest.TestCase):
    def test_runs_and_grades(self) -> None:
        res = sps.run()
        self.assertIn(res["A"], ("PASS", "FAIL"))
        self.assertEqual(res["control"], "EUCLIDEAN")

    def test_verdict_classifier(self) -> None:
        self.assertEqual(sps.verdict({"gauge": -1, "x": 1, "y": 1, "z": 1}), "MINKOWSKI")
        self.assertEqual(sps.verdict({"gauge": 1, "x": 1, "y": 1, "z": 1}), "EUCLIDEAN")
        self.assertEqual(sps.verdict({"gauge": -1, "x": 1, "y": -1, "z": 1}), "NEITHER")

    def test_degenerate_state_is_invalid(self) -> None:
        with mock.patch.object(sps, "shared", lambda t: np.eye(4, dtype=complex)):
            with self.assertRaisesRegex(sps.Invalid, "dimension"):
                sps.selected_state()

    def test_control_gate_is_fail_closed(self) -> None:
        with mock.patch.object(sps, "verdict", lambda w: "MINKOWSKI"):
            with self.assertRaisesRegex(sps.Invalid, "control"):
                sps.run()

    def test_complex_weight_is_invalid(self) -> None:
        with self.assertRaisesRegex(sps.Invalid, "not real"):
            sps.weights(lambda t: 1j)


if __name__ == "__main__":
    unittest.main()
