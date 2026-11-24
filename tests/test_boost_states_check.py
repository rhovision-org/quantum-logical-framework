"""Fail-closed gates of boost_states_check.py (Relativity_Principle.md §6b)."""
from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path
from unittest import mock

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("boost_states_check", ROOT / "boost_states_check.py")
bsc = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(bsc)


class BoostStatesCheckTests(unittest.TestCase):
    def test_registered_readings(self) -> None:
        res = bsc.run()
        self.assertLess(res["calibration_dirac_defect"], 1e-12)
        self.assertEqual(res["graded"], "PASS")
        self.assertAlmostEqual(res["half"]["slope"], 2.0, delta=0.01)
        self.assertAlmostEqual(res["raw"]["slope"], 1.0, delta=0.01)

    def test_negative_control_detects_wrong_boost(self) -> None:
        for kp in bsc.KAPPAS:
            self.assertGreaterEqual(bsc.worst(bsc.dirac_band, kp, spin_sign=-1, reduce=min), 1e-2)

    def test_calibration_gate_is_fail_closed(self) -> None:
        with mock.patch.object(bsc, "CAL_MAX", 0.0):
            with self.assertRaises(bsc.Invalid):
                bsc.run()

    def test_control_gate_is_fail_closed(self) -> None:
        with mock.patch.object(bsc, "CONTROL_MIN", 10.0):
            with self.assertRaises(bsc.Invalid):
                bsc.run()

    def test_band_rank_gate(self) -> None:
        with self.assertRaises(bsc.Invalid):
            bsc.band(np.eye(4, dtype=complex))

    def test_zero_defect_gate(self) -> None:
        original = bsc.defect

        def walk_zero(bandfn, *a, **k):
            return original(bandfn, *a, **k) if bandfn is bsc.dirac_band else 0.0

        with mock.patch.object(bsc, "defect", walk_zero):
            with self.assertRaisesRegex(bsc.Invalid, "non-finite or zero"):
                bsc.run()


if __name__ == "__main__":
    unittest.main()
