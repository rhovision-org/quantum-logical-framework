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

    @staticmethod
    def _one_bad_sample(bad, arm):
        """Patch defect so that exactly one later sample of one arm is `bad`."""
        original = bsc.defect
        seen = {"n": 0}

        def patched(bandfn, *a, **k):
            v = original(bandfn, *a, **k)
            is_walk = bandfn is not bsc.dirac_band
            if (arm == "walk") == is_walk:
                seen["n"] += 1
                if seen["n"] == 7:      # a later sample, neither first nor the extremum
                    return bad
            return v

        return mock.patch.object(bsc, "defect", patched)

    def test_single_nan_among_finite_dirac_samples(self) -> None:
        with self._one_bad_sample(float("nan"), "dirac"):
            with self.assertRaisesRegex(bsc.Invalid, "non-finite"):
                bsc.run()

    def test_single_nan_among_finite_walk_samples(self) -> None:
        with self._one_bad_sample(float("nan"), "walk"):
            with self.assertRaisesRegex(bsc.Invalid, "non-finite"):
                bsc.run()

    def test_single_zero_walk_sample_among_positive(self) -> None:
        with self._one_bad_sample(0.0, "walk"):
            with self.assertRaisesRegex(bsc.Invalid, "non-finite or zero"):
                bsc.run()

    def test_zero_calibration_sample_is_allowed(self) -> None:
        with mock.patch.object(bsc, "defect", lambda *a, **k: 0.0):
            self.assertEqual(bsc.worst(bsc.dirac_band, 0.04), 0.0)
            with self.assertRaisesRegex(bsc.Invalid, "non-finite or zero"):
                bsc.worst(bsc.dirac_band, 0.04, require_positive=True)

    def test_non_finite_slope_rejected(self) -> None:
        with mock.patch.object(bsc.np, "polyfit", lambda *a, **k: np.array([np.nan, 0.0])):
            with self.assertRaisesRegex(bsc.Invalid, "slope"):
                bsc.slope(bsc.KAPPAS, [1.0] * len(bsc.KAPPAS))


if __name__ == "__main__":
    unittest.main()
