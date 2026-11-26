"""Readings and fail-closed gates of boost_amplitudes_check.py (Relativity_Principle.md §6b, stage 4b)."""
from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path
from unittest import mock

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("boost_amplitudes_check", ROOT / "boost_amplitudes_check.py")
bac = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(bac)


class BoostAmplitudesCheckTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.res = bac.run()

    def test_registered_readings(self) -> None:
        res = self.res
        for v in res["calibration_dirac_defect"].values():
            self.assertLess(v, 1e-12)
        self.assertEqual(res["graded"], {"scalar": "PASS", "vector": "PASS", "range": "PASS",
                                         "blind": "PREDICTION_CONFIRMED"})
        for arm in ("scalar", "vector", "range"):
            self.assertAlmostEqual(res["half"][arm]["slope"], 2.0, delta=0.01)
        self.assertLess(abs(res["half"]["blind"]["slope"]), 0.01)

    def test_scalar_vertex_commutes_with_spin_action(self) -> None:
        # S^dagger beta S = beta for a boost S = exp(eta alpha / 2): the Lean theorem, numerically.
        S = bac.bsc.herm_exp(bac.ALPHA[2], 0.3)
        np.testing.assert_allclose(S.conj().T @ bac.BETA @ S, bac.BETA, atol=1e-14)
        self.assertGreater(np.abs(S.conj().T @ S - np.eye(4)).max(), 0.1)

    def test_calibration_gate_is_fail_closed(self) -> None:
        with mock.patch.object(bac, "CAL_MAX", 0.0):
            with self.assertRaises(bac.Invalid):
                bac.run()

    def test_control_gate_is_fail_closed(self) -> None:
        with mock.patch.object(bac, "CONTROL_MIN", 10.0):
            with self.assertRaises(bac.Invalid):
                bac.run()

    def test_single_nan_sample_is_caught(self) -> None:
        original = bac.defect
        seen = {"n": 0}

        def patched(*a, **k):
            seen["n"] += 1
            return float("nan") if seen["n"] == 7 else original(*a, **k)

        with mock.patch.object(bac, "defect", patched):
            with self.assertRaisesRegex(bac.Invalid, "non-finite"):
                bac.run()

    def test_single_zero_walk_sample_is_caught(self) -> None:
        original = bac.defect

        def patched(bandfn, *a, **k):
            v = original(bandfn, *a, **k)
            return 0.0 if bandfn is not bac.bsc.dirac_band and patched.n == 6 else v

        patched.n = 0

        def counting(bandfn, *a, **k):
            if bandfn is not bac.bsc.dirac_band:
                patched.n += 1
            return patched(bandfn, *a, **k)

        with mock.patch.object(bac, "defect", counting):
            with self.assertRaisesRegex(bac.Invalid, "non-finite or zero"):
                bac.run()

    def _patched_trace(self, value):
        original = bac.np.trace
        seen = {"n": 0}

        def patched(a, *args, **kw):
            seen["n"] += 1
            return value if seen["n"] == 9 else original(a, *args, **kw)

        return mock.patch.object(bac.np, "trace", patched)

    def test_negative_W_is_caught(self) -> None:
        with self._patched_trace(complex(-1e-6, 0.0)):
            with self.assertRaisesRegex(bac.Invalid, "positive real"):
                bac.run()

    def test_complex_W_is_caught(self) -> None:
        with self._patched_trace(complex(1e-6, 1e-9)):
            with self.assertRaisesRegex(bac.Invalid, "positive real"):
                bac.run()

    def test_quasienergy_mismatch_reported(self) -> None:
        mis = self.res["half_quasienergy_mismatch"]
        self.assertEqual(len(mis), len(bac.KAPPAS))
        self.assertTrue(all(np.isfinite(m) and m > 0 for m in mis))

    def test_non_finite_leg_energy_in_diagnostic_is_caught(self) -> None:
        def bad_band(k, m):
            P, E = bac.bsc.dirac_band(k, m)
            return P, float("nan")

        with self.assertRaisesRegex(bac.Invalid, "leg energy"):
            bac.energy_mismatch(bad_band, 0.04)

    def test_non_finite_slope_rejected(self) -> None:
        with mock.patch.object(bac.np, "polyfit", lambda *a, **k: np.array([np.nan, 0.0])):
            with self.assertRaisesRegex(bac.Invalid, "slope"):
                bac.slope([1.0] * len(bac.KAPPAS))


if __name__ == "__main__":
    unittest.main()
