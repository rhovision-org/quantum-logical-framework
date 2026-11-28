"""Structural checks of walk_antiparticle_check.py (Relativity_Principle.md §6b, stage 6 step 1)."""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("walk_antiparticle_check",
                                              ROOT / "walk_antiparticle_check.py")
wac = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(wac)


class WalkAntiparticleTests(unittest.TestCase):
    def test_all_structural_checks_hold(self) -> None:
        res = wac.checks(seed=1)
        self.assertIn("S5_stueckelberg", res)

    def test_two_step_is_minus_identity_on_sigma(self) -> None:
        """Where some k_i = pi/2 the two arcs meet: U^2 = -I, a scalar with no band label."""
        rng = np.random.default_rng(3)
        p = rng.uniform(-np.pi, np.pi, (50, 3))
        for axis in range(3):
            q = p.copy()
            q[:, axis] = -np.pi / 2
            u = wac.step(q, 0.1, "half")
            self.assertLess(np.abs(u @ u + np.eye(4)[None]).max(), 1e-12)

    def test_generic_two_step_is_not_scalar(self) -> None:
        """Off that surface the two-step walk still separates the arcs (control)."""
        p = np.array([[0.3, -0.2, 0.4]])
        u = wac.step(p, 0.1, "half")[0]
        self.assertGreater(np.abs(u @ u + np.eye(4)).max(), 0.1)

    def test_bad_dispersion_is_invalid(self) -> None:
        orig = wac.lbc.walk_bands

        def broken(slice_):
            f = orig(slice_)
            return lambda p, m: (lambda w, a, b: (w + 1e-3, a, b))(*f(p, m))

        wac.lbc.walk_bands = broken
        try:
            with self.assertRaises(wac.Invalid):
                wac.checks()
        finally:
            wac.lbc.walk_bands = orig


if __name__ == "__main__":
    unittest.main()
