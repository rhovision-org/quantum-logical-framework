"""Structural facts of loop_cut_check.py (Relativity_Principle.md §6b, stage 5 second run)."""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("loop_cut_check", ROOT / "loop_cut_check.py")
lcc = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(lcc)
lbc = lcc.lbc


def integrand(model, p, E, P):
    (xp, a1, b1), (xa, a2, b2) = model.terms(p, E, P)
    k = lambda x: 0.5 / np.tan((x + 0.3j) / 2)
    return (np.einsum("n,nij,nkl->nikjl", k(xp), a1, b1)
            - np.einsum("n,nij,nkl->nikjl", k(xa), a2, b2)).reshape(-1, 16, 16)


class LoopCutTests(unittest.TestCase):
    def setUp(self) -> None:
        self.mA = 0.04
        self.mB = 0.6 * self.mA
        rng = np.random.default_rng(0)
        self.p = rng.uniform(-np.pi, np.pi, (400, 3))
        self.E, self.P = 0.07, np.array([0.01, -0.02, 0.03])

    def test_split_is_invariant_under_the_pi_shift(self) -> None:
        """Unlike the arc split, the two-step split sees k and k + pi e_z as one state."""
        for s in ("half", "raw"):
            m = lcc.CutModel(lbc.walk_bands(s), self.mA, self.mB)
            q = self.p + np.array([0.0, 0.0, np.pi])
            f, f2 = integrand(m, self.p, self.E, self.P), integrand(m, q, self.E, self.P)
            self.assertLess(np.abs(f - f2).max(), 1e-10 * np.abs(f).max())

    def test_agrees_with_first_run_below_and_flips_above(self) -> None:
        for s in ("half", "raw"):
            cut = lcc.CutModel(lbc.walk_bands(s), self.mA, self.mB)
            old = lbc.Model(lbc.walk_bands(s), True, self.mA, self.mB)
            w1 = lbc.walk_bands(s)(self.p, self.mA)[0]
            w2 = lbc.walk_bands(s)(self.P[None] - self.p, self.mB)[0]
            below = (w1 < np.pi / 2) & (w2 < np.pi / 2)
            above = (w1 > np.pi / 2) & (w2 > np.pi / 2)
            fc, fo = integrand(cut, self.p, self.E, self.P), integrand(old, self.p, self.E, self.P)
            self.assertTrue(below.any() and above.any())
            self.assertLess(np.abs(fc[below] - fo[below]).max(), 1e-12)
            self.assertLess(np.abs(fc[above] + fo[above]).max(), 1e-12)

    def test_rest_frame_has_no_straddling_pairs(self) -> None:
        w = lbc.walk_bands("half")
        a = w(self.p, self.mA)[0] < np.pi / 2
        b = w(-self.p, self.mB)[0] < np.pi / 2
        self.assertTrue(np.array_equal(a, b))

    def test_breakpoints_include_every_cut_plane(self) -> None:
        b = lcc.breakpoints(0.03, 0.01, lcc.SETTINGS)
        for x in (-np.pi / 2, np.pi / 2, 0.03 - np.pi / 2, 0.03 + np.pi / 2):
            self.assertLess(np.abs(b - x).min(), 1e-12)
        self.assertEqual(b[0], -np.pi)
        self.assertEqual(b[-1], np.pi)

    def test_all_corners_are_singular_in_the_particle_term(self) -> None:
        m = lcc.CutModel(lbc.walk_bands("half"), 0.03, 0.018)
        cen = lcc.singular_centers(m, 0.05, np.zeros(3))
        self.assertEqual(len(cen), 8)
        self.assertEqual({w for _, w in cen}, {0})


if __name__ == "__main__":
    unittest.main()
