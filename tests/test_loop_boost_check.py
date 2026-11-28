"""Gates and structural facts of loop_boost_check.py (Relativity_Principle.md §6b, stage 5)."""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("loop_boost_check", ROOT / "loop_boost_check.py")
lbc = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(lbc)


class LoopBoostCheckTests(unittest.TestCase):
    def test_pv_coefficients_cancel_four_moments(self) -> None:
        co = lbc.pv_coeffs()
        for n in range(4):
            self.assertAlmostEqual(sum(c * s ** n for s, c in co), 0.0, places=9)

    def test_bump_is_one_inside_zero_outside(self) -> None:
        r = np.array([0.0, 0.29, 0.61, 2.0])
        b = lbc._bump(r, 0.3, 0.6)
        self.assertEqual(list(b), [1.0, 1.0, 0.0, 0.0])

    def test_walk_bands_are_shifted_by_pi_in_kz(self) -> None:
        """QLF_PiDoubler.halfWalk_shift_z: the bands trade places and w -> pi - w."""
        rng = np.random.default_rng(0)
        p = rng.uniform(-np.pi, np.pi, (6, 3))
        q = p + np.array([0.0, 0.0, np.pi])
        for slice_ in ("half", "raw"):
            w, lp, lm = lbc.walk_bands(slice_)(p, 0.03)
            w2, lp2, lm2 = lbc.walk_bands(slice_)(q, 0.03)
            self.assertLess(np.abs(w + w2 - np.pi).max(), 1e-12)
            self.assertLess(np.abs(lp2 - lm).max(), 1e-12)

    def test_feynman_terms_cancel_on_the_walk(self) -> None:
        """The both-positive and both-negative sums are the same integral on the walk."""
        mA = 0.04 / np.sqrt(2)
        m = lbc.Model(lbc.walk_bands("half"), True, mA, 0.6 * mA)
        n = 16
        g = (np.arange(n) + 0.5) * 2 * np.pi / n - np.pi
        pts = np.stack(np.meshgrid(g, g, g, indexing="ij"), axis=-1).reshape(-1, 3)
        (xpp, a1, b1), (xmm, a2, b2) = m.terms(pts, 0.07, np.array([0.01, -0.02, 0.03]))
        tpp = lbc._acc(0.5 / np.tan((xpp + 0.3j) / 2), a1, b1)
        tmm = lbc._acc(0.5 / np.tan((xmm + 0.3j) / 2), a2, b2)
        self.assertLess(np.abs(tpp - tmm).max(), 1e-14 * np.abs(tpp).max() + 1e-16)

    def test_zero_vertex_is_invalid(self) -> None:
        P = np.eye(4, dtype=complex) / 2
        with self.assertRaises(lbc.Invalid):
            lbc.W2([(1.0, P)] * 4, np.zeros((16, 16), complex))

    def test_corners_are_band_bottoms_or_tops(self) -> None:
        mA = 0.03
        m = lbc.Model(lbc.walk_bands("half"), True, mA, 0.6 * mA)
        cen = lbc.singular_centers(m, 0.05, np.zeros(3))
        self.assertEqual(len(cen), 8)
        self.assertEqual(sorted(w for _, w in cen), [0, 0, 0, 0, 1, 1, 1, 1])


if __name__ == "__main__":
    unittest.main()
