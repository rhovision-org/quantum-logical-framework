"""Regression test for gluon_abelian_control.py (Gluon_Abelian_Control.md section 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import gluon_abelian_control as gc  # noqa: E402


class GluonAbelianControlTest(unittest.TestCase):
    def test_gated_reproduces_pr_289(self):
        r = gc.run()
        self.assertEqual(r["states"], 494)
        self.assertEqual(r["gated"]["with_path"], 454)
        self.assertEqual(r["gated"]["classes"]["create"],
                         {"reducing": 216, "neutral": 24, "increasing": 72, "blocked": 744})

    def test_verdicts(self):
        r = gc.run()
        self.assertEqual(r["A1_first_singlet_nonreducing"], {"gated": 0, "abelian": 0})
        self.assertEqual(r["A3_states_with_different_distance"], 24)
        self.assertEqual(r["A4_states_with_different_reachability"], 32)
        self.assertTrue(r["A4_all_have_no_noncollinear_pair"])

    def test_witness(self):
        w = ((0, 1), (0, 1), (1, 0), (2, 0))
        self.assertEqual(gc.distance(w, True), 2)
        self.assertEqual(gc.distance(w, False), 1)


if __name__ == "__main__":
    unittest.main()
