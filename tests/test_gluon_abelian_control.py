"""Regression test for gluon_abelian_control.py (Gluon_Abelian_Control.md section 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import gluon_abelian_control as gc  # noqa: E402


class GluonAbelianControlTest(unittest.TestCase):
    def test_legacy_search_reproduces_pr_289(self):
        r = gc.run(legacy=True)
        self.assertEqual(r["states"], 494)
        self.assertEqual(r["gated"]["with_path"], 454)
        self.assertEqual(r["gated"]["classes"]["create"],
                         {"reducing": 216, "neutral": 24, "increasing": 72, "blocked": 744})

    def test_size_five_state_can_glue_back(self):
        # pre-registered bound: intermediate states of size <= 5 may move, including a glue to 4
        s = ((0, 1), (1, 0), (1, 1), (1, 2))
        mid = ((0, 1), (1, 0), (1, 1), (1, 2), (1, 2))
        self.assertIn(mid, gc.moves(s, True)["create"])
        self.assertIn(((0, 1), (1, 0), (1, 0), (1, 2)), gc.moves(mid, True)["glue"])
        self.assertEqual(gc.distance(s, True), 2)
        self.assertEqual(gc.distance(s, True, legacy=True), 3)

    def test_verdicts(self):
        r = gc.run()
        self.assertEqual(r["A1_first_singlet_nonreducing"], {"gated": 0, "abelian": 0})
        self.assertEqual(r["A3_states_with_different_distance"], 24)
        self.assertEqual(r["A4_states_with_different_reachability"], 32)
        self.assertTrue(r["A4_all_have_no_noncollinear_pair"])
        self.assertTrue(r["A5_classes_differ"])
        self.assertEqual(r["gated"]["classes"]["create"],
                         {"reducing": 504, "neutral": 288, "increasing": 264})

    def test_witness(self):
        w = ((0, 1), (0, 1), (1, 0), (2, 0))
        self.assertEqual(gc.distance(w, True), 2)
        self.assertEqual(gc.distance(w, False), 1)


if __name__ == "__main__":
    unittest.main()
