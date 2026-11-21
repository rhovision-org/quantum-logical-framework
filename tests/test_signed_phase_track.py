"""Regression test for signed_phase_track.py (Stationary_Action.md section 5b)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import signed_phase_track as spt  # noqa: E402


class SignedPhaseTrackTest(unittest.TestCase):
    def test_qlf_member_reproduces_signed_census(self):
        rows = spt.bound_check(6, -1, 6)
        self.assertEqual([round(r["abs_A0"]) for r in rows], [8, 120, 2144])

    def test_bound_holds_for_every_flux(self):
        for j in (0, 3, 4, 6):
            for sigma in (1, -1):
                self.assertTrue(all(r["bound_holds"] for r in spt.bound_check(j, sigma, 6)))

    def test_only_pi_flux_matches_fold(self):
        out = spt.fold_check(4)
        matching = sorted(k for k, v in out.items() if isinstance(v, dict) and v["mismatches"] == 0)
        self.assertEqual(matching, ["phi=-pi,sigma=-1", "phi=pi,sigma=-1"])


if __name__ == "__main__":
    unittest.main()
