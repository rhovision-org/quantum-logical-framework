"""Regression test for gupta_scale_free.py (Gupta_ScaleFree.md section 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import gupta_scale_free as gs  # noqa: E402


class GuptaScaleFreeTest(unittest.TestCase):
    def test_calibration_free_numbers(self):
        r = gs.run()
        self.assertTrue(r["K1_check"] and r["K2_check"])
        self.assertAlmostEqual(r["ratio_t10_t0"], 0.218713, places=6)
        self.assertAlmostEqual(r["ratio_t20_t0"], 0.129870, places=6)
        self.assertAlmostEqual(r["H0_total_t0"], 1.980656, places=6)


if __name__ == "__main__":
    unittest.main()
