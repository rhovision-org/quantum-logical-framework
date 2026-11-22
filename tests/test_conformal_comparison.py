"""Regression test for conformal_comparison.py (Conformal_Comparison.md section 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import conformal_comparison as cc  # noqa: E402


class ConformalComparisonTest(unittest.TestCase):
    def test_global_frames(self):
        self.assertEqual(len(cc.frames()), 384)

    def test_local_dilation_breaks_balance(self):
        self.assertTrue(cc.balanced("^v"))
        self.assertFalse(cc.balanced("^^^v"))


if __name__ == "__main__":
    unittest.main()
