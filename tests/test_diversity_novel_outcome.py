"""Regression test for diversity_novel_outcome.py (Diversity_Novel_Outcome_E1.md section 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import diversity_novel_outcome as dn  # noqa: E402


class DiversityNovelOutcomeTest(unittest.TestCase):
    def test_verdicts(self):
        r = dn.run()
        self.assertTrue(all(r["pass"].values()))
        self.assertEqual(r["N_hom"], ["+I"])
        self.assertEqual(r["N_mixed"], ["+I", "-I"])
        self.assertEqual(dn.ctype("^v"), "-I")


if __name__ == "__main__":
    unittest.main()
