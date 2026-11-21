"""Regression test for territory_return.py (Map_Is_Territory.md section 3a)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import territory_return as tr  # noqa: E402


class TerritoryReturnTest(unittest.TestCase):
    def test_gauge_plus_is_invisible_to_the_fold(self):
        self.assertEqual(tr.decompose(tr.fold("+")), ("I", 1 + 0j))
        self.assertFalse(tr.balanced("+"))

    def test_verdicts_at_length_three(self):
        r = tr.run(3)
        self.assertEqual(r["classes"], 64)
        self.assertGreater(r["M1_mixed_classes"], 0)
        self.assertTrue(r["M2_invariant_constant_on_classes"] and r["M2_invariant_separates_classes"])
        self.assertEqual(r["klein_parity_mismatches"], 0)
        self.assertTrue(r["M3_zfa_function_of_ledger"])


if __name__ == "__main__":
    unittest.main()
