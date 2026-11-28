"""Regression test for conscious_update_rule.py (Conscious_Update_Rule.md section 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import conscious_update_rule as cu  # noqa: E402


class ConsciousUpdateRuleTest(unittest.TestCase):
    def test_verdicts(self):
        r = cu.run()
        self.assertTrue(all(r["pass"].values()))

    def test_mode_switches_under_independent_rule(self):
        for q in (5, 6):
            c = cu.race("ind", q)
            self.assertEqual(max(c, key=c.get), "external")
        c = cu.race("ind", 3)
        self.assertEqual(max(c, key=c.get), "percept")


if __name__ == "__main__":
    unittest.main()
