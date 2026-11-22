"""Regression test for lepton_stage_b.py (Lepton_Stage_B.md section 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import lepton_stage_b as lsb  # noqa: E402


class LeptonStageBTest(unittest.TestCase):
    def test_table_and_verdicts(self):
        r = lsb.run()
        self.assertTrue(all(r["pass"].values()))
        self.assertEqual([r["table"][k]["orbit"] for k in ("e", "mu", "tau")], [24, 48, 96])
        self.assertEqual(r["separating"], ["depth", "orbit"])


if __name__ == "__main__":
    unittest.main()
