"""Regression test for conformal_comparison.py (Conformal_Comparison.md section 1).

Recomputes the full W1-W5 census at the pre-registered length (about 10 s) and compares it with
the frozen data/conformal_comparison.json, so the reported classification cannot regress while
the tests stay green.
"""

import json
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import conformal_comparison as cc  # noqa: E402

FROZEN = json.loads((ROOT / "data" / "conformal_comparison.json").read_text())


def _norm(x):
    return json.loads(json.dumps(x, sort_keys=True))


class ConformalComparisonTest(unittest.TestCase):
    def test_global_frames(self):
        self.assertEqual(len(cc.frames()), 384)

    def test_local_dilation_breaks_balance(self):
        self.assertTrue(cc.balanced("^v"))
        self.assertFalse(cc.balanced("^^^v"))

    def test_census_matches_frozen_result(self):
        r = {"W1_W2": cc.w1_w2(6), "W3": cc.w3(6), "W4": cc.w4(), "W5": cc.w5(6)}
        self.assertEqual(_norm(r), _norm(FROZEN))

    def test_headline_numbers(self):
        self.assertEqual([FROZEN["W3"][f"L={L}"]["preserving"] for L in (2, 4, 6)], [3, 3, 3])
        self.assertEqual([FROZEN["W3"][f"L={L}"]["fields"] for L in (2, 4, 6)], [9, 81, 729])
        self.assertTrue(all(v["preserving"] == 1 and v["pairs"] == 147456 for v in FROZEN["W4"].values()))
        self.assertEqual((FROZEN["W5"]["fold_preserving"], FROZEN["W5"]["frames"]), (96, 384))
        self.assertEqual(FROZEN["W1_W2"]["k=2"]["fold_failures"], 3664)
        self.assertEqual(FROZEN["W1_W2"]["k=3"]["fold_failures"], 0)


if __name__ == "__main__":
    unittest.main()
