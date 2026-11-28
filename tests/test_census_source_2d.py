"""Regression tests for #301 milestone 2, stage 2d (geometry from joint closures)."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

DATA = ROOT / "data" / "census_source_2d.json"


class CensusSource2dTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(DATA.read_text())

    def test_registered_verdict(self) -> None:
        d = self.data
        self.assertTrue(d["first_order_valid"])
        self.assertTrue(d["D1_vacuum_outside"])
        self.assertFalse(d["D2_gauss"])
        self.assertTrue(d["D3_sign"])

    def test_one_over_r_and_site_set(self) -> None:
        s = self.data["sources"]
        for r in s.values():
            self.assertGreater(r["falloff_k"], 0.95)
            self.assertLess(r["falloff_k"], 1.05)
        q = self.data["delta_K10_over_Q"]
        self.assertAlmostEqual(q["share1"] / q["excl1"], 1, places=3)


if __name__ == "__main__":
    unittest.main()
