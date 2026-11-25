"""Regression tests for #301 milestone 2, stage 2c (sources that add ways, balancing)."""

from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

DATA = ROOT / "data" / "census_source_2c.json"


class CensusSource2cTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(DATA.read_text())

    def test_registered_verdict(self) -> None:
        d = self.data
        self.assertTrue(d["all_valid"])
        self.assertTrue(d["C1_adding_ways_contracts"])
        self.assertTrue(d["C2_far_field_is_monopole"])
        self.assertTrue(d["C3_shape_blind_far"])
        self.assertFalse(d["C4_balancing_sign_change"])

    def test_sign_follows_ways_charge(self) -> None:
        for r in self.data["sources"].values():
            for v in r["shell_mean_dl_over_l"].values():
                self.assertEqual(v > 0, r["Q"] > 0)
            self.assertGreater(r["falloff_k"], 1.7)
            self.assertLess(r["falloff_k"], 2.1)

    @unittest.skipUnless(importlib.util.find_spec("numpy"), "numpy not installed")
    def test_share1_recomputes(self) -> None:
        import census_source as cs
        import census_source_2c as c2

        G = cs.green_table(1)  # cached table; no mpmath needed
        r = c2.analyse(G, "share1")
        stored = self.data["sources"]["share1"]
        self.assertAlmostEqual(r["Q"], stored["Q"], places=12)
        self.assertAlmostEqual(r["falloff_k"], stored["falloff_k"], places=9)


if __name__ == "__main__":
    unittest.main()
