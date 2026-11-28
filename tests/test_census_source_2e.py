"""Regression tests for #301 milestone 2, stage 2e (local curvature outside a source)."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

DATA = ROOT / "data" / "census_source_2e.json"


class CensusSource2eTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(DATA.read_text())

    def test_registered_verdict(self) -> None:
        d = self.data
        self.assertEqual(d["gates"], {"V_chi": True, "N_chi": False, "F_flat": True,
                                      "first_order": True})
        v = d["verdicts"]
        self.assertTrue(v["L1_not_flat"])
        self.assertEqual(v["L2_local_vacuum"], "uninformative")
        self.assertTrue(v["L3_tidal_pattern"])
        self.assertTrue(v["L4_strength_is_Q"])

    def test_census_tracks_vacuum_control(self) -> None:
        for s in self.data["sources"].values():
            for r in ("6", "8", "10"):
                c, V = s["census"]["shells"][r], s["V"]["shells"][r]
                self.assertAlmostEqual(c["chi"] / V["chi"], 1, delta=0.01)
                self.assertAlmostEqual(c["mean_t"] / V["mean_t"], 1, delta=0.02)
        self.assertGreater(self.data["N"]["shells"]["10"]["chi"], 0.2)


if __name__ == "__main__":
    unittest.main()
