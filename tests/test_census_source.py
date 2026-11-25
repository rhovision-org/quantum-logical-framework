"""Regression tests for #301 milestone 2, stage 2b (census geometry with a local source)."""

from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

DATA = ROOT / "data" / "census_source.json"


class CensusSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(DATA.read_text())

    def test_registered_verdict(self) -> None:
        for model in ("exclusion", "delay"):
            m = self.data[model]
            self.assertFalse(m["B1"])
            self.assertFalse(m["B2"])
            self.assertFalse(m["B3"])
            self.assertFalse(m["acts_as_mass"])
            for r in m["sources"]:
                self.assertGreater(r["falloff_k"], 1.9)
                self.assertLess(r["falloff_k"], 2.3)
                self.assertLess(r["diag_curvature_only"]["10"], 0)

    def test_lengths_stretch(self) -> None:
        for r in self.data["exclusion"]["sources"]:
            for v in r["mean_dl_over_l_axis_by_shell"].values():
                self.assertGreater(v, 0)

    @unittest.skipUnless(importlib.util.find_spec("numpy"), "numpy not installed")
    def test_single_site_exclusion_recomputes(self) -> None:
        import census_source as cs

        G = cs.green_table(1)  # cached table; no mpmath needed
        r = cs.measure(G, 1, "exclusion")
        stored = self.data["exclusion"]["sources"][0]
        self.assertAlmostEqual(r["falloff_k"], stored["falloff_k"], places=9)
        self.assertEqual(r["degenerate_tetrahedra"], stored["degenerate_tetrahedra"])
        self.assertAlmostEqual(r["delta_K"]["10"], stored["delta_K"]["10"], places=6)


if __name__ == "__main__":
    unittest.main()
