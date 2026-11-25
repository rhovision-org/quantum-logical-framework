"""Regression tests for #301 milestone 2, stage 2a (census geometry)."""

from __future__ import annotations

import importlib.util
import json
import math
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import census_geometry as cg  # noqa: E402

DATA = ROOT / "data" / "census_geometry.json"


class CensusGeometryTests(unittest.TestCase):
    def test_euclidean_lengths_are_flat(self) -> None:
        defs = cg.deficits(cg.type_lengths(1.0, math.sqrt(2), math.sqrt(3)))
        for v in defs.values():
            self.assertAlmostEqual(v, 0.0, places=12)

    def test_six_kuhn_tetrahedra(self) -> None:
        self.assertEqual(len(cg.cell_tetrahedra()), 6)

    def test_committed_verdict(self) -> None:
        d = json.loads(DATA.read_text())
        self.assertTrue(d["M1_positive_volume"])
        self.assertFalse(d["M2_vacuum_flat_in_large"])
        self.assertTrue(d["M3_decay_p_ge_1_5"])
        self.assertEqual(d["verdict_2a"], "FAIL")
        rows = d["primary_l_eq_inverse_G"]["rows"]
        self.assertGreater(rows[1]["max_abs_deficit"], rows[0]["max_abs_deficit"])
        self.assertGreater(rows[-1]["max_abs_deficit"], 1e-3)
        # The deficits recompute from the stored lengths.
        for r in rows:
            L = r["lengths"]
            defs = cg.deficits(cg.type_lengths(L["axis"], L["face_diagonal"], L["body_diagonal"]))
            self.assertAlmostEqual(max(abs(x) for x in defs.values()), r["max_abs_deficit"], places=12)

    @unittest.skipUnless(importlib.util.find_spec("mpmath"), "mpmath not installed")
    def test_green_origin_is_watson(self) -> None:
        # (1/(2 pi)^3) int d^3k / (3 - sum cos k) = 1.5163860592.../3
        self.assertAlmostEqual(float(cg.green((0, 0, 0), dps=20)), 1.5163860591519780 / 3, places=12)


if __name__ == "__main__":
    unittest.main()
