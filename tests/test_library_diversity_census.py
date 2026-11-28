"""Regression tests for the equal-size library diversity census (#264, #290).

The full census takes a few minutes on four cores, so these tests check the solver
on small cases, recompute the n = 6 panel-A stratum, and check the committed data.
"""

from __future__ import annotations

import json
import sys
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import library_diversity_census as ld  # noqa: E402

DATA = ROOT / "data" / "library_diversity_census.json"


class LibraryDiversityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(DATA.read_text())

    def test_solver(self) -> None:
        ld.self_test()

    def test_strata_and_verdict(self) -> None:
        d = self.data
        self.assertEqual(d["strata_count"], 28)
        self.assertEqual(d["verdict"], "PASS (ZFA), coverage-only")
        self.assertEqual(d["delta"], "344143/170347520")
        self.assertEqual(d["stratum_signs"], {"+": 25, "0": 3, "-": 0})

    def test_delta_is_the_homogeneous_redundancy(self) -> None:
        # Same shapes give the same sum of single-part savings in both groups (symmetry),
        # so Delta_s = synergy_div - synergy_hom; and diverse synergy is zero in every stratum.
        for r in self.data["strata"]:
            syn_h = Fraction(r["homogeneous"]["synergy"])
            syn_d = Fraction(r["diverse"]["synergy"])
            self.assertEqual(syn_d, 0, r)
            self.assertLessEqual(syn_h, 0, r)
            self.assertEqual(Fraction(r["delta_S"]), syn_d - syn_h, r)

    def test_panel_a_n6_recomputes(self) -> None:
        engine = ld.Engine(6, 1)
        groups = ld.libraries("A", 2)[("D", "D")]
        means = {}
        for g in ("homogeneous", "diverse"):
            libs = groups[g]
            total = sum(libs.values())
            means[g] = sum((m * engine.stats(lib)["S"] for lib, m in libs.items()),
                           Fraction(0)) / total
        row = next(r for r in self.data["strata"] if r["panel"] == "A" and r["n"] == 6)
        self.assertEqual(Fraction(row["delta_S"]), means["diverse"] - means["homogeneous"])
        self.assertEqual(row["delta_S"], "9/640")


if __name__ == "__main__":
    unittest.main()
