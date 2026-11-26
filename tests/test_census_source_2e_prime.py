"""Regression tests for #301 milestone 2, stage 2e' (calibrated tensor-fit vacuum test)."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

DATA = ROOT / "data" / "census_source_2e_prime.json"


class CensusSource2ePrimeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(DATA.read_text())

    def test_registered_verdict(self) -> None:
        d = self.data
        self.assertEqual(d["gates"], {"C_rank_condition": True, "V_chi": True, "N_chi": True,
                                      "F_flat": True, "fit_reproduces": False})
        self.assertEqual(d["verdicts"]["L2prime_local_vacuum"], "uninformative")
        self.assertTrue(d["verdicts"]["L2prime_raw"])

    def test_trace_residual_falls(self) -> None:
        for s in self.data["sources"].values():
            sh = s["census"]["shells"]
            self.assertGreater(sh["6"]["chi_prime"] / sh["10"]["chi_prime"], 2.5)
            for r in ("6", "8", "10"):
                self.assertLess(sh[r]["chi_prime"], s["V"]["shells"][r]["chi_prime"])
        self.assertGreater(self.data["N"]["shells"]["10"]["chi_prime"], 0.8)


if __name__ == "__main__":
    unittest.main()
