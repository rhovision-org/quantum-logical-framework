"""Regression tests for the D8c2 census under D3T (#290)."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import d8c2_census as d8  # noqa: E402


class D8c2Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = d8.build()
        cls.primary = cls.data["primary_extensions_le_k"]

    def test_verdict_and_deltas(self) -> None:
        rel = self.primary["relations"]
        self.assertEqual(self.primary["verdict"], "PASS (D8c2)")
        self.assertEqual(rel["R_T"]["weighted_delta"], "12/1045")
        self.assertEqual(rel["N1_no_provenance"]["weighted_delta"], "-23/55")
        self.assertEqual(rel["N2_no_first_closure"]["stratum_signs"], rel["R_T"]["stratum_signs"])
        self.assertEqual(rel["R_T"]["eligible_strata"], 4)

    def test_profile_without_phase_is_at_most_one_record(self) -> None:
        # Admitted extensions must carry the base's complement key, so the
        # phase-free profile has at most one element: K varies only by phase label.
        for row in self.primary["strata"]:
            for pop, stats in row["diag_R_T_no_phase_label"].items():
                self.assertIn(stats["mean_K"], ("0", "1"), (row, pop))

    def test_length_reading_does_not_matter(self) -> None:
        self.assertEqual(self.primary, self.data["sensitivity_extensions_eq_k"])

    def test_committed_data_reproduces(self) -> None:
        import json
        committed = json.loads((ROOT / "data" / "d8c2_census.json").read_text())
        self.assertEqual(committed, json.loads(json.dumps(self.data)))


if __name__ == "__main__":
    unittest.main()
