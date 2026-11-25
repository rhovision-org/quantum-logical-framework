"""Regression tests for the D3T typed-obligation census (#290)."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import diversity_obligation as d3t  # noqa: E402


class DiversityObligationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.summary = d3t.build_summary()
        cls.panel_a = cls.summary["panels"]["A"]  # type: ignore[index]
        cls.panel_b = cls.summary["panels"]["B"]  # type: ignore[index]
        cls.whole = cls.summary["whole_history_phase"]  # type: ignore[index]

    def test_relation_witness(self) -> None:
        base = ((0, "^"), (0, "^"), (1, "^"))
        extension = ((0, "v"), (0, "v"), (1, "v"))
        self.assertTrue(d3t.obligations_match(base, extension))
        self.assertTrue(d3t.typed_join(base, extension))
        self.assertTrue(d3t.typed_join(extension, base))

        closed_base = ((0, "^"), (0, "v"))
        self.assertFalse(d3t.typed_join(closed_base, extension))
        self.assertFalse(d3t.typed_join(base, base))

    def test_panel_a_counts(self) -> None:
        self.assertEqual(self.panel_a["open_bases"], 1536)
        self.assertEqual(self.panel_a["closed_bases_excluded"], 0)
        self.assertEqual(self.panel_a["extensions"], 1536)
        self.assertEqual(self.panel_a["typed_joins"], 12096)
        self.assertEqual(self.panel_a["aggregate_joins"], 46080)
        self.assertEqual(self.panel_a["distinct_typed_profiles"], 264)
        self.assertEqual(self.panel_a["distinct_aggregate_profiles"], 96)
        self.assertEqual(self.panel_a["closure_failures"], 0)
        self.assertEqual(self.panel_a["first_closure_failures"], 0)
        self.assertEqual(self.panel_a["boundary_groups"], 360)
        self.assertEqual(self.panel_a["boundary_groups_with_multiple_profiles"], 0)
        self.assertEqual(self.panel_a["phase_groups"], 2112)
        self.assertEqual(self.panel_a["phase_ambiguous_groups"], 1368)

    def test_panel_b_counts(self) -> None:
        self.assertEqual(self.panel_b["open_bases"], 27496)
        self.assertEqual(self.panel_b["closed_bases_excluded"], 1176)
        self.assertEqual(self.panel_b["extensions"], 56)
        self.assertEqual(self.panel_b["typed_joins"], 8736)
        self.assertEqual(self.panel_b["aggregate_joins"], 26432)
        self.assertEqual(self.panel_b["distinct_typed_profiles"], 33)
        self.assertEqual(self.panel_b["distinct_aggregate_profiles"], 33)
        self.assertEqual(self.panel_b["closure_failures"], 0)
        self.assertEqual(self.panel_b["first_closure_failures"], 0)
        self.assertEqual(self.panel_b["boundary_groups"], 2238)
        self.assertEqual(self.panel_b["boundary_groups_with_multiple_profiles"], 0)
        self.assertEqual(self.panel_b["phase_ambiguous_groups"], 2016)

    def test_whole_history_phase_failure(self) -> None:
        self.assertEqual(self.whole["4"]["closed_typed_histories"], 1176)
        self.assertEqual(self.whole["4"]["boundary_groups"], 46)
        self.assertEqual(self.whole["4"]["phase_ambiguous_groups"], 34)
        self.assertEqual(self.whole["6"]["closed_typed_histories"], 158720)
        self.assertEqual(self.whole["6"]["boundary_groups"], 199)
        self.assertEqual(self.whole["6"]["phase_ambiguous_groups"], 178)

    def test_provenance_separation(self) -> None:
        self.assertEqual(self.panel_a["aggregate_groups"], 158)
        self.assertEqual(self.panel_a["aggregate_groups_with_multiple_profiles"], 150)
        self.assertEqual(self.panel_a["word_groups"], 512)
        self.assertEqual(self.panel_a["word_groups_with_multiple_profiles"], 504)
        self.assertEqual(self.panel_a["typed_differs_from_aggregate"], 1512)
        self.assertGreater(self.panel_a["distinct_typed_profiles"], self.panel_a["distinct_aggregate_profiles"])

    def test_gate_statuses(self) -> None:
        gates = self.summary["gates"]  # type: ignore[index]
        for gate in (
            "D3T.1_interface_dependence",
            "D3T.2_closure_preservation",
            "D3T.3_provenance_separation",
            "D3T.4_first_closure_integrity",
            "D3T.5_continuation_boundary_sufficiency",
            "D3T.7_no_target_geometry",
        ):
            self.assertIn("PASS", gates[gate])
        self.assertIn("FAIL", gates["D3T.6_phase_boundary_sufficiency"])
        self.assertIn("NOT RUN", gates["D8c2"])
        self.assertIn("NOT PASSED", gates["D8c2"])

    def test_phase_witnesses(self) -> None:
        witness = self.panel_a["phase_witness"]
        self.assertIsNotNone(witness)
        phases = {entry["phase"] for entry in witness["extensions"]}
        self.assertEqual(phases, {0, 2})

        whole = self.whole["4"]["witness"]
        self.assertIsNotNone(whole)
        self.assertEqual(set(whole["phases"]), {0, 2})
        self.assertEqual({entry["phase"] for entry in whole["histories"]}, {0, 2})

    def test_same_word_different_provenance_witness(self) -> None:
        witness = self.panel_a["word_witness"]
        self.assertIsNotNone(witness)
        self.assertEqual(witness["word"], "^^v")
        self.assertEqual(len(witness["bases"]), 2)
        boundaries = [entry["boundary"] for entry in witness["bases"]]
        self.assertNotEqual(boundaries[0], boundaries[1])


if __name__ == "__main__":
    unittest.main()
