"""Regression tests for the Lean proof trust gate."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from proof_trust import (
    anchors_from_source, check_footprints, forbidden_proof_markers,
    footprints_from_log, scan_lean_tree,
)


class ProofTrustTests(unittest.TestCase):
    def test_report(self):
        data = "'QLF.a' depends on axioms: [Quot.sound, propext]\n'QLF.b' does not depend on any axioms"
        self.assertEqual(
            footprints_from_log(data),
            {"QLF.a": ["Quot.sound", "propext"], "QLF.b": []},
        )

    def test_github_duplicate_and_wrapped(self):
        prefix = "build\tstep\t2026-11-05T11:17:19.000Z "
        data = (
            prefix + "'QLF.a' depends on axioms: [propext,\n"
            + prefix + "Classical.choice]\n"
            + prefix + "'QLF.a' depends on axioms: [propext, Classical.choice]"
        )
        self.assertEqual(
            footprints_from_log(data), {"QLF.a": ["Classical.choice", "propext"]}
        )

    def test_conflicting_duplicates_rejected(self):
        with self.assertRaises(ValueError):
            footprints_from_log(
                "'QLF.a' depends on axioms: [propext]\n"
                "'QLF.a' depends on axioms: [QLF.boundary]"
            )

    def test_empty_log_rejected(self):
        with self.assertRaises(ValueError):
            footprints_from_log("CI succeeded but no axiom output")

    def test_missing_or_changed_anchor_rejected(self):
        anchors = ["QLF.a", "QLF.b"]
        baseline = {"QLF.a": ["propext"], "QLF.b": []}
        self.assertFalse(
            check_footprints(anchors, {"QLF.a": ["propext"], "QLF.b": []}, baseline)
        )
        self.assertTrue(check_footprints(anchors, {"QLF.a": ["QLF.boundary"]}, baseline))
        self.assertTrue(check_footprints(anchors, {"QLF.a": ["propext"]}, baseline))
        self.assertTrue(
            check_footprints(anchors, {"QLF.a": ["propext"], "QLF.b": []}, {"QLF.a": ["propext"]})
        )

    def test_duplicate_anchors_rejected(self):
        with self.assertRaises(ValueError):
            anchors_from_source("#print axioms QLF.a\n#print axioms QLF.a")

    def test_comment_strings_and_valid_admit_function_not_flagged(self):
        source = (
            "/- sorry /- admit -/ sorry -/\n"
            "-- sorry\n"
            "def label := \"sorry admit\"\n"
            "def admit (n : Nat) := n\n"
            "theorem use (n : Nat) : Nat := by\n  exact admit n\n"
        )
        self.assertEqual(forbidden_proof_markers(source), [])

    def test_real_proof_holes_flagged(self):
        self.assertEqual(
            len(forbidden_proof_markers("theorem x : True := by sorry\ntheorem y : True := by\n  admit\n")),
            2,
        )

    def test_scan_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            file = Path(tmp) / "X.lean"
            file.write_text("theorem x : True := by sorry")
            self.assertEqual(len(scan_lean_tree(Path(tmp))), 1)
            file.write_text("theorem x : True := by trivial")
            self.assertFalse(scan_lean_tree(Path(tmp)))


if __name__ == "__main__":
    unittest.main()
