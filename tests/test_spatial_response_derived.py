"""Regression test for spatial_response_derived.py (Spatial_Response_Derived.md)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import spatial_response_derived as srd  # noqa: E402


class SpatialResponseDerivedTest(unittest.TestCase):
    def test_verdicts(self):
        r = srd.run(3)
        self.assertTrue(r["R1_binding_events_with_dS_ge_0"])
        self.assertLess(r["R2_closer"], r["R2_opposite_events"])
        self.assertTrue(r["R3_mean_equals_2_minus_dS"])
        self.assertEqual(r["R3_identity_failures"], 0)
        self.assertEqual(r["R4_mean_growth_by_class"], {"like": ["0"], "opposite": ["4"], "orthogonal": ["2"]})


if __name__ == "__main__":
    unittest.main()
