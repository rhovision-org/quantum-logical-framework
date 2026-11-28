"""Regression test for fluxoid_regge.py (Continuum_Limit.md, issue #301 milestone 1)."""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import fluxoid_regge as fr  # noqa: E402


class FluxoidReggeTest(unittest.TestCase):
    def test_plaquette_circulates_and_is_curved(self):
        cur = fr.walk_current(">^<v", 10)
        assert fr.action_vector(">^<v") == (0, 0)
        assert any(fr.face_obligations(cur, 10))
        d = fr.deficits(cur, 10, fr.LENGTH_MAPS["1+m"])
        assert d is not None and any(abs(x) > fr.TOL for x in d)
        assert abs(sum(d)) < 1e-12  # Gauss-Bonnet on the torus

    def test_verdicts_at_length_four(self):
        r = fr.run(10, 4)
        assert r["closed"] == 41
        assert r["K1_closed_with_nonzero_face_obligation"] == 8
        assert r["K4_flat_set_identical_across_maps"] and r["K2_flat_iff_zero_current"]
        assert all(v["closed_histories_div_changed"] == 0 and v["div_commutes_with_smoothing_failures"] == 0
                   for v in r["K5"].values())
        assert r["K6"]["per_body_order_violations"] == 0
        assert r["K7_labeling_B_geometries_on_closed"] == 1
        assert r["labeling_A"]["1+m"]["geometries_in_closed_class"] > 1


if __name__ == "__main__":
    unittest.main()
