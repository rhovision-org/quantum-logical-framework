import json
from pathlib import Path
import unittest
from kinetic_phase_scale import run

class KineticScaleTest(unittest.TestCase):
    def test_frozen_scale_control(self):
        actual = run()
        recorded = json.loads((Path(__file__).resolve().parents[1] /
                               "data/kinetic_phase_scale.json").read_text())
        self.assertEqual(actual["comparisons"], recorded["comparisons"])
        for a,b in zip(actual["rows"], recorded["rows"]):
            for key in ("scaled_census_correction", "scaled_walk_correction",
                        "scaled_phase_difference", "scaled_radial_derivative_difference"):
                self.assertAlmostEqual(a[key], b[key], delta=1e-7)
        self.assertLessEqual(actual["finest_max_error"], .0005)
