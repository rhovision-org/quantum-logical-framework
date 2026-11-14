"""Independent checks of the external reference; no QLF bridge claim."""
import importlib.util
import math
from pathlib import Path
import unittest

FILE = Path(__file__).resolve().parents[1] / 'tools/gupta_ccc_tl_reference.py'
spec = importlib.util.spec_from_file_location('gupta_reference', FILE)
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)


class GuptaReferenceTests(unittest.TestCase):
    def setUp(self):
        self.model = g.Reference(panels=64)

    def test_present_boundary(self):
        row = self.model.at_redshift(0)
        self.assertEqual(row['f'], 1)
        self.assertEqual(row['scale_factor'], 1)
        self.assertEqual(row['H_expansion_km_s_Mpc'], 59.51)
        self.assertEqual(row['proper_distance_Mpc'], 0)

    def test_analytic_solution_obeys_original_ode(self):
        m = self.model
        for a in [0.05, 0.2, 0.7]:
            def age(scale):
                return -2 * math.log(m.x(scale)/m.x_bang) / m.r
            step = 1e-5
            derivative = (age(a+step)-age(a-step))/(2*step)
            expected = 1/(a*m.expansion(1/a-1))
            self.assertAlmostEqual(derivative/expected, 1, places=6)

    def test_redshift_distance_and_age_cross_checks(self):
        previous_age = math.inf
        for z in [0, 1, 10, 20]:
            row = self.model.at_redshift(z)
            self.assertLess(row['age_Gyr'], previous_age)
            previous_age = row['age_Gyr']
            self.assertAlmostEqual(row['age_Gyr'], row['age_quadrature_Gyr'], places=6)
            self.assertAlmostEqual(row['composition_residual'], 0, places=12)
            self.assertAlmostEqual(row['distance_match_residual'], 0, places=12)
            self.assertLessEqual(row['z_expansion'], z)

    def test_low_redshift_total_slope(self):
        m = self.model
        z = 1e-5
        row = m.at_redshift(z)
        slope = g.C_KM_S*z/row['proper_distance_Mpc']
        self.assertAlmostEqual(slope/(m.hc*(1+m.ht_over_hc)), 1, places=4)

    def test_external_scale_sensitivity(self):
        first = self.model.at_redshift(10)
        second = g.Reference(hc=2*self.model.hc, panels=64).at_redshift(10)
        self.assertEqual(first['z_expansion'], second['z_expansion'])
        self.assertAlmostEqual(first['age_Gyr'], 2*second['age_Gyr'])
        self.assertAlmostEqual(first['proper_distance_Mpc'], 2*second['proper_distance_Mpc'])

    def test_mismatch_blocks_acceptance(self):
        import json
        frozen = json.loads(g.SPEC.read_text())
        frozen["targets"] = [{"z": 0, "age_Gyr": 0, "tolerance_Gyr": 0.05}]
        frozen["numerics"]["simpson_panels"] = 32
        frozen["numerics"]["refinement_panels"] = 64
        self.assertEqual(g.benchmark(frozen)["benchmark_acceptance"], "FAIL")

    def test_domain_rejected(self):
        for args in [{'hc':0}, {'hc':math.inf}, {'ratio':0}, {'ratio':-1}, {'panels':3}]:
            with self.assertRaises(ValueError):
                g.Reference(**args)
        for z in [-1, math.nan, math.inf]:
            with self.assertRaises(ValueError):
                self.model.at_redshift(z)


if __name__ == '__main__':
    unittest.main()
