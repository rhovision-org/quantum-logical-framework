"""Protect positive acceptance without changing the frozen original test artifact."""
import importlib.util
from pathlib import Path
import unittest

FILE = Path(__file__).resolve().parents[1] / 'tools/gupta_ccc_tl_reference.py'
spec = importlib.util.spec_from_file_location('gupta_reference_acceptance', FILE)
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)


class GuptaAcceptanceTests(unittest.TestCase):
    def test_frozen_targets_accepted(self):
        import json
        frozen = json.loads(g.SPEC.read_text())
        report = g.benchmark(frozen)
        self.assertEqual(report['benchmark_acceptance'], 'PASS')
        self.assertEqual(len(report['rows']), 3)
        for row, target in zip(report['rows'], frozen['targets']):
            with self.subTest(z=target['z']):
                self.assertEqual(row['z_observed'], target['z'])
                self.assertTrue(row['target_pass'])
                self.assertTrue(row['numerics_pass'])
                self.assertLessEqual(abs(row['age_residual_Gyr']), target['tolerance_Gyr'])
                self.assertLess(row['refinement_change_Gyr'], frozen['numerics']['age_convergence_Gyr'])
                self.assertLess(row['age_quadrature_difference_Gyr'], frozen['numerics']['age_convergence_Gyr'])


if __name__ == "__main__":
    unittest.main()
