import unittest

from perspective_holography import factor_reconstruction



class FactorizationCriterionTests(unittest.TestCase):
    def test_reconstructible_observable_returns_map(self):
        audit = factor_reconstruction(["b0", "b1", "b0", "b2"], [10, 20, 10, 30])
        self.assertTrue(audit.reconstructible)
        self.assertEqual(audit.reconstruction_map, {"b0": 10, "b1": 20, "b2": 30})

    def test_collision_with_different_observable_returns_counterexample(self):
        audit = factor_reconstruction(["same", "other", "same"], [1, 2, 3])
        self.assertFalse(audit.reconstructible)
        self.assertEqual(audit.counterexample_indices, (0, 2))
        self.assertEqual(audit.boundary_value, "same")
        self.assertEqual(audit.observable_values, (1, 3))
        self.assertEqual(audit.reconstruction_map, {})

    def test_empty_sample_factors_vacuously(self):
        audit = factor_reconstruction([], [])
        self.assertTrue(audit.reconstructible)
        self.assertEqual(audit.reconstruction_map, {})

    def test_mismatched_sample_lengths_are_rejected(self):
        with self.assertRaises(ValueError):
            factor_reconstruction(["b"], [])



if __name__ == "__main__":
    unittest.main()
