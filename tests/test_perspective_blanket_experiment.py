import unittest

from perspective_blanket_experiment import DEFAULT_BLANKETS, enumerate_closed_histories, record, run_experiment
from twist_core import calculate_action


class TwoBlanketExperimentTests(unittest.TestCase):
    def test_blankets_have_nonempty_coordinate_overlap(self):
        overlap = set(DEFAULT_BLANKETS[0].visible_coordinates) & set(DEFAULT_BLANKETS[1].visible_coordinates)
        self.assertEqual(overlap, {1})

    def test_prefix_sample_contains_closed_leaves_and_open_prefixes(self):
        sample = enumerate_closed_histories(4)
        self.assertTrue(sample)
        self.assertTrue(any(len(h) < 4 for h in sample))
        self.assertTrue(any(len(h) == 4 for h in sample))

    def test_blanket_record_is_only_declared_projection(self):
        h = "^v<>"
        for b in DEFAULT_BLANKETS:
            expected = tuple(calculate_action(h)[i] for i in b.visible_coordinates)
            self.assertEqual(record(h, b), expected)

    def test_experiment_reports_full_and_component_audits(self):
        result = run_experiment(length=4)
        names = {b.name for b in DEFAULT_BLANKETS}
        self.assertGreater(result.sample_size, 0)
        self.assertEqual(result.shared_action_coordinates, (1,))
        self.assertEqual(set(result.full_action_reconstructible), names)
        self.assertEqual(set(result.bloch_reconstructible), names)
        self.assertEqual(set(result.full_action_witnesses), names)
        self.assertEqual(set(result.bloch_witnesses), names)
        for blanket in names:
            self.assertEqual(set(result.action_component_reconstructible[blanket]), {"vertical", "horizontal", "depth", "local_gauge"})
            self.assertEqual(set(result.bloch_component_reconstructible[blanket]), {"X", "Y", "Z"})

    def test_witnesses_are_concrete_collisions(self):
        result = run_experiment(length=4)
        for blanket in DEFAULT_BLANKETS:
            witness = result.full_action_witnesses[blanket.name]
            self.assertIsNotNone(witness)
            h1, h2 = witness.histories
            self.assertEqual(record(h1, blanket), witness.boundary_value)
            self.assertEqual(record(h2, blanket), witness.boundary_value)
            self.assertNotEqual(calculate_action(h1), calculate_action(h2))
            self.assertEqual(witness.observable_values, (calculate_action(h1), calculate_action(h2)))
            self.assertEqual(witness.indices, result.full_action_counterexamples[blanket.name])
            for component, reconstructible in result.action_component_reconstructible[blanket.name].items():
                component_witness = result.action_component_witnesses[blanket.name][component]
                self.assertEqual(reconstructible, component_witness is None)


if __name__ == "__main__":
    unittest.main()
