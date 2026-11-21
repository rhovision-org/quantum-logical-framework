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

    def test_experiment_reports_both_blankets_and_explicit_scope(self):
        result = run_experiment(length=4)
        self.assertGreater(result.sample_size, 0)
        self.assertEqual(result.shared_action_coordinates, (1,))
        self.assertEqual(set(result.full_action_reconstructible), {b.name for b in DEFAULT_BLANKETS})
        self.assertEqual(set(result.bloch_reconstructible), {b.name for b in DEFAULT_BLANKETS})
        self.assertEqual(set(result.full_action_counterexamples), {b.name for b in DEFAULT_BLANKETS})
        self.assertEqual(set(result.bloch_counterexamples), {b.name for b in DEFAULT_BLANKETS})


if __name__ == "__main__":
    unittest.main()
