"""Replay the frozen #296 bounded surrogate and compare its retained evidence."""
import json
from pathlib import Path
import unittest

from perspective_frontier import run


class FrontierTest(unittest.TestCase):
    def test_frozen_screen(self):
        expected = json.loads((Path(__file__).resolve().parents[1] /
                               "data/perspective_frontier.json").read_text())
        self.assertEqual(json.loads(json.dumps(run())), expected)
        self.assertEqual(expected["histories"], 14425)
        self.assertTrue(expected["nested_record_restrictions"])
        self.assertFalse(expected["checks"]["B_fold_B_zfa"]["reconstructible"])
