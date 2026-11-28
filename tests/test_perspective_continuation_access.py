import json
from pathlib import Path
import unittest
from perspective_continuation_access import run

class ContinuationTest(unittest.TestCase):
    def test_frozen_screen(self):
        expected = json.loads((Path(__file__).resolve().parents[1] /
                               "data/perspective_continuation_access.json").read_text())
        self.assertEqual(json.loads(json.dumps(run())), expected)
        self.assertEqual(expected["prefixes"], 456)
        self.assertFalse(expected["base_reconstructs"])
        self.assertTrue(expected["augmented_record_matches_all"])
