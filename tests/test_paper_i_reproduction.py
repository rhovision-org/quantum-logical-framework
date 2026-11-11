"""Preserve the reviewed finite and SPARC numerical outputs, without modifying data."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class PaperIReproductionTests(unittest.TestCase):
    def test_finite_mo2_counts(self):
        out = subprocess.check_output([sys.executable, str(ROOT / 'scripts/mo2_finite_audit.py')], text=True)
        data = json.loads(out)
        self.assertEqual(data['comparable_pairs'], 15)
        self.assertEqual(data['orthomodular_implications'], 36)
        self.assertEqual(data['nonvacuous_orthomodular'], 15)
        self.assertEqual(data['nondistributive_meet_over_join'], 24)
        self.assertEqual(data['nondistributive_join_over_meet'], 24)
        self.assertEqual(len(data['lattice_checks']), 19)
        self.assertTrue(all(data['lattice_checks'].values()))

    def test_committed_receipt_artifacts_match_their_digests(self):
        receipt_path = ROOT / 'verification/paper-i-v0.3/receipt.json'
        receipt = json.loads(receipt_path.read_text())
        for artifact in receipt['artifacts']:
            target = (ROOT / artifact['path']).resolve()
            self.assertIn(ROOT.resolve(), target.parents)
            self.assertEqual(hashlib.sha256(target.read_bytes()).hexdigest(), artifact['sha256'])

    def test_sparc_reproduces_frozen_data_scores_and_csv(self):
        expected_hashes = {
            'MassModels_Lelli2016c.mrt': '9108994b12cc401b94a1768beca61c53ec354779385c9c9cc571049f3043244c',
            'SPARC_Lelli2016c.mrt': '5aa0501f6b0d881fa579030e315e7b5b6ef561a5bd3a07472f9929c7e5728243',
        }
        for name, expected in expected_hashes.items():
            self.assertEqual(hashlib.sha256((ROOT / 'sparc' / name).read_bytes()).hexdigest(), expected)
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for name in [*expected_hashes, 'sparc_blind_pipeline.py']:
                shutil.copyfile(ROOT / 'sparc' / name, directory / name)
            subprocess.run([sys.executable, 'sparc_blind_pipeline.py'], cwd=directory,
                           check=True, capture_output=True, text=True)
            receipt = json.loads((directory / 'receipt.json').read_text())
            expected = {'newton': (0.4309, 0.2809), 'nfw': (-0.005, 0.0593),
                        'rarfit': (-0.0094, 0.1326), 'qlf': (-0.0002, 0.1327)}
            for model, (mean, scatter) in expected.items():
                self.assertEqual(receipt['results_dex'][model]['N'], 2696)
                self.assertEqual(receipt['results_dex'][model]['mean_dex'], mean)
                self.assertEqual(receipt['results_dex'][model]['scatter_dex'], scatter)
            blob = (directory / 'predictions_sealed.csv').read_bytes()
            self.assertEqual(blob, (ROOT / 'sparc/predictions_sealed.csv').read_bytes())
            body = blob.split(b'\n', 1)[1].rstrip(b'\n')
            self.assertEqual(hashlib.sha256(body).hexdigest(), '5f06582c8058c6c14f3ef2805b872574afcfe63773624c9b10aaa2fdedabfb90')
            self.assertEqual(receipt['parameter_accounting']['optimized_here']['rarfit'], 0)


if __name__ == '__main__':
    unittest.main()
