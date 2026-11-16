"""Independent regression checks for the retrospective Gupta three-model Mpc diagnostic."""
import importlib.util
from decimal import Decimal
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("three_model_mpc", ROOT / "tools/gupta_three_model_mpc_audit.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

class ThreeModelMpcAuditTests(unittest.TestCase):
    def test_three_rounded_entries_match_printed_table(self):
        result = m.evaluate()
        self.assertTrue(result["all_three_rounded_match"])
        self.assertEqual([r["model"] for r in result["rows"]], ["CCC", "LCDM+TL", "CCC+TL"])
        self.assertTrue(all(not r["nominal_matches_printed"] for r in result["rows"]))

    def test_exact_linear_unit_scaling_each_model(self):
        ratio = m.MPC_ROUNDED_KM / m.MPC_NOMINAL_KM
        for row in m.evaluate()["rows"]:
            actual = Decimal(row["rounded_Mpc_Gyr"])
            expected = Decimal(row["nominal_Gyr"]) * ratio
            self.assertLess(abs(actual-expected), Decimal("1e-50"))

    def test_existing_ccc_tl_frozen_baseline_is_preserved(self):
        result = next(r for r in m.evaluate()["rows"] if r["model"] == "CCC+TL")
        self.assertLess(abs(Decimal(result["nominal_Gyr"])-Decimal("26.66721185884256")), Decimal("1e-11"))
        self.assertLess(abs(Decimal(result["rounded_Mpc_Gyr"])-Decimal("26.7045673009029")), Decimal("1e-11"))

    def test_no_boundary_is_crossed_by_rounding(self):
        for row in m.evaluate()["rows"]:
            self.assertGreater(Decimal(row["distance_to_upper_rounding_boundary_Gyr"]), 0)

    def test_invalid_domains_rejected(self):
        with self.assertRaises(ValueError):
            m.age_ccc(Decimal("72"), Decimal("-1"), m.MPC_NOMINAL_KM)
        with self.assertRaises(ValueError):
            m.age_lcdm(Decimal("60"), Decimal("1"), m.MPC_NOMINAL_KM)

if __name__ == "__main__":
    unittest.main()
