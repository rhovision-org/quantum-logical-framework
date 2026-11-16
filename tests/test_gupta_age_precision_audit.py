"""Checks for the separately scoped Gupta source-precision audit."""
from decimal import Decimal, localcontext
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
source = importlib.util.spec_from_file_location('gupta_age_audit', ROOT/'tools/gupta_age_precision_audit.py')
audit = importlib.util.module_from_spec(source)
source.loader.exec_module(audit)


class AgePrecisionAuditTests(unittest.TestCase):
    def test_closed_form_matches_frozen_baseline_without_rerun(self):
        frozen = json.loads((ROOT/'verification/gupta-ccc-tl/result.json').read_text())
        expected = Decimal(str(frozen['rows'][0]['age_Gyr']))
        self.assertLess(abs(audit.age_gyr('59.51', '-0.7997')-expected), Decimal('1e-12'))

    def test_rounding_rectangle_does_not_reach_table_precision(self):
        spec = json.loads(audit.SPEC.read_text())
        report = audit.audit(spec)
        low, high = map(Decimal, report['nearest_rounding_bounds_Gyr'])
        table_low, _ = map(Decimal, report['published_reporting_interval_Gyr'])
        self.assertLess(low, audit.age_gyr('59.51', '-0.7997'))
        self.assertLess(audit.age_gyr('59.51', '-0.7997'), high)
        self.assertLess(high, table_low)
        self.assertFalse(report['displayed_parameter_rounding_sufficient'])

    def test_predeclared_single_diagnostics_do_not_resolve_source(self):
        report = audit.audit(json.loads(audit.SPEC.read_text()))
        low, high = map(Decimal, report['published_reporting_interval_Gyr'])
        diagnostics = [report['ratio_rounding_diagnostic'], *report['year_diagnostics']]
        for row in diagnostics:
            self.assertFalse(low <= Decimal(row['age_Gyr']) <= high)
        self.assertTrue(report['source_precision_gate'].startswith('UNRESOLVED'))

    def test_matter_limit_has_expected_two_thirds_hubble_age(self):
        with localcontext() as ctx:
            ctx.prec = 60
            hubble_gyr = Decimal('3.0856775814913673e19')/Decimal('59.51')/(Decimal(10)**9*Decimal('365.25')*86400)
            expected = Decimal(2)/3*hubble_gyr
            self.assertLess(abs(audit.age_gyr('59.51','-0.000000000001')-expected),Decimal('1e-9'))

    def test_domain_refuses_invalid_clock_or_units(self):
        for hc, r in [('0','-0.8'),('59.51','0'),('59.51','-1'),('NaN','-0.8')]:
            with self.assertRaises(ValueError):
                audit.age_gyr(hc,r)
        with self.assertRaises(ValueError):
            audit.age_gyr('59.51','-0.8',year_days='0')


if __name__ == '__main__':
    unittest.main()
