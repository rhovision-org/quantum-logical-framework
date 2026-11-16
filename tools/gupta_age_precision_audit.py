#!/usr/bin/env python3
"""Retrospective source-precision audit; see verification/gupta-clock-conventions/.

Independent closed-form present-age calculation from the published past cubic
endpoint. Does not import, rerun or modify the frozen stage-1 implementation.
No optimizer or target-inversion is used.
"""
from decimal import Decimal, localcontext
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / 'verification/gupta-clock-conventions/audit_specification.json'


def age_gyr(hc, ratio, *, year_days='365.25', mpc_km='3.0856775814913673e19'):
    """Equation-50 coordinate age, not a newly identified physical clock age."""
    with localcontext() as ctx:
        ctx.prec = 60
        h, r, year, mpc = map(lambda x: Decimal(str(x)), (hc, ratio, year_days, mpc_km))
        if not all(x.is_finite() for x in (h, r, year, mpc)):
            raise ValueError('Finite inputs required')
        if h <= 0 or not -1 < r < 0 or year <= 0 or mpc <= 0:
            raise ValueError('Requires Hc > 0, -1 < r < 0 and positive units')
        hubble_gyr = mpc / h / (Decimal(10)**9 * year * 86400)
        return +(((3+r)/(3*(1+r))).ln()/(-r)*hubble_gyr)


def audit(spec):
    v = spec['inputs']
    kwargs = dict(year_days=v['year_days'], mpc_km=v['Mpc_km'])
    age = age_gyr(v['Hc'], v['r'], **kwargs)
    h_lo, h_hi = spec['rounding_intervals']['Hc']
    r_lo, r_hi = spec['rounding_intervals']['r']
    # The analytic monotonicity argument is in the audit README: age increases
    # with -r and decreases with Hc throughout this domain.
    lower = age_gyr(h_hi, r_hi, **kwargs)
    upper = age_gyr(h_lo, r_lo, **kwargs)
    target_lo, target_hi = map(lambda x: Decimal(str(x)), spec['reporting_interval_Gyr'])
    result = {
        'scope': 'Retrospective diagnostic; original benchmark and tolerance unchanged; no historical cause inferred.',
        'central_coordinate_age_Gyr': str(age),
        'nearest_rounding_bounds_Gyr': [str(lower), str(upper)],
        'published_reporting_interval_Gyr': [str(target_lo), str(target_hi)],
        'displayed_parameter_rounding_sufficient': not (upper < target_lo or lower > target_hi),
        'ratio_rounding_diagnostic': {
            'r': spec['diagnostics']['ratio_rounding_only'],
            'age_Gyr': str(age_gyr(v['Hc'], spec['diagnostics']['ratio_rounding_only'], **kwargs)),
            'interpretation': 'Predeclared rounding diagnostic; not evidence of an author-used intermediate or a refitted input.'
        },
        'year_diagnostics': [
            {'year_days': d, 'age_Gyr': str(age_gyr(v['Hc'], v['r'], year_days=d, mpc_km=v['Mpc_km']))}
            for d in spec['diagnostics']['alternative_year_days']
        ],
        'source_precision_gate': 'UNRESOLVED: author-used intermediate/constants/code not available in the cited source.',
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = audit(json.loads(SPEC.read_text()))
    result['specification_sha256'] = hashlib.sha256(SPEC.read_bytes()).hexdigest()
    result['implementation_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['executed_source_revision'] = subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
