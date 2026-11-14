#!/usr/bin/env python3
"""External Gupta 2023 benchmark; see ../Gupta_CCC_TL.md. No QLF inputs.

Uses equations 20, 25–26, 35, 43–45, 49–50 of arXiv:2309.13100v1.
Standard library only. Targets and tolerances are read solely by the scorer.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / 'verification/gupta-ccc-tl/specification.json'
MPC_KM = 3.0856775814913673e19
GYR_SECONDS = 1e9 * 365.25 * 86400
C_KM_S = 299792.458


def simpson(fn, lower, upper, panels):
    if panels < 2 or panels % 2:
        raise ValueError('Simpson panels must be positive and even')
    step = (upper - lower) / panels
    total = fn(lower) + fn(upper)
    total += math.fsum((4 if i % 2 else 2) * fn(lower + i * step)
                       for i in range(1, panels))
    return total * step / 3


class Reference:
    def __init__(self, hc=59.51, ratio=-0.7997, panels=2048, iterations=80):
        if not math.isfinite(hc) or hc <= 0 or not -1 < ratio < 0:
            raise ValueError('Reference branch requires Hc > 0 and -1 < alpha/Hc < 0')
        if panels < 2 or panels % 2 or iterations < 1:
            raise ValueError('Even panels >= 2 and iterations >= 1 required')
        self.hc, self.r, self.panels, self.iterations = hc, ratio, panels, iterations
        self.cubic_c = 1.5 * (1 + ratio) / ratio
        self.cubic_a = 1 - self.cubic_c
        self.x_bang = math.sqrt(-self.cubic_c / self.cubic_a)
        self.ht_over_hc = (1 + ratio) * (3 + ratio) / 2
        self.hubble_gyr = MPC_KM / hc / GYR_SECONDS

    def x(self, a):
        if not 0 <= a <= 1:
            raise ValueError('Past branch requires 0 <= a <= 1')
        if a == 0:
            return self.x_bang
        if a == 1:
            return 1.0
        lo, hi = self.x_bang, 1.0
        target = a ** 1.5
        for _ in range(self.iterations):
            mid = (lo + hi) / 2
            if self.cubic_a * mid**3 + self.cubic_c * mid < target:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2

    def expansion(self, zc):
        a = 1 / (1 + zc)
        return (1 + self.r) * a**-1.5 * self.x(a) - self.r

    def distance_integral(self, zc):
        return simpson(lambda z: 1 / self.expansion(z), 0, zc, self.panels)

    def at_redshift(self, z):
        if not math.isfinite(z) or z < 0:
            raise ValueError('Observed redshift must be finite and nonnegative')
        lo, hi = 0.0, z
        for _ in range(self.iterations):
            zc = (lo + hi) / 2
            total_log = math.log1p(zc) + self.ht_over_hc * self.distance_integral(zc)
            if total_log < math.log1p(z):
                lo = zc
            else:
                hi = zc
        zc = (lo + hi) / 2
        a = 1 / (1 + zc)
        x = self.x(a)
        age = -2 * math.log(x / self.x_bang) / self.r * self.hubble_gyr
        # Independent age quadrature of eq. 50, a=s^2 removes endpoint sqrt.
        def age_integrand(s):
            return 2 * s*s / ((1 + self.r) * self.x(s*s) - self.r * s**3)
        quadrature_age = simpson(age_integrand, 0, math.sqrt(a), self.panels) * self.hubble_gyr
        integral = self.distance_integral(zc)
        zt = (1 + z) / (1 + zc) - 1
        dp = C_KM_S / self.hc * integral
        return {'z_observed': z, 'z_expansion': zc, 'z_tired_light': zt,
                'scale_factor': a, 'f': x**-2, 'age_Gyr': age,
                'age_quadrature_Gyr': quadrature_age,
                'H_expansion_km_s_Mpc': self.hc * self.expansion(zc),
                'proper_distance_Mpc': dp,
                'luminosity_distance_Mpc': dp * math.sqrt((1+z)*(1+zc)),
                'angular_distance_Mpc': a * x**-2 * dp,
                'composition_residual': (1+zc)*(1+zt)-(1+z),
                'distance_match_residual': self.ht_over_hc*integral-math.log1p(zt)}


def benchmark(spec):
    params = spec['parameters']
    cfg = spec['numerics']
    kwargs = dict(hc=params['Hc_km_s_Mpc'], ratio=params['alpha_over_Hc'],
                  iterations=cfg['bisection_iterations'])
    model = Reference(**kwargs, panels=cfg['simpson_panels'])
    refined = Reference(**kwargs, panels=cfg['refinement_panels'])
    rows = []
    for target in spec['targets']:
        row = model.at_redshift(target['z'])
        finer = refined.at_redshift(target['z'])
        row['published_age_Gyr'] = target['age_Gyr']
        row['age_residual_Gyr'] = row['age_Gyr'] - target['age_Gyr']
        row['refinement_change_Gyr'] = abs(row['age_Gyr'] - finer['age_Gyr'])
        row['age_quadrature_difference_Gyr'] = abs(row['age_Gyr'] - row['age_quadrature_Gyr'])
        row['target_pass'] = abs(row['age_residual_Gyr']) <= target['tolerance_Gyr']
        row['numerics_pass'] = max(row['refinement_change_Gyr'], row['age_quadrature_difference_Gyr']) < cfg['age_convergence_Gyr']
        rows.append(row)
    passed = all(row['target_pass'] and row['numerics_pass'] for row in rows)
    return {'benchmark_acceptance': 'PASS' if passed else 'FAIL',
            'scope': 'Self-run retrospective external equation reproduction; F absent; E absent; QLF bridge B-OPEN',
            'Hc_km_s_Mpc': model.hc, 'Ht_km_s_Mpc': model.hc*model.ht_over_hc,
            'H0_total_km_s_Mpc': model.hc*(1+model.ht_over_hc), 'rows': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write deterministic JSON report')
    args = parser.parse_args()
    spec = json.loads(SPEC.read_text())
    report = benchmark(spec)
    report['specification_sha256'] = hashlib.sha256(SPEC.read_bytes()).hexdigest()
    report['implementation_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['executed_source_revision'] = subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip()
    rendered = json.dumps(report, indent=2, allow_nan=False) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')
    return 0 if report['benchmark_acceptance'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
