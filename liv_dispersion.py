#!/usr/bin/env python3
"""Photon dispersion of the twist walk at Planck spacing (issue #207, ledger benchmark B-LIV).

Part of the Quantum Logical Framework (QLF). Write-up: QM_Postulates_QLF.md §5a.

The twist-walk resolvent (Hidden_Zeros_Closure.md §11) has inverse propagator
sum_a (1 - cos a K_a) over the four axes. A massless mode is a zero of it. How the
time axis is continued decides the sign:

  euclid : K_4 = i E (the Wick rotation used in round 8)
           cosh(aE) = 1 + sum_i 2 sin^2(a k_i / 2)
  real   : time on the lattice directly
           cos(aE)  = 1 - sum_i 2 sin^2(a k_i / 2)   [sign-flipped spatial part]

Both give E^2 = k^2 [1 - xi (a k)^2] + O(a^4) with a direction-dependent xi.
Matching to the convention E^2 = p^2 [1 - s (p / E_QG2)^2] gives
E_QG2 = E_P / sqrt(|xi|) when a is the Planck length.

Usage:
    python3 liv_dispersion.py
"""
from __future__ import annotations

import math

E_PLANCK_GEV = 1.220890e19          # Planck energy, CODATA 2018 value
LHAASO_EQG2 = 6e-8                  # lower limit, units of E_P (LHAASO, PRL 133, 071501, 2024)


def energy(k, mode, a=1.0):
    s = sum(2 * math.sin(a * c / 2) ** 2 for c in k)
    if mode == 'euclid':
        return math.acosh(1 + s) / a
    c = 1 - s
    if c < -1:
        return float('nan')
    return math.acos(c) / a


def xi_numeric(n, mode, eps=1e-3):
    """xi from E^2 = k^2 (1 - xi k^2) at small |k| along unit vector n."""
    k = [eps * c for c in n]
    E = energy(k, mode)
    return (1 - E * E / eps ** 2) / eps ** 2


def xi_formula(n, mode):
    s4 = sum(c ** 4 for c in n)
    # euclid: E^2 = k^2 - a^2 (sum k_i^4 + E^4)/12  ->  xi = (1 + s4)/12
    # real:   E^2 = k^2 + a^2 (E^4 - sum k_i^4)/12  ->  xi = (s4 - 1)/12
    return (1 + s4) / 12 if mode == 'euclid' else (s4 - 1) / 12


def main():
    dirs = {'axis (1,0,0)': (1.0, 0.0, 0.0),
            'face diagonal': (1 / math.sqrt(2), 1 / math.sqrt(2), 0.0),
            'body diagonal': (1 / math.sqrt(3),) * 3}
    for mode in ('euclid', 'real'):
        print(f'[{mode}]')
        for name, n in dirs.items():
            xn, xf = xi_numeric(n, mode), xi_formula(n, mode)
            if abs(xf) < 1e-12:
                print(f'  {name:14s} xi = {xn:+.2e} (formula 0): no quadratic term')
                continue
            eqg = 1 / math.sqrt(abs(xf))
            dv = 1.5 * xf * (10e3 / E_PLANCK_GEV) ** 2   # |1 - v_group| at 10 TeV
            kind = 'subluminal' if xf > 0 else 'superluminal'
            print(f'  {name:14s} xi = {xn:+.6f} (formula {xf:+.6f}); {kind}; '
                  f'E_QG2 = {eqg:.2f} E_P, margin over LHAASO {eqg / LHAASO_EQG2:.1e}; '
                  f'|1 - v| at 10 TeV = {abs(dv):.1e}')


if __name__ == '__main__':
    main()
