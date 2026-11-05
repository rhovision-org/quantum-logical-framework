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

The realizable Weyl walk (QLF_RealizableWalk: realWalk = step_y step_x step_z,
each step exp(i k sigma)) is also solved, in its Lean order and in the
palindromic (half step in each order) form.

Usage:
    python3 liv_dispersion.py
"""
from __future__ import annotations

import cmath
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


SIG = {'y': ((0, -1j), (1j, 0)), 'x': ((0, 1), (1, 0)), 'z': ((1, 0), (0, -1))}


def mmul(A, B):
    return tuple(tuple(sum(A[r][t] * B[t][c] for t in range(2)) for c in range(2)) for r in range(2))


def step(k, ax):
    s = SIG[ax]
    return tuple(tuple((math.cos(k) if r == c else 0) + 1j * math.sin(k) * s[r][c]
                       for c in range(2)) for r in range(2))


def walk_omega(k, palindromic):
    kk = dict(zip('yxz', k))
    M = ((1, 0), (0, 1))
    if palindromic:
        for ax in 'yxzzxy':
            M = mmul(M, step(kk[ax] / 2, ax))
    else:
        for ax in 'yxz':
            M = mmul(M, step(kk[ax], ax))
    # SU(2): eigenvalues exp(+-i omega), cos omega = tr/2
    return math.acos(max(-1.0, min(1.0, ((M[0][0] + M[1][1]) / 2).real)))


def walk_report():
    diag = (1 / math.sqrt(3),) * 3
    for pal in (False, True):
        name = 'palindromic' if pal else 'Lean order y,x,z'
        rows = []
        for label, n in (('axis', (1.0, 0.0, 0.0)), ('(+,+,+)', diag),
                         ('(-,-,-)', tuple(-c for c in diag))):
            eps = 1e-3
            w = walk_omega([eps * c for c in n], pal)
            rows.append(f'{label}: (w-k)/k^2 = {(w - eps) / eps ** 2:+.4f}, (w-k)/k^3 = {(w - eps) / eps ** 3:+.3e}')
        print(f'[walk, {name}]  ' + '; '.join(rows))
    # linear term: w = k + k^2 n_x n_y n_z, so v - 1 = 2 k n_x n_y n_z, max |.| = 2/(3 sqrt 3)
    lin = 2 / (3 * math.sqrt(3))
    print(f'  Lean order: linear term |v - 1| <= {lin:.4f} (E/E_P), E_QG1 = {1 / lin:.2f} E_P '
          f'(LHAASO E_QG1 > 10 E_P for photons)')


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
    walk_report()


if __name__ == '__main__':
    main()
