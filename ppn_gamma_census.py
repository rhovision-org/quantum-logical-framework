#!/usr/bin/env python3
"""PPN gamma from the closure census: balance versus phase.

Part of the [Quantum Logical Framework (QLF)](README.md). See
Collective_Electrodynamics.md §7 and lean/QLF_MagneticOrientation.lean §10.

For every closure (count-balanced twist history) of length L, count the steps it spends on
each axis. Summed over the census:

* unsigned (balance): every axis gets the same total, so a spatial axis over the gauge axis
  is exactly 1. This is `census_axis_blind` / `censusGamma_eq_one` in Lean.
* signed (each closure weighted by its Pauli phase): the gauge axis gets more than the spatial
  axes, because the half-spin phase lives on spatial plaquettes only. Read as gamma, this gives
  about 0.6, which the Cassini bound (gamma - 1 = (2.1 +/- 2.3) x 10^-5) excludes.

So if delay is read from the census, it must be the balance census, not the phase census.
"""
import itertools
from twist_core import pauli_fold, calculate_action

TWISTS = '^v<>/\\+-'
AXIS = {'^': 'Y', 'v': 'Y', '<': 'X', '>': 'X', '/': 'Z', '\\': 'Z', '+': 'I', '-': 'I'}


def census(L):
    unsigned = {a: 0 for a in 'IXYZ'}
    signed = {a: 0 for a in 'IXYZ'}
    for h in itertools.product(TWISTS, repeat=L):
        s = ''.join(h)
        if any(calculate_action(s)):
            continue
        phase = round(pauli_fold(s)[0].real)  # balanced => fold is +-I
        for a in 'IXYZ':
            n = sum(1 for c in s if AXIS[c] == a)
            unsigned[a] += n
            signed[a] += phase * n
    return unsigned, signed


if __name__ == '__main__':
    for L in (2, 4, 6):
        u, s = census(L)
        print(f"L={L}  unsigned {u}  gamma={u['Y'] / u['I']:.4f}   "
              f"signed {s}  gamma={s['Y'] / s['I']:.4f}")
