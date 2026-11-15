#!/usr/bin/env python3
"""
lepton_phase_series.py -- the pre-registered census-LIMIT test for the Koide phase (#140).

Context: Weak_Force.md 5c'''' item 7 proves (Lindemann-Weierstrass) that no phase
read off a FINITE closure can equal a non-zero rational number of radians.  So if
Delta = 3*delta is exactly 2/3, any derivation must be a limit.  This script tests
the one limit built from the frozen selection rules of Lepton_Mass_Ratio_Protocol.md.

PRE-REGISTRATION (frozen in the commit that adds this file, before any value of
the series below was computed).  No muon or tau mass is read anywhere.

  Object.  Rooted spatial twist histories (alphabet ^v<>/\\), protocol rules 1-6:
    no immediate Hermitian reversal; first-return ZFA (closes, no proper prefix
    closes); rooted B = 0 (classifier's sign-triple winding); final Pauli fold -I.
    w_L = number of such rooted histories of length L (ways, not classes).

  Measure.  The uniform non-backtracking measure those rules already imply:
    weight 1/6 for the first twist, 1/5 for each later twist, so a history of
    length L has weight 1 / (6 * 5^(L-1)).

  The ONE statistic (no menu):
    P = sum_L  w_L / (6 * 5^(L-1))
  = the probability that a non-backtracking spatial walk's first closure is an
    electron-like free half-spin closure.  Hypothesis H: Delta = P (radians).

  Why this and nothing else: it is the only limit that uses the frozen rules
  unchanged and adds no choice of its own (rules -> ways -> the measure the rules
  already define).  Variants (class counts, other weights, ratios to all closures,
  fold +I, other L-parities) are NOT tested; testing any of them would be a menu.

  Kill condition, stated first.  Compute partial sums S_N to N_max (as deep as
  runtime allows, at least 20), fit the tail from the last increments, and form
  the bracket [S_N, S_N + T_N].
    FAIL       if 2/3 lies outside the bracket (by more than the bracket's own width).
    PASS-CAND  only if 2/3 lies inside a bracket of width < 0.01; then the 3.4e-5
               test against Delta's measured band is the next pre-registered step.
    UNDECIDED  otherwise.
  A FAIL closes this route only; per the 'incomplete, not negative' rule it says
  nothing about deeper selections.

RESULT: recorded below this line in the commit after the pre-registration.
"""

from __future__ import annotations

import sys
from collections import defaultdict
from fractions import Fraction

# twist index t = 2*axis + (0 for +, 1 for -); axes 0,1,2 = x,y,z
TW = [">", "<", "^", "v", "/", "\\"]
AX = [0, 0, 1, 1, 2, 2]
SG = [1, -1, 1, -1, 1, -1]
CONJ = [1, 0, 3, 2, 5, 4]

_EVEN = {(0, 1, 2), (1, 2, 0), (2, 0, 1)}
_ODD = {(0, 2, 1), (2, 1, 0), (1, 0, 2)}


def sign_triple(a, b, c):
    t = (a, b, c)
    return 1 if t in _EVEN else -1 if t in _ODD else 0


# Pauli group element i^k * sigma_p, p in {0:I, 1:X, 2:Y, 3:Z}
def pmul(k1, p1, k2, p2):
    k = k1 + k2
    if p1 == 0:
        return k % 4, p2
    if p2 == 0:
        return k % 4, p1
    if p1 == p2:
        return k % 4, 0
    # sigma_a sigma_b = i eps_abc sigma_c
    c = 6 - p1 - p2
    eps = 1 if (p1, p2) in {(1, 2), (2, 3), (3, 1)} else -1
    return (k + (1 if eps == 1 else 3)) % 4, c


def twist_pauli(t):
    return (0 if SG[t] == 1 else 2), AX[t] + 1


def series(n_max):
    """w_L for L = 1..n_max under protocol rules 1-6 (exact integers)."""
    w = [0] * (n_max + 1)
    # state: (x, y, z, last, prev_axis, B, k, p) -> count ; prev_axis = -1 if none
    states = defaultdict(int)
    for t in range(6):
        pos = [0, 0, 0]
        pos[AX[t]] += SG[t]
        k, p = twist_pauli(t)
        states[(pos[0], pos[1], pos[2], t, -1, 0, k, p)] += 1
    for n in range(1, n_max):
        new = defaultdict(int)
        rem_after = n_max - (n + 1)
        for (x, y, z, last, pa, B, k, p), c in states.items():
            for t in range(6):
                if t == CONJ[last]:
                    continue
                pos = [x, y, z]
                pos[AX[t]] += SG[t]
                B2 = B + (sign_triple(pa, AX[last], AX[t]) if pa >= 0 else 0)
                k2, p2 = pmul(k, p, *twist_pauli(t))
                if pos == [0, 0, 0]:
                    if B2 == 0 and k2 == 2 and p2 == 0:
                        w[n + 1] += c
                    continue  # first return: never continue past a closure
                if abs(pos[0]) + abs(pos[1]) + abs(pos[2]) > rem_after:
                    continue
                if abs(B2) > rem_after + 1:
                    continue
                new[(pos[0], pos[1], pos[2], t, AX[last], B2, k2, p2)] += c
        states = new
        print(f"  L={n + 1:3d}  w_L={w[n + 1]}  states={len(states)}", file=sys.stderr)
    return w


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    w = series(n_max)
    S = Fraction(0)
    rows = []
    for L in range(1, n_max + 1):
        if w[L]:
            inc = Fraction(w[L], 6 * 5 ** (L - 1))
            S += inc
            rows.append((L, w[L], float(inc), float(S)))
    print(f"{'L':>4} {'w_L':>16} {'increment':>14} {'S_L':>14}")
    for r in rows:
        print(f"{r[0]:4d} {r[1]:16d} {r[2]:14.6e} {r[3]:14.10f}")
    # tail fit: increments at even L, fit inc ~ C * r^L * L^-a from the last three
    import math
    if len(rows) >= 3:
        (L1, _, i1, _), (L2, _, i2, _), (L3, _, i3, _) = rows[-3:]
        # local geometric ratio per 2 steps from the last two increments
        r = i3 / i2
        tail = i3 * r / (1 - r) if r < 1 else float("inf")
        print(f"\nlast ratio per step-pair r = {r:.4f}; geometric tail T_N = {tail:.6e}")
        lo, hi = float(S), float(S) + tail
        print(f"bracket [S_N, S_N + T_N] = [{lo:.8f}, {hi:.8f}], width {hi - lo:.2e}")
        target = 2 / 3
        if lo <= target <= hi:
            verdict = "PASS-CAND" if hi - lo < 0.01 else "UNDECIDED"
        elif min(abs(target - lo), abs(target - hi)) > hi - lo:
            verdict = "FAIL"
        else:
            verdict = "UNDECIDED"
        print(f"verdict against Delta = 2/3: {verdict}")


if __name__ == "__main__":
    main()
