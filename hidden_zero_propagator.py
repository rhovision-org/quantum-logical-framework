#!/usr/bin/env python3
"""The propagator from summed twist histories (issue #207, G2c round 5).

Part of the Quantum Logical Framework (QLF). Write-up: Hidden_Zeros_Closure.md §11.

Every twist history of every length, weighted by its cylinder measure 8^-L
(QLF_KraftMeasure) and phased by e^{i k.d} for its net displacement d on Z^4,
sums to G(k) = 1/(1 - phi(k)) with phi(k) = (1/4) sum_a cos k_a. At lattice
spacing a the derived inverse propagator is X_der = -8 (1 - phi(aK)) / a^2,
with K = (x, y, z, i t) the Euclidean image of the spinor momentum P (so
-K^2 = det P = X). The Tr(phi^3) triangulation sum is evaluated with 1/X_der
in place of 1/X on round 4's hidden-zero locus points and generic points.

Usage:
    python3 hidden_zero_propagator.py --max-n 7 --points 20
"""
from __future__ import annotations

import argparse
import cmath
import itertools
import math
import random
import statistics

import curve_cover_census as cc
from hidden_zero_closures import diagonals
from hidden_zero_spinors import point_on_locus, generic_point, outer, madd

TWISTS = [(a, s) for a in range(4) for s in (1, -1)]   # the eight twists are +-e_a


def phi(k):
    return sum(cmath.cos(c) for c in k) / 4


def one_minus_phi(k):
    return sum(2 * cmath.sin(c / 2) ** 2 for c in k) / 4


def check_d1(rng, max_len=6, trials=3):
    worst = 0.0
    for _ in range(trials):
        k = [rng.uniform(-math.pi, math.pi) for _ in range(4)]
        walk = 0j
        for L in range(max_len + 1):
            tot = 0j
            for h in itertools.product(TWISTS, repeat=L):
                d = [0, 0, 0, 0]
                for a, s in h:
                    d[a] += s
                tot += cmath.exp(1j * sum(k[c] * d[c] for c in range(4)))
            walk += tot / 8 ** L
        series = sum(phi(k) ** L for L in range(max_len + 1))
        worst = max(worst, abs(walk - series))
    return worst


def to_complex(M):
    return [[complex(float(e.a), float(e.b)) for e in row] for row in M]


def euclid(P):
    t = (P[0][0] + P[1][1]) / 2
    z = (P[0][0] - P[1][1]) / 2
    x = (P[0][1] + P[1][0]) / 2
    y = (P[1][0] - P[0][1]) / 2j
    return [x, y, z, 1j * t]


def chord_K(n, lam, lamt, diags):
    p = [None] + [to_complex(outer(lam[k], lamt[k])) for k in range(1, n + 1)]
    cum = [[[0j, 0j], [0j, 0j]]]
    for k in range(1, n + 1):
        cum.append([[cum[-1][r][c] + p[k][r][c] for c in range(2)] for r in range(2)])
    K = {}
    for (a, b) in diags:
        D = [[cum[b - 1][r][c] - cum[a - 1][r][c] for c in range(2)] for r in range(2)]
        K[(a, b)] = euclid(D)
    scale = max(abs(c) for v in K.values() for c in v)
    return {d: [c / scale for c in v] for d, v in K.items()}


def ratio(tris, X):
    terms = []
    for t in tris:
        q = 1
        for d in t:
            q /= X[d]
        terms.append(q)
    return abs(sum(terms)) / sum(abs(q) for q in terms)


def X_cont(K):
    return -sum(c * c for c in K)


def X_der(K, a):
    return -8 * one_minus_phi([a * c for c in K]) / a ** 2


def slope(xs, ys):
    lx = [math.log(x) for x in xs]
    ly = [math.log(y) for y in ys]
    mx, my = statistics.fmean(lx), statistics.fmean(ly)
    return sum((u - mx) * (v - my) for u, v in zip(lx, ly)) / sum((u - mx) ** 2 for u in lx)


AS = [10 ** (-1 - 0.5 * i) for i in range(5)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-n', type=int, default=7)
    ap.add_argument('--points', type=int, default=20)
    ap.add_argument('--seed', type=int, default=207)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    print(f'D1: max |walk sum - geometric series| over L <= 6 = {check_d1(rng):.2e}')

    for n in range(5, args.max_n + 1):
        diags = diagonals(n)
        tris = [tuple(sorted(t)) for t in cc.triangulations(list(range(1, n + 1)))]
        d2_err = 0.0
        loc_slopes, loc_min, gen_slopes, gen_lim = [], math.inf, [], []
        for (i, j) in diags:
            for _ in range(args.points):
                pt = point_on_locus(n, i, j, rng)
                if pt is None:
                    continue
                K = chord_K(n, *pt, diags)
                Xc = {d: X_cont(v) for d, v in K.items()}
                if min(abs(v) for v in Xc.values()) < 1e-9:
                    continue   # singular in the continuum: skipped as in round 4
                amin = AS[-1]
                for d, v in K.items():
                    want = sum(c ** 4 for c in v) / 12
                    got = (X_der(v, amin) - Xc[d]) / amin ** 2
                    if abs(want) > 1e-6:
                        d2_err = max(d2_err, abs(got - want) / abs(want))
                Rs = [ratio(tris, {d: X_der(v, a) for d, v in K.items()}) for a in AS]
                loc_min = min(loc_min, min(Rs))
                loc_slopes.append(slope(AS, Rs))
        gen = 0
        while gen < args.points * len(diags):
            pt = generic_point(n, rng)
            if pt is None:
                continue
            K = chord_K(n, *pt, diags)
            Xc = {d: X_cont(v) for d, v in K.items()}
            if min(abs(v) for v in Xc.values()) < 1e-9:
                continue
            gen += 1
            R0 = ratio(tris, Xc)
            Rs = [ratio(tris, {d: X_der(v, a) for d, v in K.items()}) for a in AS]
            gen_lim.append(R0)
            diffs = [abs(r - R0) for r in Rs]
            if min(diffs) > 0:
                gen_slopes.append(slope(AS, diffs))
        print(f'n={n}: D2 max rel err {d2_err:.2e}; locus points {len(loc_slopes)}, '
              f'median slope {statistics.median(loc_slopes):.3f} '
              f'(range {min(loc_slopes):.3f}..{max(loc_slopes):.3f}), min R {loc_min:.2e}; '
              f'generic {gen}, min R(0) {min(gen_lim):.2e}, median R(0) {statistics.median(gen_lim):.3f}, '
              f'median slope of R-R(0) {statistics.median(gen_slopes):.3f} '
              f'(range {min(gen_slopes):.3f}..{max(gen_slopes):.3f}, {len(gen_slopes)} fitted)')


if __name__ == '__main__':
    main()
