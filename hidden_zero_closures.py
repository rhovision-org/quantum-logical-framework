#!/usr/bin/env python3
"""Hidden zeros from closure decompositions (issue #207, target G2c).

Part of the Quantum Logical Framework (QLF). Write-up: Hidden_Zeros_Closure.md.

A_n^W = sum over triangulations T of W(T) * prod_{(i,j) in T} 1/X_ij, evaluated in
exact rationals at random points of each hidden-zero locus c_ab = 0
(a in [i, j-2], b in [j, i-2], cyclic). Weights W0 (unit), W1 (closure
orderings), W2 (1-D closure ways). See the write-up for definitions.

Usage:
    python3 hidden_zero_closures.py --max-n 7 --points 20
"""
from __future__ import annotations

import argparse
import itertools
import random
from fractions import Fraction
from math import comb, factorial

import curve_cover_census as cc


def diagonals(n):
    return [(i, j) for i in range(1, n + 1) for j in range(i + 2, n + 1) if not (i == 1 and j == n)]


def X(vals, i, j, n):
    i, j = min(i, j), max(i, j)
    if j - i == 1 or (i == 1 and j == n) or i == j:
        return Fraction(0)
    return vals[(i, j)]


def mesh_row(a, b, n, diags):
    """c_ab as a dict diag -> coefficient (linear in X)."""
    nx = lambda k: (k % n) + 1
    terms = [((a, b), 1), ((nx(a), nx(b)), 1), ((a, nx(b)), -1), ((nx(a), b), -1)]
    row = {}
    for (u, v), s in terms:
        u, v = min(u, v), max(u, v)
        if v - u <= 1 or (u == 1 and v == n) or u == v:
            continue
        row[(u, v)] = row.get((u, v), 0) + s
    return {k: c for k, c in row.items() if c}


def cyc_range(start, end, n):
    """start, start+1, ..., end (cyclic, inclusive), 1-based."""
    out = [start]
    while out[-1] != end:
        out.append(out[-1] % n + 1)
    return out


def zero_conditions(i, j, n):
    A = cyc_range(i, (j - 2 - 1) % n + 1, n)
    B = cyc_range(j, (i - 2 - 1) % n + 1, n)
    return [(a, b) for a in A for b in B]


def random_point_on(rows, diags, rng):
    """Random rational X satisfying every row = 0 (Gaussian elimination)."""
    rows = [dict(r) for r in rows if r]
    pivots = {}
    M = []
    for r in rows:
        r = {k: Fraction(v) for k, v in r.items()}
        for p, pr in pivots.items():
            if p in r:
                f = r[p]
                for k, v in pr.items():
                    r[k] = r.get(k, 0) - f * v
                r = {k: v for k, v in r.items() if v}
        if not r:
            continue
        p = sorted(r)[0]
        f = r[p]
        r = {k: v / f for k, v in r.items()}
        for q in list(pivots):
            if p in pivots[q]:
                g = pivots[q][p]
                pivots[q] = {k: pivots[q].get(k, 0) - g * r.get(k, 0)
                             for k in set(pivots[q]) | set(r)}
                pivots[q] = {k: v for k, v in pivots[q].items() if v}
        pivots[p] = r
    vals = {}
    for d in diags:
        if d not in pivots:
            vals[d] = Fraction(rng.randint(-50, 50) or 1, rng.randint(1, 13))
    for p, r in pivots.items():
        vals[p] = -sum(v * vals[k] for k, v in r.items() if k != p)
    return vals


def side_size(d, base, n):
    """Particles on the side of chord d=(i,j) not containing step `base`
    (step k is the side (k, k+1)). Side 1: steps i..j-1."""
    i, j = d
    inside = set(range(i, j))
    return set(inside) if base not in inside else set(range(1, n + 1)) - inside


def orderings(T, base, n):
    """Linear extensions of the nesting order (inner before outer)."""
    sets = {d: frozenset(side_size(d, base, n)) for d in T}
    ds = list(T)
    count = 0
    for perm in itertools.permutations(ds):
        ok = True
        for x in range(len(perm)):
            for y in range(x + 1, len(perm)):
                if sets[perm[y]] < sets[perm[x]]:
                    ok = False
                    break
            if not ok:
                break
        count += ok
    return count


def weights(T, n):
    w0 = Fraction(1)
    w1 = Fraction(sum(orderings(T, b, n) for b in range(1, n + 1)), n)
    w2 = Fraction(1)
    for (i, j) in T:
        L = min(j - i, n - (j - i))
        w2 *= comb(2 * L, L)
    return w0, w1, w2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-n', type=int, default=7)
    ap.add_argument('--points', type=int, default=20)
    ap.add_argument('--seed', type=int, default=207)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    for n in range(4, args.max_n + 1):
        diags = diagonals(n)
        tris = [tuple(sorted(t)) for t in cc.triangulations(list(range(1, n + 1)))]
        W = {t: weights(t, n) for t in tris}
        distinct = [len({W[t][k] for t in tris}) for k in range(3)]
        fails = [0, 0, 0]
        tests = 0
        for (i, j) in diags:
            rows = [mesh_row(a, b, n, diags) for a, b in zero_conditions(i, j, n)]
            for _ in range(args.points):
                vals = random_point_on(rows, diags, rng)
                if any(v == 0 for v in vals.values()):
                    continue
                tests += 1
                for k in range(3):
                    A = sum(W[t][k] * Fraction(1) / eval_prod(t, vals) for t in tris)
                    fails[k] += (A != 0)
        print(f'n={n}: {len(tris)} decompositions; distinct weights W0/W1/W2 = {distinct}; '
              f'{tests} points; nonzero A for W0/W1/W2 = {fails}')


def eval_prod(t, vals):
    p = Fraction(1)
    for d in t:
        p *= vals[d]
    return p


if __name__ == '__main__':
    main()
