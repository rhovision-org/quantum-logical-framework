#!/usr/bin/env python3
"""Hidden zeros on complex momenta from Gaussian-integer spinors (issue #207, G2c round 4).

Part of the Quantum Logical Framework (QLF). Write-up: Hidden_Zeros_Closure.md §9.

Each particle's momentum is the rank-one 2x2 matrix p = lam lamt^T with spinor
entries in Z[i] (the ring of QLF's Pauli phases {+-1, +-i}, QLF_Pauli). det p = 0,
so p is null (QLF_Minkowski: det Form = interval); X_ij = det(p_i + ... + p_{j-1}).
lam and lamt are independent, so momenta are complex and p_a.p_b = 0 holds when
<ab> = 0 or [ab] = 0, without the momenta being parallel.

On the hidden-zero locus of chord (i, j) with rectangle A x B, the smaller side S
keeps generic spinors and each momentum on the larger side T is built from them
so that every pair (a in S, b in T) has <ab> = 0 or [ab] = 0. The two particles
outside A and B take generic lam; their lamt are solved from conservation.

Usage:
    python3 hidden_zero_spinors.py --max-n 7 --points 20
"""
from __future__ import annotations

import argparse
import random
from fractions import Fraction

import curve_cover_census as cc
from hidden_zero_closures import diagonals, zero_conditions, cyc_range


class G:
    """Gaussian rational a + b i, exact."""
    __slots__ = ('a', 'b')

    def __init__(self, a=0, b=0):
        self.a, self.b = Fraction(a), Fraction(b)

    def __add__(s, o): o = _g(o); return G(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __sub__(s, o): o = _g(o); return G(s.a - o.a, s.b - o.b)
    def __rsub__(s, o): return _g(o) - s
    def __neg__(s): return G(-s.a, -s.b)
    def __mul__(s, o): o = _g(o); return G(s.a * o.a - s.b * o.b, s.a * o.b + s.b * o.a)
    __rmul__ = __mul__
    def inv(s):
        d = s.a * s.a + s.b * s.b
        return G(s.a / d, -s.b / d)
    def __truediv__(s, o): return s * _g(o).inv()
    def __eq__(s, o): o = _g(o); return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a, s.b))
    def iszero(s): return s.a == 0 and s.b == 0
    def __repr__(s): return f'({s.a}+{s.b}i)'


def _g(x):
    return x if isinstance(x, G) else G(x)


def rg(rng):
    while True:
        z = G(rng.randint(-5, 5), rng.randint(-5, 5))
        if not z.iszero():
            return z


def rspinor(rng):
    return (rg(rng), rg(rng))


def outer(l, lt):
    return [[l[0] * lt[0], l[0] * lt[1]], [l[1] * lt[0], l[1] * lt[1]]]


def madd(P, Q):
    return [[P[r][c] + Q[r][c] for c in range(2)] for r in range(2)]


def det(P):
    return P[0][0] * P[1][1] - P[0][1] * P[1][0]


def solve_two(l1, l2, R):
    """lt1, lt2 with l1 lt1^T + l2 lt2^T = -R (needs <12> != 0)."""
    ang = l1[0] * l2[1] - l1[1] * l2[0]
    if ang.iszero():
        return None
    # dual basis: row vectors d1, d2 with d1.l1 = 1, d1.l2 = 0, etc.
    d1 = (l2[1] / ang, -l2[0] / ang)
    d2 = (-l1[1] / ang, l1[0] / ang)
    lt1 = tuple(-(d1[0] * R[0][c] + d1[1] * R[1][c]) for c in range(2))
    lt2 = tuple(-(d2[0] * R[0][c] + d2[1] * R[1][c]) for c in range(2))
    return lt1, lt2


def point_on_locus(n, i, j, rng):
    A = cyc_range(i, (j - 2 - 1) % n + 1, n)
    B = cyc_range(j, (i - 2 - 1) % n + 1, n)
    S, T = (A, B) if len(A) <= len(B) else (B, A)
    free = [k for k in range(1, n + 1) if k not in A and k not in B]
    assert len(free) == 2
    lam, lamt = {}, {}
    for s in S:
        lam[s], lamt[s] = rspinor(rng), rspinor(rng)
    for idx, t in enumerate(T):
        r1, r2 = rg(rng), rg(rng)
        if len(S) == 1:
            (s,) = S
            if idx % 2 == 0:   # [s t] = 0
                lam[t] = rspinor(rng)
                lamt[t] = (lamt[s][0] * r2, lamt[s][1] * r2)
            else:              # <s t> = 0
                lam[t] = (lam[s][0] * r1, lam[s][1] * r1)
                lamt[t] = rspinor(rng)
        else:
            s1, s2 = S
            x, y = (s1, s2) if idx % 2 == 0 else (s2, s1)
            lam[t] = (lam[x][0] * r1, lam[x][1] * r1)
            lamt[t] = (lamt[y][0] * r2, lamt[y][1] * r2)
    for f in free:
        lam[f] = rspinor(rng)
    R = [[G(), G()], [G(), G()]]
    for k in range(1, n + 1):
        if k not in free:
            R = madd(R, outer(lam[k], lamt[k]))
    sol = solve_two(lam[free[0]], lam[free[1]], R)
    if sol is None:
        return None
    lamt[free[0]], lamt[free[1]] = sol
    return lam, lamt


def generic_point(n, rng):
    lam = {k: rspinor(rng) for k in range(1, n + 1)}
    lamt = {k: rspinor(rng) for k in range(1, n - 1)}
    R = [[G(), G()], [G(), G()]]
    for k in range(1, n - 1):
        R = madd(R, outer(lam[k], lamt[k]))
    sol = solve_two(lam[n - 1], lam[n], R)
    if sol is None:
        return None
    lamt[n - 1], lamt[n] = sol
    return lam, lamt


def evaluate(n, lam, lamt, tris, diags, loci):
    p = {k: outer(lam[k], lamt[k]) for k in range(1, n + 1)}
    tot = [[G(), G()], [G(), G()]]
    for k in p:
        tot = madd(tot, p[k])
    assert all(tot[r][c].iszero() for r in range(2) for c in range(2))
    P = [[[G(), G()], [G(), G()]]]
    for k in range(1, n + 1):
        P.append(madd(P[-1], p[k]))
    X = {}
    for (a, b) in diags:
        D = [[P[b - 1][r][c] - P[a - 1][r][c] for c in range(2)] for r in range(2)]
        X[(a, b)] = det(D)
    if any(v.iszero() for v in X.values()):
        return 'singular', None
    nx = lambda k: (k % n) + 1

    def Xf(a, b):
        a, b = min(a, b), max(a, b)
        if b - a <= 1 or (a == 1 and b == n):
            return G()
        return X[(a, b)]
    on = any(all((Xf(a, b) + Xf(nx(a), nx(b)) - Xf(a, nx(b)) - Xf(nx(a), b)).iszero()
                 for a, b in L) for L in loci)
    Aval = G()
    for t in tris:
        q = G(1)
        for d in t:
            q = q * X[d]
        Aval = Aval + q.inv()
    return on, Aval.iszero()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-n', type=int, default=7)
    ap.add_argument('--points', type=int, default=20)
    ap.add_argument('--seed', type=int, default=207)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    for n in range(5, args.max_n + 1):
        diags = diagonals(n)
        tris = [tuple(sorted(t)) for t in cc.triangulations(list(range(1, n + 1)))]
        loci = [zero_conditions(i, j, n) for (i, j) in diags]
        built = sing = good = zero_on = 0
        for (i, j) in diags:
            for _ in range(args.points):
                pt = point_on_locus(n, i, j, rng)
                if pt is None:
                    continue
                built += 1
                r = evaluate(n, *pt, tris, diags, loci)
                if r[0] == 'singular':
                    sing += 1
                    continue
                on, z = r
                assert on, 'construction missed the locus'
                good += 1
                zero_on += z
        gen = gzero = gsing = 0
        while gen < args.points * len(diags):
            pt = generic_point(n, rng)
            if pt is None:
                continue
            r = evaluate(n, *pt, tris, diags, loci)
            if r[0] == 'singular':
                gsing += 1
                continue
            gen += 1
            gzero += r[1]
        print(f'n={n}: locus points built {built}, singular {sing}, non-singular {good}, '
              f'A = 0 on {zero_on}/{good}; control: generic points {gen}, A = 0 on {gzero} '
              f'({gsing} singular skipped)')


if __name__ == '__main__':
    main()
