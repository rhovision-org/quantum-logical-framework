#!/usr/bin/env python3
"""Hidden zeros on momenta from long twist words (issue #207, G2c round 3).

Part of the Quantum Logical Framework (QLF). Write-up: Hidden_Zeros_Closure.md §7.

A particle's momentum is eta * (|k|, k), with k the net displacement of a twist
word and |k| the realizable walk's on-shell energy; |k| integer, <= 3.

Usage:
    python3 hidden_zero_words.py
"""
from __future__ import annotations

import itertools
import random
from fractions import Fraction

import curve_cover_census as cc
from hidden_zero_closures import diagonals, zero_conditions


def directions(R=3):
    out = []
    for x, y, z in itertools.product(range(-R, R + 1), repeat=3):
        q = x * x + y * y + z * z
        if q == 0:
            continue
        r = round(q ** 0.5)
        if r * r == q and r <= R:
            out.append((r, x, y, z))
    return out


NULL = [(e * r, e * x, e * y, e * z) for (r, x, y, z) in directions() for e in (1, -1)]
NULLSET = set(NULL)


def dot(u, v):
    return u[0] * v[0] - u[1] * v[1] - u[2] * v[2] - u[3] * v[3]


def add(u, v):
    return tuple(a + b for a, b in zip(u, v))


def neg(u):
    return tuple(-a for a in u)


def analyse(p, n, diags, tris, loci):
    P = [(0, 0, 0, 0)]
    for v in p:
        P.append(add(P[-1], v))
    X = {}
    for (i, j) in diags:
        d = tuple(a - b for a, b in zip(P[j - 1], P[i - 1]))
        X[(i, j)] = dot(d, d)
    if any(v == 0 for v in X.values()):
        return 'singular', None
    nx = lambda k: (k % n) + 1

    def Xf(i, j):
        i, j = min(i, j), max(i, j)
        if j - i <= 1 or (i == 1 and j == n):
            return 0
        return X[(i, j)]
    bad = 0
    c = {}
    for a in range(1, n + 1):
        for b in range(1, n + 1):
            if a == b or nx(a) == b or nx(b) == a:
                continue
            c[(a, b)] = Xf(a, b) + Xf(nx(a), nx(b)) - Xf(a, nx(b)) - Xf(nx(a), b)
            bad += c[(a, b)] != -2 * dot(p[a - 1], p[b - 1])
    A = Fraction(0)
    for t in tris:
        q = 1
        for d in t:
            q *= X[d]
        A += Fraction(1, q)
    on = any(all(c[(a, b)] == 0 for a, b in L) for L in loci)
    return (on, A == 0, bad), None


def run(n, histories):
    diags = diagonals(n)
    tris = [tuple(sorted(t)) for t in cc.triangulations(list(range(1, n + 1)))]
    loci = [zero_conditions(i, j, n) for (i, j) in diags]
    tot = sing = k1 = on = k2bad = zeros = off = 0
    ex = None
    for p in histories:
        tot += 1
        r, _ = analyse(p, n, diags, tris, loci)
        if r == 'singular':
            sing += 1
            continue
        o, z, b = r
        k1 += b
        on += o
        if o and not z:
            k2bad += 1
        if z:
            zeros += 1
            if not o:
                off += 1
                ex = ex or p
    print(f'n={n}: {tot} conserving histories, {sing} singular; K1 mismatches {k1}; '
          f'non-singular on a locus {on} (K2 nonzero {k2bad}); zeros {zeros}, off every locus {off}'
          + (f'; example {ex}' if ex else ''))


def four():
    for p1, p2, p3 in itertools.product(NULL, repeat=3):
        p4 = neg(add(add(p1, p2), p3))
        if p4 in NULLSET:
            yield (p1, p2, p3, p4)


def six(cap=200000, seed=207):
    rng = random.Random(seed)
    seen = 0
    while seen < cap:
        p = [rng.choice(NULL) for _ in range(4)]
        q = neg(add(add(p[0], p[1]), add(p[2], p[3])))
        splits = [a for a in NULL if add(q, neg(a)) in NULLSET]
        if not splits:
            continue
        a = rng.choice(splits)
        seen += 1
        yield tuple(p + [a, add(q, neg(a))])


if __name__ == '__main__':
    print(f'{len(NULL)} null momenta (|k| <= 3, both energy signs)')
    run(4, four())
    run(6, six())
