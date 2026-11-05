#!/usr/bin/env python3
"""Non-planar one-loop curve covers on the annulus (issue #207, target G4b).

Part of the Quantum Logical Framework (QLF). Write-up: Curve_Covers_QLF.md §9.

Same handedness reading as curve_cover_loop.py, on a one-loop n-gon whose
gluons attach to the loop from either side, so the surface is an annulus with
marked points on both boundaries. There is no puncture, so no curve spirals.
Each curve's kinematic variable is computed from momentum flow: X_C is the
square of the momentum crossing the curve, the start leg plus every branch the
walk passes on its right. X_C vanishes when that momentum is zero, a single
external scalar, an on-shell gluon (a scaffold), or a cut loop propagator.
Curves with the same momentum share a variable.

Usage:
    python3 curve_cover_nonplanar.py --tree-check 5   # momentum naming vs eq. (13)
    python3 curve_cover_nonplanar.py --sides oi       # one split; o = outer, i = inner
    python3 curve_cover_nonplanar.py --all 4          # every split up to 4 gluons
"""
from __future__ import annotations

import argparse
import itertools
from collections import Counter

import curve_cover_census as cc
import curve_cover_loop as cl


def vec_add(a, b, s=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + s * v
        if out[k] == 0:
            del out[k]
    return out


class Momenta:
    """Oriented momenta on a ribbon graph. into[(side, t)] is the momentum
    flowing into triangle t through side. Basis: external legs p_k and l, with
    sum_k p_k = 0 used to eliminate the last leg."""

    def __init__(self, R, into, legs_order):
        self.R, self.into, self.legs = R, into, legs_order
        last = legs_order[-1]
        self.last = last

    def reduce(self, v):
        v = dict(v)
        c = v.pop(('p', self.last), 0)
        if c:
            for k in self.legs[:-1]:
                v = vec_add(v, {('p', k): -c})
        return {k: x for k, x in v.items() if x}

    def canon(self, v):
        v = self.reduce(v)
        items = tuple(sorted(v.items()))
        neg = tuple(sorted((k, -x) for k, x in v.items()))
        return min(items, neg)


def make_namer(M, zero_set):
    R = M.R

    def namer(leg, edges, turns, end):
        (t,) = R.where[leg]
        mom = dict(M.into[(leg, t)])  # the start leg
        s_in = leg
        path = list(edges) + [end]
        for hand, s_out in zip(turns, path):
            sides = R.tris[t]
            i = sides.index(s_in)
            third = sides[(i - 1) % 3] if hand == 'L' else sides[(i + 1) % 3]
            if hand == 'R':  # the branch passed on the left (the side holding a+1 .. b-1)
                mom = vec_add(mom, M.into[(third, t)])
            if s_out == end:
                break
            t = R.other(s_out, t)
            s_in = s_out
        c = M.canon(mom)
        if c in zero_set:
            return None
        return c

    return namer


def tree_momenta(n, T):
    R = cl.tree_ribbon(n, T)
    N = 2 * n
    into = {}
    # momentum into triangle through each side: leg k carries p_k inward;
    # an internal side carries the total of the legs behind it
    def behind(side, t):
        # sum of leg momenta on the far side of `side` from triangle t
        if side in R.legs:
            return {('p', R.legs[side]): 1}
        u = R.other(side, t)
        tot = {}
        for s in R.tris[u]:
            if s != side:
                tot = vec_add(tot, behind(s, u))
        return tot
    for t, sides in enumerate(R.tris):
        for s in sides:
            into[(s, t)] = behind(s, t)
    M = Momenta(R, into, list(range(1, N + 1)))
    zero = {M.canon({})}
    for k in range(1, N + 1):
        zero.add(M.canon({('p', k): 1}))
    for t, sides in enumerate(R.tris):
        for s in sides:
            if s not in R.legs:
                zero.add(M.canon(into[(s, t)]))  # propagators of T are cut
    return R, M, zero


def annulus(sides):
    """One-loop n-gon with gluon i attached on side sides[i] ('o' or 'i')."""
    n = len(sides)
    tris = []
    for i in range(1, n + 1):
        a = 2 * i - 1
        tris.append((('leg', a), ('leg', a + 1), ('s', i)))
        if sides[i - 1] == 'o':
            tris.append((('s', i), ('q', i % n + 1), ('q', i)))
        else:
            tris.append((('s', i), ('q', i), ('q', i % n + 1)))
    legs = {('leg', k): k for k in range(1, 2 * n + 1)}
    R = cl.Ribbon(tris, legs)
    into = {}
    l = {('l',): 1}
    for i in range(1, n + 1):
        ear, loop = 2 * (i - 1), 2 * (i - 1) + 1
        a = 2 * i - 1
        into[(('leg', a), ear)] = {('p', a): 1}
        into[(('leg', a + 1), ear)] = {('p', a + 1): 1}
        g = {('p', a): 1, ('p', a + 1): 1}
        into[(('s', i), loop)] = g
        into[(('s', i), ear)] = {k: -v for k, v in g.items()}
    # q_i flows from loop vertex i-1 into loop vertex i: l + gluons 1..i-1
    flow = {}
    acc = dict(l)
    for i in range(1, n + 1):
        flow[i] = dict(acc)
        a = 2 * i - 1
        acc = vec_add(acc, {('p', a): 1, ('p', a + 1): 1})
    for i in range(1, n + 1):
        loop_i = 2 * (i - 1) + 1
        loop_prev = 2 * ((i - 2) % n) + 1
        into[(('q', i), loop_i)] = flow[i]
        into[(('q', i), loop_prev)] = {k: -v for k, v in flow[i].items()}
    M = Momenta(R, into, list(range(1, 2 * n + 1)))
    zero = {M.canon({})}
    for k in range(1, 2 * n + 1):
        zero.add(M.canon({('p', k): 1}))
    for i in range(1, n + 1):
        a = 2 * i - 1
        zero.add(M.canon({('p', a): 1, ('p', a + 1): 1}))
        zero.add(M.canon(flow[i]))
    spokes = [('q', i) for i in range(1, n + 1)]
    return R, M, zero, spokes


def name(c):
    if not c:
        return '0'
    terms = []
    for k, x in c:
        lab = 'l' if k == ('l',) else f'p{k[1]}'
        terms.append(('+' if x > 0 else '-') + (str(abs(x)) if abs(x) != 1 else '') + lab)
    return 'X[' + ''.join(terms).lstrip('+') + ']'


def summarize(ls):
    rows = []
    for opens, poly in ls.items():
        c0 = sum(v for s, v in poly.items() if len(s) == 0)
        c1 = sum(v for s, v in poly.items() if len(s) == 1)
        if c0 == 0 and c1 == 0:
            continue
        rows.append((opens, c0, c1))
    return rows


def run_sides(sides, delta_value='-D'):
    R, M, zero, spokes = annulus(sides)
    ls, nconf = cl.leading_singularity(R, closed=[('Delta', spokes)],
                                      namer=make_namer(M, zero))
    return summarize(ls), nconf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tree-check', type=int, default=0)
    ap.add_argument('--sides', default='')
    ap.add_argument('--all', type=int, default=0)
    args = ap.parse_args()

    for n in range(3, args.tree_check + 1):
        agree = total = 0
        for T in cc.scaffolded_fatgraphs(n):
            R, M, zero = tree_momenta(n, T)
            ls, _ = cl.leading_singularity(R, namer=make_namer(M, zero))
            mine = Counter()
            for opens, poly in ls.items():
                if poly[()]:
                    mine[opens] += poly[()]
            # eq. (13) with X_{a,b} renamed by momentum p_a + ... + p_{b-1}
            ref = Counter()
            for mono, c in cc.curve_summary(2 * n, T)['poly'].items():
                if c:
                    key = tuple(sorted(M.canon({('p', k): 1 for k in range(a, b)})
                                       for a, b in mono))
                    ref[key] += c
            mine = {k: v for k, v in mine.items() if v}
            ref = {k: v for k, v in ref.items() if v}
            agree += (mine == ref)
            total += 1
        print(f'tree n={n}: momentum-named walker == eq. (13) on {agree}/{total} graphs')

    todo = []
    if args.sides:
        todo.append(args.sides)
    for n in range(2, args.all + 1):
        for sides in itertools.product('oi', repeat=n):
            if 'i' in sides and 'o' in sides and sides[0] == 'o':
                todo.append(''.join(sides))
    for sides in todo:
        rows, nconf = run_sides(sides)
        closed = [(o, c0, c1) for o, c0, c1 in rows if c1]
        print(f'--- sides {sides}: {nconf} configurations, {len(rows)} monomials, '
              f'{len(closed)} carry the closed curve')
        for opens, c0, c1 in closed:
            # coefficient c0 + c1 * Delta with Delta = -D
            print(f'   ({c0}{-c1:+d}D) * ' + ' '.join(name(o) for o in opens))


if __name__ == '__main__':
    main()
