#!/usr/bin/env python3
"""One-loop curve covers on the punctured disk (issue #207, target G4b).

Part of the Quantum Logical Framework (QLF). Write-up: Curve_Covers_QLF.md §7.

Curves are walks on the fatgraph read by handedness: a curve enters from an
external leg, turns L or R at each vertex, and leaves by another leg, or spirals
into the puncture (L forever). Its core and extensions are read from the turn
word alone (the dictionary that Curve_Covers_QLF.md §5 verified on every tree
fatgraph through 7 gluons):

    walk a -> b with turns t_0 .. t_m over internal edges e_1 .. e_m
    extension at a = e_1 .. e_i   where t_0 .. t_{i-1} = R and t_i = L
    extension at b = e_{j+1} ..   where t_j is the last R
    core           = everything between

The leading singularity is the coefficient of prod_P y_P in

    prod_C (1 - X_C y^core (1 - E_a)(1 - E_b)) * (1 - Delta * prod_spokes y),

with Delta the closed curve around the puncture (paper eq. 14), Delta = 1 - D
for the planar one-loop case.

Usage:
    python3 curve_cover_loop.py --tree-check 6    # walker vs eq. (13) on trees
    python3 curve_cover_loop.py --ngon 5          # planar one-loop n-gons (n = 1..5)
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction

import curve_cover_census as cc


class Ribbon:
    """A triangulated surface as its dual cubic ribbon graph.

    tris: list of 3-tuples of side labels in counter-clockwise order.
    legs: dict side label -> marked point k (the boundary side (k, k+1)).
    Every non-leg side appears in exactly two triangles."""

    def __init__(self, tris, legs):
        self.tris = tris
        self.legs = legs
        self.where = defaultdict(list)
        for t, sides in enumerate(tris):
            for s in sides:
                self.where[s].append(t)
        self.internal = sorted(s for s, ts in self.where.items() if s not in legs)
        for s in self.internal:
            assert len(self.where[s]) == 2, s

    def step(self, t, s_in, hand):
        sides = self.tris[t]
        i = sides.index(s_in)
        return sides[(i + 1) % 3] if hand == 'L' else sides[(i - 1) % 3]

    def other(self, s, t):
        a, b = self.where[s]
        return b if a == t else a


def walks_from_leg(R, leg, max_len, spiral_ok):
    """Enumerate walks from a leg. Yields ('open', edges, turns, end_leg) and,
    when spiral_ok(t, s_in) says L-forever circulates the puncture,
    ('spiral', edges, turns, (t, s_in))."""
    (t0,) = R.where[leg]

    def rec(t, s_in, edges, turns, used):
        if len(edges) > max_len:
            return
        if spiral_ok is not None and edges and spiral_ok(t, s_in):
            yield ('spiral', tuple(edges), tuple(turns), (t, s_in))
        for hand in 'LR':
            s_out = R.step(t, s_in, hand)
            if s_out in R.legs:
                yield ('open', tuple(edges), tuple(turns) + (hand,), s_out)
                continue
            if used[s_out] >= 2:
                continue
            used[s_out] += 1
            yield from rec(R.other(s_out, t), s_out, edges + [s_out], turns + [hand], used)
            used[s_out] -= 1

    yield from rec(t0, leg, [], [], Counter())


def spiral_tail(R, t, s_in, k):
    """First k edges of the L-forever continuation from state (t, s_in)."""
    out = []
    for _ in range(k):
        s_out = R.step(t, s_in, 'L')
        out.append(s_out)
        t, s_in = R.other(s_out, t), s_out
    return out


def read_curve(edges, turns, tail=None):
    """Core and extensions from the turn word. turns has len(edges)+1 entries for
    an open walk (t_0 .. t_m) and len(edges) for a spiral prefix (t_0 .. t_{m-1}),
    the spiral itself contributing L forever with the edges in `tail`."""
    if tail is not None:
        edges = list(edges) + list(tail)
        turns = list(turns) + ['L'] * len(tail)
    m = len(edges)
    i = 0
    while i < len(turns) and turns[i] == 'R':
        i += 1
    js = [j for j, h in enumerate(turns) if h == 'R']
    j = js[-1] if js else -1
    if j < i:  # no core
        return None
    ext_a = list(reversed(edges[:i]))
    core = edges[i:j]
    ext_b = edges[j:]
    return core, ext_a, ext_b


def linear_factor(core, ext_a, ext_b):
    """Options (edge multiset, sign, n_ext) of y^core (1-E_a)(1-E_b), keeping only
    terms linear in every y (no repeated edge)."""
    out = []
    if len(set(core)) < len(core):
        return out

    def prefixes(ext):
        res = [((), 0)]
        for k in range(1, len(ext) + 1):
            pre = tuple(ext[:k])
            if len(set(pre)) < k:
                break
            res.append((pre, 1))
        return res

    for pa, ea in prefixes(ext_a):
        for pb, eb in prefixes(ext_b):
            es = list(core) + list(pa) + list(pb)
            if len(set(es)) == len(es):
                out.append((frozenset(es), (-1) ** (ea + eb), ea + eb))
    return out


def curves(R, spiral_ok=None, puncture_label='p', zero=lambda a, b: False):
    """All curves with non-zero X: label -> list of linear options.
    zero(a, b) says the kinematic variable of a curve from a to b vanishes
    (b may be the puncture label). A label is (kinematic name, walk key): curves
    differing only by winding share a kinematic name, as in the paper."""
    max_len = 2 * len(R.internal) + 2
    K = 3 * len(R.internal) + 3
    seen = {}
    for leg, k in R.legs.items():
        for kind, edges, turns, end in walks_from_leg(R, leg, max_len, spiral_ok):
            if kind == 'open':
                k2 = R.legs[end]
                if k2 == k or zero(k, k2):
                    continue  # tadpole X_{k,k}, massless or on-shell: X = 0
                key = min((k, edges, k2), (k2, tuple(reversed(edges)), k))
                rc = read_curve(edges, turns)
                if rc is None:
                    continue
                if key in seen:
                    continue
                label = ((min(k, k2), max(k, k2)), key)
                seen[key] = (label, rc)
            else:
                if zero(k, puncture_label):
                    continue
                t, s_in = end
                tail = spiral_tail(R, t, s_in, K)
                full = (tuple(edges) + tuple(tail))[:K]
                key = ('spiral', leg, full)
                rc = read_curve(edges, turns, tail)
                if rc is None:
                    continue
                if key in seen:
                    continue
                seen[key] = (((k, puncture_label), key), rc)
    out = {}
    for key, (label, (core, ea, eb)) in seen.items():
        opts = linear_factor(core, ea, eb)
        if opts:
            out[label] = opts
    return out


def leading_singularity(R, closed=None, spiral_ok=None, zero=lambda a, b: False):
    """Coefficient of prod y over all internal edges. closed: list of
    (name, edge set) closed curves, each weighted by its own symbol.
    Returns Counter: (frozenset of curve labels) -> polynomial in symbols,
    represented as Counter of (tuple of symbols) -> int."""
    C = curves(R, spiral_ok, zero=zero)
    options = []
    for label, opts in C.items():
        for es, sg, ne in opts:
            options.append((label, es, sg))
    for name, es in (closed or []):
        options.append((('closed', name), frozenset(es), 1))
    by_edge = defaultdict(list)
    for o in options:
        for s in o[1]:
            by_edge[s].append(o)
    order = list(R.internal)
    result = defaultdict(Counter)
    nconf = [0]

    def rec(covered, used, chosen):
        free = [s for s in order if s not in covered]
        if not free:
            sign = (-1) ** len(chosen)
            for _, _, sg in chosen:
                sign *= sg
            opens = tuple(sorted(lab[0] for lab, _, _ in chosen if lab[0] != 'closed'))
            syms = tuple(sorted(lab[1] for lab, _, _ in chosen if lab[0] == 'closed'))
            result[opens][syms] += sign
            nconf[0] += 1
            return
        s0 = free[0]
        for o in by_edge[s0]:
            if o[0] in used or not covered.isdisjoint(o[1]):
                continue
            chosen.append(o)
            rec(covered | o[1], used | {o[0]}, chosen)
            chosen.pop()

    rec(frozenset(), frozenset(), [])
    return result, nconf[0]


# ---------------------------------------------------------------------------
# Surfaces
# ---------------------------------------------------------------------------

def tree_ribbon(n, T):
    N = 2 * n
    tris = []
    for (a, b, c) in cc.triangles(N, T):
        sides = []
        for (u, v) in ((a, b), (b, c), (c, a)):
            if {u, v} == {1, N}:
                sides.append(('leg', N))
            elif abs(u - v) == 1:
                sides.append(('leg', min(u, v)))
            else:
                sides.append(('ch',) + cc.norm(u, v))
        tris.append(tuple(sides))
    legs = {('leg', k): k for k in range(1, N + 1)}
    return Ribbon(tris, legs)


def ngon_ribbon(n):
    """Planar one-loop n-gon, scaffolded: marked points 1..2n, puncture p.
    Ear E_i = (2i-1, 2i, 2i+1), loop triangle V_i = (2i-1, 2i+1, p)."""
    N = 2 * n
    nxt = lambda k: (k % N) + 1
    tris = []
    for i in range(1, n + 1):
        a = 2 * i - 1
        tris.append((('leg', a), ('leg', a + 1), ('s', i)))                 # ear
        tris.append((('s', i), ('q', i % n + 1), ('q', i)))                 # loop
    legs = {('leg', k): k for k in range(1, N + 1)}
    R = Ribbon(tris, legs)
    spokes = [('q', i) for i in range(1, n + 1)]

    def spiral_ok(t, s_in):
        # entered a loop triangle through a spoke such that L goes to the next spoke
        sides = R.tris[t]
        return s_in[0] == 'q' and R.step(t, s_in, 'L')[0] == 'q'

    return R, spokes, spiral_ok


def ngon_zero(n):
    """Vanishing kinematics for the scaffolded n-gon: tadpoles, massless
    neighbours, on-shell scaffolds (2i-1, 2i+1), and loop propagators (odd, p)."""
    N = 2 * n

    def zero(a, b):
        if b == 'p':
            return a % 2 == 1
        a, b = min(a, b), max(a, b)
        if b - a == 1 or (a, b) == (1, N):
            return True
        if a % 2 == 1 and b % 2 == 1 and (b - a == 2 or (a, b) == (1, N - 1)):
            return True
        if n == 2 and a % 2 == 1 and b % 2 == 1:
            return True
        return False

    return zero


def label_name(lab):
    a, b = lab
    return f'X{a},{b}'


def fmt(ls, D_sub=True):
    out = []
    for opens, poly in sorted(ls.items(), key=lambda kv: (len(kv[0]), sorted(map(str, kv[0])))):
        # substitute Delta = 1 - D: poly is Counter over tuples of 'Delta'
        c0 = sum(v for s, v in poly.items() if len(s) == 0)
        c1 = sum(v for s, v in poly.items() if len(s) == 1)
        assert all(len(s) <= 1 for s in poly)
        a, b = c0 + c1, -c1  # c0 + c1 (1 - D)
        if a == 0 and b == 0:
            continue
        coef = f'({a}{b:+d}D)' if b else f'{a}'
        out.append(coef + '*' + '*'.join(sorted(label_name(l) for l in opens)))
    return '\n'.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tree-check', type=int, default=0)
    ap.add_argument('--ngon', type=int, default=0)
    args = ap.parse_args()

    for n in range(3, args.tree_check + 1):
        agree = total = 0
        for T in cc.scaffolded_fatgraphs(n):
            R = tree_ribbon(n, T)
            ls, nconf = leading_singularity(R)
            mine = Counter()
            for opens, poly in ls.items():
                key = frozenset(opens)
                mine[key] += poly[()]
            ref = cc.curve_summary(2 * n, T)['poly']
            agree += ({k: v for k, v in mine.items() if v} == {k: v for k, v in ref.items() if v})
            total += 1
        print(f'tree n={n}: turn-word walker == eq. (13) on {agree}/{total} graphs')

    for n in range(1, args.ngon + 1):
        R, spokes, ok = ngon_ribbon(n)
        ls, nconf = leading_singularity(R, closed=[('Delta', spokes)], spiral_ok=ok,
                                        zero=ngon_zero(n))
        print(f'--- planar one-loop {n}-gon: {nconf} configurations')
        print(fmt(ls))


if __name__ == '__main__':
    main()
