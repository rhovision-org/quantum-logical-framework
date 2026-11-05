#!/usr/bin/env python3
"""Curve covers vs closure covers on small fatgraphs (issue #207, target G3).

Part of the Quantum Logical Framework (QLF). Write-up and pre-registration:
Curve_Covers_QLF.md.

Two sides, computed independently.

CURVE SIDE (Carrôlo & Figueiredo, arXiv:2512.17019, eqs. 12-13). The n-gluon
tree leading singularity on the scaffolded 2n-gon with triangulation T is the
coefficient of prod_{P in T} y_P in

    prod_C ( 1 - X_C * y^{core(C)} * (1 - E_a(C)) * (1 - E_b(C)) ),

where C runs over the chords (a,b) not in T, core(C) is the set of chords of T
that C crosses, and E_a = y_{p1} + y_{p1} y_{p2} + ... runs over the
extension chords at end a (the extra chords the laminated curve crosses),
ordered from the core outward. A "configuration" is one term of the
expansion that covers every chord of T exactly once: a set of curves, each
with a chosen extension prefix length at each end. Its sign is
(-1)^{#curves} (-1)^{#extended ends}.

QLF SIDE (pre-registered before the curve side was run beyond n = 3). The
fatgraph is the dual tree of T. A strand is a path of fatgraph edges; at each
interior vertex it turns L or R. Candidates:
  Q0  partitions of the edges into strands (no labels);
  Q1  partitions into ZFA-balanced strands (#L = #R on every strand);
  Q2  sum over partitions of 2^{#strands} (each strand a ket or a bra).

Usage:
    python3 curve_cover_census.py --qlf 6        # QLF side only, n = 3..6
    python3 curve_cover_census.py --curves 6     # curve side, n = 3..6
    python3 curve_cover_census.py --check3       # paper's 3-point example
    python3 curve_cover_census.py --json out.json --curves 6 --qlf 6
"""
from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter, defaultdict
from functools import lru_cache


# ---------------------------------------------------------------------------
# Fatgraphs: scaffolded triangulations of the 2n-gon
# ---------------------------------------------------------------------------

def norm(c, d):
    return (c, d) if c < d else (d, c)


def triangulations(verts):
    """All triangulations of the convex polygon with the given cyclic vertex list,
    as frozensets of diagonals."""
    verts = tuple(verts)

    @lru_cache(maxsize=None)
    def tri(i, j):
        # triangulations of the sub-polygon verts[i..j]; returns list of frozensets
        if j - i < 2:
            return [frozenset()]
        out = []
        for k in range(i + 1, j):
            for L in tri(i, k):
                for R in tri(k, j):
                    s = set(L) | set(R)
                    if k - i > 1:
                        s.add(norm(verts[i], verts[k]))
                    if j - k > 1:
                        s.add(norm(verts[k], verts[j]))
                    out.append(frozenset(s))
        return out

    return tri(0, len(verts) - 1)


def scaffolded_fatgraphs(n):
    """Triangulations T of the 2n-gon (vertices 1..2n) containing every
    scaffolding chord (2j-1, 2j+1). Returns a list of sorted chord tuples."""
    N = 2 * n
    scaff = {norm(2 * j - 1, (2 * j + 1 - 1) % N + 1) for j in range(1, n + 1)}
    odd = list(range(1, N, 2))
    out = []
    for inner in triangulations(odd):
        out.append(tuple(sorted(scaff | set(inner))))
    return out


def triangles(N, T):
    """Triangles of the triangulation (polygon sides + chords T)."""
    edges = set(T) | {norm(i, i % N + 1) for i in range(1, N + 1)}
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    tris = set()
    for a, b in edges:
        for c in adj[a] & adj[b]:
            tris.add(tuple(sorted((a, b, c))))
    assert len(tris) == N - 2, (N, T, tris)
    return sorted(tris)


def dual_tree(N, T):
    """Fatgraph = dual tree. Vertices = triangles; edges = chords of T.
    Returns (tris, ends) with ends[chord] = (tri_index, tri_index)."""
    tris = triangles(N, T)
    ends = defaultdict(list)
    for k, (a, b, c) in enumerate(tris):
        for s in (norm(a, b), norm(b, c), norm(a, c)):
            if s in T:
                ends[s].append(k)
    for s in T:
        assert len(ends[s]) == 2
    return tris, {s: tuple(v) for s, v in ends.items()}


def turn(tri, s_in, s_out):
    """Handedness of passing through triangle tri (vertices a<b<c, which are in
    counter-clockwise order on the polygon) from side s_in to side s_out.
    'L' if s_out is the next side counter-clockwise after s_in, else 'R'."""
    a, b, c = tri
    sides = [norm(a, b), norm(b, c), norm(c, a)]  # ccw boundary order
    i, j = sides.index(s_in), sides.index(s_out)
    return 'L' if j == (i + 1) % 3 else 'R'


# ---------------------------------------------------------------------------
# QLF side: strand covers of the fatgraph
# ---------------------------------------------------------------------------

def strand_partitions(N, T):
    """All partitions of the chords of T (fatgraph edges) into paths.
    Yields lists of strands; each strand is a tuple of chords in path order."""
    tris, ends = dual_tree(N, T)
    T = list(T)
    inc = defaultdict(list)  # triangle -> incident chords
    for s, (u, v) in ends.items():
        inc[u].append(s)
        inc[v].append(s)

    # Enumerate all paths (as edge sequences) in the tree, up to reversal.
    paths = set()

    def grow(path, tri_at_end):
        paths.add(tuple(path) if path[0] <= path[-1] else tuple(reversed(path)))
        for s in inc[tri_at_end]:
            if s in path:
                continue
            u, v = ends[s]
            nxt = v if u == tri_at_end else u
            grow(path + [s], nxt)

    for s in T:
        u, v = ends[s]
        grow([s], u)
        grow([s], v)
    paths = sorted(paths, key=lambda p: (len(p), p))

    by_edge = defaultdict(list)
    for p in paths:
        for s in p:
            by_edge[s].append(p)

    order = sorted(T)

    def rec(covered, chosen):
        free = [s for s in order if s not in covered]
        if not free:
            yield list(chosen)
            return
        s0 = free[0]
        for p in by_edge[s0]:
            if covered.isdisjoint(p):
                chosen.append(p)
                yield from rec(covered | set(p), chosen)
                chosen.pop()

    yield from rec(frozenset(), [])


def turn_word(N, T, strand):
    tris, ends = dual_tree(N, T)
    w = []
    for s, t in zip(strand, strand[1:]):
        common = set(ends[s]) & set(ends[t])
        (k,) = common
        w.append(turn(tris[k], s, t))
    return ''.join(w)


def qlf_counts(N, T):
    q0 = q1 = q2 = 0
    for part in strand_partitions(N, T):
        q0 += 1
        q2 += 2 ** len(part)
        if all(turn_word(N, T, p).count('L') == turn_word(N, T, p).count('R') for p in part):
            q1 += 1
    return {'Q0': q0, 'Q1': q1, 'Q2': q2}


def handedness_splits(w, mirror=False):
    """Ways to read a strand with turn word w as core + extensions under the
    handedness rule: an extended end is one opposite-handed turn at the core
    junction followed by a constant-handed run. Returns (ka, kb) pairs."""
    A, B = ('L', 'R') if mirror else ('R', 'L')
    m = len(w) + 1
    out = []
    for ka in range(m):
        for kb in range(m - ka):
            if ka > 0 and w[:ka] != A * (ka - 1) + B:
                continue
            if kb > 0 and w[m - 1 - kb:] != A + B * (kb - 1):
                continue
            out.append((ka, kb))
    return out


def core_curve(N, T, core):
    """The unique curve whose core is the given fatgraph path (tuple of chords):
    join the far vertices of the two end triangles."""
    tris, ends = dual_tree(N, T)

    def far_vertex(e, nxt):
        cands = [k for k in ends[e] if nxt is None or nxt not in _sides(tris[k])]
        return cands

    if len(core) == 1:
        (u, v) = ends[core[0]]
        a = (set(tris[u]) - set(core[0])).pop()
        b = (set(tris[v]) - set(core[0])).pop()
    else:
        (ku,) = [k for k in ends[core[0]] if core[1] not in _sides(tris[k])]
        (kv,) = [k for k in ends[core[-1]] if core[-2] not in _sides(tris[k])]
        a = (set(tris[ku]) - set(core[0])).pop()
        b = (set(tris[kv]) - set(core[-1])).pop()
    return norm(a, b)


def _sides(tri):
    a, b, c = tri
    return {norm(a, b), norm(b, c), norm(a, c)}


def handedness_polynomial(N, T, mirror=False):
    """The leading-singularity polynomial rebuilt from strand covers and turn
    words alone (QLF side, candidate Q3). Returns (Counter poly, #configs)."""
    poly = Counter()
    nconf = 0
    for part in strand_partitions(N, T):
        per_strand = []
        for s in part:
            w = turn_word(N, T, s)
            opts = []
            for ka, kb in handedness_splits(w, mirror):
                core = s[ka:len(s) - kb]
                sign = (-1) ** ((ka > 0) + (kb > 0))
                opts.append((core_curve(N, T, core), sign))
            per_strand.append(opts)
        for combo in itertools.product(*per_strand):
            curves = [c for c, _ in combo]
            if len(set(curves)) < len(curves):
                continue  # a curve appears once in the product over C
            sign = (-1) ** len(curves)
            for _, sg in combo:
                sign *= sg
            poly[frozenset(curves)] += sign
            nconf += 1
    return poly, nconf


# ---------------------------------------------------------------------------
# Curve side: Carrôlo-Figueiredo eq. (13) expanded exactly
# ---------------------------------------------------------------------------

def curve_data(N, T):
    """For every chord C=(a,b) not in T (and not a polygon side), return
    (core set, ext_a list, ext_b list), extensions ordered from the core out."""
    Tset = set(T)
    data = {}
    for a in range(1, N + 1):
        for b in range(a + 2, N + 1):
            if (a, b) == (1, N) or (a, b) in Tset:
                continue
            I = set(range(a + 1, b + 1))           # laminated interval
            inside = set(range(a + 1, b))          # strictly inside
            outside = set(range(1, N + 1)) - set(range(a, b + 1))
            core, ext_a, ext_b = set(), [], []
            for (c, d) in T:
                if (c in I) == (d in I):
                    continue  # laminated curve does not cross
                if (c in inside and d in outside) or (d in inside and c in outside):
                    core.add((c, d))
                elif a in (c, d):
                    ext_a.append((c, d))
                elif b in (c, d):
                    ext_b.append((c, d))
                else:
                    raise AssertionError((a, b, c, d))
            assert core, (a, b)
            other_a = lambda ch: ch[0] if ch[1] == a else ch[1]
            other_b = lambda ch: ch[0] if ch[1] == b else ch[1]
            # end a: core-adjacent fan chord has the largest partner d in (a,b)
            ext_a.sort(key=lambda ch: -other_a(ch))
            # end b: partner d lies cyclically in (b, a); core-adjacent is the one
            # cyclically closest to a going backwards from a
            ext_b.sort(key=lambda ch: (a - other_b(ch)) % N)
            data[(a, b)] = (frozenset(core), tuple(ext_a), tuple(ext_b))
    return data


def curve_configurations(N, T):
    """All configurations: (frozenset of curves, sign, tuple of (curve, ka, kb))."""
    data = curve_data(N, T)
    options = []  # (curve, ka, kb, edges)
    for C, (core, ea, eb) in data.items():
        for ka in range(len(ea) + 1):
            for kb in range(len(eb) + 1):
                edges = set(core) | set(ea[:ka]) | set(eb[:kb])
                assert len(edges) == len(core) + ka + kb
                options.append((C, ka, kb, frozenset(edges)))
    by_edge = defaultdict(list)
    for o in options:
        for s in o[3]:
            by_edge[s].append(o)
    order = sorted(T)
    out = []

    def rec(covered, used, chosen):
        free = [s for s in order if s not in covered]
        if not free:
            n_ext = sum((ka > 0) + (kb > 0) for _, ka, kb, _ in chosen)
            sign = (-1) ** (len(chosen) + n_ext)
            out.append((frozenset(c for c, *_ in chosen), sign,
                        tuple((c, ka, kb) for c, ka, kb, _ in chosen)))
            return
        s0 = free[0]
        for o in by_edge[s0]:
            if o[0] in used or not covered.isdisjoint(o[3]):
                continue
            chosen.append(o)
            rec(covered | o[3], used | {o[0]}, chosen)
            chosen.pop()

    rec(frozenset(), frozenset(), [])
    return out


def curve_summary(N, T):
    confs = curve_configurations(N, T)
    poly = Counter()
    nconf = Counter()
    for mono, sign, _ in confs:
        poly[mono] += sign
        nconf[mono] += 1
    degs = [len(m) for m in poly]
    dmin = min(degs)
    surviving = {m: c for m, c in poly.items() if c != 0}
    ym = {m: c for m, c in surviving.items() if len(m) == dmin}
    return {
        'configs': len(confs),
        'configs_YM': sum(1 for m, _, _ in confs if len(m) == dmin),
        'monomials_generated': len(poly),
        'monomials_surviving': len(surviving),
        'monomials_surviving_YM': len(ym),
        'degree_YM': dmin,
        'coef_values': sorted(Counter(surviving.values()).items()),
        'configs_per_monomial': sorted(Counter(nconf.values()).items()),
        'max_abs_imbalance': max(abs(c) for c in poly.values()),
        'path_partitions_realized': len({frozenset(
            frozenset(_edges_of(N, T, c, ka, kb)) for c, ka, kb in detail)
            for _, _, detail in confs}),
        'poly': poly,
        'nconf': nconf,
    }


_cd_cache = {}


def _edges_of(N, T, C, ka, kb):
    key = (N, tuple(T))
    if key not in _cd_cache:
        _cd_cache[key] = curve_data(N, T)
    core, ea, eb = _cd_cache[key][C]
    return set(core) | set(ea[:ka]) | set(eb[:kb])


def fmt_poly(poly, deg=None):
    terms = []
    for m, c in sorted(poly.items(), key=lambda kv: (len(kv[0]), sorted(kv[0]))):
        if c == 0 or (deg is not None and len(m) != deg):
            continue
        name = '*'.join(f'X{a},{b}' for a, b in sorted(m))
        terms.append(f"{'+' if c > 0 else '-'}{abs(c) if abs(c) != 1 else ''}{name}")
    return ' '.join(terms)


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--qlf', type=int, default=0, help='QLF side for n = 3..QLF')
    ap.add_argument('--curves', type=int, default=0, help='curve side for n = 3..CURVES')
    ap.add_argument('--check3', action='store_true', help="paper's 3-point LS")
    ap.add_argument('--json', help='write results to this file')
    args = ap.parse_args()
    results = {}

    if args.check3:
        N, (T,) = 6, scaffolded_fatgraphs(3)
        s = curve_summary(N, T)
        print('3-point, degree-2 (YM) part:', fmt_poly(s['poly'], 2))
        print('3-point, degree-3 part:     ', fmt_poly(s['poly'], 3))
        paper = Counter({frozenset({(1, 4), (2, 6)}): 1, frozenset({(3, 6), (2, 4)}): 1,
                         frozenset({(2, 5), (4, 6)}): 1, frozenset({(2, 5), (3, 6)}): -1,
                         frozenset({(1, 4), (3, 6)}): -1, frozenset({(1, 4), (2, 5)}): -1})
        mine = Counter({m: c for m, c in s['poly'].items() if len(m) == 2 and c})
        print('matches paper eq. (16):', mine == paper)

    for n in range(3, max(args.qlf, args.curves) + 1):
        N = 2 * n
        for gi, T in enumerate(scaffolded_fatgraphs(n)):
            key = f'n={n} graph={gi} T={list(T)}'
            row = results.setdefault(key, {})
            if n <= args.qlf:
                row.update(qlf_counts(N, T))
            if n <= args.curves:
                s = curve_summary(N, T)
                row.update({k: v for k, v in s.items() if k not in ('poly', 'nconf')})
            print(key, {k: v for k, v in row.items()})

    if args.json:
        with open(args.json, 'w') as f:
            json.dump(results, f, indent=1, default=str)


if __name__ == '__main__':
    main()
