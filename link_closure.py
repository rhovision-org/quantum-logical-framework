#!/usr/bin/env python3
"""
link_closure.py -- exact companion to lean/QLF_LinkClosure.lean (issue #303 section 3.2).

A history is a list of signed axis steps on the torus S = (Z_L)^d with d axes.  Its current J
counts each link traversal with its sign.  The link action of QLF_LinkAction,

    S[a] = 1/4 sum_x sum_i sum_j F_ij(x)^2 - sum_x sum_i J_i(x) a_i(x),

is stationary under every single-link variation iff curl F = J (`stationary_iff_ampere`).

Lean proves the forward direction: if a stationary configuration exists, the history is
count-balanced on every axis and returns (`stationary_forces_count_balance`,
`stationary_forces_return`).  This script tests the converse EXACTLY (rational arithmetic, no
floats): curl curl is a symmetric integer operator M on link fields, so curl F = J is solvable iff
J is orthogonal to the null space of M.  It enumerates every history up to a length bound and
reports, for each, whether a stationary configuration exists, against

    count-balanced on every axis      (the Lean necessary condition, ZFA's count condition)
    returns to its start on the torus (weaker: allows winding around the torus)

The prediction (finite Hodge decomposition) is: solvable  <=>  count-balanced.  Winding histories
return on the torus but are not count-balanced, so they separate the two conditions.

Usage: python3 link_closure.py [L] [d] [max_len]     (default 3 2 6)
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction


def build(L: int, d: int):
    sites = list(itertools.product(range(L), repeat=d))
    idx = {s: k for k, s in enumerate(sites)}

    def add(x, i, s):
        y = list(x)
        y[i] = (y[i] + s) % L
        return tuple(y)

    links = [(i, x) for i in range(d) for x in sites]
    lidx = {l: k for k, l in enumerate(links)}

    def F(a, i, j, x):  # a: dict link -> value
        return a.get((i, x), 0) + a.get((j, add(x, i, 1)), 0) - a.get((i, add(x, j, 1)), 0) - a.get((j, x), 0)

    def ampere(a, k, y):
        return sum(F(a, k, j, y) - F(a, k, j, add(y, j, -1)) for j in range(d))

    n = len(links)
    M = [[0] * n for _ in range(n)]
    for c, (l, z) in enumerate(links):
        a = {(l, z): 1}
        for r, (k, y) in enumerate(links):
            M[r][c] = ampere(a, k, y)
    assert all(M[r][c] == M[c][r] for r in range(n) for c in range(n)), "curl curl not symmetric"
    return sites, links, lidx, M, add


def null_space(M):
    n = len(M)
    A = [[Fraction(v) for v in row] for row in M]
    piv, r = [], 0
    for c in range(n):
        p = next((k for k in range(r, n) if A[k][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [v * inv for v in A[r]]
        for k in range(n):
            if k != r and A[k][c] != 0:
                f = A[k][c]
                A[k] = [vk - f * vr for vk, vr in zip(A[k], A[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * n
        v[f] = Fraction(1)
        for row, c in enumerate(piv):
            v[c] = -A[row][f]
        basis.append(v)
    return basis


def main() -> None:
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    d = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    max_len = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    sites, links, lidx, M, add = build(L, d)
    N = null_space(M)
    print(f"torus (Z_{L})^{d}: {len(sites)} sites, {len(links)} links, null space of curl curl has dim {len(N)}")
    print(f"  (expected {len(sites) - 1 + d}: gradients {len(sites) - 1} + constant fields {d})")

    steps = [(i, s) for i in range(d) for s in (1, -1)]
    start = tuple([0] * d)
    tally = {}
    for length in range(1, max_len + 1):
        for w in itertools.product(steps, repeat=length):
            J = [0] * len(links)
            x = start
            net = [0] * d
            for i, s in w:
                if s == 1:
                    J[lidx[(i, x)]] += 1
                    x = add(x, i, 1)
                else:
                    x = add(x, i, -1)
                    J[lidx[(i, x)]] -= 1
                net[i] += s
            solvable = all(sum(v[k] * J[k] for k in range(len(J))) == 0 for v in N)
            balanced = all(c == 0 for c in net)
            returns = x == start
            key = (balanced, returns, solvable)
            tally[key] = tally.get(key, 0) + 1
    print(f"\nall histories of length 1..{max_len} from the origin:")
    print(f"{'count-balanced':>15} {'returns':>8} {'stationary exists':>18} {'histories':>10}")
    for (b, r, s), c in sorted(tally.items(), reverse=True):
        print(f"{str(b):>15} {str(r):>8} {str(s):>18} {c:>10}")
    agree = all(b == s for (b, r, s) in tally)
    forward = all(b for (b, r, s) in tally if s)
    print(f"\nLean forward direction (stationary => balanced) holds on every history: {forward}")
    print(f"converse (balanced => stationary) holds on every history: {agree}")
    assert forward
    if not agree:
        raise SystemExit("converse FAILS on this torus")


if __name__ == "__main__":
    main()
