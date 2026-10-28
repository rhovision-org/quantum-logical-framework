#!/usr/bin/env python3
"""Hofstadter's butterfly from closure counts — the pre-registered test of
Hofstadter_Butterfly_QLF.md §2 (H1-H5).

A closure on one spatial plane (twists > < ^ v) is a closed walk on Z^2. With a phase
zeta_q^p on every plaquette, a closed walk carries zeta_q^(p*A), A its signed area. The
flux census

    M_L(p/q) = sum over closures of length L from the origin of zeta_q^(p*A)

is a finite exact count: c_k = #closures with A = k (mod q). This script computes it by
dynamic programming over (x, y, A mod q), with integers only, and compares it with

  H1  the Harper (Bloch) matrix moments (1/q)<Tr H(k)^L>          -- a code check
  H2  QLF's proved fold-sign connection, closure_walk.edge_sign    -- tests QLF_EdgeSign
  H3  QLF's colour transport through colour_flux.cocycle()         -- tests QLF_ColourFlux
  H4  integrality of M_L by Galois conjugates                      -- bookkeeping (Niven)
  H5  the butterfly rendered from the census's transfer operator   -- rendering check

Usage:  python3 hofstadter_closure.py [--svg hofstadter_butterfly.svg] [--qmax 30]
"""
import argparse
import cmath
import math
import os
import sys
from collections import defaultdict
from fractions import Fraction
from math import gcd

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import closure_walk   # noqa: E402  (QLF fold-sign connection)
import colour_flux    # noqa: E402  (QLF colour transport, explicit Weyl matrices)

# One spatial plane: '>' '<' on x, '^' 'v' on y.
STEPS = {'>': (1, 0), '<': (-1, 0), '^': (0, 1), 'v': (0, -1)}


# ---------------------------------------------------------------- the census
def area_census(L: int, q: int) -> list[int]:
    """c_k = number of closed walks of length L from the origin with signed area = k (mod q).
    Area in the Landau gauge: an x-step dx at height y adds -y*dx."""
    states = {(0, 0, 0): 1}
    for _ in range(L):
        nxt = defaultdict(int)
        for (x, y, a), n in states.items():
            for dx, dy in STEPS.values():
                nxt[(x + dx, y + dy, (a - y * dx) % q)] += n
        states = nxt
    c = [0] * q
    for (x, y, a), n in states.items():
        if x == 0 and y == 0:
            c[a] += n
    return c


def census_value(c: list[int], p: int, q: int) -> float:
    """sum_k c_k zeta_q^(p k), which is real because a walk and its reverse have opposite areas."""
    return sum(n * math.cos(2 * math.pi * p * k / q) for k, n in enumerate(c))


# ---------------------------------------------------------------- H1: Harper oracle
def harper(p: int, q: int, kx: float, ky: float) -> np.ndarray:
    """Bloch matrix of the square-lattice Hofstadter model, Landau gauge, magnetic cell q in y."""
    phi = p / q
    H = np.zeros((q, q), dtype=complex)
    for m in range(q):
        H[m, m] += 2 * math.cos(kx - 2 * math.pi * phi * m)
        H[m, (m + 1) % q] += cmath.exp(1j * q * ky) if m == q - 1 else 1
        H[(m + 1) % q, m] += cmath.exp(-1j * q * ky) if m == q - 1 else 1
    if q == 1:
        H = np.array([[2 * math.cos(kx) + 2 * math.cos(ky)]], dtype=complex)
    return H


def harper_moment(p: int, q: int, L: int) -> float:
    n = L + 2                       # a trig polynomial of degree <= L is averaged exactly
    tot = 0.0
    for i in range(n):
        for j in range(n):
            kx = 2 * math.pi * i / n
            ky = 2 * math.pi * j / (n * q)
            H = harper(p, q, kx, ky)
            tot += np.trace(np.linalg.matrix_power(H, L)).real
    return tot / (n * n * q)


# ---------------------------------------------------------------- H2: QLF fold sign
# closure_walk axes: '^' = axis 0, '>' = axis 1.
QLF_AX = {'>': (1, 1), '<': (1, -1), '^': (0, 1), 'v': (0, -1)}


def edge_sign_census(L: int) -> int:
    """Sum over closed plane walks of the product of closure_walk.edge_sign along the walk."""
    states = {(0, 0, 1): 1}
    for _ in range(L):
        nxt = defaultdict(int)
        for (x, y, s), n in states.items():
            for a, sg in QLF_AX.values():
                pos = [y, x, 0, 0]          # axis 0 = y ('^'), axis 1 = x ('>')
                e = closure_walk.edge_sign(pos, a, sg)
                dx, dy = (sg, 0) if a == 1 else (0, sg)
                nxt[(x + dx, y + dy, s * e)] += n
        states = nxt
    return sum(n * s for (x, y, s), n in states.items() if x == 0 and y == 0)


# ---------------------------------------------------------------- H3: QLF colour transport
QMAT = {'>': (0, 2, 1, 0), '<': (0, 1, 2, 0), '^': (2, 1, 1, 1), 'v': (1, 2, 2, 2)}   # Lean qMat


def col_vec(t: str) -> tuple:
    a, b, c, d = QMAT[t]
    return (a % 3, c % 3)                   # qMat t applied to (1, 0)


COCYCLE = colour_flux.cocycle()             # D(u) D(v) = omega^c(u,v) D(u+v), from the 3x3 matrices


def colour_census(L: int) -> list[int]:
    """n_k = number of closed plane walks whose product of Weyl displacements is omega^k I."""
    states = {(0, 0, (0, 0), 0): 1}
    for _ in range(L):
        nxt = defaultdict(int)
        for (x, y, v, k), n in states.items():
            for t, (dx, dy) in STEPS.items():
                u = col_vec(t)
                k2 = (k + COCYCLE[(v, u)]) % 3
                v2 = ((v[0] + u[0]) % 3, (v[1] + u[1]) % 3)
                nxt[(x + dx, y + dy, v2, k2)] += n
        states = nxt
    out = [0, 0, 0]
    for (x, y, v, k), n in states.items():
        if x == 0 and y == 0:
            assert v == (0, 0)
            out[k] += n
    return out


# ---------------------------------------------------------------- H4: integrality
COS_RATIONAL = {1: {0: Fraction(1)},
                2: {0: Fraction(1), 1: Fraction(-1)},
                3: {0: Fraction(1), 1: Fraction(-1, 2), 2: Fraction(-1, 2)},
                4: {0: Fraction(1), 1: Fraction(0), 2: Fraction(-1), 3: Fraction(0)},
                6: {0: Fraction(1), 1: Fraction(1, 2), 2: Fraction(-1, 2), 3: Fraction(-1),
                    4: Fraction(-1, 2), 5: Fraction(1, 2)}}


def exact_value(c, p, q) -> Fraction:
    return sum(n * COS_RATIONAL[q][(p * k) % q] for k, n in enumerate(c))


def conjugates(c, q) -> list[float]:
    return [census_value(c, a, q) for a in range(1, q) if gcd(a, q) == 1] or [census_value(c, 0, 1)]


# ---------------------------------------------------------------- H5: butterfly
def bands(p: int, q: int, grid: int = 6) -> list[tuple[float, float]]:
    ks = [(2 * math.pi * i / grid, 2 * math.pi * j / (grid * q)) for i in range(grid) for j in range(grid)]
    ks += [(0.0, 0.0), (math.pi / q, math.pi / q), (math.pi / q, 0.0), (0.0, math.pi / q)]
    ev = np.array([np.linalg.eigvalsh(harper(p, q, kx, ky)) for kx, ky in ks])
    return [(float(ev[:, b].min()), float(ev[:, b].max())) for b in range(q)]


def components(iv, tol=1e-6) -> int:
    iv = sorted(iv)
    n, hi = 1, iv[0][1]
    for lo, h in iv[1:]:
        if lo > hi + tol:
            n += 1
        hi = max(hi, h)
    return n


def write_svg(path: str, qmax: int) -> None:
    W, H, pad = 900, 700, 40
    sx = lambda f: pad + f * (W - 2 * pad)
    sy = lambda e: H - pad - (e + 4) / 8 * (H - 2 * pad)
    lines = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">',
             f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
             f'<text x="{pad}" y="24" font-family="sans-serif" font-size="15" fill="#222">'
             f'Hofstadter butterfly from closure counts, all p/q with q &lt;= {qmax}</text>']
    for q in range(1, qmax + 1):
        for p in range(0, q + 1):
            if gcd(p, q) != 1:
                continue
            col = '#d1495b' if q in (2, 3) else '#2b59c3'
            w = 2.5 if q in (2, 3) else 0.9
            for lo, hi in (bands(p % q, q) if q > 1 else bands(0, 1)):
                x = sx(p / q)
                lines.append(f'<line x1="{x:.1f}" y1="{sy(lo):.1f}" x2="{x:.1f}" y2="{sy(hi):.1f}" '
                             f'stroke="{col}" stroke-width="{w}"/>')
    lines.append(f'<line x1="{pad}" y1="{H-pad}" x2="{W-pad}" y2="{H-pad}" stroke="#555"/>')
    lines.append(f'<text x="{W/2-60}" y="{H-12}" font-family="sans-serif" font-size="13" fill="#222">'
                 f'flux per plaquette p/q (0 to 1)</text>')
    lines.append(f'<text x="{W-pad-330}" y="24" font-family="sans-serif" font-size="13" fill="#d1495b">'
                 f'red: q = 2 (fold sign) and q = 3 (colour)</text>')
    lines.append('</svg>')
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')


# ---------------------------------------------------------------- run
def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--svg', default=None)
    ap.add_argument('--qmax', type=int, default=30)
    args = ap.parse_args(argv)
    ok = True

    print('H1  census vs Harper moments, q <= 8, even L <= 16')
    worst = 0.0
    for q in range(1, 9):
        for L in range(0, 17, 2):
            c = area_census(L, q)
            for p in range(q):
                if gcd(p, q) != 1 and not (q == 1 and p == 0):
                    continue
                m = census_value(c, p, q)
                worst = max(worst, abs(m - harper_moment(p, q, L)) / max(1.0, abs(m)))
    h1 = worst < 1e-9
    print(f'    max relative difference = {worst:.3e}   -> {"PASS" if h1 else "FAIL"}')
    ok &= h1

    print('H2  QLF edge-sign census vs (-1)^(L/2) M_L(1/2), even L <= 20')
    h2 = True
    for L in range(0, 21, 2):
        e = edge_sign_census(L)
        m = exact_value(area_census(L, 2), 1, 2)
        match = e == (-1) ** (L // 2) * m
        h2 &= match
        print(f'    L={L:2d}  edge-sign {e:>14d}   (-1)^(L/2) M_L(1/2) {int((-1) ** (L // 2) * m):>14d}  '
              f'{"ok" if match else "MISMATCH"}')
    print(f'    -> {"PASS" if h2 else "FAIL"}')
    ok &= h2

    print('H3  QLF colour-transport census vs M_L(1/3), even L <= 20')
    h3 = True
    for L in range(0, 21, 2):
        n = colour_census(L)
        col = Fraction(n[0]) + Fraction(n[1] + n[2]) * Fraction(-1, 2)    # n0 + n1 w + n2 w^2, real part
        imag_zero = n[1] == n[2]
        m = exact_value(area_census(L, 3), 1, 3)
        match = imag_zero and col == m
        h3 &= match
        print(f'    L={L:2d}  colour {str(col):>14s}  (counts {n})   M_L(1/3) {str(m):>14s}  '
              f'{"ok" if match else "MISMATCH"}')
    print(f'    -> {"PASS" if h3 else "FAIL"}')
    ok &= h3

    print('H4  integrality: Galois conjugates of M_L(p/q) agree iff the census is an integer')
    h4 = True
    for q in (1, 2, 3, 4, 6, 5, 7, 8):
        first_irr = None
        for L in range(0, 17, 2):
            c = area_census(L, q)
            cj = conjugates(c, q)
            if max(cj) - min(cj) > 1e-6:
                first_irr = first_irr or L
            elif q in COS_RATIONAL:
                v = exact_value(c, 1 if q > 1 else 0, q)
                assert v.denominator == 1, (q, L, v)
        expect_int = q in COS_RATIONAL
        good = (first_irr is None) == expect_int
        h4 &= good
        print(f'    q={q}: {"integer at every L" if first_irr is None else f"irrational from L={first_irr}"}'
              f'   {"ok" if good else "UNEXPECTED"}')
    print(f'    -> {"PASS" if h4 else "FAIL"}')
    ok &= h4

    print(f'H5  butterfly, q <= {args.qmax}')
    h5 = True
    for q in (2, 3, 4, 5, 6, 7, 8, 9, 10):
        p = 1
        b = bands(p, q)
        comp = components(b)
        bm = bands(q - p, q)
        sym_phi = all(abs(a[0] - c[0]) < 1e-6 and abs(a[1] - c[1]) < 1e-6 for a, c in zip(b, bm))
        sym_e = all(abs(a[0] + c[1]) < 1e-6 for a, c in zip(b, reversed(b)))
        width = sum(hi - lo for lo, hi in b)
        print(f'    q={q:2d}: {len(b)} bands, {comp} connected pieces, total width {width:.4f}, '
              f'phi->1-phi {"ok" if sym_phi else "NO"}, E->-E {"ok" if sym_e else "NO"}')
        h5 &= len(b) == q and sym_phi and sym_e
    print(f'    -> {"PASS" if h5 else "FAIL"}')
    ok &= h5

    if args.svg:
        write_svg(args.svg, args.qmax)
        print(f'wrote {args.svg}')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
