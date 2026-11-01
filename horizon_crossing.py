#!/usr/bin/env python3
"""
horizon_crossing.py: the keep/flip split of the spatial-to-gauge horizon crossing, counted exactly.

Part of the Quantum Logical Framework (QLF), see README.md. ZFA (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF.

BLACK-HOLES.md section 4a measures the crossing H (the Z axis exchanged with the gauge pair:
'/' <-> '+', '\\' <-> '-') on balanced histories and splits them into those whose fold is kept and
those whose fold flips sign. It leaves open the shape of R(L) = W_keep(L) / W_flip(L), with exact
values inf, 17/4, 53/27, 13781/9984 at L = 2, 4, 6, 8.

PRE-REGISTERED STATEMENT (fixed in Jim's message of 2026-11-01 before this file existed; this
commit freezes it alongside the checker):

    Let chi(h) = +1 if fold(H h) = fold(h), -1 if fold(H h) = -fold(h), on balanced h.
    D_L = sum of chi over balanced histories of length L = W_keep(L) - W_flip(L).
    Claim:  D_L / W_L -> 0,  hence  R(L) = (W_L + D_L) / (W_L - D_L) -> 1.
    Kill conditions:  D_L / W_L tends to a positive constant (R -> c > 1), or D_L < 0 for some
    large L (R < 1 eventually).

Honesty note: the closed form below was derived and checked numerically in a scratch session
before this commit, so the claim is pre-registered by Jim's message, not by this file.

What this script checks:
  1. the one-bit cocycle chi_bit (a bit flips on every Z or gauge twist; each X/Y twist read while
     the bit is set contributes -1) equals the fold-ratio chi, history by history, against the real
     Pauli fold of twist_core.py (lengths <= --brute, default 6);
  2. chi = +1 on every "pure-pair" history (each aligned pair both in {X,Y} or both in {Z,gauge}),
     and the number of pure-pair balanced histories equals D_L;
  3. the closed form D_{2n} = sum_k C(n,k) C(2k,k)^2 C(2n-2k,n-k)^2 against the brute counts, and
     prints R(L) and D_L / W_L out to --max-len.

Lean: lean/QLF_HorizonCrossing.lean.
"""
import argparse
import itertools
from fractions import Fraction
from math import comb

from twist_core import TWISTS, pauli_fold

H = {'/': '+', '\\': '-', '+': '/', '-': '\\'}
XY = set('^v<>')


def balanced(h):
    return all(h.count(a) == h.count(b) for a, b in ('^v', '<>', '/\\', '+-'))


def chi_bit(h):
    bit = parity = 0
    for t in h:
        if t in XY:
            parity ^= bit
        else:
            bit ^= 1
    return -1 if parity else 1


def pure_pairs(h):
    return all((h[i] in XY) == (h[i + 1] in XY) for i in range(0, len(h) - 1, 2))


def w2(m):
    """Closed walks of length m on Z^2 (four steps): C(2j, j)^2 at m = 2j, else 0."""
    return comb(m, m // 2) ** 2 if m % 2 == 0 else 0


def walk_count(L):
    """W_L, the balanced-history count (QLF_PolyaTransience.walkCount)."""
    return sum(comb(L, k) * w2(k) * w2(L - k) for k in range(L + 1))


def signed_count(L):
    """D_L in closed form; 0 at odd L (no balanced history has odd length)."""
    if L % 2:
        return 0
    n = L // 2
    return sum(comb(n, k) * w2(2 * k) * w2(2 * (n - k)) for k in range(n + 1))


def brute(L):
    keep = flip = d = pure = 0
    for w in itertools.product(TWISTS, repeat=L):
        if not balanced(w):
            continue
        h = ''.join(w)
        same = all(abs(a - b) < 1e-9 for a, b in zip(pauli_fold(h), pauli_fold(''.join(H.get(t, t) for t in h))))
        c = chi_bit(h)
        assert (c == 1) == same, f"cocycle disagrees with fold at {h}"
        if pure_pairs(h):
            assert c == 1, f"pure-pair history with chi = -1: {h}"
            pure += 1
        keep += same
        flip += not same
        d += c
    return keep, flip, d, pure


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[1])
    ap.add_argument('--brute', type=int, default=6, help='largest even length checked against the fold')
    ap.add_argument('--max-len', type=int, default=40, help='largest even length printed from the closed form')
    a = ap.parse_args()

    print("brute force against the Pauli fold")
    print(f"{'L':>3} {'W_keep':>10} {'W_flip':>10} {'D_L':>10} {'pure':>10}  closed form")
    for L in range(2, a.brute + 1, 2):
        keep, flip, d, pure = brute(L)
        ok = d == pure == signed_count(L) and keep + flip == walk_count(L)
        print(f"{L:>3} {keep:>10} {flip:>10} {d:>10} {pure:>10}  {'ok' if ok else 'MISMATCH'}")
        assert ok

    print("\nclosed form")
    print(f"{'L':>3} {'R(L)':>22} {'D_L/W_L':>12} {'2^(1-L/2)':>12}")
    for L in range(2, a.max_len + 1, 2):
        W, D = walk_count(L), signed_count(L)
        keep, flip = (W + D) // 2, (W - D) // 2
        R = 'inf' if flip == 0 else str(Fraction(keep, flip)) if L <= 8 else f"{keep / flip:.12f}"
        print(f"{L:>3} {R:>22} {D / W:>12.3e} {2 ** (1 - L / 2):>12.3e}")


if __name__ == '__main__':
    main()
