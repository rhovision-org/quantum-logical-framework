#!/usr/bin/env python3
"""
zipf_closures.py -- the rank-frequency law of the prime (first-return) closure inventory.

Ranks every prime closure by its frequency, the cylinder (Kraft) weight (2d)^-L of a
history of length L, and reports how frequency falls with rank r.  Counts are exact
integers: closed-walk counts W_L on Z^d from the product of d one-axis series, and
prime counts I_L from the renewal identity I = 1 - 1/W (power series in z^2).

Result (Bridge_Tools.md §4).  The frequency at rank r obeys

    f(r)  ~  C / ( r * (ln r)^(d/2) ),

with d = 4 for the eight-twist alphabet and d = 3 for the six spatial twists.  The
local exponent d ln f / d ln r tends to -1 and f * r * (ln r)^(d/2) settles to a
constant.

What is and is not content (method rule 4).  The exponent -1 is bookkeeping: it holds
for ANY inventory whose words of length L share the weight (2d)^-L and whose count
grows like (2d)^L times a subexponential factor -- Miller's (1957) random-typing
argument, after Mandelbrot (1953).  The correction (ln r)^(-d/2) is not: it is the
L^(-d/2) decay of first returns, i.e. the number of independent axes (Polya), and it
also fixes the total prime mass, sum f = 0.193 for d = 4 (Closure_Walk.md).

Usage: python3 zipf_closures.py [half_length]   (default 150, under a second)
"""

import math
import sys
from fractions import Fraction


def closed_counts(d, n_half):
    """W_{2n} for n <= n_half: closed walks of length 2n on Z^d (exact)."""
    one = [Fraction(1, math.factorial(k) ** 2) for k in range(n_half + 1)]
    p = [Fraction(1)] + [Fraction(0)] * n_half
    for _ in range(d):
        q = [Fraction(0)] * (n_half + 1)
        for i, a in enumerate(p):
            if a:
                for j in range(n_half + 1 - i):
                    q[i + j] += a * one[j]
        p = q
    return [int(p[n] * math.factorial(2 * n)) for n in range(n_half + 1)]


def prime_counts(W):
    """I_{2n}: first returns, from I = 1 - 1/W as a power series in z^2."""
    inv = [0] * len(W)
    inv[0] = 1
    for k in range(1, len(W)):
        inv[k] = -sum(W[j] * inv[k - j] for j in range(1, k + 1))
    return [0] + [-x for x in inv[1:]]


def main():
    n_half = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    for d in (3, 4):
        W = closed_counts(d, n_half)
        I = prime_counts(W)
        base = 2 * d
        assert all(x >= 0 for x in I)
        print(f"d = {d} ({base} twists)")
        print(f"{'L':>5} {'log10 rank':>11} {'local exponent':>15} {'f*r*(ln r)^(d/2)':>18}")
        r = 0
        for n in range(1, n_half + 1):
            r += I[n]
            L = 2 * n
            ln_r = math.log(r)
            ln_f = -L * math.log(base)
            if n in (5, 10, 20, 40, 80, n_half):
                print(f"{L:5d} {ln_r / math.log(10):11.1f} {ln_f / ln_r:15.4f} "
                      f"{math.exp(ln_f + ln_r) * ln_r ** (d / 2):18.4f}")
        mass = sum(Fraction(I[n], base ** (2 * n)) for n in range(1, n_half + 1))
        print(f"  prime mass through L = {2 * n_half}: {float(mass):.6f}\n")


if __name__ == "__main__":
    main()
