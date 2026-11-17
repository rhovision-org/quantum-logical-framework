#!/usr/bin/env python3
"""
zipf_closures.py -- the rank-frequency law of the prime (first-return) closure inventory.

Ranks every prime closure by its frequency, the cylinder (Kraft) weight (2d)^-L of a
history of length L, and reports how frequency falls with rank r.  Counts are exact
integers: closed-walk counts W_L on Z^d from the product of d one-axis series, and
prime counts I_L from the renewal identity I = 1 - 1/W (power series in z^2).

Result (Bridge_Tools.md §4).  The law is a STAIRCASE: every prime closure of one
length L has the same frequency, so a block of ranks whose size grows like
(2d)^L shares one value of f.  Along the block endpoints r_L (the cumulative count
through length L),

    f(r_L) * r_L * (ln r_L)^(d/2)  ->  C        (endpoint ranks only),

and for arbitrary ranks only the two-sided bound holds,

    f(r)  =  Theta( 1 / ( r * (ln r)^(d/2) ) ),

because within a block f is constant while r grows by the factor (2d)^2 (so the
normalized product varies by about that factor inside each block).  Here d = 4 for
the eight-twist alphabet and d = 3 for the six spatial twists.  The script prints,
at endpoints, the endpoint finite-difference slope
[ln f(r_L) - ln f(r_(L-2))] / [ln r_L - ln r_(L-2)], which tends to -1, the
global ratio ln f / ln r, and the normalized product, plus the size of the
in-block variation.

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
        print(f"{'L':>5} {'log10 r_L':>10} {'endpoint slope':>15} {'ln f / ln r':>12} "
              f"{'f*r*(ln r)^(d/2)':>17} {'in-block factor':>16}")
        r = 0
        prev_ln_r = None
        for n in range(1, n_half + 1):
            r_start = r + 1
            r += I[n]
            L = 2 * n
            ln_r = math.log(r)
            ln_f = -L * math.log(base)
            if n in (5, 10, 20, 40, 80, n_half):
                slope = -2 * math.log(base) / (ln_r - prev_ln_r)
                ln_s = math.log(r_start)
                # ratio of the normalized product at the block's last and first rank
                block = math.exp(ln_r - ln_s) * (ln_r / ln_s) ** (d / 2)
                print(f"{L:5d} {ln_r / math.log(10):10.1f} {slope:15.4f} {ln_f / ln_r:12.4f} "
                      f"{math.exp(ln_f + ln_r) * ln_r ** (d / 2):17.4f} {block:16.2f}")
            prev_ln_r = ln_r
        mass = sum(Fraction(I[n], base ** (2 * n)) for n in range(1, n_half + 1))
        print(f"  prime mass through L = {2 * n_half}: {float(mass):.6f}\n")


if __name__ == "__main__":
    main()
