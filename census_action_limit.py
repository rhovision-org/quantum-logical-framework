#!/usr/bin/env python3
"""
census_action_limit.py -- numerical companion to lean/QLF_CensusActionLimit.lean (issue #303, S1/S2).

The one-axis census of a 2n-step +/- history has W_n(k) = C(2n, k) ways with k up-steps; balance
(ZFA closure) is k = n.  The normalized census cost of a displacement d is

    I_n(d) = log W_n(n) - log W_n(n + d).

The Lean module proves, with no asymptotics, the exact sandwich

    d^2 / (n + d)  <=  I_n(d)  <=  d^2 / (n - d + 1)        (0 <= d <= n),

and from it, at d = floor(x sqrt n):

    I_n(d)                                  -> x^2      (value limit, S1)
    sqrt(n) * (I_n(d+1) - I_n(d))           -> 2x       (variation limit, S2)
    n * (I_n(1) + I_n(-1) - 2 I_n(0))       -> 2        (curvature, the conservative return)

This script is NUMERICAL EVIDENCE, not a certificate: it evaluates those quantities in floating
point (math.lgamma and log1p sums, cross-checked against exact math.comb for small n) and shows the
rate.  The proof is the Lean module.

It also runs check K4 of #303 (normalization ambiguity): the cost 1 - W(n+d)/W(n) has the same
discrete minimum at balance, but its continuum limit is 1 - exp(-x^2), not x^2.  The Gaussian limit
fixes the log-count cost; it does not single out that cost among monotone costs with the same mode.

Usage: python3 census_action_limit.py
"""

from __future__ import annotations

import math


def cost(n: int, d: int) -> float:
    """I_n(d) as a sum of the exact one-step increments log((n+j+1)/(n-j))."""
    return math.fsum(math.log1p((2 * j + 1) / (n - j)) for j in range(d))


def cost_exact(n: int, d: int) -> float:
    """I_n(d) from exact binomials (small n only)."""
    return math.log(math.comb(2 * n, n)) - math.log(math.comb(2 * n, n + d))


def main() -> None:
    for n in (5, 12, 40):
        for d in range(n + 1):
            a, b = cost(n, d), cost_exact(n, d)
            assert abs(a - b) <= 1e-9 * max(1.0, b), (n, d, a, b)
            lo, hi = d * d / (n + d) if n + d else 0.0, d * d / (n - d + 1)
            assert lo - 1e-12 <= a <= hi + 1e-12, (n, d, lo, a, hi)
    print("increment sum agrees with exact binomials, and the sandwich holds, for n in {5, 12, 40}")

    print("\nS1  value limit  I_n(floor(x sqrt n)) -> x^2")
    print(f"{'x':>5} {'n':>9} {'d':>6} {'I_n(d)':>12} {'x^2':>8} {'error':>10} {'sqrt(n)*err':>12}")
    for x in (0.5, 1.0, 2.0):
        for n in (10**2, 10**3, 10**4, 10**5, 10**6):
            d = math.floor(x * math.sqrt(n))
            i = cost(n, d)
            print(f"{x:5.1f} {n:9d} {d:6d} {i:12.8f} {x*x:8.4f} {i - x*x:10.2e} "
                  f"{math.sqrt(n) * (i - x*x):12.4f}")

    print("\nS2  variation limit  sqrt(n) * (I_n(d+1) - I_n(d)) -> 2x")
    print(f"{'x':>5} {'n':>9} {'scaled variation':>18} {'2x':>6}")
    for x in (0.0, 0.5, 1.0, 2.0):
        for n in (10**2, 10**4, 10**6):
            d = math.floor(x * math.sqrt(n))
            dv = math.sqrt(n) * math.log1p((2 * d + 1) / (n - d))
            print(f"{x:5.1f} {n:9d} {dv:18.8f} {2*x:6.2f}")

    print("\nReturn  curvature at balance  n * (I_n(1) + I_n(-1) - 2 I_n(0)) -> 2")
    for n in (10, 10**2, 10**4, 10**6):
        print(f"  n = {n:8d}: {n * 2 * cost(n, 1):.10f}")

    print("\nK4  same discrete mode, different continuum cost: 1 - W(n+d)/W(n) -> 1 - exp(-x^2)")
    for x in (0.5, 1.0, 2.0):
        n = 10**6
        d = math.floor(x * math.sqrt(n))
        alt = -math.expm1(-cost(n, d))
        print(f"  x = {x:3.1f}: alt cost {alt:.6f}, 1 - exp(-x^2) = {-math.expm1(-x*x):.6f}, x^2 = {x*x:.4f}")


if __name__ == "__main__":
    main()
