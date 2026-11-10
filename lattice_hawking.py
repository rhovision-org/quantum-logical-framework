#!/usr/bin/env python3
"""Hawking emission with the census's own light cone (Relativity_Principle.md §6).

lean/QLF_LorentzSymbol.lean proves the census's massless modes lie on the lattice light cone
sin^2(w) = sum_a sin^2(k_a): exact along a lattice axis (axis_light_exact) and faster than c along
a diagonal (diagonal_light_superluminal). This script asks what that does to a black hole's
Hawking emission.

Model (stated, not derived): the horizon emits thermally at the Hawking temperature
T = 1/(8 pi M) (Planck units), in the lattice rest frame, with no greybody factor. The robustness
of T itself under modified short-distance dispersion is the Jacobson (1991) / Unruh (1995) /
Corley-Jacobson (1996) result, which holds for T << 1; near the Planck mass the semiclassical
picture is itself in doubt, so those rows are indicative only.

Per direction n, the spectral power is  S(w, n) = kappa_n(w)^2 * w / (e^{w/T} - 1),  where kappa_n(w)
solves the lattice dispersion along n (continuum: kappa = w, giving w^3). Modes stop at the band
edge sum sin^2 = 1.

Usage: python3 lattice_hawking.py
"""
import math

ZETA4 = math.pi ** 4 / 90
ZETA6 = math.pi ** 6 / 945
DIRS = {"axis (1,0,0)": (1, 0, 0), "face diagonal (1,1,0)": (1, 1, 0),
        "body diagonal (1,1,1)": (1, 1, 1)}


def unit(v):
    r = math.sqrt(sum(c * c for c in v))
    return tuple(c / r for c in v)


def s2(kappa, n):
    return sum(math.sin(kappa * c) ** 2 for c in n)


def kappa_of_omega(w, n):
    """Smallest kappa >= 0 with sin^2(w) = s2(kappa, n); None past the band edge."""
    target = math.sin(w) ** 2
    lo, hi = 0.0, math.pi / 2 / max(abs(c) for c in n)  # s2 increasing on [0, hi]
    if s2(hi, n) < target:
        return None
    for _ in range(80):
        mid = (lo + hi) / 2
        if s2(mid, n) < target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def omega_edge(n):
    """Band edge along n: largest w with a real mode (w <= pi/2)."""
    hi = math.pi / 2 / max(abs(c) for c in n)
    return math.asin(min(1.0, math.sqrt(s2(hi, n))))


def power(T, n, lattice=True, steps=4000):
    wmax = omega_edge(n) if lattice else 60 * T
    wmax = min(wmax, 60 * T)
    h = wmax / steps
    tot = 0.0
    for i in range(1, steps + 1):
        w = (i - 0.5) * h
        x = w / T
        if x > 700:
            break
        kap = kappa_of_omega(w, n) if lattice else w
        if kap is None:
            break
        tot += kap ** 2 * w / math.expm1(x) * h
    return tot


def check_superluminal(samples=20000, seed=7):
    import random
    rng = random.Random(seed)
    worst = 1.0
    for _ in range(samples):
        n = unit([rng.gauss(0, 1) for _ in range(3)])
        kap = rng.uniform(1e-3, math.pi / 2 / max(abs(c) for c in n))
        v = s2(kap, n)
        if v > 1:
            continue
        w = math.asin(math.sqrt(v))
        worst = min(worst, w / kap)
    print(f"phase velocity w/|k| over {samples} random in-band modes: minimum {worst:.12f}"
          " (>= 1: never subluminal; = 1 only on the axes)")


def main():
    check_superluminal()
    print()
    masses = [("Sun (1e38 M_P)", 1e38), ("1e15 g primordial (4.6e19 M_P)", 4.6e19),
              ("1000 M_P", 1e3), ("100 M_P", 1e2), ("10 M_P", 10.0), ("3 M_P", 3.0),
              ("1 M_P", 1.0), ("0.3 M_P", 0.3)]
    print(f"{'black hole':32s} {'T (Planck)':>11s} {'diag(111)/axis - 1':>20s} "
          f"{'leading-order':>14s} {'axis/continuum - 1':>19s}")
    d111 = (1 - 1 / 3) / 6
    for name, M in masses:
        T = 1 / (8 * math.pi * M)
        lead = -40 * d111 * ZETA6 / ZETA4 * T ** 2
        if T < 1e-4:
            print(f"{name:32s} {T:11.3e} {lead:20.3e} {lead:14.3e} {'~0 (exact on axis)':>19s}")
            continue
        pa = power(T, unit(DIRS["axis (1,0,0)"]))
        pd = power(T, unit(DIRS["body diagonal (1,1,1)"]))
        pc = power(T, (1, 0, 0), lattice=False)
        print(f"{name:32s} {T:11.3e} {pd / pa - 1:20.4%} {lead:14.4%} {pa / pc - 1:19.4%}")
    print()
    print("Reading: along a lattice axis the emission is the continuum Planck spectrum up to the")
    print("band edge; off-axis, light is faster than c, fewer modes fit below a given frequency, and")
    print("less power comes out. Leading order: -40*delta*zeta(6)/zeta(4)*T^2, delta=(1-sum n^4)/6.")


if __name__ == "__main__":
    main()
