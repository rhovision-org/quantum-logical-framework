#!/usr/bin/env python3
"""
rogue_census.py — the census amplitude against the random-phase baseline, and the
measure of straight-line histories. Companion to `No_Continuum_Conjecture.md`.

Two exact computations, integers throughout:

1. **Coherence of the signed census.** `W_L` counts closed walks of length L on ℤ⁴
   (the count-balanced twist histories, `Closure_Walk.md`); `A_L` sums their fold phases,
   computed as the holonomy of the ℤ₂ edge-sign connection (`closure_walk.edge_sign`,
   proved equal to the fold on balanced histories in `lean/QLF_EdgeSign.lean`).
   If the W_L signs were independent fair coins, `A_L` would be a sum of W_L random ±1,
   with E[A_L²] = W_L, so |A_L| ≈ √W_L. The ratio κ_L = |A_L|/√W_L measures how far
   the realized amplitude sits above that random-phase (Gaussian) baseline, in units of
   its standard deviation. The script also prints the Gaussian log-probability of a
   fluctuation that large, log₁₀ P ≈ −κ²/(2 ln 10), next to the ocean's rogue-wave
   threshold (Rayleigh sea, crest-to-trough H > 2 H_s: P = e^{−8} ≈ 3.4·10⁻⁴).

2. **Straight-line histories.** A history is *geodesic* (net displacement equal to its
   length, |x|₁ = L) iff it never uses both twists of a conjugate pair. G_L counts them:
   G_L = Σ_k C(4,k)·2^k·k!·S(L,k)  (choose k axes, a sign on each, a surjective word).
   G_L/8^L ≤ 16·2^{−L}. A geodesic history of positive length is never count-balanced,
   so no closure is a straight line.

Run:  python3 rogue_census.py [--max-len 40]     (L=40 ≈ 25 s; L=20 under 1 s)
Writes data/rogue_census.json.
"""
from __future__ import annotations

import argparse
import json
import math
import os

from closure_walk import edge_sign, closed_walk_count

_HERE = os.path.dirname(os.path.abspath(__file__))
OUT_PATH = os.path.join(_HERE, "data", "rogue_census.json")
STEPS = [(a, s) for a in range(4) for s in (1, -1)]
ORIGIN = (0, 0, 0, 0)


def signed_census(max_len: int) -> dict[int, tuple[int, int]]:
    """{L: (W_L, A_L)} for even L ≤ max_len, by a transfer recursion on ℤ⁴ nodes.
    Nodes farther (ℓ¹) from the origin than the remaining steps are dropped: they
    cannot return. One pass per target length keeps the pruning exact."""
    out = {}
    for L in range(2, max_len + 1, 2):
        W = {ORIGIN: 1}
        A = {ORIGIN: 1}
        for k in range(1, L + 1):
            rem = L - k
            nW: dict = {}
            nA: dict = {}
            for x, c in W.items():
                ax = A[x]
                xl = list(x)
                for a, s in STEPS:
                    y = list(x)
                    y[a] += s
                    if sum(map(abs, y)) > rem:
                        continue
                    y = tuple(y)
                    nW[y] = nW.get(y, 0) + c
                    nA[y] = nA.get(y, 0) + edge_sign(xl, a, s) * ax
            W, A = nW, nA
        out[L] = (W.get(ORIGIN, 0), A.get(ORIGIN, 0))
        assert out[L][0] == closed_walk_count(L), f"W_{L} mismatch with closure_walk"
    return out


def stirling2(n: int, k: int) -> int:
    return sum((-1) ** j * math.comb(k, j) * (k - j) ** n for j in range(k + 1)) // math.factorial(k)


def geodesic_count(L: int) -> int:
    return sum(math.comb(4, k) * 2 ** k * math.factorial(k) * stirling2(L, k) for k in range(5))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-len", type=int, default=40)
    args = ap.parse_args(argv)

    census = signed_census(args.max_len)
    # regression: the signed census printed in Closure_Walk.md §3
    assert [census[L][1] for L in (2, 4, 6)] == [-8, 120, -2144]

    rows = []
    print(" L            W_L                  A_L      |A|/W     kappa=|A|/sqrt(W)  "
          "log10 P_gauss   A_L/A_{L-2}")
    prevA = None
    for L, (W, A) in census.items():
        kappa = abs(A) / math.sqrt(W)
        log10p = -kappa ** 2 / (2 * math.log(10))
        ratio = (A / prevA) if prevA else None
        rows.append({"L": L, "W": W, "A": A, "abs_A_over_W": abs(A) / W, "kappa": kappa,
                     "log10_gauss_tail": log10p, "A_ratio": ratio})
        print(f"{L:2d} {W:22d} {A:20d}  {abs(A)/W:8.5f}  {kappa:16.2f}  {log10p:14.4g}   "
              f"{'' if ratio is None else f'{ratio:9.4f}'}")
        prevA = A

    print("\nOcean rogue-wave threshold (Rayleigh, H > 2 H_s): P = e^-8 =", f"{math.exp(-8):.3e}")

    geo = []
    print("\n L   G_L (geodesic)        G_L/8^L        bound 16*2^-L")
    for L in range(1, args.max_len + 1):
        G = geodesic_count(L)
        geo.append({"L": L, "G": G, "fraction": G / 8 ** L})
        assert G <= 16 * 4 ** L
        if L <= 4 or L % 4 == 0:
            print(f"{L:2d} {G:18d}  {G/8**L:14.4e}  {16*2.0**-L:14.4e}")
    # brute-force check of the geodesic formula for small L
    import itertools
    for L in range(1, 6):
        brute = sum(1 for w in itertools.product(STEPS, repeat=L)
                    if not any((a, 1) in w and (a, -1) in w for a in range(4)))
        assert brute == geodesic_count(L), f"G_{L} formula mismatch"

    os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
    with open(OUT_PATH, "w") as f:
        json.dump({"signed_census": rows, "geodesic": geo,
                   "rayleigh_rogue_threshold_p": math.exp(-8)}, f, indent=1)
    print(f"\nwrote {os.path.relpath(OUT_PATH, _HERE)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
