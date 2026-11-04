#!/usr/bin/env python3
"""
discrete_mt.py — test D-MT of `No_Continuum_Conjecture.md` §5a: does the census wave violate a
discrete Mizohata–Takeuchi bound?

The wave is ψ_k(x), the signed sum over twist histories of length k from the origin ending at x ∈ ℤ⁴,
each history weighted by the holonomy of the ℤ₂ edge-sign connection (`closure_walk.edge_sign`).
Per time slice, ρ_k(x) = ψ_k(x)² / Σ_y ψ_k(y)². The random-phase baseline is p_k(x) = W_k(x)/8^k.

Lines are the substrate's own straight lines in discrete spacetime (x, k), 0 ≤ k ≤ L: rest lines and
the eight null directions. V_L = max Σ ρ w over w ≥ 0 with every line sum ≤ 1 — a linear program,
solved exactly enough by HiGHS. Mizohata–Takeuchi holding for this wave means V_L stays bounded.

Registered prediction (commit 2880998, before this script existed): V_L rises at every step, and
V_L / V_L^rp rises at every step. Either failing is a FAIL at the depth reached.

Needs numpy + scipy (not stdlib).   Run:  python3 discrete_mt.py [--max-len 8]   (~10 s; the L=10 program did not finish in 12 min)
Writes data/discrete_mt.json.
"""
from __future__ import annotations

import argparse
import json
import os
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from closure_walk import edge_sign

_HERE = os.path.dirname(os.path.abspath(__file__))
OUT_PATH = os.path.join(_HERE, "data", "discrete_mt.json")
STEPS = [(a, s) for a in range(4) for s in (1, -1)]
ORIGIN = (0, 0, 0, 0)


def slices(L: int):
    """[(A_k, W_k)] for k = 0..L, each a dict node -> exact integer."""
    A, W = {ORIGIN: 1}, {ORIGIN: 1}
    out = [(A, W)]
    for _ in range(L):
        nA, nW = {}, {}
        for x, c in W.items():
            ax, xl = A[x], list(x)
            for a, s in STEPS:
                y = list(x); y[a] += s; y = tuple(y)
                nW[y] = nW.get(y, 0) + c
                nA[y] = nA.get(y, 0) + edge_sign(xl, a, s) * ax
        A, W = nA, nW
        out.append((A, W))
    return out


def lines_through(x, k):
    yield ("r", x)
    for a, s in STEPS:
        x0 = list(x); x0[a] -= s * k
        yield ("n", a, s, tuple(x0))


def mt_constant(dens):
    """dens: list over k of {x: density}. Returns (V, sum_k max_x dens_k)."""
    pts, c = [], []
    for k, d in enumerate(dens):
        for x, v in d.items():
            if v > 0:
                pts.append((x, k)); c.append(v)
    line_id, rows, cols = {}, [], []
    for j, (x, k) in enumerate(pts):
        for ln in lines_through(x, k):
            i = line_id.setdefault(ln, len(line_id))
            rows.append(i); cols.append(j)
    A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(line_id), len(pts))).tocsr()
    res = linprog(-np.array(c), A_ub=A, b_ub=np.ones(len(line_id)), bounds=(0, None), method="highs")
    assert res.status == 0, res.message
    return -res.fun, sum(max(d.values()) for d in dens), len(pts), len(line_id)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-len", type=int, default=8)
    args = ap.parse_args(argv)
    sl = slices(args.max_len)
    # check: Σ_x A_k(x)² = (−1)^k A_{2k}(0)  (the transfer operator is antisymmetric)
    for k in range(1, args.max_len // 2 + 1):
        assert sum(v * v for v in sl[k][0].values()) == (-1) ** k * sl[2 * k][0].get(ORIGIN, 0)
    rows = []
    print(" L   V_signed   V_randomphase   ratio    sum_k max rho (signed / rp)   vars  lines")
    for L in range(2, args.max_len + 1, 2):
        sig, rp = [], []
        for k in range(L + 1):
            A, W = sl[k]
            nA = sum(v * v for v in A.values())
            sig.append({x: float(Fraction(v * v, nA)) for x, v in A.items()})
            rp.append({x: float(Fraction(v, 8 ** k)) for x, v in W.items()})
        Vs, ms, nv, nl = mt_constant(sig)
        Vr, mr, _, _ = mt_constant(rp)
        rows.append({"L": L, "V_signed": Vs, "V_rp": Vr, "ratio": Vs / Vr,
                     "sum_max_signed": ms, "sum_max_rp": mr})
        print(f"{L:2d}  {Vs:9.5f}   {Vr:12.5f}   {Vs/Vr:7.4f}   {ms:9.5f} / {mr:9.5f}   {nv:6d} {nl:6d}")
    up = all(b["V_signed"] > a["V_signed"] for a, b in zip(rows, rows[1:]))
    rup = all(b["ratio"] > a["ratio"] for a, b in zip(rows, rows[1:]))
    verdict = "PASS (MT violated as predicted)" if up and rup else "FAIL"
    print(f"\nV_signed rises every step: {up};  ratio rises every step: {rup}  ->  {verdict}")
    os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
    with open(OUT_PATH, "w") as f:
        json.dump({"rows": rows, "V_rises": up, "ratio_rises": rup, "verdict": verdict}, f, indent=1)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
