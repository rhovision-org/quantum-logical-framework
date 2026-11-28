#!/usr/bin/env python3
"""signed_phase_track.py -- is the closure phase an action? (#303 S4-S5, K5-K7)

Part of the Quantum Logical Framework (QLF); see README.md. The tests P1-P4 and the verdict rule
are pre-registered in Stationary_Action.md section 5b, committed before this script existed.

The QLF phase of a history is the product of edge signs (QLF_EdgeSign): a step from x along axis a
with sign s carries s * (-1)^{P_a(x)}, where P_X = y + z, P_Y = z, P_Z = P_I = 0. The countermodel
family replaces it by a U(1) connection with flux phi through every spatial plaquette and a sign
sigma on every negative step:

    positive step from x along a:  exp(+i phi P_a(x))
    negative step from x along a:  sigma * exp(-i phi P_a(x))

QLF is (phi, sigma) = (pi, -1). Amplitudes are kept exactly in Z[zeta_12] (phi = 2 pi j / 12),
as integer coefficient vectors on the powers of zeta; only the final modulus is a float.

    python3 signed_phase_track.py                 # 2m <= 10, fold check to length 6
    python3 signed_phase_track.py --max-len 8 --fold-len 4 --json data/signed_phase_track.json
"""

from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
from collections import defaultdict

import twist_core

# axis index: 0 = I (gauge), 1 = X, 2 = Y, 3 = Z
TWIST_STEP = {"+": (0, +1), "-": (0, -1), ">": (1, +1), "<": (1, -1),
              "^": (2, +1), "v": (2, -1), "/": (3, +1), "\\": (3, -1)}
N = 12                                   # zeta = exp(2 pi i / 12)
FLUXES = {"0": 0, "pi/2": 3, "2pi/3": 4, "pi": 6, "-pi": -6}
SIGMAS = (+1, -1)


def P(axis: int, x: tuple) -> int:
    """The potential an edge on `axis` reads at position x (QLF_EdgeSign.edgeParity, unreduced)."""
    if axis == 1:
        return x[2] + x[3]
    if axis == 2:
        return x[3]
    return 0


def step_power(j: int, sigma: int, axis: int, s: int, x: tuple) -> int:
    """The weight of one step, as a power of zeta."""
    k = j * P(axis, x) if s > 0 else -j * P(axis, x)
    if s < 0 and sigma < 0:
        k += N // 2
    return k % N


def to_complex(vec) -> complex:
    return sum(c * cmath.exp(2j * math.pi * k / N) for k, c in enumerate(vec) if c)


# --------------------------------------------------------------------------- P1: the bound

def amplitudes(j: int, sigma: int, L: int) -> dict:
    """amp[x] after L steps from the origin, as Z[zeta_12] coefficient vectors."""
    amp = {(0, 0, 0, 0): [1] + [0] * (N - 1)}
    for _ in range(L):
        new: dict = defaultdict(lambda: [0] * N)
        for x, vec in amp.items():
            for axis in range(4):
                for s in (+1, -1):
                    k = step_power(j, sigma, axis, s, x)
                    y = list(x)
                    y[axis] += s
                    tgt = new[tuple(y)]
                    for e, c in enumerate(vec):
                        if c:
                            tgt[(e + k) % N] += c
        amp = {x: v for x, v in new.items() if any(v)}
    return amp


def bound_check(j: int, sigma: int, max_len: int) -> list:
    rows = []
    for L in range(2, max_len + 1, 2):
        amp = amplitudes(j, sigma, L)
        a0 = abs(to_complex(amp.get((0, 0, 0, 0), [0] * N)))
        worst_x, worst = None, -1.0
        for x, v in amp.items():
            if x == (0, 0, 0, 0):
                continue
            m = abs(to_complex(v))
            if m > worst:
                worst, worst_x = m, x
        rows.append({"L": L, "abs_A0": a0, "max_abs_A_off": worst, "argmax": worst_x,
                     "bound_holds": worst <= a0 * (1 + 1e-9) + 1e-9})
    return rows


# --------------------------------------------------------------------------- P2, P3: per history

def weight(j: int, sigma: int, h: str) -> int:
    """The weight of history h as a power of zeta."""
    x = [0, 0, 0, 0]
    k = 0
    for t in h:
        axis, s = TWIST_STEP[t]
        k += step_power(j, sigma, axis, s, tuple(x))
        x[axis] += s
    return k % N


def balanced(h: str) -> bool:
    v = [0, 0, 0, 0]
    for t in h:
        a, s = TWIST_STEP[t]
        v[a] += s
    return v == [0, 0, 0, 0]


def fold_power(h: str) -> int:
    """The Pauli fold of a balanced history, which is +-I, as a power of zeta (0 or 6)."""
    m = twist_core.pauli_fold(h)
    a, b, c, d = m
    assert abs(b) < 1e-9 and abs(c) < 1e-9 and abs(a - d) < 1e-9 and abs(abs(a) - 1) < 1e-9
    assert abs(a.imag) < 1e-9, "count balance never folds to +-iI"
    return 0 if a.real > 0 else N // 2


def fold_check(fold_len: int) -> dict:
    hist = [h for n in range(2, fold_len + 1, 2)
            for h in ("".join(w) for w in itertools.product(TWIST_STEP, repeat=n)) if balanced(h)]
    folds = {h: fold_power(h) for h in hist}
    out = {"balanced_histories": len(hist)}
    for (fname, j), sigma in itertools.product(FLUXES.items(), SIGMAS):
        mism = [h for h in hist if weight(j, sigma, h) != folds[h]]
        out[f"phi={fname},sigma={sigma:+d}"] = {
            "mismatches": len(mism), "example": min(mism, key=len) if mism else None}
    return out


def composition_check(fold_len: int) -> dict:
    """P3: multiplicativity under concatenation of closed histories, and reversal."""
    closed = [h for n in range(0, min(fold_len, 4) + 1, 2)
              for h in ("".join(w) for w in itertools.product(TWIST_STEP, repeat=n)) if balanced(h)]
    conj = {"+": "-", "-": "+", ">": "<", "<": ">", "^": "v", "v": "^", "/": "\\", "\\": "/"}
    out = {}
    for (fname, j), sigma in itertools.product(FLUXES.items(), SIGMAS):
        comp_fail = sum(1 for u in closed for w in closed
                        if weight(j, sigma, u + w) != (weight(j, sigma, u) + weight(j, sigma, w)) % N)
        rev_fail = 0
        for h in closed:
            r = "".join(conj[t] for t in reversed(h))     # the walk run backwards
            want = (-weight(j, sigma, h) + (N // 2 if sigma < 0 and len(h) % 2 else 0)) % N
            if weight(j, sigma, r) != want:
                rev_fail += 1
        out[f"phi={fname},sigma={sigma:+d}"] = {"composition_failures": comp_fail,
                                                 "reversal_failures": rev_fail}
    out["closed_histories"] = len(closed)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--max-len", type=int, default=10)
    ap.add_argument("--fold-len", type=int, default=6)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()

    res = {"max_len": a.max_len, "fold_len": a.fold_len, "P1": {}, "P2": None, "P3": None}
    print(f"P1 (K5): |A(2m;0,x)| <= |A(2m;0,0)| on Z^4, 2m <= {a.max_len}")
    for (fname, j), sigma in itertools.product(FLUXES.items(), SIGMAS):
        if fname == "-pi":
            continue
        rows = bound_check(j, sigma, a.max_len)
        res["P1"][f"phi={fname},sigma={sigma:+d}"] = rows
        ok = all(r["bound_holds"] for r in rows)
        last = rows[-1]
        print(f"  phi={fname:>5}, sigma={sigma:+d}: bound {'holds' if ok else 'FAILS'};"
              f" at 2m={last['L']}: |A0| = {last['abs_A0']:.6g}, max off-origin = {last['max_abs_A_off']:.6g}")
    p1_others = [k for k, rows in res["P1"].items()
                 if k != "phi=pi,sigma=-1" and all(r["bound_holds"] for r in rows)]
    print(f"  -> the bound holds for {len(p1_others)} of the {len(res['P1']) - 1} non-QLF members:"
          f" P1 {'FAILS (the bound does not identify the phase)' if p1_others else 'PASSES'}")

    res["P2"] = fold_check(a.fold_len)
    print(f"P2 (K6): weight = Pauli fold on all {res['P2']['balanced_histories']} balanced histories of length <= {a.fold_len}")
    matching = []
    for k, v in res["P2"].items():
        if k == "balanced_histories":
            continue
        print(f"  {k:<20} mismatches {v['mismatches']:>7}  e.g. {v['example']!r}")
        if v["mismatches"] == 0:
            matching.append(k)
    print(f"  -> members matching the fold: {matching}")

    res["P3"] = composition_check(a.fold_len)
    bad = {k: v for k, v in res["P3"].items() if isinstance(v, dict)
           and (v["composition_failures"] or v["reversal_failures"])}
    print(f"P3 (S4 laws): composition and reversal on {res['P3']['closed_histories']} closed histories:"
          f" {'all hold' if not bad else bad}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
