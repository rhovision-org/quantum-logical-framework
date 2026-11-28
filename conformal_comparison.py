#!/usr/bin/env python3
"""conformal_comparison.py -- does ZFA admit a local scale or frame symmetry? (#302, C1)

Part of the Quantum Logical Framework (QLF); see README.md. Tests W1-W5 and the verdict rule are
pre-registered in Conformal_Comparison.md section 1, committed before this script existed.

A position-dependent letter substitution replaces letter t_p by sigma_p(t_p) repeated k_p times,
where sigma_p is one of the 384 signed permutations of the four axes (gauge included).

    python3 conformal_comparison.py [--json data/conformal_comparison.json]
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter

import twist_core

AX = {"+": 0, "-": 0, ">": 1, "<": 1, "^": 2, "v": 2, "/": 3, "\\": 3}
SG = {"+": 1, "-": -1, ">": 1, "<": -1, "^": 1, "v": -1, "/": 1, "\\": -1}
LETTER = {(AX[t], SG[t]): t for t in AX}
CONJ = {t: LETTER[(AX[t], -SG[t])] for t in AX}
TOL = 1e-9


def frames():
    """All 384 signed axis permutations, as letter maps."""
    out = []
    for perm in itertools.permutations(range(4)):
        for signs in itertools.product((1, -1), repeat=4):
            out.append({t: LETTER[(perm[AX[t]], signs[perm[AX[t]]] * SG[t])] for t in AX})
    return out


def balanced(h) -> bool:
    c = Counter(h)
    return all(c[t] == c[CONJ[t]] for t in AX)


def fold_scalar(h: str) -> complex:
    m = twist_core.pauli_fold(h) if h else (1, 0, 0, 1)
    assert abs(m[1]) < TOL and abs(m[2]) < TOL and abs(m[0] - m[3]) < TOL, h
    return complex(round(m[0].real), round(m[0].imag))


def balanced_histories(L: int):
    return ["".join(w) for w in itertools.product(AX, repeat=L) if balanced(w)]


def apply(h: str, sig, k) -> str:
    return "".join(sig[p][t] * k[p] for p, t in enumerate(h))


def w1_w2(max_len: int) -> dict:
    out = {}
    ident = {t: t for t in AX}
    allh = ["".join(w) for n in range(1, max_len + 1) for w in itertools.product(AX, repeat=n)]
    for k in (1, 2, 3, 4, 5):
        zfa_fail = fold_fail = 0
        folds = set()
        for h in allh:
            img = apply(h, [ident] * len(h), [k] * len(h))
            if balanced(h) != balanced(img):
                zfa_fail += 1
            if balanced(h):
                f = fold_scalar(img)
                folds.add(f)
                if f != fold_scalar(h):
                    fold_fail += 1
        out[f"k={k}"] = {"zfa_failures": zfa_fail, "fold_failures": fold_fail,
                         "folds_on_balanced": sorted(str(f) for f in folds)}
    return out


def w3(max_len: int) -> dict:
    out = {}
    for L in range(2, max_len + 1, 2):
        hs = balanced_histories(L)
        good = [k for k in itertools.product((1, 2, 3), repeat=L)
                if all(_weighted_balanced(h, k) for h in hs)]
        out[f"L={L}"] = {"fields": 3 ** L, "preserving": len(good),
                         "all_constant": all(len(set(k)) == 1 for k in good)}
    return out


def _weighted_balanced(h, k) -> bool:
    c = Counter()
    for t, kp in zip(h, k):
        c[t] += kp
    return all(c[t] == c[CONJ[t]] for t in AX)


def w4() -> dict:
    F = frames()
    ident = {t: t for t in AX}
    hs = balanced_histories(4)
    out = {}
    for i, j in itertools.combinations(range(4), 2):
        # cheap witnesses first: t at i, conj t at j, gauge pair elsewhere
        others = [p for p in range(4) if p not in (i, j)]
        wit = []
        for t in AX:
            w = [None] * 4
            w[i], w[j] = t, CONJ[t]
            w[others[0]], w[others[1]] = "+", "-"
            wit.append("".join(w))
        survivors = []
        for a, b in itertools.product(range(len(F)), repeat=2):
            sig = [ident] * 4
            sig[i], sig[j] = F[a], F[b]
            if all(balanced(apply(h, sig, [1] * 4)) for h in wit):
                if all(balanced(apply(h, sig, [1] * 4)) for h in hs):
                    survivors.append((a, b))
        out[f"({i},{j})"] = {"pairs": len(F) ** 2, "preserving": len(survivors),
                             "all_equal": all(F[a] == F[b] for a, b in survivors)}
    return out


def w5(max_len: int) -> dict:
    F = frames()
    hs = [h for L in range(2, max_len + 1, 2) for h in balanced_histories(L)]
    base = {h: fold_scalar(h) for h in hs}
    keep = [s for s in F if all(fold_scalar("".join(s[t] for t in h)) == base[h] for h in hs)]
    gauge_fixed = sum(1 for s in keep if s["+"] in "+-")
    return {"frames": len(F), "balanced_histories": len(hs), "fold_preserving": len(keep),
            "of_which_keep_gauge_axis": gauge_fixed}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--max-len", type=int, default=6)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = {"W1_W2": w1_w2(a.max_len), "W3": w3(a.max_len), "W4": w4(), "W5": w5(a.max_len)}
    for k, v in r["W1_W2"].items():
        print(f"dilation {k}: ZFA failures {v['zfa_failures']}, fold failures {v['fold_failures']}, folds on balanced {v['folds_on_balanced']}")
    for k, v in r["W3"].items():
        print(f"W3 {k}: {v['preserving']} of {v['fields']} scale fields preserve ZFA; all constant: {v['all_constant']}")
    for k, v in r["W4"].items():
        print(f"W4 positions {k}: {v['preserving']} of {v['pairs']} frame pairs preserve ZFA; all equal: {v['all_equal']}")
    print(f"W5: {r['W5']['fold_preserving']} of {r['W5']['frames']} global frames preserve the fold on "
          f"{r['W5']['balanced_histories']} balanced histories ({r['W5']['of_which_keep_gauge_axis']} keep the gauge axis)")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
