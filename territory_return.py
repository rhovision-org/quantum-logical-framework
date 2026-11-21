#!/usr/bin/env python3
"""territory_return.py -- does the joint-closure record return ZFA? (#213, M1-M4)

Part of the Quantum Logical Framework (QLF); see README.md. The tests M1-M4 and the verdict rule
are pre-registered in Map_Is_Territory.md section 3a, committed before this script existed.

Two-body histories are words over the 16 tokens (body, twist). The record is the joint fold
foldA (x) foldB, which by QLF_ObservationalEquivalence is exactly what joint closure tests with
phase can distinguish. ZFA for a two-body history: each body's projection is count-balanced.
The ledger: each body's signed action vector in Z^4.

    python3 territory_return.py                # every history of length <= 4
    python3 territory_return.py --max-len 5 --json data/territory_return.json
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import defaultdict

import twist_core

AXIS = {"+": 0, "-": 0, ">": 1, "<": 1, "^": 2, "v": 2, "/": 3, "\\": 3}
SIGN = {"+": 1, "-": -1, ">": 1, "<": -1, "^": 1, "v": -1, "/": 1, "\\": -1}
# Pauli representatives, (a, b, c, d) row-major: I, X, Y, Z
SIGMA = {"I": (1, 0, 0, 1), "X": (0, 1, 1, 0), "Y": (0, -1j, 1j, 0), "Z": (1, 0, 0, -1)}
TOL = 1e-9


def ledger(proj: str) -> tuple:
    v = [0, 0, 0, 0]
    for t in proj:
        v[AXIS[t]] += SIGN[t]
    return tuple(v)


def balanced(proj: str) -> bool:
    return ledger(proj) == (0, 0, 0, 0)


def klein_from_parity(proj: str) -> str:
    """The Klein class of the spatial count parities, (px, py, pz) modulo (1, 1, 1)."""
    p = [sum(1 for t in proj if AXIS[t] == a) % 2 for a in (1, 2, 3)]
    if p[0] == p[1] == p[2]:
        return "I"
    # the odd-one-out axis names the class: (1,0,0) ~ (0,1,1) -> X, etc.
    for a, name in zip(range(3), "XYZ"):
        others = [p[b] for b in range(3) if b != a]
        if others[0] == others[1] != p[a]:
            return name
    raise AssertionError(p)


def decompose(m) -> tuple:
    """Write a fold as phase * sigma_K; return (K, phase)."""
    for k, s in SIGMA.items():
        idx = next(i for i in range(4) if s[i] != 0)
        a = m[idx] / s[idx]
        if all(abs(m[i] - a * s[i]) < TOL for i in range(4)):
            return k, complex(round(a.real), round(a.imag))
    raise AssertionError(m)


def kron_key(ma, mb) -> tuple:
    A = [[ma[0], ma[1]], [ma[2], ma[3]]]
    B = [[mb[0], mb[1]], [mb[2], mb[3]]]
    out = []
    for i, j, k, l in itertools.product(range(2), repeat=4):
        z = A[i][k] * B[j][l]
        out.append((round(z.real, 9) + 0.0, round(z.imag, 9) + 0.0))
    return tuple(out)


def fold(proj: str) -> tuple:
    """The Pauli fold; the empty history folds to I."""
    return twist_core.pauli_fold(proj) if proj else (1 + 0j, 0j, 0j, 1 + 0j)


def run(max_len: int) -> dict:
    tokens = [(b, t) for b in "AB" for t in twist_core.TWISTS]
    classes: dict = defaultdict(list)
    meta = {}
    parity_mismatch = 0
    total = 0
    for n in range(max_len + 1):
        for w in itertools.product(tokens, repeat=n):
            total += 1
            pa = "".join(t for b, t in w if b == "A")
            pb = "".join(t for b, t in w if b == "B")
            fa, fb = fold(pa), fold(pb)
            (ka, a), (kb, b) = decompose(fa), decompose(fb)
            if ka != klein_from_parity(pa) or kb != klein_from_parity(pb):
                parity_mismatch += 1
            key = kron_key(fa, fb)
            zfa = balanced(pa) and balanced(pb)
            classes[key].append((zfa, ledger(pa), ledger(pb), len(w)))
            meta.setdefault(key, set()).add((ka, kb, a * b))

    m1_mixed = [k for k, v in classes.items() if {z for z, *_ in v} == {True, False}]
    with_zfa = [k for k, v in classes.items() if any(z for z, *_ in v)]
    # M2: class <-> (K_A, K_B, phase) one-to-one
    invariant_per_class_ok = all(len(s) == 1 for s in meta.values())
    inv_to_class = defaultdict(set)
    for k, s in meta.items():
        inv_to_class[next(iter(s))].add(k)
    class_per_invariant_ok = all(len(s) == 1 for s in inv_to_class.values())
    # M3: ZFA is a function of the ledger
    by_ledger: dict = defaultdict(set)
    for v in classes.values():
        for z, la, lb, _ in v:
            by_ledger[(la, lb)].add(z)
    m3_ok = all(len(s) == 1 for s in by_ledger.values())
    # M4: inside classes holding a ZFA history, how many members are not ZFA
    m4 = {}
    for k in with_zfa:
        v = classes[k]
        inv = next(iter(meta[k]))
        m4[f"K_A={inv[0]},K_B={inv[1]},phase={inv[2].real:+.0f}{inv[2].imag:+.0f}i"] = {
            "members": len(v), "zfa": sum(1 for z, *_ in v if z),
            "non_zfa": sum(1 for z, *_ in v if not z),
            "shortest_non_zfa_len": min((n for z, *_, n in v if not z), default=None),
            "distinct_ledgers": len({(la, lb) for _, la, lb, _ in v}),
        }
    return {
        "max_len": max_len, "histories": total, "classes": len(classes),
        "klein_parity_mismatches": parity_mismatch,
        "M1_classes_with_zfa": len(with_zfa), "M1_mixed_classes": len(m1_mixed),
        "M2_invariant_constant_on_classes": invariant_per_class_ok,
        "M2_invariant_separates_classes": class_per_invariant_ok,
        "M2_distinct_invariants": len(inv_to_class),
        "M3_zfa_function_of_ledger": m3_ok,
        "M4": m4,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--max-len", type=int, default=4)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = run(a.max_len)
    print(f"{r['histories']} two-body histories of length <= {r['max_len']}, {r['classes']} observational classes")
    print(f"M1 ZFA is a class function:   {'PASS' if r['M1_mixed_classes'] == 0 else 'FAIL'}"
          f"  ({r['M1_mixed_classes']} of the {r['M1_classes_with_zfa']} classes holding a ZFA history also hold non-ZFA ones)")
    m2 = r["M2_invariant_constant_on_classes"] and r["M2_invariant_separates_classes"] and r["klein_parity_mismatches"] == 0
    print(f"M2 class = (K_A, K_B, phase): {'PASS' if m2 else 'FAIL'}"
          f"  ({r['M2_distinct_invariants']} invariants; Klein class = parity class on every history: {r['klein_parity_mismatches'] == 0})")
    print(f"M3 ledger returns ZFA:        {'PASS' if r['M3_zfa_function_of_ledger'] else 'FAIL'}")
    print("M4 classes holding a ZFA history:")
    for k, v in r["M4"].items():
        print(f"   {k:<28} members {v['members']:>6}  ZFA {v['zfa']:>5}  non-ZFA {v['non_zfa']:>6}"
              f"  (shortest non-ZFA length {v['shortest_non_zfa_len']}, {v['distinct_ledgers']} ledgers)")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
