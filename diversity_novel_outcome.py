#!/usr/bin/env python3
"""diversity_novel_outcome.py -- does complementary composition create a closure type? (#290 E1)

Part of the Quantum Logical Framework (QLF); see README.md. The tests N1-N5 and the verdict rule
are pre-registered in Diversity_Novel_Outcome_E1.md section 1, committed before this script existed.

A closed (count-balanced) history has type +I or -I, its Pauli fold. Composition is concatenation.
Homogeneous generators are pairs (a, a); complementary ones are open pairs whose nets cancel.

    python3 diversity_novel_outcome.py
    python3 diversity_novel_outcome.py --json data/diversity_novel_outcome.json
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter

import twist_core

AXIS = {"+": 0, "-": 0, ">": 1, "<": 1, "^": 2, "v": 2, "/": 3, "\\": 3}
SIGN = {"+": 1, "-": -1, ">": 1, "<": -1, "^": 1, "v": -1, "/": 1, "\\": -1}


def net(h: str) -> tuple:
    v = [0, 0, 0, 0]
    for t in h:
        v[AXIS[t]] += SIGN[t]
    return tuple(v)


def closed(h: str) -> bool:
    return net(h) == (0, 0, 0, 0)


def ctype(h: str) -> str:
    """The type of a closed history: its fold, +I or -I."""
    if not h:
        return "+I"
    a, b, c, d = twist_core.pauli_fold(h)
    assert abs(b) < 1e-9 and abs(c) < 1e-9 and abs(a - d) < 1e-9 and abs(a.imag) < 1e-9
    return "+I" if a.real > 0 else "-I"


def words(lo: int, hi: int):
    for n in range(lo, hi + 1):
        for w in itertools.product(twist_core.TWISTS, repeat=n):
            yield "".join(w)


def run() -> dict:
    n1 = sum(1 for a in words(1, 4) if not closed(a) and closed(a + a))
    n2_types = Counter(ctype(a + a) for a in words(0, 6) if closed(a))
    wit_a, wit_b = "^<", "v>"
    n3 = {"a": wit_a, "b": wit_b, "a_open": not closed(wit_a), "b_open": not closed(wit_b),
          "type": ctype(wit_a + wit_b) if closed(wit_a + wit_b) else None}
    opens = [a for a in words(1, 3) if not closed(a)]
    by_net: dict = {}
    for b in opens:
        by_net.setdefault(net(b), []).append(b)
    n5: Counter = Counter()
    for a in opens:
        need = tuple(-x for x in net(a))
        for b in by_net.get(need, []):
            n5[ctype(a + b)] += 1
    hom = set(n2_types)                      # N1: no open a contributes
    mixed = set(n5) | ({n3["type"]} if n3["type"] else set())
    return {
        "N1_open_self_closures": n1,
        "N2_closed_self_types": dict(n2_types),
        "N3_witness": n3,
        "N5_open_pair_types": dict(n5),
        "N_hom": sorted(hom), "N_mixed": sorted(mixed),
        "pass": {"N1": n1 == 0, "N2": set(n2_types) == {"+I"},
                 "N3": n3["a_open"] and n3["b_open"] and n3["type"] == "-I"},
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = run()
    p = r["pass"]
    print(f"N1 open a with a++a closed (|a| <= 4):      {r['N1_open_self_closures']}  {'PASS' if p['N1'] else 'FAIL'}")
    print(f"N2 types of a++a, closed a (|a| <= 6):      {r['N2_closed_self_types']}  {'PASS' if p['N2'] else 'FAIL'}")
    w = r["N3_witness"]
    print(f"N3 {w['a']} ++ {w['b']}: open/open = {w['a_open']}/{w['b_open']}, type {w['type']}  {'PASS' if p['N3'] else 'FAIL'}")
    print(f"N5 closing open pairs, |a|,|b| <= 3:         {r['N5_open_pair_types']}")
    print(f"N_hom = {r['N_hom']}, N_mixed = {r['N_mixed']}: E1 {'holds' if all(p.values()) else 'fails'} on this relation")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
