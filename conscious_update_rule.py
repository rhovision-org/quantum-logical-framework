#!/usr/bin/env python3
"""conscious_update_rule.py -- which update rule gives the receiver regime? (#278)

Part of the Quantum Logical Framework (QLF); see README.md. The tests C1-C4 and the verdict rule
are pre-registered in Conscious_Update_Rule.md section 1, committed before this script existed.

Eligible candidates from PR #279's table; the next expression is the least remaining distance d
(ties by the declared order); U_ind resets only the winner, U_res resets everyone.

    python3 conscious_update_rule.py
    python3 conscious_update_rule.py --json data/conscious_update_rule.json
"""

from __future__ import annotations

import argparse
import json
from collections import Counter

ORDER = ("percept", "thought", "feeling", "external")
PERIODS = {"percept": 2, "thought": 5, "feeling": 7, "external": 8}
INTERNAL = {"percept", "thought", "feeling"}
H = 840


def periods(q: int) -> dict:
    return {k: (T * q if k in INTERNAL else T) for k, T in PERIODS.items()}


def race(rule: str, q: int = 1, horizon: int = H) -> Counter:
    T = periods(q)
    d = dict(T)
    t = 0
    counts: Counter = Counter()
    while True:
        win = min(ORDER, key=lambda k: (d[k], ORDER.index(k)))
        step = d[win]
        if t + step > horizon:
            return counts
        t += step
        counts[win] += 1
        if rule == "ind":
            for k in ORDER:
                d[k] -= step
            d[win] = T[win]
        elif rule == "res":
            d = dict(T)
        else:
            raise ValueError(rule)


def run() -> dict:
    out = {"H": H, "periods": PERIODS, "ind": {}, "res": {}}
    for q in range(1, 7):
        out["ind"][q] = dict(race("ind", q))
        out["res"][q] = dict(race("res", q))
    ind1, res1 = out["ind"][1], out["res"][1]
    c1 = all(ind1.get(k, 0) == H // PERIODS[k] for k in ORDER)
    c2 = set(res1) == {"percept"}
    c3 = all((set(out["res"][q]) == {"external"}) == (2 * q > 8)
             and (("external" in out["res"][q]) == (2 * q > 8)) for q in range(1, 7))
    c4 = len({out["ind"][q].get("external", 0) for q in range(1, 7)}) == 1 and \
        out["ind"][1].get("external", 0) == H // 8
    out["pass"] = {"C1": c1, "C2": c2, "C3": c3, "C4": c4}
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = run()
    for q in range(1, 7):
        print(f"q={q}:  U_ind {r['ind'][q]}")
        print(f"       U_res {r['res'][q]}")
    print(f"pass: {r['pass']}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
