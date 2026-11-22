#!/usr/bin/env python3
"""spatial_response_derived.py -- #287 SR3 with both ledgers derived from the same twist steps.

Part of the Quantum Logical Framework (QLF); see README.md. Tests R1-R4 and the verdict rule are
pre-registered in Spatial_Response_Derived.md section 1, committed before this script existed.

Event (p, q): body A steps p, body B steps q (spatial twists only).
    Delta S = 2 e_p . e_q                      (QLF_MagneticOrientation joint-cost identity)
    Delta d = |r + e_p - e_q|_1 - |r|_1        (r = x_A - x_B, the integer ledger)
Exact integer / Fraction arithmetic throughout.

    python3 spatial_response_derived.py [--radius 4] [--json data/spatial_response_derived.json]
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import defaultdict
from fractions import Fraction

E = {">": (1, 0, 0), "<": (-1, 0, 0), "^": (0, 1, 0), "v": (0, -1, 0), "/": (0, 0, 1), "\\": (0, 0, -1)}


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def l1(a):
    return sum(abs(x) for x in a)


def delta_S(p: str, q: str) -> int:
    return 2 * dot(E[p], E[q])


def ball(R: int):
    rng = range(-R, R + 1)
    return [r for r in itertools.product(rng, rng, rng) if l1(r) <= R]


def run(R: int) -> dict:
    pts = ball(R)
    events = list(itertools.product(E, repeat=2))
    cls_name = {2: "like", -2: "opposite", 0: "orthogonal"}
    r1_bad = defaultdict(int)          # Delta d < 0 with Delta S >= 0, by class
    r2_total = r2_closer = r2_farther = r2_same = 0
    identity_fail = 0
    mean_sq = {}
    counts = defaultdict(lambda: defaultdict(int))
    for p, q in events:
        dS = delta_S(p, q)
        step = tuple(a - b for a, b in zip(E[p], E[q]))
        tot = Fraction(0)
        for r in pts:
            r2 = tuple(a + b for a, b in zip(r, step))
            dd = l1(r2) - l1(r)
            dsq = dot(r2, r2) - dot(r, r)
            if dsq != 2 * dot(r, step) + 2 - dS:
                identity_fail += 1
            tot += dsq
            sign = "closer" if dd < 0 else "farther" if dd > 0 else "same"
            counts[cls_name[dS]][sign] += 1
            if dd < 0 and dS >= 0:
                r1_bad[cls_name[dS]] += 1
            if dS < 0:
                r2_total += 1
                r2_closer += dd < 0
                r2_farther += dd > 0
                r2_same += dd == 0
        mean_sq[f"{p}{q}"] = (tot / len(pts), Fraction(2 - dS))
    r3_ok = all(m == want for m, want in mean_sq.values())
    by_class = defaultdict(set)
    for (pq, (m, _)) in mean_sq.items():
        by_class[cls_name[delta_S(pq[0], pq[1:])]].add(m)
    return {
        "radius": R, "sites": len(pts), "events": len(events),
        "R1_binding_events_with_dS_ge_0": dict(r1_bad),
        "R2_opposite_events": r2_total, "R2_closer": r2_closer, "R2_farther": r2_farther, "R2_same": r2_same,
        "R3_identity_failures": identity_fail, "R3_mean_equals_2_minus_dS": r3_ok,
        "R4_mean_growth_by_class": {k: [str(x) for x in sorted(v)] for k, v in by_class.items()},
        "separation_change_by_class": {k: dict(v) for k, v in counts.items()},
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--radius", type=int, default=4)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = run(a.radius)
    print(f"{r['events']} events x {r['sites']} sites (|r|_1 <= {r['radius']})")
    bad = r["R1_binding_events_with_dS_ge_0"]
    print(f"R1 Delta d < 0 => Delta S < 0:  {'PASS' if not bad else 'FAIL'}  (counterexamples by class: {bad})")
    print(f"R2 Delta S < 0 => Delta d < 0:  {'PASS' if r['R2_closer'] == r['R2_opposite_events'] else 'FAIL'}"
          f"  (opposite events: {r['R2_closer']} closer, {r['R2_farther']} farther, {r['R2_same']} same)")
    print(f"R3 mean Delta|r|^2 = 2 - Delta S: {'PASS' if r['R3_mean_equals_2_minus_dS'] and r['R3_identity_failures'] == 0 else 'FAIL'}"
          f"  (identity failures {r['R3_identity_failures']})")
    print(f"R4 mean separation growth by class: {r['R4_mean_growth_by_class']}")
    for k, v in r["separation_change_by_class"].items():
        print(f"   {k:<10} {v}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
