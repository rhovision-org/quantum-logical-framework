#!/usr/bin/env python3
"""gluon_abelian_control.py -- does the non-Abelian vertex do work on singlet distance? (#286)

Part of the Quantum Logical Framework (QLF); see README.md. The tests A1-A5 and the verdict rule
are pre-registered in Gluon_Abelian_Control.md section 1, committed before this script existed.

The gated relation is PR #289's two vertex channels on multisets of nonzero F3^2 colour labels
(create: add p = -(q + r); glue: replace q, r by p), with q, r non-collinear. The Abelian control
drops the gate and keeps every pair with q + r != 0. States, singlet predicate and search bound
are #289's. This file re-implements them so that it runs without that branch.

    python3 gluon_abelian_control.py
    python3 gluon_abelian_control.py --json data/gluon_abelian_control.json
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict, deque
from itertools import combinations, combinations_with_replacement

MAX_STATE_SIZE = 4
MAX_SEARCH_SIZE = 5
LABELS = tuple((a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0))


def add(u, v):
    return ((u[0] + v[0]) % 3, (u[1] + v[1]) % 3)


def neg(u):
    return ((-u[0]) % 3, (-u[1]) % 3)


def symp(u, v):
    return (u[0] * v[1] - u[1] * v[0]) % 3


def total(s):
    t = (0, 0)
    for c in s:
        t = add(t, c)
    return t


def singlet(s) -> bool:
    return total(s) == (0, 0)


def pairs(s, gated: bool):
    out = []
    for i, j in combinations(range(len(s)), 2):
        q, r = s[i], s[j]
        if add(q, r) == (0, 0):
            continue                     # p would be 0, not a label
        if gated and symp(q, r) == 0:
            continue
        out.append((q, r, neg(add(q, r))))
    return out


def moves(s, gated: bool) -> dict:
    create, glue = set(), set()
    for q, r, p in pairs(s, gated):
        create.add(tuple(sorted(s + (p,))))
        rest = list(s)
        rest.remove(q)
        rest.remove(r)
        rest.append(p)
        glue.add(tuple(sorted(rest)))
    return {"create": create, "glue": glue}


def distance(s, gated: bool, legacy: bool = False):
    """Shortest path to a singlet through states of size <= MAX_SEARCH_SIZE.

    legacy=True reproduces PR #289's search, which expands no state of size MAX_SEARCH_SIZE (so a
    size-5 state cannot glue back to size 4). The default allows every move whose result has size
    <= MAX_SEARCH_SIZE, which is the pre-registered bound.
    """
    if singlet(s):
        return 0
    seen, queue = {s: 0}, deque([s])
    while queue:
        cur = queue.popleft()
        if legacy and len(cur) >= MAX_SEARCH_SIZE:
            continue
        for nxts in moves(cur, gated).values():
            for n in nxts:
                if n in seen or len(n) > MAX_SEARCH_SIZE:
                    continue
                seen[n] = seen[cur] + 1
                if singlet(n):
                    return seen[n]
                queue.append(n)
    return None


def states():
    return [s for n in range(1, MAX_STATE_SIZE + 1) for s in combinations_with_replacement(LABELS, n)]


def census(gated: bool, legacy: bool = False) -> dict:
    ss = states()
    d = {s: distance(s, gated, legacy) for s in ss}
    cls = {"create": Counter(), "glue": Counter()}
    first = Counter()
    for s in ss:
        if d[s] is None:
            continue
        for kind, nxts in moves(s, gated).items():
            for n in nxts:
                dn = 0 if singlet(n) else (d[n] if n in d else distance(n, gated, legacy))
                c = ("blocked" if dn is None else "reducing" if dn < d[s]
                     else "neutral" if dn == d[s] else "increasing")
                cls[kind][c] += 1
                if singlet(n) and not singlet(s):
                    first[c] += 1
    return {"d": d, "classes": {k: dict(v) for k, v in cls.items()}, "first_singlet": dict(first)}


def run(legacy: bool = False) -> dict:
    g, a = census(True, legacy), census(False, legacy)
    ss = states()
    # A2: is gated d a function of (total, size)?
    by_key = defaultdict(set)
    for s in ss:
        by_key[(total(s), len(s))].add(g["d"][s])
    a2_split = sum(1 for v in by_key.values() if len(v) > 1)
    diff_d = [s for s in ss if g["d"][s] != a["d"][s]]
    diff_dist = [s for s in diff_d if g["d"][s] is not None and a["d"][s] is not None]
    diff_reach = [s for s in diff_d if (g["d"][s] is None) != (a["d"][s] is None)]
    reach_all_collinear = all(not pairs(s, True) for s in diff_reach)
    return {
        "search": "legacy #289 (no expansion of size-5 states)" if legacy else "pre-registered (results of size <= 5)",
        "states": len(ss),
        "gated": {"with_path": sum(v is not None for v in g["d"].values()),
                  "distance_counts": dict(Counter(str(v) for v in g["d"].values())),
                  "classes": g["classes"], "first_singlet": g["first_singlet"]},
        "abelian": {"with_path": sum(v is not None for v in a["d"].values()),
                    "distance_counts": dict(Counter(str(v) for v in a["d"].values())),
                    "classes": a["classes"], "first_singlet": a["first_singlet"]},
        "A1_first_singlet_nonreducing": {"gated": sum(v for k, v in g["first_singlet"].items() if k != "reducing"),
                                         "abelian": sum(v for k, v in a["first_singlet"].items() if k != "reducing")},
        "A2_keys": len(by_key), "A2_keys_with_several_distances": a2_split,
        "A3_states_with_different_distance": len(diff_dist),
        "A3_examples": [{"state": s, "gated": g["d"][s], "abelian": a["d"][s]} for s in diff_dist[:5]],
        "A4_states_with_different_reachability": len(diff_reach),
        "A4_all_have_no_noncollinear_pair": reach_all_collinear,
        "A4_examples": [{"state": s, "gated": g["d"][s], "abelian": a["d"][s]} for s in diff_reach[:5]],
        "A5_classes_differ": g["classes"] != a["classes"],
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    r = run()
    print(f"{r['states']} states; with a singlet path: gated {r['gated']['with_path']}, Abelian {r['abelian']['with_path']}")
    print(f"  gated classes   {r['gated']['classes']}")
    print(f"  Abelian classes {r['abelian']['classes']}")
    print(f"A1 non-reducing first-singlet moves: {r['A1_first_singlet_nonreducing']}")
    print(f"A2 (total, size) keys with several gated distances: {r['A2_keys_with_several_distances']} of {r['A2_keys']}")
    print(f"A3 states whose distance changes with the gate: {r['A3_states_with_different_distance']}  e.g. {r['A3_examples'][:2]}")
    print(f"A4 states whose reachability changes: {r['A4_states_with_different_reachability']}"
          f" (all without a non-collinear pair: {r['A4_all_have_no_noncollinear_pair']})  e.g. {r['A4_examples'][:2]}")
    print(f"A5 move classes differ: {r['A5_classes_differ']}")
    leg = run(legacy=True)
    print(f"legacy #289 search: gated classes {leg['gated']['classes']}; A3 {leg['A3_states_with_different_distance']}, A4 {leg['A4_states_with_different_reachability']}")
    if args.json:
        out = {"preregistered": r, "legacy_289_search": leg}
        with open(args.json, "w") as f:
            json.dump(out, f, indent=2, sort_keys=True, default=list)
            f.write("\n")


if __name__ == "__main__":
    main()
