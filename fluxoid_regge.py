#!/usr/bin/env python3
"""fluxoid_regge.py -- the #301 milestone-1 toy model, run against its pre-registered kill conditions.

Part of the Quantum Logical Framework (QLF); see README.md. The kill conditions K1-K7 and the
verdict rule are in Continuum_Limit.md section 1, committed before this script existed.

Complex: the periodic L x L lattice, each square split by its (+1,+1) diagonal.
History:  a twist word on two axes ('>' '<' on x, '^' 'v' on y), read as a walk from the origin.
Labeling A (current): n_e = net signed crossings of edge e (QLF_LinkClosure.walkCurrent).
Labeling B (axis):    n_e = the action-vector component of e's axis.
Lengths:  l_e = l_ref(e) * g(|n_e|), l_ref = 1 (axis edges), sqrt 2 (diagonals).
Regge:    deficit at v = 2 pi - (sum of triangle angles at v), angles by the law of cosines.

Exact integer / Fraction arithmetic everywhere except the angles, which are floats compared to
a 1e-9 tolerance.

    python3 fluxoid_regge.py            # default: L = 10, words up to length 8
    python3 fluxoid_regge.py --max-len 6 --json data/fluxoid_regge.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import defaultdict
from fractions import Fraction

STEPS = {">": (0, +1), "<": (0, -1), "^": (1, +1), "v": (1, -1)}
LENGTH_MAPS = {
    "1+m/4": lambda m: 1 + m / 4,
    "1+m/2": lambda m: 1 + m / 2,
    "1+m": lambda m: 1 + m,
    "sqrt(1+m)": lambda m: math.sqrt(1 + m),
}
TOL = 1e-9


# --------------------------------------------------------------------------- the complex

def walk_current(word: str, L: int) -> dict:
    """Net signed crossings per axis edge. Key (axis, i, j): edge from (i,j) along +axis."""
    cur: dict = defaultdict(int)
    p = [0, 0]
    for t in word:
        a, s = STEPS[t]
        if s > 0:
            cur[(a, p[0], p[1])] += 1
            p[a] = (p[a] + 1) % L
        else:
            p[a] = (p[a] - 1) % L
            cur[(a, p[0], p[1])] -= 1
    return {k: v for k, v in cur.items() if v != 0}


def action_vector(word: str) -> tuple:
    v = [0, 0]
    for t in word:
        a, s = STEPS[t]
        v[a] += s
    return tuple(v)


def triangles(L: int):
    """Each square (i,j) gives T1 = (i,j),(i+1,j),(i+1,j+1) and T2 = (i,j),(i+1,j+1),(i,j+1).
    Edges as (kind, i, j): kind 0 = x-edge, 1 = y-edge, 2 = diagonal; with orientation signs for
    the counterclockwise boundary."""
    for i in range(L):
        for j in range(L):
            i1, j1 = (i + 1) % L, (j + 1) % L
            yield (((i, j), (i1, j), (i1, j1)),
                   [((0, i, j), +1), ((1, i1, j), +1), ((2, i, j), -1)])
            yield (((i, j), (i1, j1), (i, j1)),
                   [((2, i, j), +1), ((0, i, j1), -1), ((1, i, j), -1)])


def face_obligations(labels: dict, L: int) -> list:
    return [sum(s * labels.get(e, 0) for e, s in edges) for _, edges in triangles(L)]


def deficits(labels: dict, L: int, g) -> list | None:
    """Vertex deficits, or None if some triangle violates the triangle inequality."""
    def length(e):
        base = math.sqrt(2) if e[0] == 2 else 1.0
        return base * g(abs(labels.get(e, 0)))

    angle_sum: dict = defaultdict(float)
    for verts, edges in triangles(L):
        a_e, b_e, c_e = (length(e) for e, _ in edges)
        # in both triangles the edges are listed as v0v1, v1v2, v0v2
        d01, d12, d02 = a_e, b_e, c_e
        sides = {0: d12, 1: d02, 2: d01}           # side opposite each vertex
        if not (d01 + d12 > d02 + TOL and d01 + d02 > d12 + TOL and d12 + d02 > d01 + TOL):
            return None
        for k, v in enumerate(verts):
            opp = sides[k]
            adj = [s for kk, s in sides.items() if kk != k]
            c = (adj[0] ** 2 + adj[1] ** 2 - opp ** 2) / (2 * adj[0] * adj[1])
            angle_sum[v] += math.acos(max(-1.0, min(1.0, c)))
    return [2 * math.pi - angle_sum[(i, j)] for i in range(L) for j in range(L)]


def axis_labels(word: str, L: int) -> dict:
    av = action_vector(word)
    return {(a, i, j): av[a] for a in (0, 1) for i in range(L) for j in range(L) if av[a] != 0}


def key_of(defs, digits=9):
    return None if defs is None else tuple(round(d, digits) + 0.0 for d in defs)


# --------------------------------------------------------------------------- smoothing (K5)

def binomial_smooth(cur: dict, L: int, N: int) -> dict:
    """Periodic tensor-product binomial (degree-N Bernstein weight) smoothing of each axis field."""
    w = [Fraction(math.comb(N, k), 2 ** N) for k in range(N + 1)]
    shifts = [k - N // 2 for k in range(N + 1)]
    out: dict = defaultdict(Fraction)
    for (a, i, j), v in cur.items():
        for (wx, dx), (wy, dy) in itertools.product(zip(w, shifts), repeat=2):
            out[(a, (i + dx) % L, (j + dy) % L)] += wx * wy * v
    return {k: v for k, v in out.items() if v != 0}


def divergence(cur: dict, L: int) -> dict:
    d: dict = defaultdict(Fraction)
    for (a, i, j), v in cur.items():
        q = [i, j]
        q[a] = (q[a] + 1) % L
        d[(i, j)] -= v      # flows out of the tail ...
        d[tuple(q)] += v    # ... into the head
    return {k: v for k, v in d.items() if v != 0}


# --------------------------------------------------------------------------- two-body order (K6)

def closure_events(proj: list) -> list:
    """Indices (in the body's own projection) at which its prefix count-balances."""
    s, out = 0, []
    for k, t in enumerate(proj, 1):
        s += 1 if t == "+" else -1
        if s == 0:
            out.append(k)
    return out


def two_body_check(max_len: int) -> dict:
    """Step class = equal projections (Mazurkiewicz trace with A and B commuting)."""
    tokens = ["A+", "A-", "B+", "B-"]
    classes: dict = defaultdict(list)
    for n in range(max_len + 1):
        for w in itertools.product(tokens, repeat=n):
            pa = tuple(t[1] for t in w if t[0] == "A")
            pb = tuple(t[1] for t in w if t[0] == "B")
            classes[(pa, pb)].append(w)
    per_body_violations = 0
    total_order_varies = 0
    with_both = 0
    for (pa, pb), ws in classes.items():
        ref = (closure_events(list(pa)), closure_events(list(pb)))
        orders = set()
        for w in ws:
            a_seen = [t[1] for t in w if t[0] == "A"]
            b_seen = [t[1] for t in w if t[0] == "B"]
            if (closure_events(a_seen), closure_events(b_seen)) != ref:
                per_body_violations += 1
            # the merged sequence of closure events, labelled by body
            sa = sb = ca = cb = 0
            seq = []
            for t in w:
                if t[0] == "A":
                    ca += 1; sa += 1 if t[1] == "+" else -1
                    if sa == 0: seq.append("A")
                else:
                    cb += 1; sb += 1 if t[1] == "+" else -1
                    if sb == 0: seq.append("B")
            orders.add(tuple(seq))
        if ref[0] and ref[1]:
            with_both += 1
            if len(orders) > 1:
                total_order_varies += 1
    return {
        "classes": len(classes),
        "per_body_order_violations": per_body_violations,
        "classes_with_closures_in_both_bodies": with_both,
        "of_those_cross_body_order_varies": total_order_varies,
    }


# --------------------------------------------------------------------------- the run

def run(L: int, max_len: int, smooth_degrees=(2, 4)) -> dict:
    words = ["".join(w) for n in range(max_len + 1) for w in itertools.product(STEPS, repeat=n)]
    closed = [w for w in words if action_vector(w) == (0, 0)]

    # Gauss-Bonnet code check on the reference geometry and on a few labelled ones.
    ref = deficits({}, L, LENGTH_MAPS["1+m"])
    assert ref is not None and all(abs(d) < TOL for d in ref), "reference lattice must be flat"

    res: dict = {"L": L, "max_len": max_len, "histories": len(words), "closed": len(closed)}

    # K1: face identity on closed histories
    k1_bad = [w for w in closed if any(face_obligations(walk_current(w, L), L))]
    res["K1_closed_with_nonzero_face_obligation"] = len(k1_bad)
    res["K1_example"] = min(k1_bad, key=len) if k1_bad else None

    # K2, K3, K4 per length map, labeling A
    per_map = {}
    for name, g in LENGTH_MAPS.items():
        by_class: dict = defaultdict(set)
        flat_closed, curved_closed, undefined_closed = set(), 0, 0
        gb_max = 0.0
        undefined_all = 0
        for w in words:
            d = deficits(walk_current(w, L), L, g)
            if d is None:
                undefined_all += 1
            else:
                gb_max = max(gb_max, abs(sum(d)))
            by_class[action_vector(w)].add(key_of(d))
            if action_vector(w) == (0, 0):
                if d is None:
                    undefined_closed += 1
                elif all(abs(x) < TOL for x in d):
                    flat_closed.add(w)
                else:
                    curved_closed += 1
        multi = {c: len(s) for c, s in by_class.items() if len(s) > 1}
        per_map[name] = {
            "closed_flat": len(flat_closed),
            "closed_curved": curved_closed,
            "closed_undefined": undefined_closed,
            "all_undefined": undefined_all,
            "gauss_bonnet_max_abs_sum": gb_max,
            "classes": len(by_class),
            "classes_with_more_than_one_geometry": len(multi),
            "geometries_in_closed_class": len(by_class[(0, 0)]),
            "_flat_set": flat_closed,
        }
    flat_sets = [v.pop("_flat_set") for v in per_map.values()]
    res["labeling_A"] = per_map
    res["K4_flat_set_identical_across_maps"] = all(s == flat_sets[0] for s in flat_sets)
    res["K4_flat_closed_histories"] = sorted(flat_sets[0], key=lambda w: (len(w), w))[:12]
    # are the flat closed histories exactly those with zero current (retraced walks)?
    zero_current = {w for w in closed if not walk_current(w, L)}
    res["K2_flat_iff_zero_current"] = all(s == zero_current for s in flat_sets)
    res["closed_with_zero_current"] = len(zero_current)

    # K5: smoothing
    k5 = {}
    for N in smooth_degrees:
        commute_fail = closed_div_changed = open_div_changed = integral_kept = 0
        face_commute_fail = 0
        for w in words:
            cur = walk_current(w, L)
            sm = binomial_smooth(cur, L, N)
            div0 = divergence({k: Fraction(v) for k, v in cur.items()}, L)
            div1 = divergence(sm, L)
            # smoothed divergence must equal the smoothing of the (scalar) divergence field
            smdiv: dict = defaultdict(Fraction)
            wts = [Fraction(math.comb(N, k), 2 ** N) for k in range(N + 1)]
            sh = [k - N // 2 for k in range(N + 1)]
            for (i, j), v in div0.items():
                for (wx, dx), (wy, dy) in itertools.product(zip(wts, sh), repeat=2):
                    smdiv[((i + dx) % L, (j + dy) % L)] += wx * wy * v
            smdiv = {k: v for k, v in smdiv.items() if v != 0}
            if smdiv != div1:
                commute_fail += 1
            if div1 != div0:
                if action_vector(w) == (0, 0):
                    closed_div_changed += 1
                else:
                    open_div_changed += 1
            if all(v.denominator == 1 for v in sm.values()) and cur:
                integral_kept += 1
        k5[f"N={N}"] = {
            "div_commutes_with_smoothing_failures": commute_fail,
            "closed_histories_div_changed": closed_div_changed,
            "open_histories_div_changed": open_div_changed,
            "nonzero_currents_still_integral": integral_kept,
        }
    res["K5"] = k5

    # K6
    res["K6"] = two_body_check(min(max_len, 8))

    # K7: labeling B
    geoms = {key_of(deficits(axis_labels(w, L), L, LENGTH_MAPS["1+m"])) for w in closed}
    res["K7_labeling_B_geometries_on_closed"] = len(geoms)
    return res


def verdict(r: dict) -> list:
    A = r["labeling_A"]
    lines = []
    lines.append(f"K1 ZFA = face identity:     {'PASS' if r['K1_closed_with_nonzero_face_obligation'] == 0 else 'FAIL'}"
                 f"  ({r['K1_closed_with_nonzero_face_obligation']} of {r['closed']} closed histories have dF != 0; e.g. {r['K1_example']!r})")
    k2 = all(v["closed_curved"] == 0 and v["closed_undefined"] == 0 for v in A.values())
    lines.append(f"K2 ZFA => Regge flat:       {'PASS' if k2 else 'FAIL'}"
                 + "".join(f"\n     g={n}: flat {v['closed_flat']}, curved {v['closed_curved']}, undefined {v['closed_undefined']}"
                           for n, v in A.items()))
    k3 = all(v["classes_with_more_than_one_geometry"] == 0 for v in A.values())
    lines.append(f"K3 geometry is a class fn:  {'PASS' if k3 else 'FAIL'}"
                 + "".join(f"\n     g={n}: {v['classes_with_more_than_one_geometry']} of {v['classes']} classes split; closed class holds {v['geometries_in_closed_class']} geometries"
                           for n, v in A.items()))
    lines.append(f"K4 no free parameters:      {'PASS' if r['K4_flat_set_identical_across_maps'] else 'FAIL'}"
                 f"  (flat set identical across the four maps; flat iff zero current: {r['K2_flat_iff_zero_current']})")
    k5 = all(v["div_commutes_with_smoothing_failures"] == 0 and v["closed_histories_div_changed"] == 0 for v in r["K5"].values())
    lines.append(f"K5 smoothing keeps div = 0: {'PASS' if k5 else 'FAIL'}"
                 + "".join(f"\n     {n}: commute failures {v['div_commutes_with_smoothing_failures']}, closed changed {v['closed_histories_div_changed']},"
                           f" open smeared {v['open_histories_div_changed']}, still integral {v['nonzero_currents_still_integral']}"
                           for n, v in r["K5"].items()))
    k6 = r["K6"]
    lines.append(f"K6 per-body order invariant:{'PASS' if k6['per_body_order_violations'] == 0 else 'FAIL'}"
                 f"  ({k6['classes']} Step classes; cross-body order varies in {k6['of_those_cross_body_order_varies']}"
                 f" of {k6['classes_with_closures_in_both_bodies']} with closures in both bodies)")
    lines.append(f"K7 labeling B has content:  {'PASS' if r['K7_labeling_B_geometries_on_closed'] > 1 else 'FAIL'}"
                 f"  ({r['K7_labeling_B_geometries_on_closed']} geometry over all closed histories)")
    gb = max(v["gauss_bonnet_max_abs_sum"] for v in A.values())
    lines.append(f"code check: Gauss-Bonnet |sum of deficits| <= {gb:.1e} on the torus")
    return lines


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--L", type=int, default=10)
    ap.add_argument("--max-len", type=int, default=8)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = run(a.L, a.max_len)
    print(f"L = {r['L']}, words up to length {r['max_len']}: {r['histories']} histories, {r['closed']} closed")
    for line in verdict(r):
        print(line)
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
