#!/usr/bin/env python3
"""Stage 2c of #301 milestone 2: sources that add ways, balancing, and the far field.

Pre-registration: ``Continuum_Limit.md`` section 8 (committed in 414d010, before this
file existed).  Results: ``Continuum_Limit.md`` section 9.

General finite-rank source: a step onto source site a has weight w_a, Lambda =
diag(1 - w_a), and for x, y outside S

    G'(x, y) = G(x, y) - g_x^T Lambda (I + (G_SS - I) Lambda)^-1 g_y.

Lengths l = 1/G' on axis edges; shell means of delta l / l at r = 2..10 from the
source centroid; ways charge Q = 1^T Lambda (I + (G_SS - I) Lambda)^-1 1 and the
monopole prediction Q gbar(u) gbar(v) / G(v - u).  Uses the cached Green's table of
``census_source.py`` (numpy only).
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import defaultdict
from pathlib import Path

import numpy as np

import census_source as cs

OUTPUT = Path("data/census_source_2c.json")
SHARED = 9 / 8
AXIS = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
NEIGH = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
SOURCES = {
    "share1": {(0, 0, 0): SHARED},
    "line4": {(0, k, 0): SHARED for k in range(4)},
    "plaq4": {(0, 0, 0): SHARED, (0, 1, 0): SHARED, (1, 1, 0): SHARED, (1, 0, 0): SHARED},
    "mixed": {(0, 0, 0): 0.0, **{n: SHARED for n in NEIGH}},
}
SHELLS = range(2, 11)


def analyse(G, name: str) -> dict[str, object]:
    src = SOURCES[name]
    S = list(src)
    lam = np.diag([1 - src[a] for a in S])
    GSS = np.array([[G[cs._key(np.subtract(a, b))] for b in S] for a in S])
    M = np.eye(len(S)) + (GSS - np.eye(len(S))) @ lam
    valid = abs(np.linalg.det(M)) > 1e-12
    K = lam @ np.linalg.inv(M)
    Q = float(np.ones(len(S)) @ K @ np.ones(len(S)))
    centre = tuple(sum(a[i] for a in S) / len(S) for i in range(3))
    gcache: dict = {}

    def gvec(x):
        if x not in gcache:
            gcache[x] = np.array([G[cs._key(np.subtract(x, a))] for a in S])
        return gcache[x]

    meas = defaultdict(list)
    pred = defaultdict(list)
    nonpos = 0
    Sset = set(S)
    H = cs.HALF
    for u in itertools.product(range(-H, H + 1), repeat=3):
        if u in Sset:
            continue
        for e in AXIS:
            v = tuple(a + b for a, b in zip(u, e))
            if v in Sset or max(abs(c) for c in v) > H:
                continue
            g0 = G[cs._key(e)]
            gp = g0 - float(gvec(u) @ K @ gvec(v))
            if gp <= 0:
                nonpos += 1
                continue
            dl = (1 / gp - 1 / g0) * g0
            r = math.dist([(a + b) / 2 for a, b in zip(u, v)], centre)
            sh = round(r)
            if sh in SHELLS:
                meas[sh].append(dl)
                pred[sh].append(Q * gvec(u).mean() * gvec(v).mean() / g0)
    shell = {str(r): sum(meas[r]) / len(meas[r]) for r in SHELLS}
    shell_pred = {str(r): sum(pred[r]) / len(pred[r]) for r in SHELLS}
    xs = [math.log(r) for r in range(4, 11)]
    ys = [math.log(abs(shell[str(r)])) for r in range(4, 11)]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    k = -sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    return {
        "Q": Q,
        "valid": bool(valid and nonpos == 0),
        "nonpositive_edges": nonpos,
        "shell_mean_dl_over_l": shell,
        "monopole_prediction": shell_pred,
        "ratio_measured_over_predicted": {r: shell[r] / shell_pred[r] for r in shell},
        "falloff_k": k,
    }


def build() -> dict[str, object]:
    G = cs.green_table(1)
    res = {name: analyse(G, name) for name in SOURCES}
    c1 = all(v < 0 for n in ("share1", "line4", "plaq4")
             for v in res[n]["shell_mean_dl_over_l"].values())
    c2 = all(0.85 <= res[n]["ratio_measured_over_predicted"][str(r)] <= 1.15
             for n in SOURCES for r in (8, 9, 10))
    a = res["line4"]["shell_mean_dl_over_l"]["10"] / res["line4"]["Q"]
    b = res["plaq4"]["shell_mean_dl_over_l"]["10"] / res["plaq4"]["Q"]
    c3 = abs(a - b) / abs((a + b) / 2) < 0.05
    mx = res["mixed"]["shell_mean_dl_over_l"]
    signs = [math.copysign(1, mx[str(r)]) for r in SHELLS]
    c4 = len(set(signs)) > 1 and signs[-1] == math.copysign(1, res["mixed"]["Q"])
    return {
        "prereg": "Continuum_Limit.md section 8 @ 414d010",
        "sources": res,
        "C1_adding_ways_contracts": c1,
        "C2_far_field_is_monopole": c2,
        "C3_shape_blind_far": c3,
        "C3_line_over_Q": a,
        "C3_plaq_over_Q": b,
        "C4_balancing_sign_change": c4,
        "all_valid": all(r["valid"] for r in res.values()),
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    args = p.parse_args()
    data = build()
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    for n, r in data["sources"].items():
        print(n, "Q=%.4f" % r["Q"], "valid", r["valid"], "k=%.3f" % r["falloff_k"],
              {k: "%.2e" % v for k, v in r["shell_mean_dl_over_l"].items()},
              {k: "%.3f" % v for k, v in r["ratio_measured_over_predicted"].items()})
    print({k: v for k, v in data.items() if k.startswith("C") or k == "all_valid"})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
