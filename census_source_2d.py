#!/usr/bin/env python3
"""Stage 2d of #301 milestone 2: geometry from joint closures with the source.

Pre-registration: ``Continuum_Limit.md`` section 10 (committed in abba91c, before this
file existed).  Results: ``Continuum_Limit.md`` section 11.

Joint-closure field phi(x) = 1^T K g_x, K = Lambda (I + (G_SS - I) Lambda)^-1.  Edge
length l = l0 (1 + lam (phi(u) + phi(v)) / 2), l0 = 1/G(v - u).  Measured: the curvature
change Delta K(R) = (1/lam) sum l0 (eps - eps0) over interior edges with midpoint within R.
Uses the cached Green's table of ``census_source.py`` (numpy only).
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import statistics
from collections import defaultdict
from pathlib import Path

import numpy as np

import census_geometry as cg
import census_source as cs
import census_source_2c as c2

OUTPUT = Path("data/census_source_2d.json")
LAM = 1e-3
RADII = (6, 8, 10)
SOURCES = dict(c2.SOURCES)
for _n in (1, 8, 27):
    SOURCES[f"excl{_n}"] = {tuple(a): 0.0 for a in cs.SOURCES[_n]}


def field(G, src):
    S = list(src)
    lam = np.diag([1 - src[a] for a in S])
    GSS = np.array([[G[cs._key(np.subtract(a, b))] for b in S] for a in S])
    K = lam @ np.linalg.inv(np.eye(len(S)) + (GSS - np.eye(len(S))) @ lam)
    Q = float(np.ones(len(S)) @ K @ np.ones(len(S)))
    w = np.ones(len(S)) @ K
    cache: dict = {}

    def phi(x):
        if x not in cache:
            cache[x] = float(w @ np.array([G[cs._key(np.subtract(x, a))] for a in S]))
        return cache[x]

    return Q, phi


def measure(G, name: str, lam: float = LAM) -> dict[str, object]:
    src = SOURCES[name]
    S = set(src)
    centre = tuple(sum(a[i] for a in src) / len(src) for i in range(3))
    Q, phi = field(G, src)
    ring = cs.ring_sizes()
    angle, angle0, count = defaultdict(float), defaultdict(float), defaultdict(int)
    touched, lengths = set(), {}
    degenerate = 0
    H = cs.HALF
    edges = list(itertools.combinations(range(4), 2))
    for base in itertools.product(range(-H, H), repeat=3):
        for tet in cg.cell_tetrahedra():
            verts = [tuple(b + t for b, t in zip(base, v)) for v in tet]
            keys = [tuple(sorted((verts[i], verts[j]))) for i, j in edges]
            if any(v in S for v in verts):
                touched.update(keys)
                continue
            d, d0 = {}, {}
            for e, k in zip(edges, keys):
                if k not in lengths:
                    u, v = k
                    l0 = 1 / G[cs._key(np.subtract(v, u))]
                    lengths[k] = (l0, l0 * (1 + lam * (phi(u) + phi(v)) / 2))
                d0[e], d[e] = lengths[k]
            try:
                p = cg.embed(d)
            except ValueError:
                degenerate += 1
                touched.update(keys)
                continue
            p0 = cg.embed(d0)
            for (i, j), k in zip(edges, keys):
                angle[k] += cg.dihedral(p, i, j)
                angle0[k] += cg.dihedral(p0, i, j)
                count[k] += 1
    dK = {R: 0.0 for R in RADII}
    dK_full = {R: 0.0 for R in RADII}
    shell = defaultdict(list)
    for k, c in count.items():
        vec = tuple(abs(a - b) for a, b in zip(*k))
        l0, l = lengths[k]
        r = math.dist([(a + b) / 2 for a, b in zip(*k)], centre)
        if sum(vec) == 1:
            shell[round(r)].append((l - l0) / l0)
        if k in touched or c != ring[vec]:
            continue
        eps, eps0 = 2 * math.pi - angle[k], 2 * math.pi - angle0[k]
        for R in RADII:
            if r <= R:
                dK[R] += l0 * (eps - eps0) / lam
                dK_full[R] += (l * eps - l0 * eps0) / lam
    means = {r: sum(v) / len(v) for r, v in shell.items() if 4 <= r <= 10}
    xs = [math.log(r) for r in sorted(means)]
    ys = [math.log(abs(means[r])) for r in sorted(means)]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    k_fit = -sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    return {"Q": Q, "delta_K": {str(R): dK[R] for R in RADII},
            "full_lK": {str(R): dK_full[R] for R in RADII},
            "falloff_k": k_fit, "degenerate_tetrahedra": degenerate}


def build() -> dict[str, object]:
    G = cs.green_table(1)
    res = {n: measure(G, n) for n in SOURCES}
    lin = {n: measure(G, n, 2 * LAM)["delta_K"]["10"] for n in SOURCES}
    for n in SOURCES:
        res[n]["delta_K_10_at_2lam"] = lin[n]
    valid = all(abs(lin[n] / res[n]["delta_K"]["10"] - 1) <= 0.02 for n in SOURCES)
    d1 = all(abs(r["delta_K"][R] / r["delta_K"]["10"] - 1) <= 0.10
             for r in res.values() for R in ("6", "8"))
    per_q = {n: r["delta_K"]["10"] / r["Q"] for n, r in res.items()}
    med = statistics.median(per_q.values())
    d2 = all(abs(v / med - 1) <= 0.10 for v in per_q.values())
    d3 = all(math.copysign(1, r["delta_K"]["10"]) == math.copysign(1, r["Q"]) for r in res.values())
    return {"prereg": "Continuum_Limit.md section 10 @ abba91c", "lambda": LAM, "sources": res,
            "first_order_valid": valid, "D1_vacuum_outside": d1, "D2_gauss": d2,
            "D3_sign": d3, "delta_K10_over_Q": per_q, "median_over_Q": med}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    args = p.parse_args()
    data = build()
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    for n, r in data["sources"].items():
        print(n, "Q=%.4f" % r["Q"], "k=%.3f" % r["falloff_k"], r["delta_K"],
              "2lam", "%.4g" % r["delta_K_10_at_2lam"], "full", r["full_lK"], "deg", r["degenerate_tetrahedra"])
    print({k: v for k, v in data.items() if k not in ("sources",)})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
