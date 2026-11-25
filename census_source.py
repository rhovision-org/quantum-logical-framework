#!/usr/bin/env python3
"""Stage 2b of #301 milestone 2: does a local source act like a mass?

Pre-registration: ``Continuum_Limit.md`` section 6.2 (committed in 9c00b36, before
this file existed).  Results: ``Continuum_Limit.md`` section 7.

* Vacuum census weight: G(d) = 4 * census_geometry.green(d), the Green's function
  sum_n P^n of the lazy walk (each spatial letter 1/8, gauge pair a hold).
* Exclusion (primary): ways avoiding the source set S,
  G_S(x,y) = G(x,y) - g_x^T [G_SS]^-1 g_y.
* Delay (sensitivity): a step onto a source site costs an extra factor 1/8, so
  G_D(x,y) = G(x,y) - (7/8) g_x^T M^-1 g_y,  M = I + (7/8)(G_SS - I), for x not in S.
* Length l = 1/G_S on the edges of the Freudenthal triangulation of Z^3 (s = 1),
  in a box of half-width 12.  Tetrahedra touching S are dropped; an edge is
  interior if it has its full ring of tetrahedra.
* Measured: delta l / l on axis edges by shell (falloff exponent k over r = 4..10),
  and Delta K(R) = sum (l eps - l0 eps0) over interior edges with midpoint within R.

Needs ``mpmath`` and ``numpy``.  The Green's-function table is cached in
``data/census_source_green.json``.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import census_geometry as cg

OUTPUT = Path("data/census_source.json")
GREEN_CACHE = Path("data/census_source_green.json")
HALF = 12
DMAX = 15
SOURCES = {
    1: [(0, 0, 0)],
    8: list(itertools.product((0, 1), repeat=3)),
    27: list(itertools.product((-1, 0, 1), repeat=3)),
}
RADII = (4, 6, 8, 10)
SHELLS = range(4, 11)


def _key(d) -> tuple[int, int, int]:
    return tuple(sorted(abs(int(c)) for c in d))


def _green_one(key: tuple[int, int, int]) -> tuple[tuple[int, int, int], float]:
    return key, float(4 * cg.green(key, dps=30))


def green_table(jobs: int) -> dict[tuple[int, int, int], float]:
    if GREEN_CACHE.exists():
        raw = json.loads(GREEN_CACHE.read_text())
        table = {tuple(map(int, k.split(","))): v for k, v in raw.items()}
        if len(table) == len(_all_keys()):
            return table
    with ProcessPoolExecutor(jobs) as ex:
        table = dict(ex.map(_green_one, _all_keys()))
    GREEN_CACHE.write_text(json.dumps({",".join(map(str, k)): v for k, v in sorted(table.items())},
                                      indent=0, sort_keys=True) + "\n")
    return table


def _all_keys() -> list[tuple[int, int, int]]:
    return sorted({_key(d) for d in itertools.product(range(DMAX + 1), repeat=3)})


def build_geometry(G, source: list, model: str):
    import numpy as np

    S = [tuple(a) for a in source]
    Sset = set(S)
    GSS = np.array([[G[_key(np.subtract(a, b))] for b in S] for a in S])
    if model == "exclusion":
        Minv = np.linalg.inv(GSS)
        factor = 1.0
    else:
        Minv = np.linalg.inv(np.eye(len(S)) + 7 / 8 * (GSS - np.eye(len(S))))
        factor = 7 / 8
    gcache: dict = {}

    def gvec(x):
        if x not in gcache:
            gcache[x] = np.array([G[_key(np.subtract(x, a))] for a in S])
        return gcache[x]

    def lengths(u, v):
        g0 = G[_key(np.subtract(v, u))]
        corr = factor * float(gvec(u) @ Minv @ gvec(v))
        return 1 / g0, 1 / (g0 - corr)

    angle = defaultdict(float)
    angle0 = defaultdict(float)
    count = defaultdict(int)
    touched = set()
    degenerate: list = []
    length_of: dict = {}
    for base in itertools.product(range(-HALF, HALF), repeat=3):
        for tet in cg.cell_tetrahedra():
            verts = [tuple(b + t for b, t in zip(base, v)) for v in tet]
            edges = list(itertools.combinations(range(4), 2))
            keys = [tuple(sorted((verts[i], verts[j]))) for i, j in edges]
            if any(v in Sset for v in verts):
                touched.update(keys)
                continue
            d, d0 = {}, {}
            for (i, j), k in zip(edges, keys):
                if k not in length_of:
                    length_of[k] = lengths(*k)
                d0[(i, j)], d[(i, j)] = length_of[k]
            p0 = cg.embed(d0)
            try:
                p = cg.embed(d)
            except ValueError:
                # Disclosed deviation (Continuum_Limit.md 7): the prereg did not say how to treat
                # a sourced tetrahedron with no Euclidean realisation.  As in milestone 1, such
                # cases are counted, not repaired; their edges are excluded like edges touching S.
                degenerate.append(verts)
                touched.update(keys)
                continue
            for (i, j), k in zip(edges, keys):
                angle[k] += cg.dihedral(p, i, j)
                angle0[k] += cg.dihedral(p0, i, j)
                count[k] += 1
    return angle, angle0, count, touched, length_of, degenerate


def ring_sizes() -> dict[tuple[int, int, int], int]:
    """Number of tetrahedra around an edge of each type, in the full lattice."""
    ring = defaultdict(int)
    for tet in cg.cell_tetrahedra():
        for i, j in itertools.combinations(range(4), 2):
            ring[tuple(abs(a - b) for a, b in zip(tet[i], tet[j]))] += 1
    return dict(ring)


def measure(G, n: int, model: str) -> dict[str, object]:
    src = SOURCES[n]
    centre = tuple(sum(c[i] for c in src) / len(src) for i in range(3))
    angle, angle0, count, touched, length_of, degenerate = build_geometry(G, src, model)
    ring = ring_sizes()

    def mid_r(k):
        u, v = k
        return math.dist([(a + b) / 2 for a, b in zip(u, v)], centre)

    dK = {R: 0.0 for R in RADII}
    # Post-hoc diagnostic (not a decision input): the curvature change alone, l0 (eps - eps0),
    # without the term (l - l0) eps0 that the anisotropic s = 1 background contributes.
    dK_curv = {R: 0.0 for R in RADII}
    shell = defaultdict(list)
    for k, c in count.items():
        vec = tuple(abs(a - b) for a, b in zip(*k))
        l0, l = length_of[k]
        r = mid_r(k)
        if sum(vec) == 1:
            shell[round(r)].append((l - l0) / l0)
        if k in touched or c != ring[vec]:
            continue
        eps = 2 * math.pi - angle[k]
        eps0 = 2 * math.pi - angle0[k]
        for R in RADII:
            if r <= R:
                dK[R] += l * eps - l0 * eps0
                dK_curv[R] += l0 * (eps - eps0)
    means = {r: sum(v) / len(v) for r, v in shell.items() if r in SHELLS and v}
    xs = [math.log(r) for r in sorted(means)]
    ys = [math.log(abs(means[r])) for r in sorted(means)]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    k_fit = -sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    return {
        "n": n,
        "model": model,
        "delta_K": {str(R): dK[R] for R in RADII},
        "diag_curvature_only": {str(R): dK_curv[R] for R in RADII},
        "mean_dl_over_l_axis_by_shell": {str(r): means[r] for r in sorted(means)},
        "falloff_k": k_fit,
        "degenerate_tetrahedra": len(degenerate),
        "degenerate_max_distance": max((math.dist([sum(c) / 4 for c in zip(*v)], centre)
                                        for v in degenerate), default=None),
    }


def build(jobs: int) -> dict[str, object]:
    G = green_table(jobs)
    out: dict[str, object] = {"prereg": "Continuum_Limit.md section 6.2 @ 9c00b36"}
    for model in ("exclusion", "delay"):
        res = [measure(G, n, model) for n in SOURCES]
        b1 = all(v > 0 for r in res for v in r["delta_K"].values())
        b2 = all(0.8 <= r["falloff_k"] <= 1.2 for r in res)
        ks = [r["delta_K"]["10"] for r in res]
        if all(k > 0 for k in ks):
            xs = [math.log(n) for n in SOURCES]
            ys = [math.log(k) for k in ks]
            mx, my = sum(xs) / 3, sum(ys) / 3
            q = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        else:
            q = None
        b3 = q is not None and 0.8 <= q <= 1.2
        out[model] = {"sources": res, "B1": b1, "B2": b2, "B3": b3, "q": q,
                      "acts_as_mass": b1 and b2 and b3}
        print(model, "B1", b1, "B2", b2, "B3", b3, "q", q,
              [(r["n"], round(r["falloff_k"], 3), {R: f"{v:.3e}" for R, v in r["delta_K"].items()},
                {R: f"{v:.3e}" for R, v in r["diag_curvature_only"].items()},
                r["degenerate_tetrahedra"], r["degenerate_max_distance"])
               for r in res], flush=True)
    return out


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    p.add_argument("--jobs", type=int, default=4)
    args = p.parse_args()
    data = build(args.jobs)
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
