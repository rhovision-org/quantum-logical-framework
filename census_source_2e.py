#!/usr/bin/env python3
"""Stage 2e of #301 milestone 2: local curvature outside a source.

Pre-registration: ``Continuum_Limit.md`` section 12 (committed in 3600c5c, before this file
existed).  Results: ``Continuum_Limit.md`` section 13.

Same map as stage 2d (``census_source_2d.py``): l = l0 (1 + lam (f(u) + f(v)) / 2) with
f = phi, the joint-closure field.  Reads the deficit changes locally: per vertex (local scalar
s and unsigned t, cancellation index chi = mean|s| / mean t per shell) and per axis edge
(radial / tangential tidal ratio rho).  Controls V (continuum monopole), N (zero-sum ripple)
and F (uniform rescaling) use the same background and formula.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import defaultdict
from pathlib import Path

import numpy as np

import census_geometry as cg
import census_source as cs
import census_source_2d as d2

OUTPUT = Path("data/census_source_2e.json")
LAM = d2.LAM
SHELLS = range(4, 11)
GATE_R = (6, 8, 10)


def deficit_changes(G, S: set, f, lam: float = LAM) -> dict:
    """Delta eps / lam for every counted edge, with l0 and the edge key."""
    ring = cs.ring_sizes()
    angle, angle0, count = defaultdict(float), defaultdict(float), defaultdict(int)
    touched, lengths = set(), {}
    edges = list(itertools.combinations(range(4), 2))
    H = cs.HALF
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
                    lengths[k] = (l0, l0 * (1 + lam * (f(u) + f(v)) / 2))
                d0[e], d[e] = lengths[k]
            try:
                p = cg.embed(d)
            except ValueError:
                touched.update(keys)
                continue
            p0 = cg.embed(d0)
            for (i, j), k in zip(edges, keys):
                angle[k] += cg.dihedral(p, i, j)
                angle0[k] += cg.dihedral(p0, i, j)
                count[k] += 1
    out = {}
    for k, c in count.items():
        vec = tuple(abs(a - b) for a, b in zip(*k))
        if k in touched or c != ring[vec]:
            continue
        out[k] = (lengths[k][0], (angle0[k] - angle[k]) / lam)  # (eps - eps0)/lam
    return out


def local_measures(de: dict, centre) -> dict:
    inc = defaultdict(list)
    for k, (l0, d) in de.items():
        for x in k:
            inc[x].append(0.5 * l0 * d)
    shells = defaultdict(lambda: [0.0, 0.0, 0.0, 0])  # sum|s|, sum t, sum s, n
    for x, terms in inc.items():
        if len(terms) != 14:
            continue
        r = round(math.dist(x, centre))
        if r not in SHELLS:
            continue
        s, t = sum(terms), sum(abs(a) for a in terms)
        sh = shells[r]
        sh[0] += abs(s); sh[1] += t; sh[2] += s; sh[3] += 1
    per = {r: {"chi": a / b if b else float("nan"), "mean_t": b / n, "mean_s": c / n, "n": n}
           for r, (a, b, c, n) in sorted(shells.items())}
    rad, tan = [], []
    for k, (l0, d) in de.items():
        vec = tuple(abs(a - b) for a, b in zip(*k))
        if sum(vec) != 1:
            continue
        m = [(a + b) / 2 - ci for a, b, ci in zip(*k, centre)]
        mm = math.sqrt(sum(a * a for a in m))
        if not 6 <= mm <= 10:
            continue
        cos = abs(m[vec.index(1)]) / mm
        if cos >= 0.95:
            rad.append(d * mm ** 3)
        elif cos <= 0.10:
            tan.append(d * mm ** 3)
    tmean = sum(tan) / len(tan)
    rho = (sum(rad) / len(rad)) / tmean if tmean else float("nan")
    rs = [r for r in per if r in SHELLS]
    xs = [math.log(r) for r in rs]
    ys = [math.log(per[r]["mean_t"]) for r in rs]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    p = -sum((a - mx) * (b - my) for a, b in zip(xs, ys)) / sum((a - mx) ** 2 for a in xs)
    return {"shells": {str(r): v for r, v in per.items()}, "rho": rho, "p": p,
            "n_radial": len(rad), "n_tangential": len(tan),
            "radial_mean": sum(rad) / len(rad), "tangential_mean": sum(tan) / len(tan),
            "max_abs_delta": max(abs(d) for _, d in de.values())}


def build() -> dict:
    G = cs.green_table(1)
    out: dict = {"prereg": "Continuum_Limit.md section 12 @ 3600c5c", "lambda": LAM, "sources": {}}
    for name, src in d2.SOURCES.items():
        S = set(src)
        c = tuple(sum(a[i] for a in src) / len(src) for i in range(3))
        Q, phi = d2.field(G, src)
        cen = local_measures(deficit_changes(G, S, phi), c)
        fV = lambda x, Q=Q, c=c: Q * (2 / math.pi) / math.dist(x, c)
        V = local_measures(deficit_changes(G, S, fV), c)
        cen2 = local_measures(deficit_changes(G, S, phi, 2 * LAM), c)
        out["sources"][name] = {"Q": Q, "census": cen, "V": V,
                                "mean_t8_at_2lam": cen2["shells"]["8"]["mean_t"]}
    O = (0.0, 0.0, 0.0)
    def fN(x):
        r = math.dist(x, O)
        return (2 / math.pi) / r + 0.005 * math.prod(math.cos(math.pi * a / 8) for a in x) if r else 0.0
    S0 = {O}
    out["N"] = local_measures(deficit_changes(G, S0, fN), O)
    out["F"] = local_measures(deficit_changes(G, S0, lambda x: 1.0), O)["max_abs_delta"] * LAM
    return verdicts(out)


def verdicts(out: dict) -> dict:
    src = out["sources"]
    g1 = all(v["V"]["shells"][str(r)]["chi"] <= 0.10 for v in src.values() for r in GATE_R)
    g2 = all(out["N"]["shells"][str(r)]["chi"] >= 0.30 for r in GATE_R)
    g3 = out["F"] < 1e-9
    g4 = all(abs(v["mean_t8_at_2lam"] / v["census"]["shells"]["8"]["mean_t"] - 1) <= 0.02
             for v in src.values())
    L1 = all(2.5 <= v["census"]["p"] <= 3.5 for v in src.values())
    L2 = all(v["census"]["shells"][str(r)]["chi"] <= 0.10 for v in src.values() for r in GATE_R)
    L3_inform = {n: -2.5 <= v["V"]["rho"] <= -1.5 for n, v in src.items()}
    L3 = all(-2.5 <= v["census"]["rho"] <= -1.5 for v in src.values())
    L4 = all(0.80 <= v["census"]["shells"]["8"]["mean_t"] / v["V"]["shells"]["8"]["mean_t"] <= 1.25
             for v in src.values())
    out["gates"] = {"V_chi": g1, "N_chi": g2, "F_flat": g3, "first_order": g4}
    out["L3_informative"] = L3_inform
    out["verdicts"] = {"L1_not_flat": L1,
                       "L2_local_vacuum": L2 if (g1 and g2) else "uninformative",
                       "L3_tidal_pattern": L3, "L4_strength_is_Q": L4}
    return out


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    args = p.parse_args()
    data = build()
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    for n, v in data["sources"].items():
        c, V = v["census"], v["V"]
        print(n, "Q=%.4f p=%.3f rho=%.3f rhoV=%.3f" % (v["Q"], c["p"], c["rho"], V["rho"]))
        for r in map(str, SHELLS):
            a, b = c["shells"][r], V["shells"][r]
            print("   r=%s chi=%.4f chiV=%.4f t=%.4g t/tV=%.4f s=%.3g n=%d" %
                  (r, a["chi"], b["chi"], a["mean_t"], a["mean_t"] / b["mean_t"], a["mean_s"], a["n"]))
    print("N", {r: round(x["chi"], 4) for r, x in data["N"]["shells"].items()}, "rhoN", data["N"]["rho"])
    print("F", data["F"])
    print(data["gates"], data["L3_informative"], data["verdicts"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
