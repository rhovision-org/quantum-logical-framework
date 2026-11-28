#!/usr/bin/env python3
"""Stage 2e' of #301 milestone 2: calibrated tensor-fit test of the local vacuum.

Pre-registration: ``Continuum_Limit.md`` section 14 (committed in 7247d90, before this file
existed).  Results: ``Continuum_Limit.md`` section 15.

At each qualifying vertex, y_t = mean Delta eps / lam over the two edges of type t.  A 7x6
calibration matrix C (y = C h for a constant Hessian h) is measured from the six quadratic
fields on the same background; h(x) is the least-squares fit, tau = |tr H|, eta = ||H||_F, and
chi' = mean tau / mean eta per shell.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from pathlib import Path

import numpy as np

import census_geometry as cg
import census_source as cs
import census_source_2d as d2
import census_source_2e as e2

OUTPUT = Path("data/census_source_2e_prime.json")
LAM = d2.LAM
TYPES = cg.EDGE_TYPES
PAIRS = [(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2)]
GATE_R = (6, 8, 10)


def vertex_y(de: dict) -> dict:
    inc = defaultdict(dict)
    for k, (_, d) in de.items():
        u, v = k
        t = tuple(abs(a - b) for a, b in zip(u, v))
        inc[u].setdefault(t, []).append(d)
        inc[v].setdefault(t, []).append(d)
    out = {}
    for x, by in inc.items():
        if len(by) == 7 and all(len(by[t]) == 2 for t in TYPES):
            out[x] = np.array([sum(by[t]) / 2 for t in TYPES])
    return out


def quad(i, j):
    return (lambda z: 0.5 * z[i] * z[i]) if i == j else (lambda z: z[i] * z[j])


def calibrate(G):
    O = (0, 0, 0)
    cols = []
    for i, j in PAIRS:
        cols.append(vertex_y(e2.deficit_changes(G, set(), quad(i, j)))[O])
    return np.column_stack(cols)


def fit_measures(ys: dict, C, centre) -> dict:
    pinv = np.linalg.pinv(C)
    sh = defaultdict(lambda: [0.0, 0.0, 0.0, 0])
    axis = []
    for x, y in ys.items():
        r = round(math.dist(x, centre))
        if r not in e2.SHELLS:
            continue
        h = pinv @ y
        tau = abs(h[0] + h[1] + h[2])
        eta = math.sqrt(h[0] ** 2 + h[1] ** 2 + h[2] ** 2 + 2 * (h[3] ** 2 + h[4] ** 2 + h[5] ** 2))
        res = float(np.linalg.norm(C @ h - y) / np.linalg.norm(y)) if np.linalg.norm(y) else 0.0
        s = sh[r]
        s[0] += tau; s[1] += eta; s[2] += res; s[3] += 1
        m = [a - c for a, c in zip(x, centre)]
        if 6 <= math.dist(x, centre) <= 10 and sorted(abs(a) for a in m)[1] < 1e-9:
            H = np.array([[h[0], h[3], h[4]], [h[3], h[1], h[5]], [h[4], h[5], h[2]]])
            a = int(np.argmax([abs(q) for q in m]))
            ev = [H[a, a]] + [H[b, b] for b in range(3) if b != a]
            axis.append([e / ev[0] for e in ev])
    shells = {str(r): {"chi_prime": a / b, "mean_tau": a / n, "mean_eta": b / n,
                       "mean_residual": c / n, "n": n} for r, (a, b, c, n) in sorted(sh.items())}
    ratio = [sum(v[i] for v in axis) / len(axis) for i in range(3)] if axis else None
    return {"shells": shells, "axis_hessian_ratio": ratio, "n_axis_vertices": len(axis)}


def build() -> dict:
    G = cs.green_table(1)
    C = calibrate(G)
    sv = np.linalg.svd(C, compute_uv=False)
    out: dict = {"prereg": "Continuum_Limit.md section 14 @ 7247d90", "lambda": LAM,
                 "C": C.tolist(), "rank": int(np.linalg.matrix_rank(C)),
                 "condition": float(sv[0] / sv[-1]), "sources": {}}
    xx = vertex_y(e2.deficit_changes(G, set(), quad(0, 0)))
    probe = (4, 1, 2)
    h = np.linalg.pinv(C) @ xx[probe]
    out["calibration_check"] = {"vertex": probe, "h": h.tolist()}
    for name, src in d2.SOURCES.items():
        S = set(src)
        c = tuple(sum(a[i] for a in src) / len(src) for i in range(3))
        Q, phi = d2.field(G, src)
        fV = lambda x, Q=Q, c=c: Q * (2 / math.pi) / math.dist(x, c)
        out["sources"][name] = {
            "Q": Q,
            "census": fit_measures(vertex_y(e2.deficit_changes(G, S, phi)), C, c),
            "V": fit_measures(vertex_y(e2.deficit_changes(G, S, fV)), C, c)}
    O = (0.0, 0.0, 0.0)

    def fN(x):
        r = math.dist(x, O)
        return (2 / math.pi) / r + 0.06 * math.prod(math.cos(math.pi * a / 8) for a in x) if r else 0.0

    S0 = {(0, 0, 0)}
    out["N"] = fit_measures(vertex_y(e2.deficit_changes(G, S0, fN)), C, O)
    deF = e2.deficit_changes(G, S0, lambda x: 1.0)
    out["F"] = max(abs(d) for _, d in deF.values()) * LAM
    return verdicts(out)


def verdicts(out: dict) -> dict:
    src = out["sources"]
    h = out["calibration_check"]["h"]
    gates = {
        "C_rank_condition": out["rank"] == 6 and out["condition"] < 1e3,
        "V_chi": all(v["V"]["shells"][str(r)]["chi_prime"] <= 0.05 for v in src.values() for r in GATE_R),
        "N_chi": all(out["N"]["shells"][str(r)]["chi_prime"] >= 0.30 for r in GATE_R),
        "F_flat": out["F"] < 1e-9,
        "fit_reproduces": abs(h[0] - 1) < 1e-6 and all(abs(a) < 1e-6 for a in h[1:]),
    }
    L2 = all(v["census"]["shells"][str(r)]["chi_prime"] <= 0.05 for v in src.values() for r in GATE_R)
    out["gates"] = gates
    out["verdicts"] = {"L2prime_local_vacuum": L2 if all(gates.values()) else "uninformative",
                       "L2prime_raw": L2}
    return out


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    args = p.parse_args()
    data = build()
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print("rank", data["rank"], "cond %.3g" % data["condition"], "check", data["calibration_check"])
    for n, v in data["sources"].items():
        c, V = v["census"], v["V"]
        print(n, "Q=%.4f" % v["Q"], "axis ratio", c["axis_hessian_ratio"], "n", c["n_axis_vertices"])
        for r in map(str, e2.SHELLS):
            a, b = c["shells"][r], V["shells"][r]
            print("   r=%s chi'=%.5f chi'V=%.5f eta=%.4g res=%.3g n=%d" %
                  (r, a["chi_prime"], b["chi_prime"], a["mean_eta"], a["mean_residual"], a["n"]))
    print("N", {r: round(x["chi_prime"], 4) for r, x in data["N"]["shells"].items()})
    print("F", data["F"])
    print(data["gates"], data["verdicts"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
