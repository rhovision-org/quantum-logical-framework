#!/usr/bin/env python3
"""Stage 2a of #301 milestone 2: the vacuum census geometry (calibration).

Pre-registration: ``Continuum_Limit.md`` section 4 (committed in c4dd459, before
this file existed).  Results: ``Continuum_Limit.md`` section 5.

* A way from x to y is any twist history whose spatial displacement is y - x;
  the gauge pair does not move the walk.
* G(x) = sum_L 8^-L #{histories of length L with displacement x}.  With each
  spatial letter at 1/8 and the two gauge letters as a hold (1/4),
  G(x) = int_0^inf prod_i [e^-t I_{x_i}(t)] dt, using
  1/(1 - phi) = int e^{-t(1 - phi)} dt and the Bessel generating function.
  ``green`` returns G/4: the factor 4 from 1 - phi = (3 - sum cos)/4 is the time
  scale of the lazy walk, and only ratios of lengths enter the curvature.
* Length l(x) = 1/G(x).  Sensitivity: G4 (four-axis walk at zero gauge net),
  l = G4^-1/2.
* Complex: Freudenthal (Kuhn) triangulation of s Z^3; deficits at the seven edge
  types are 2 pi minus the summed dihedral angles of the six tetrahedra of a cell.

Needs ``mpmath`` (not used by the CI tests, which check the geometry code and the
committed data).
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

OUTPUT = Path("data/census_geometry.json")
SCALES = (1, 2, 4, 8, 16, 32)
EDGE_TYPES = [v for v in itertools.product((0, 1), repeat=3) if any(v)]


# ---------------------------------------------------------------------------
# Census weight
# ---------------------------------------------------------------------------

def green(x: tuple[int, int, int], four_axis: bool = False, dps: int = 40):
    """Kraft-weighted census count of ways with spatial displacement x."""
    import mpmath as mp

    mp.mp.dps = dps
    xs = [abs(int(c)) for c in x]

    def ive(n, t):
        return mp.besseli(n, t) * mp.exp(-t)

    def f(t):
        val = ive(xs[0], t) * ive(xs[1], t) * ive(xs[2], t)
        if four_axis:
            val *= ive(0, t)
        return val

    # The integrand is smooth and decays like t^-3/2 (t^-2 with the gauge axis).
    edges = [0, 1, 10, 100, 1000, 10000, 100000, mp.inf]
    return mp.quad(f, edges)


def length(x: tuple[int, int, int], four_axis: bool = False) -> float:
    g = green(x, four_axis)
    return float(1 / g) if not four_axis else float(g ** -0.5)


# ---------------------------------------------------------------------------
# Regge geometry of the Freudenthal triangulation
# ---------------------------------------------------------------------------

def cell_tetrahedra() -> list[tuple[tuple[int, int, int], ...]]:
    """The six Kuhn simplices of the unit cube: 0 -> e_a -> e_a+e_b -> (1,1,1)."""
    tets = []
    for perm in itertools.permutations(range(3)):
        v = [0, 0, 0]
        verts = [tuple(v)]
        for a in perm:
            v[a] = 1
            verts.append(tuple(v))
        tets.append(tuple(verts))
    return tets


def embed(d: dict[tuple[int, int], float]) -> list[tuple[float, float, float]]:
    """Coordinates for four points with the given pairwise distances."""
    d01, d02, d03 = d[(0, 1)], d[(0, 2)], d[(0, 3)]
    d12, d13, d23 = d[(1, 2)], d[(1, 3)], d[(2, 3)]
    p0 = (0.0, 0.0, 0.0)
    p1 = (d01, 0.0, 0.0)
    x2 = (d01 ** 2 + d02 ** 2 - d12 ** 2) / (2 * d01)
    y2sq = d02 ** 2 - x2 ** 2
    if y2sq <= 0:
        raise ValueError("degenerate triangle")
    y2 = math.sqrt(y2sq)
    p2 = (x2, y2, 0.0)
    x3 = (d01 ** 2 + d03 ** 2 - d13 ** 2) / (2 * d01)
    y3 = (d02 ** 2 + d03 ** 2 - d23 ** 2 - 2 * x2 * x3) / (2 * y2)
    z3sq = d03 ** 2 - x3 ** 2 - y3 ** 2
    if z3sq <= 0:
        raise ValueError("degenerate tetrahedron")
    p3 = (x3, y3, math.sqrt(z3sq))
    return [p0, p1, p2, p3]


def _sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def _cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def _dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def dihedral(p: list, i: int, j: int) -> float:
    """Interior dihedral angle of tetrahedron p at edge (i, j)."""
    k, m = [q for q in range(4) if q not in (i, j)]
    e = _sub(p[j], p[i])
    u = _sub(p[k], p[i])
    w = _sub(p[m], p[i])
    nu = _cross(e, u)
    nw = _cross(e, w)
    c = _dot(nu, nw) / math.sqrt(_dot(nu, nu) * _dot(nw, nw))
    return math.acos(max(-1.0, min(1.0, c)))


def deficits(lengths: dict[tuple[int, int, int], float]) -> dict[str, float]:
    """Deficit angle at each edge type, given a length for each type."""
    total = {v: 0.0 for v in EDGE_TYPES}
    for tet in cell_tetrahedra():
        d = {}
        for i, j in itertools.combinations(range(4), 2):
            vec = tuple(abs(a - b) for a, b in zip(tet[i], tet[j]))
            d[(i, j)] = lengths[vec]
        p = embed(d)
        for i, j in itertools.combinations(range(4), 2):
            vec = tuple(abs(a - b) for a, b in zip(tet[i], tet[j]))
            total[vec] += dihedral(p, i, j)
    return {"".join(map(str, v)): 2 * math.pi - total[v] for v in EDGE_TYPES}


def type_lengths(a: float, b: float, c: float) -> dict[tuple[int, int, int], float]:
    out = {}
    for v in EDGE_TYPES:
        out[v] = {1: a, 2: b, 3: c}[sum(v)]
    return out


# ---------------------------------------------------------------------------
# Census
# ---------------------------------------------------------------------------

def run(four_axis: bool) -> dict[str, object]:
    rows = []
    for s in SCALES:
        a = length((s, 0, 0), four_axis)
        b = length((s, s, 0), four_axis)
        c = length((s, s, s), four_axis)
        try:
            defs = deficits(type_lengths(a, b, c))
            ok = True
        except ValueError:
            defs, ok = {}, False
        rows.append({
            "s": s,
            "lengths": {"axis": a, "face_diagonal": b, "body_diagonal": c},
            "ratios": {"b/a": b / a, "c/a": c / a},
            "positive_volume": ok,
            "deficits": defs,
            "max_abs_deficit": max(abs(x) for x in defs.values()) if defs else None,
        })
    fit = [(math.log(r["s"]), math.log(r["max_abs_deficit"])) for r in rows
           if r["s"] >= 4 and r["max_abs_deficit"]]
    n = len(fit)
    mx = sum(x for x, _ in fit) / n
    my = sum(y for _, y in fit) / n
    slope = sum((x - mx) * (y - my) for x, y in fit) / sum((x - mx) ** 2 for x, _ in fit)
    return {"rows": rows, "decay_exponent_p": -slope}


def build() -> dict[str, object]:
    primary = run(four_axis=False)
    sens = run(four_axis=True)
    rows = primary["rows"]
    m1 = all(r["positive_volume"] for r in rows)
    decreasing = all(rows[i + 1]["max_abs_deficit"] < rows[i]["max_abs_deficit"]
                     for i in range(len(rows) - 1)) if m1 else False
    m2 = m1 and decreasing and rows[-1]["max_abs_deficit"] < 1e-3
    m3 = primary["decay_exponent_p"] >= 1.5
    verdict = "PASS" if (m1 and m2) else "FAIL"
    return {
        "prereg": "Continuum_Limit.md section 4 @ c4dd459",
        "primary_l_eq_inverse_G": primary,
        "sensitivity_four_axis": sens,
        "M1_positive_volume": m1,
        "M2_vacuum_flat_in_large": m2,
        "M3_decay_p_ge_1_5": m3,
        "verdict_2a": verdict,
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    args = p.parse_args()
    data = build()
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    for key in ("primary_l_eq_inverse_G", "sensitivity_four_axis"):
        print(key, "p =", round(data[key]["decay_exponent_p"], 3))
        for r in data[key]["rows"]:
            print("  s", r["s"], r["ratios"], r["max_abs_deficit"], r["deficits"])
    print("M1", data["M1_positive_volume"], "M2", data["M2_vacuum_flat_in_large"],
          "M3", data["M3_decay_p_ge_1_5"], "verdict", data["verdict_2a"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
