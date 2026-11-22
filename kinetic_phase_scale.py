"""Conditional long-time phase comparison, independent of propagator selection."""
import json
import math
from itertools import combinations

DIRECTIONS = {"axis": (1., 0., 0.),
              "face": (1/math.sqrt(2), 1/math.sqrt(2), 0.),
              "body": (1/math.sqrt(3),)*3}
RADII = (.5, 1., 2.)
SCALES = tuple(2.**-k for k in range(3, 9))


def shells(a, r, n):
    angles = tuple(a*r*x for x in n)
    ss = tuple(math.sin(x) for x in angles)
    cc = tuple(math.cos(x) for x in angles)
    norm = math.sqrt(math.fsum(x*x for x in ss))
    c = math.asin(norm)/a
    dc = math.fsum(x*y*z for x,y,z in zip(ss, cc, n))/(norm*math.sqrt(1-norm*norm))
    # Stable 1-product(cos) using half angles, avoiding cancellation at small k.
    deficit = 0.
    for x in angles:
        u = 2*math.sin(x/2)**2
        deficit += u - deficit*u
    w = 2*math.asin(math.sqrt(deficit/2))/a
    dw = math.fsum(n[i]*ss[i]*math.prod(cc[j] for j in range(3) if j != i)
                   for i in range(3))/math.sqrt(deficit*(2-deficit))
    return c, w, dc, dw


def run():
    rows = []
    for name, n in DIRECTIONS.items():
        j = sum(n[i]**2*n[k]**2 for i,k in combinations(range(3), 2))
        for r in RADII:
            expected = (r**3*j/3, -r**3*j/6, r**3*j/2, 3*r*r*j/2)
            for a in SCALES:
                c, w, dc, dw = shells(a, r, n)
                vals = ((c-r)/a**2, (w-r)/a**2, (c-w)/a**2, (dc-dw)/a**2)
                error = max(abs(x-y) for x,y in zip(vals, expected))
                rows.append({"direction": name, "radius": r, "a": a,
                             "scaled_census_correction": vals[0],
                             "scaled_walk_correction": vals[1],
                             "scaled_phase_difference": vals[2],
                             "scaled_radial_derivative_difference": vals[3],
                             "expected": expected, "max_error": error})
    finest = [r for r in rows if r["a"] == SCALES[-1]]
    assert all(row["max_error"] <= .0005 for row in finest), finest
    assert all(abs(row["scaled_phase_difference"]) <= .0005 and
               abs(row["scaled_radial_derivative_difference"]) <= .0005
               for row in finest if row["direction"] == "axis")
    assert all(row["scaled_phase_difference"] > .0005 and
               row["scaled_radial_derivative_difference"] > .0005
               for row in finest if row["direction"] != "axis")
    return {"rows": rows, "comparisons": len(rows),
            "finest_max_error": max(row["max_error"] for row in finest),
            "scope": "conditional principal shells; no physical propagator or S5 concentration derived"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
