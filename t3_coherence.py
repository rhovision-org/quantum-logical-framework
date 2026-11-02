#!/usr/bin/env python3
"""
t3_coherence.py — test T3 of `No_Continuum_Conjecture.md` §5 (registered in commit 743c7e8, run in 2880998).

Coherence diagnostic for the signed two-electron joint census. Calls `census_dp` from
`logical_bang_census.py` unchanged (the §44 definition of entangled: the two loops' spans overlap;
remainder any count-balanced word), and for every class reports N (ways), S (signed sum) and
kappa = |S|/sqrt(N): the signed sum in units of the standard deviation it would have under a
hypothetical null model in which the N ways carried independent fair signs. kappa is a model-relative
coherence diagnostic, not an observable.

Registered criterion: pass iff kappa >= 4 for the entangled collinear class (P and A pooled) at lengths
10, 12 and 14, and kappa does not decrease from 10 to 14. The threshold 4 is a registered convention.

Run:  python3 t3_coherence.py     (~12 s).  Writes data/t3_coherence.json.
"""
from __future__ import annotations

import json
import math
import os

from logical_bang_census import census_dp

_HERE = os.path.dirname(os.path.abspath(__file__))
OUT_PATH = os.path.join(_HERE, "data", "t3_coherence.json")
LENGTHS = (10, 12, 14)


def main() -> int:
    out = {"lengths": {}, "criterion": "collinear entangled kappa >= 4 at 10,12,14 and non-decreasing"}
    kap = []
    for L in LENGTHS:
        tab = census_dp(L)
        agg = {}
        for rel in ("collinear", "O"):
            n = sum(v[0] for k, v in tab.items() if k[0] == rel and k[2] == "entangled")
            s = sum(v[1] for k, v in tab.items() if k[0] == rel and k[2] == "entangled")
            agg[rel] = {"N": n, "S": s, "kappa": abs(s) / math.sqrt(n) if n else 0.0}
            print(f"L={L:2d} {rel:9s} entangled  N={n:<14d} S={s:<13d} kappa={agg[rel]['kappa']:.2f}")
        kap.append(agg["collinear"]["kappa"])
        classes = [{"relation": k[0], "remainder": k[1], "entangled": k[2], "N": v[0], "S": v[1],
                    "kappa": abs(v[1]) / math.sqrt(v[0]) if v[0] else 0.0}
                   for k, v in sorted(tab.items())]
        out["lengths"][str(L)] = {"entangled_pooled": agg, "classes": classes}
    ok = all(k >= 4 for k in kap) and kap[-1] >= kap[0]
    out["verdict"] = "PASS" if ok else "FAIL"
    print(f"\nT3: {out['verdict']}")
    os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
    with open(OUT_PATH, "w") as f:
        json.dump(out, f, indent=1)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
