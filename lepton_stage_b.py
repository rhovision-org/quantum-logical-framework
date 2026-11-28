#!/usr/bin/env python3
"""lepton_stage_b.py -- what can the admissible lepton observables carry? (#140, Stage B)

Part of the Quantum Logical Framework (QLF); see README.md. The tests L1-L4 and the verdict rule
are pre-registered in Lepton_Stage_B.md section 1, committed before this script existed. The
observables are Lepton_Mass_Ratio_Protocol.md section 4's list, computed with the functions of
lepton_blind_classifier.py on the three frozen rungs. No muon or tau mass is read. L4 is bookkeeping (any datum on three
distinguishable rungs is a function of the index); L3 is the content.

    python3 lepton_stage_b.py
    python3 lepton_stage_b.py --json data/lepton_stage_b.json
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json

with contextlib.redirect_stdout(io.StringIO()):
    import lepton_blind_classifier as lbc

RUNGS = {"e": lbc.E_REP, "mu": lbc.MU_REP, "tau": lbc.TAU_REP}


def observables(h: str) -> dict:
    return {
        "axes": len(lbc.axes_engaged(h)),
        "depth": len(h),
        "first_return": lbc.first_return_zfa(h),
        "fold": lbc.fold_phase(h),
        "B": lbc.baryon_number(h),
        "orbit": len(lbc.orbit(h)),
    }


def run() -> dict:
    table = {k: observables(h) for k, h in RUNGS.items()}
    names = ["axes", "depth", "fold", "B", "orbit"]
    separating = [n for n in names if len({table[r][n] for r in RUNGS}) == 3]
    ks = {r: (table[r]["depth"] - 4) // 2 for r in RUNGS}
    l3 = all(table[r]["orbit"] == 24 * 2 ** ks[r] and table[r]["depth"] == 4 + 2 * ks[r] for r in RUNGS)
    # L4: the map rung -> observable tuple factors through k iff distinct k give the tuples and
    # equal k (none here) give equal tuples; on three rungs with distinct k this is injectivity of
    # k -> tuple, checked directly.
    tuples = {ks[r]: tuple(table[r][n] for n in names) for r in RUNGS}
    l4 = len(tuples) == 3 and l3
    return {"table": table, "k": ks, "separating": separating,
            "pass": {"L1": all(table[r]["first_return"] for r in RUNGS),
                     "L2": sorted(separating) == ["depth", "orbit"], "L3": l3, "L4": l4}}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = run()
    for k, v in r["table"].items():
        print(f"  {k:<4} {RUNGS[k]:<10} {v}")
    print(f"L2 separating observables: {r['separating']}")
    print(f"L3 orbit = 24*2^k and L = 4+2k on the ladder: {r['pass']['L3']}  (k = {r['k']})")
    print(f"pass: {r['pass']}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
