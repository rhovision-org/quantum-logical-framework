#!/usr/bin/env python3
"""gupta_scale_free.py -- the calibration-free content of the Gupta benchmark (#234, K4)

Part of the Quantum Logical Framework (QLF); see README.md. The tests K1-K4 and the verdict rule
are pre-registered in Gupta_ScaleFree.md section 1, committed before this script existed. K1-K3 are
Lean (QLF_ClockCalibration); this script computes K4 from the frozen stage-1 result and checks K1
and K2 numerically. It reads no new data and fits nothing.

    python3 gupta_scale_free.py
    python3 gupta_scale_free.py --json data/gupta_scale_free.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

RESULT = Path(__file__).resolve().parent / "verification" / "gupta-ccc-tl" / "result.json"
MPC_KM = 3.0856775814913673e19      # km per Mpc (IAU 2015 parsec)
GYR_S = 1e9 * 365.25 * 86400.0      # s per Gyr (Julian year)


def h_times_t(h_km_s_mpc: float, t_gyr: float) -> float:
    return (h_km_s_mpc / MPC_KM) * (t_gyr * GYR_S)


def run() -> dict:
    r = json.loads(RESULT.read_text())
    ages = {int(row["z_observed"]): row["age_Gyr"] for row in r["rows"]}
    t0 = ages[0]
    out = {
        "source": str(RESULT.relative_to(RESULT.parents[2])),
        "executed_source_revision": r["executed_source_revision"],
        "ages_Gyr": ages,
        "ratio_t10_t0": ages[10] / t0,
        "ratio_t20_t0": ages[20] / t0,
        "H0_total_t0": h_times_t(r["H0_total_km_s_Mpc"], t0),
        "Hc_t0": h_times_t(r["Hc_km_s_Mpc"], t0),
    }
    # K1, K2 numerically: an arbitrary calibration leaves these unchanged
    s = 0.37
    out["K1_check"] = abs((s * ages[10]) / (s * t0) - out["ratio_t10_t0"]) < 1e-12
    out["K2_check"] = abs(h_times_t(r["H0_total_km_s_Mpc"] / s, s * t0) - out["H0_total_t0"]) < 1e-12
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    r = run()
    print(f"frozen ages (Gyr): {r['ages_Gyr']}")
    print(f"t(10)/t(0) = {r['ratio_t10_t0']:.6f}   t(20)/t(0) = {r['ratio_t20_t0']:.6f}")
    print(f"H0_total * t0 = {r['H0_total_t0']:.6f}   Hc * t0 = {r['Hc_t0']:.6f}")
    print(f"K1, K2 numerical checks: {r['K1_check']}, {r['K2_check']}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
            f.write("\n")


if __name__ == "__main__":
    main()
