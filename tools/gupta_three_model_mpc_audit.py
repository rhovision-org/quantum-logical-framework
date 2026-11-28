#!/usr/bin/env python3
"""Retrospective, read-only three-model Mpc sensitivity check of Gupta (2023), Table 1.

Independent closed-form ages. No fitting, optimizer, network, or writes by default.
The printed Table 1 values were known before this diagnostic.
"""
from decimal import Decimal, localcontext
import json
from pathlib import Path

MPC_NOMINAL_KM = Decimal("3.0856775814913673e19")
MPC_ROUNDED_KM = Decimal("3.09e19")
SECONDS_PER_GYR = Decimal("1e9") * Decimal("365.25") * Decimal("86400")
MODELS = (
    ("CCC", Decimal("72.70"), Decimal("-0.4953"), Decimal("13.69")),
    ("LCDM+TL", Decimal("60.48"), Decimal("0.1351"), Decimal("19.25")),
    ("CCC+TL", Decimal("59.51"), Decimal("-0.7997"), Decimal("26.70")),
)

def age_ccc(h, r, mpc):
    if h <= 0 or not -1 < r < 0 or mpc <= 0:
        raise ValueError("CCC domain: H > 0, -1 < r < 0, Mpc > 0")
    return mpc / h / SECONDS_PER_GYR * ((Decimal(3)+r)/(Decimal(3)*(1+r))).ln() / (-r)

def age_lcdm(h, omega, mpc):
    """Flat matter+Lambda age, expressed with logarithms rather than asinh."""
    if h <= 0 or not 0 < omega < 1 or mpc <= 0:
        raise ValueError("LCDM domain: H > 0, 0 < Omega_m < 1, Mpc > 0")
    root = (1-omega).sqrt()
    x = ((1-omega)/omega).sqrt()
    asinh_x = (x + (x*x+1).sqrt()).ln()
    return mpc / h / SECONDS_PER_GYR * Decimal(2)/(Decimal(3)*root) * asinh_x

def evaluate():
    with localcontext() as ctx:
        ctx.prec = 60
        rows = []
        for name, h, parameter, published in MODELS:
            f = age_lcdm if name == "LCDM+TL" else age_ccc
            nominal = f(h, parameter, MPC_NOMINAL_KM)
            rounded = f(h, parameter, MPC_ROUNDED_KM)
            lo, hi = published-Decimal(".005"), published+Decimal(".005")
            rows.append({
                "model": name, "H_expansion_km_s_Mpc": str(h),
                "omega_m_or_alpha_over_H": str(parameter),
                "published_Gyr": str(published),
                "nominal_Gyr": str(nominal),
                "rounded_Mpc_Gyr": str(rounded),
                "nominal_matches_printed": lo <= nominal < hi,
                "rounded_matches_printed": lo <= rounded < hi,
                "distance_to_upper_rounding_boundary_Gyr": str(hi-rounded),
            })
        return {
            "scope": "Retrospective Table 1 sensitivity check; NOT proof of author-used conversion or physical clock correspondence",
            "source": "Gupta (2023), MNRAS 524, 3385-3395, Table 1; doi:10.1093/mnras/stad2032",
            "year_days": "365.25",
            "Mpc_nominal_km": str(MPC_NOMINAL_KM),
            "Mpc_rounded_km": str(MPC_ROUNDED_KM),
            "scale_ratio": str(MPC_ROUNDED_KM/MPC_NOMINAL_KM),
            "rows": rows,
            "all_three_rounded_match": all(row["rounded_matches_printed"] for row in rows),
            "source_precision_gate": "OPEN: author-used constants or source code not established",
        }

if __name__ == "__main__":
    print(json.dumps(evaluate(), indent=2))
