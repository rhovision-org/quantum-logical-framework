#!/usr/bin/env python3
"""Planck-scale dispersion prediction for issue #11.

Part of the Quantum Logical Framework (QLF); see Planck_Dispersion_Prediction.md.

The Dirac walk (lean/QLF_DiracWalk.lean) has the exact dispersion

    cos E = cos m * cos k_x * cos k_y * cos k_z            (diracWalk_dispersion)

with E the phase per step and k in radians per step. Taking one step to be one Planck time,
E_phys = E * E_P. For a massless mode in direction n (|n| = 1), with P4 = sum n_a^4,

    E^2 = k^2 - (1 - P4) k^4 / 6 + O(k^6)
    v_phase = 1 - (1 - P4) k^2 / 12,   v_group = 1 - (1 - P4) k^2 / 4.

Derivation: log cos x = -x^2/2 - x^4/12 + O(x^6); equate log cos E with sum log cos(n_a k).

The census-symbol reading of Relativity_Principle.md section 5 (sin^2 w = sum sin^2 k_a) gives the
opposite sign: w^2 = k^2 + (1 - P4) k^4 / 3, v_group = 1 + (1 - P4) k^2 / 2.

This script checks those coefficients numerically against the exact dispersion, takes the direction
average (<P4> = 3/5 on the sphere), converts to the standard LIV parametrisation

    v = 1 - s (n+1)/2 (E / E_QG,n)^n      (n = 2:  deficit = (3/2) (E/E_QG,2)^2)

and compares with published bounds. Pure Python, runs in about a second.
Writes data/planck_dispersion_prediction.json.
"""
import json
import math
import os
import random

E_PLANCK_GEV = 1.220890e19          # sqrt(hbar c^5 / G), CODATA 2022
H0_KM_S_MPC = 67.4                  # Planck 2018
OMEGA_M, OMEGA_L = 0.315, 0.685
MPC_KM = 3.0856775814913673e19
GEV_PER_TEV = 1e3


def walk_energy(k_vec):
    """Exact massless walk quasi-energy in the first band."""
    c = 1.0
    for ka in k_vec:
        c *= math.cos(ka)
    return math.acos(c)


def census_energy(k_vec):
    """Census-symbol reading: sin^2 w = sum sin^2 k_a (first band, w <= pi/2)."""
    s2 = sum(math.sin(ka) ** 2 for ka in k_vec)
    return math.asin(math.sqrt(s2))


def p4(n):
    return sum(x ** 4 for x in n)


def unit(v):
    r = math.sqrt(sum(x * x for x in v))
    return [x / r for x in v]


def group_speed(energy, n, k, h=1e-6):
    """Magnitude of grad_k E at k n, by central differences."""
    g = []
    for a in range(3):
        kp = [k * x for x in n]
        km = [k * x for x in n]
        kp[a] += h
        km[a] -= h
        g.append((energy(kp) - energy(km)) / (2 * h))
    return math.sqrt(sum(x * x for x in g))


def check_coefficients(rng, samples=200):
    """Fit the k^2 coefficient of the phase and group deficits at small k."""
    worst = {"walk_phase": 0.0, "walk_group": 0.0, "census_phase": 0.0, "census_group": 0.0}
    k = 0.02
    for _ in range(samples):
        n = unit([rng.gauss(0, 1) for _ in range(3)])
        q = 1 - p4(n)
        if q < 1e-3:
            continue
        kv = [k * x for x in n]
        pred = {
            "walk_phase": -q / 12,
            "walk_group": -q / 4,
            "census_phase": q / 6,
            "census_group": q / 2,
        }
        got = {
            "walk_phase": (walk_energy(kv) / k - 1) / k ** 2,
            "walk_group": (group_speed(walk_energy, n, k) - 1) / k ** 2,
            "census_phase": (census_energy(kv) / k - 1) / k ** 2,
            "census_group": (group_speed(census_energy, n, k) - 1) / k ** 2,
        }
        for key in worst:
            worst[key] = max(worst[key], abs(got[key] - pred[key]) / abs(pred[key]))
    return worst


def never_superluminal(rng, samples=20000):
    """Walk: phase velocity <= 1 for every sampled in-band mode (k <= 1)."""
    worst = -1.0
    for _ in range(samples):
        n = unit([rng.gauss(0, 1) for _ in range(3)])
        k = rng.uniform(1e-3, 1.0)
        v = walk_energy([k * x for x in n]) / k
        worst = max(worst, v - 1)
    return worst


def mean_p4(rng, samples=200000):
    return sum(p4(unit([rng.gauss(0, 1) for _ in range(3)])) for _ in range(samples)) / samples


def e_qg2(q, group_coeff):
    """E_QG,2 / E_P from deficit = group_coeff * q * (E/E_P)^2 = (3/2) (E/E_QG)^2."""
    return math.sqrt(1.5 / (group_coeff * q))


def delay_seconds(e_high_gev, e_qg_gev, z, n=2, steps=2000):
    """Jacobson-Piran time delay for a subluminal order-n effect."""
    h0 = H0_KM_S_MPC / MPC_KM  # 1/s
    integ = 0.0
    dz = z / steps
    for i in range(steps):
        zz = (i + 0.5) * dz
        integ += (1 + zz) ** n / math.sqrt(OMEGA_M * (1 + zz) ** 3 + OMEGA_L) * dz
    return (1 + n) / (2 * h0) * (e_high_gev / e_qg_gev) ** n * integ


def main():
    rng = random.Random(20261127)
    coeff = check_coefficients(rng)
    superlum = never_superluminal(rng)
    p4_mean = mean_p4(rng)

    body, face, avg = 1 - 1 / 3, 1 - 1 / 2, 1 - 3 / 5
    walk = {
        "body_diagonal": e_qg2(body, 1 / 4),
        "face_diagonal": e_qg2(face, 1 / 4),
        "direction_average": e_qg2(avg, 1 / 4),
    }
    census = {
        "body_diagonal": e_qg2(body, 1 / 2),
        "direction_average": e_qg2(avg, 1 / 2),
    }
    lhaaso_eqg2 = 6e-8                 # E_QG,2 > 6e-8 E_P, LHAASO GRB 221009A (PRL 133, 071501)
    fermi_eqg2 = 1.3e11 / E_PLANCK_GEV  # E_QG,2 > 1.3e11 GeV, Fermi-LAT GRB 090510 (arXiv:1305.3463)
    strongest = min(min(walk.values()), min(census.values()))

    # 10 TeV photon from GRB 221009A (z = 0.151), strongest walk direction
    dt = delay_seconds(10 * GEV_PER_TEV, walk["body_diagonal"] * E_PLANCK_GEV, 0.151)

    out = {
        "coefficient_check_max_relative_error": coeff,
        "walk_max_phase_velocity_excess_sampled": superlum,
        "mean_P4_sampled": p4_mean,
        "mean_P4_exact": 0.6,
        "walk_EQG2_over_EP": walk,
        "census_reading_EQG2_over_EP": census,
        "kill_threshold_EQG2_over_EP": strongest,
        "kill_threshold_max_abs_dv_coeff": 1 / 3,
        "lhaaso_bound_EQG2_over_EP": lhaaso_eqg2,
        "fermi_bound_EQG2_over_EP": fermi_eqg2,
        "gap_in_EQG2_vs_lhaaso": walk["body_diagonal"] / lhaaso_eqg2,
        "gap_in_dv_vs_lhaaso": (walk["body_diagonal"] / lhaaso_eqg2) ** 2,
        "grb221009a_10TeV_delay_s_body_diagonal": dt,
    }

    print("Planck-scale dispersion of the Dirac walk (issue #11)")
    print("coefficient check, max relative error at k = 0.02:")
    for key, val in coeff.items():
        print(f"  {key:14s} {val:.2e}")
    print(f"walk phase velocity excess over c, 20000 in-band modes: max {superlum:.2e} (<= 0 means never faster)")
    print(f"<P4> on the sphere: sampled {p4_mean:.4f}, exact 3/5")
    print("E_QG,2 / E_P (walk, subluminal):", {k: round(v, 3) for k, v in walk.items()})
    print("E_QG,2 / E_P (census reading, superluminal):", {k: round(v, 3) for k, v in census.items()})
    print(f"kill threshold: E_QG,2 < {strongest:.2f} E_P, i.e. |dv| > (1/3)(E/E_P)^2")
    print(f"LHAASO bound E_QG,2 > {lhaaso_eqg2:.0e} E_P; prediction is {out['gap_in_EQG2_vs_lhaaso']:.1e} times higher")
    print(f"  in speed deficit, {out['gap_in_dv_vs_lhaaso']:.1e} times smaller than the current reach")
    print(f"Fermi-LAT bound E_QG,2 > {fermi_eqg2:.1e} E_P")
    print(f"GRB 221009A, 10 TeV photon, body diagonal: predicted delay {dt:.1e} s")

    for key, val in coeff.items():
        assert val < 1e-2, key
    assert superlum <= 1e-12
    assert abs(p4_mean - 0.6) < 5e-3

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "planck_dispersion_prediction.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
        f.write("\n")
    print("wrote", os.path.relpath(path))


if __name__ == "__main__":
    main()
