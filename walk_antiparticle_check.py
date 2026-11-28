"""Stage 6, step 1: what separates the walk's particles from its antiparticles.

Part of the [Quantum Logical Framework (QLF)](README.md), the relativity dependency chain
([Relativity_Principle.md](Relativity_Principle.md) §6b, "Stage 6, step 1"). Structural checks, not a
graded test: every quantity below is fixed by the step's algebra, and the script fails closed if one
of them does not hold.

  S1  dispersion: cos w = cos m * prod_i cos k_i on both slices.
  S2  on the full lattice the step is gapped at quasi-energy 0 and at pi (w in [m, pi - m]), so a
      global split into a forward arc e^{+iw} and a backward arc e^{-iw} exists.
  S3  the pi-doubler (QLF_PiDoubler): k -> k + pi e_z swaps the arcs, so that split is odd under a
      symmetry of the step.
  S4  two steps are pi-periodic in k_z (halfWalk_sq_shift_z): on the walk's conserved parity
      sector, k and k + pi e_z are one momentum, and on the surface where some k_i = pi/2 the
      two-step walk is -I. The two arcs meet there, so the sector has no global split.
  S5  the Feynman ordering is Stueckelberg's: the forward arc propagated forward in time and the
      backward arc backward in time sum to the kernels stage 5 used.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
_spec = importlib.util.spec_from_file_location("loop_boost_check", ROOT / "loop_boost_check.py")
lbc = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(lbc)

SEED = 6
N = 20000
MASSES = (0.03, 0.3)
TOL = 1e-12


class Invalid(Exception):
    """A structural check failed: the analysis it supports does not apply."""


def step(p, m, slice_):
    h = lbc._handed(p)
    if slice_ == "raw":
        return lbc.bsc.mass_step(m)[None] @ h
    ms = lbc.bsc.mass_step(m / 2)[None]
    return ms @ h @ ms


def checks(seed=SEED):
    rng = np.random.default_rng(seed)
    p = rng.uniform(-np.pi, np.pi, (N, 3))
    out = {}
    for slice_ in ("half", "raw"):
        for m in MASSES:
            key = f"{slice_}_m{m}"
            w, lp, lm = lbc.walk_bands(slice_)(p, m)
            disp = float(np.abs(np.cos(w) - np.cos(m) * np.prod(np.cos(p), axis=1)).max())
            lo, hi = float(w.min()), float(w.max())
            q = p + np.array([0.0, 0.0, np.pi])
            w2, lp2, lm2 = lbc.walk_bands(slice_)(q, m)
            swap = float(max(np.abs(lp2 - lm).max(), np.abs(w2 - (np.pi - w)).max()))
            u, u2 = step(p, m, slice_), step(q, m, slice_)
            sq = float(np.abs(u @ u - u2 @ u2).max())
            s = p.copy()
            s[:, 1] = np.pi / 2
            us = step(s, m, slice_)
            sigma = float(np.abs(us @ us + np.eye(4)[None]).max())
            out[key] = {"S1_dispersion_residual": disp, "S2_w_min": lo, "S2_w_max": hi,
                        "S3_swap_residual": swap, "S4_two_step_periodic_residual": sq,
                        "S4_two_step_on_sigma_plus_I": sigma}
            if not disp < TOL:
                raise Invalid(f"{key}: dispersion residual {disp:.2e}")
            if not (lo >= m - TOL and hi <= np.pi - m + TOL):
                raise Invalid(f"{key}: w outside [m, pi - m]: [{lo}, {hi}]")
            if not (swap < 1e-9 and sq < TOL and sigma < TOL):
                raise Invalid(f"{key}: S3/S4 residuals {swap:.2e} {sq:.2e} {sigma:.2e}")
    out["S5_stueckelberg"] = stueckelberg(rng)
    return out


def stueckelberg(rng, eta=0.05, T=2000):
    """Time-ordered sum vs the closed-form kernels, for one random momentum on the half slice."""
    p = rng.uniform(-np.pi, np.pi, (1, 3))
    m = MASSES[0]
    u = step(p, m, "half")[0]
    w, lp, lm = (a[0] for a in lbc.walk_bands("half")(p, m))
    E = rng.uniform(-np.pi, np.pi)
    # forward arc e^{+iw} (lp), forward in time; backward arc e^{-iw} (lm), backward in time
    fwd = np.zeros((4, 4), complex)
    bwd = np.zeros((4, 4), complex)
    ut, udt = np.eye(4, dtype=complex), np.eye(4, dtype=complex)
    for t in range(1, T):
        ut = ut @ u
        fwd += np.exp(-1j * E * t - eta * t) * ut @ lp
    for t in range(0, T):
        bwd += np.exp(1j * E * t - eta * t) * udt @ lm
        udt = udt @ u.conj().T
    x = E - w - 1j * eta
    y = E + w + 1j * eta  # backward arc: e^{-iw} under u^dagger is e^{+iw}
    fwd_closed = lp * np.exp(-1j * x) / (1 - np.exp(-1j * x))
    bwd_closed = lm / (1 - np.exp(1j * y))
    res = float(max(np.abs(fwd - fwd_closed).max(), np.abs(bwd - bwd_closed).max()))
    if not res < 1e-9:
        raise Invalid(f"Stueckelberg sum differs from its closed form by {res:.2e}")
    return {"residual": res, "eta": eta, "T": T}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    try:
        res = checks()
    except Invalid as e:
        print(f"INVALID: {e}")
        raise SystemExit(2)
    for k, v in res.items():
        print(k, json.dumps(v))
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
