#!/usr/bin/env python3
"""Pre-registered check for stage 4 of the relativity dependency chain.

Part of the Quantum Logical Framework (QLF), see README.md. The pre-registration is
Relativity_Principle.md §6b; it was committed before this script was run on the walk.

Question. The approved frame-comparison map (Relativity_Principle.md §6b) turns a walk
eigenmode's spinor with the chiral SL(2,C) action S(A) and lands it in the walk's positive band
at the boosted momentum. That is only a covariant comparison if the walk's band carries the
Dirac covariance to second order in kappa = size of (k, m). A first-order defect would be a frame
dependence at O(L_P / lambda), which breaks the relativity principle at low energy.

Graded quantity. For a walk step U(k, m), let P(k) be its positive-energy band projector
(eigenvalues e^{iE}, 0 < E < pi) and E(k) its energy. The covariant projector is
Pi(k) = E(k) P(k) beta, the walk analogue of (pslash + m)/2. For a boost of rapidity eta along
axis i, with S = exp(eta alpha_i / 2), boost (E(k), k) to (E', k') and measure

    defect = || S Pi(k) S^{-1} - Pi(k') ||_max / E'.

For the continuum Dirac operator this is zero to rounding (calibration below). The fitted
log-log slope of the worst defect against kappa is the order at which covariance fails.

Two time slices of the same walk are graded:
  raw   U = massStep(m) * handed(k)                       (QLF_DiracWalk.diracWalk)
  half  U = massStep(m/2) * handed(k) * massStep(m/2)     (raw conjugated by massStep(m/2))
They differ by a k-independent unitary, so they have the same spectrum.

Usage: python3 boost_states_check.py [--json data/boost_states_check.json]
"""
import argparse
import json

import numpy as np

SX = np.array([[0, 1], [1, 0]], complex)
SY = np.array([[0, -1j], [1j, 0]], complex)
SZ = np.diag([1, -1]).astype(complex)
I2 = np.eye(2, dtype=complex)
# Twist.toMatrix: up = σy, left = -σx, slash = σz, right = σx; conj negates.
UP, LEFT, SLASH, RIGHT = SY, -SX, SZ, SX
BETA = np.kron(RIGHT, I2)                                  # Mass.beta
ALPHA = [np.kron(SLASH, T) for T in (UP, LEFT, SLASH)]     # Mass.alpha, order (y, x, z)


def fix(T):
    return (I2 + T) / 2


def real_step(T, k):
    return np.exp(1j * k) * fix(T) + np.exp(-1j * k) * fix(-T)


def real_walk(ky, kx, kz):
    a, b, c = real_step(UP, ky / 2), real_step(LEFT, kx / 2), real_step(SLASH, kz / 2)
    return a @ b @ c @ c @ b @ a


def handed(k):
    ky, kx, kz = k
    return np.kron(fix(SLASH), real_walk(ky, kx, kz)) + np.kron(fix(-SLASH), real_walk(-ky, -kx, -kz))


def mass_step(m):
    return np.cos(m) * np.eye(4) + 1j * np.sin(m) * BETA


def walk(k, m, slice_):
    if slice_ == "raw":
        return mass_step(m) @ handed(k)
    return mass_step(m / 2) @ handed(k) @ mass_step(m / 2)


def herm_exp(A, c):
    """exp(c A) for Hermitian A and real c."""
    w, v = np.linalg.eigh(A)
    return v @ np.diag(np.exp(c * w)) @ v.conj().T


def band(U):
    """Positive-energy band projector and energy of a unitary step (doubly degenerate band)."""
    w, v = np.linalg.eig(U)
    E = np.angle(w)
    idx = E > 0
    q, _ = np.linalg.qr(v[:, idx])
    return q @ q.conj().T, float(np.mean(E[idx]))


def dirac_band(k, m):
    H = sum(ki * a for ki, a in zip(k, ALPHA)) + m * BETA
    E = float(np.sqrt(sum(x * x for x in k) + m * m))
    return (np.eye(4) + H / E) / 2, E


def boost(E, k, i, eta):
    k = list(k)
    ki = k[i]
    E2 = E * np.cosh(eta) + ki * np.sinh(eta)
    k[i] = ki * np.cosh(eta) + E * np.sinh(eta)
    return E2, tuple(k)


def defect(bandfn, k, m, i, eta):
    P, E = bandfn(k, m)
    E2, k2 = boost(E, k, i, eta)
    P2, _ = bandfn(k2, m)
    S = herm_exp(ALPHA[i], eta / 2)
    lhs = S @ (E * P @ BETA) @ np.linalg.inv(S)
    rhs = E2 * P2 @ BETA
    return float(np.abs(lhs - rhs).max() / E2)


# ---- pre-registered grid (Relativity_Principle.md §6b) ----
SEED = 20261122
N_DIRS = 12
MASS_RATIOS = (0.5, 1.0)
ETA = 0.5
KAPPAS = (0.08, 0.04, 0.02, 0.01, 0.005)
PASS_SLOPE = 1.8
KILL_SLOPE = 1.5


def directions():
    rng = np.random.default_rng(SEED)
    v = rng.normal(size=(N_DIRS, 3))
    return v / np.linalg.norm(v, axis=1, keepdims=True)


def worst(bandfn, kappa):
    out = 0.0
    for d in directions():
        for r in MASS_RATIOS:
            n = np.sqrt(1 + r * r)        # |(k, m)| = kappa
            k = tuple(kappa * d / n)
            m = kappa * r / n
            for i in range(3):
                out = max(out, defect(bandfn, k, m, i, ETA))
    return out


def slope(xs, ys):
    return float(np.polyfit(np.log(xs), np.log(ys), 1)[0])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    res = {"seed": SEED, "eta": ETA, "kappas": list(KAPPAS), "pass_slope": PASS_SLOPE,
           "kill_slope": KILL_SLOPE}
    cal = worst(dirac_band, 0.04)
    res["calibration_dirac_defect"] = cal
    print(f"calibration (continuum Dirac): worst defect {cal:.2e}")
    for name in ("raw", "half"):
        fn = lambda k, m, s=name: band(walk(k, m, s))
        ys = [worst(fn, kp) for kp in KAPPAS]
        s = slope(KAPPAS, ys)
        verdict = "PASS" if s >= PASS_SLOPE else ("FAIL" if s < KILL_SLOPE else "INCONCLUSIVE")
        res[name] = {"worst_defect": ys, "slope": s, "verdict": verdict}
        print(f"{name:5s} slope {s:.3f}  {verdict}  " + "  ".join(f"{y:.3e}" for y in ys))
    res["graded"] = res["half"]["verdict"]
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
