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

    defect = || S Pi(k) S^{-1} - E' P(k') beta ||_max / E'.

Here E' is the boosted continuum energy E(k) cosh eta + k_i sinh eta, not the walk's own
energy E(k') at the boosted momentum: the right-hand side uses P(k') from the walk but the scalar
E' from the boost. The two differ by the stage-1 shell error.

For the continuum Dirac operator this is zero to rounding (calibration below). The fitted
log-log slope of the worst defect against kappa is the order at which covariance fails.

Two time slices of the same walk are graded:
  raw   U = massStep(m) * handed(k)                       (QLF_DiracWalk.diracWalk)
  half  U = massStep(m/2) * handed(k) * massStep(m/2)     (raw conjugated by massStep(m/2))
They differ by a k-independent unitary, so they have the same spectrum.

Gates (fail closed). Nothing is graded, and the script exits non-zero with INVALID, unless:
  - the continuum Dirac calibration defect is finite and below 1e-12 (registered in §6b);
  - every walk step has a positive band of rank exactly 2, and every graded defect is finite and
    non-zero (a zero defect would make the log-log slope undefined);
  - the negative control fails as it should: the continuum Dirac band boosted with the wrong
    spinor sign, S = exp(-eta alpha_i / 2), must give a defect of at least 1e-2 at every kappa.
    The control checks that the defect can detect a wrong boost; it was added after review and
    does not change the registered grid or the graded readings.

What this is evidence for. The fitted slope is evidence on this finite grid. It is not a uniform
asymptotic theorem, and it does not test the projected and rescaled packet map's composition law
or any interacting amplitude.

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


class Invalid(Exception):
    """A fail-closed gate tripped: nothing is graded."""


def band(U):
    """Positive-energy band projector and energy of a unitary step (doubly degenerate band)."""
    w, v = np.linalg.eig(U)
    E = np.angle(w)
    idx = E > 0
    if int(np.count_nonzero(idx)) != 2:
        raise Invalid(f"positive band has rank {int(np.count_nonzero(idx))}, expected 2")
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


def defect(bandfn, k, m, i, eta, spin_sign=1):
    P, E = bandfn(k, m)
    E2, k2 = boost(E, k, i, eta)
    P2, _ = bandfn(k2, m)
    S = herm_exp(ALPHA[i], spin_sign * eta / 2)
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


def worst(bandfn, kappa, spin_sign=1, reduce=max):
    vals = []
    for d in directions():
        for r in MASS_RATIOS:
            n = np.sqrt(1 + r * r)        # |(k, m)| = kappa
            k = tuple(kappa * d / n)
            m = kappa * r / n
            for i in range(3):
                vals.append(defect(bandfn, k, m, i, ETA, spin_sign))
    return float(reduce(vals))


def slope(xs, ys):
    return float(np.polyfit(np.log(xs), np.log(ys), 1)[0])


CAL_MAX = 1e-12
CONTROL_MIN = 1e-2


def run():
    res = {"seed": SEED, "eta": ETA, "kappas": list(KAPPAS), "pass_slope": PASS_SLOPE,
           "kill_slope": KILL_SLOPE, "calibration_max": CAL_MAX, "control_min": CONTROL_MIN,
           "defect_scalar": "boosted continuum E', not the walk's E(k')"}
    cal = worst(dirac_band, 0.04)
    res["calibration_dirac_defect"] = cal
    print(f"calibration (continuum Dirac): worst defect {cal:.2e}")
    if not (np.isfinite(cal) and cal < CAL_MAX):
        raise Invalid(f"calibration defect {cal!r} is not finite and below {CAL_MAX}")
    ctrl = [worst(dirac_band, kp, spin_sign=-1, reduce=min) for kp in KAPPAS]
    res["negative_control_min_defect"] = ctrl
    print("negative control (wrong spinor sign), least defect: " + "  ".join(f"{y:.3e}" for y in ctrl))
    if not all(np.isfinite(y) and y >= CONTROL_MIN for y in ctrl):
        raise Invalid("negative control did not fail: the defect cannot detect a wrong boost")
    for name in ("raw", "half"):
        fn = lambda k, m, s=name: band(walk(k, m, s))
        ys = [worst(fn, kp) for kp in KAPPAS]
        if not all(np.isfinite(y) and y > 0 for y in ys):
            raise Invalid(f"{name}: non-finite or zero defect {ys!r}")
        s = slope(KAPPAS, ys)
        if name == "half":
            verdict = "PASS" if s >= PASS_SLOPE else ("FAIL" if s < KILL_SLOPE else "INCONCLUSIVE")
        else:
            verdict = "NOT_GRADED (expected about 1)"
        res[name] = {"worst_defect": ys, "slope": s, "verdict": verdict}
        print(f"{name:5s} slope {s:.3f}  {verdict}  " + "  ".join(f"{y:.3e}" for y in ys))
    res["graded"] = res["half"]["verdict"]
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    try:
        res = run()
    except Invalid as e:
        print(f"INVALID, NOT_GRADED: {e}")
        raise SystemExit(2)
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
