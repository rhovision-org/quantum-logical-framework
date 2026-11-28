#!/usr/bin/env python3
"""Pre-registered check for stage 4b of the relativity dependency chain.

Part of the Quantum Logical Framework (QLF), see README.md. The pre-registration is
Relativity_Principle.md §6b, "Stage 4b"; it was committed before this script was run on the walk.

Question. Stage 4a showed that the Dirac walk's positive band carries Dirac covariance to second
order in kappa on the half-step slice. Stage 4b asks the same of a tree amplitude: two walk
particles A and B meet at one site and pick up a contact phase exp(i g Gamma), where Gamma acts on
the joint spinor space C^4 (x) C^4. To first order in g (tree level) the amplitude from
(k1, k2) to (k1', k2') is the spinor matrix element of Gamma between band states, times the
coupling's Fourier transform ghat(q) at the momentum transfer q = k1' - k1.

Graded quantity. W below is a vertex proxy, not an energy-conserving S-matrix element: the grid is
elastic for the continuum shell, and the walk's quasi-energy mismatch between in and out legs is
reported separately as a diagnostic. Phases of band eigenvectors are arbitrary, so the spin-summed
square is used:

    W(p) = |ghat(q)|^2 Tr[(Pi1' (x) Pi2') Gamma (Pi1 (x) Pi2) Gamma^dagger],   Pi = E P(k),

with P(k) the positive band projector, the walk analogue of sum_s u u^dagger / 2. For the
continuum Dirac operator and a Lorentz-scalar vertex, W is a Lorentz invariant. For a boost of
rapidity eta along axis i, each leg (E(k), k) goes to (E', k') = Lambda (E(k), k), and

    defect = |W(Lambda p) - W(p)| / |W(p)|.

As in stage 4a, frame 1 uses the walk's own energies E(k) and frame 2 uses the boosted energies E',
with the walk's projectors P(k') at the boosted momenta.

Vertices.
  scalar  Gamma_S = beta (x) beta                    psibar psi psibar psi
  vector  Gamma_V = 1 (x) 1 - sum_i alpha_i (x) alpha_i   J^mu J_mu
  blind   Gamma_0 = 1 (x) 1                          the spinor-blind contact phase g(x1 - x2) of
                                                     QLF_InteractingKinematics.twoBodyStep, J^0 J^0
  range   Gamma_S with ghat(q) = 1 + G1 sum_i 2 cos q_i  (nearest-neighbour range)

Kinematics. Centre-of-momentum elastic scattering: k1 = p d, k2 = -p d, k1' = p d', k2' = -p d',
with random unit d, d' and |(p, mA)| = kappa, mB = MB_RATIO mA.

Gates (fail closed, every sample checked before reduction). Nothing is graded, and the script
exits non-zero with INVALID, unless: the continuum calibration (scalar and vector) is below 1e-12;
the continuum blind vertex gives a median defect of at least 1e-2 at every kappa (the defect
detects a frame-dependent vertex; the median, because a few configurations are close to invariant
even for this vertex); every W is finite, real and positive (relative imaginary residual at most 1e-12, a gate added
after review); every graded defect is finite and
positive; every fitted slope is finite.

What this is evidence for. Finite-grid evidence on tree amplitudes of one contact vertex. It is not
a theorem, and it says nothing about loops (stage 5) or a varying number of particles (stage 6).

Usage: python3 boost_amplitudes_check.py [--json data/boost_amplitudes_check.json]
"""
import argparse
import importlib.util
import json
from pathlib import Path

import numpy as np

_spec = importlib.util.spec_from_file_location(
    "boost_states_check", Path(__file__).resolve().parent / "boost_states_check.py")
bsc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(bsc)

Invalid = bsc.Invalid
BETA, ALPHA = bsc.BETA, bsc.ALPHA
I4 = np.eye(4, dtype=complex)

GAMMA = {
    "scalar": np.kron(BETA, BETA),
    "vector": np.kron(I4, I4) - sum(np.kron(a, a) for a in ALPHA),
    "blind": np.kron(I4, I4),
}

# ---- pre-registered grid (Relativity_Principle.md §6b, Stage 4b) ----
SEED = 20261125
N_SAMPLES = 12
MASS_RATIOS = (0.5, 1.0)
MB_RATIO = 0.6
ETA = 0.5
KAPPAS = (0.08, 0.04, 0.02, 0.01, 0.005)
G1 = 0.5
PASS_SLOPE = 1.8
KILL_SLOPE = 1.5
CAL_MAX = 1e-12
CONTROL_MIN = 1e-2
BLIND_MAX_SLOPE = 0.5
IMAG_TOL = 1e-12          # added after review: relative imaginary residual allowed in W


def ghat(q, ranged):
    return 1.0 + G1 * sum(2 * np.cos(x) for x in q) if ranged else 1.0


def samples():
    rng = np.random.default_rng(SEED)
    v = rng.normal(size=(N_SAMPLES, 2, 3))
    return v / np.linalg.norm(v, axis=2, keepdims=True)


def legs(kappa, d, d2, r):
    n = np.sqrt(1 + r * r)
    p, mA = kappa / n, kappa * r / n
    mB = MB_RATIO * mA
    return [(tuple(p * d), mA), (tuple(-p * d), mB), (tuple(p * d2), mA), (tuple(-p * d2), mB)]


def W(bandfn, gamma, frame, ranged):
    """frame: list of (E, k, m) for legs 1, 2, 1', 2'; projectors from bandfn at (k, m)."""
    pis = [E * bandfn(k, m)[0] for E, k, m in frame]
    pin = np.kron(pis[0], pis[1])
    pout = np.kron(pis[2], pis[3])
    q = np.subtract(frame[2][1], frame[0][1])
    w = np.trace(pout @ gamma @ pin @ gamma.conj().T)
    # W is a spin-summed square, so it must be real and positive up to rounding.
    if not (np.isfinite(w) and w.real > 0 and abs(w.imag) <= IMAG_TOL * w.real):
        raise Invalid(f"W is not positive real within {IMAG_TOL}: {w!r}")
    return float(abs(ghat(q, ranged)) ** 2 * w.real)


def defect(bandfn, gamma, kappa, d, d2, r, i, ranged):
    frame1 = []
    for k, m in legs(kappa, d, d2, r):
        frame1.append((bandfn(k, m)[1], k, m))
    frame2 = []
    for E, k, m in frame1:
        E2, k2 = bsc.boost(E, k, i, ETA)
        frame2.append((E2, k2, m))
    w1 = W(bandfn, gamma, frame1, ranged)
    w2 = W(bandfn, gamma, frame2, ranged)
    if not (np.isfinite(w1) and np.isfinite(w2) and w1 != 0 and w2 != 0):
        raise Invalid(f"non-finite or zero W ({w1!r}, {w2!r}) at kappa={kappa}, axis={i}")
    return abs(w2 - w1) / abs(w1)


def worst(bandfn, gamma, kappa, ranged=False, reduce=max, require_positive=False):
    vals = []
    for d, d2 in samples():
        for r in MASS_RATIOS:
            for i in range(3):
                v = defect(bandfn, gamma, kappa, d, d2, r, i, ranged)
                if not np.isfinite(v):
                    raise Invalid(f"non-finite defect {v!r} at kappa={kappa}, axis={i}")
                if require_positive and not v > 0:
                    raise Invalid(f"non-finite or zero defect {v!r} at kappa={kappa}, axis={i}")
                vals.append(v)
    return float(reduce(vals))


def slope(ys):
    s = float(np.polyfit(np.log(KAPPAS), np.log(ys), 1)[0])
    if not np.isfinite(s):
        raise Invalid(f"fitted slope {s!r} is not finite")
    return s


def energy_mismatch(bandfn, kappa):
    """Diagnostic, not graded: worst |E1 + E2 - E1' - E2'| / (E1 + E2) with the walk's own energies.

    The grid is elastic for the continuum shell. The walk's shell cos E = cos m prod cos k_i is not
    isotropic, so equal |k| in different directions need not give equal quasi-energy.
    """
    worst_ = 0.0
    for d, d2 in samples():
        for r in MASS_RATIOS:
            E = [bandfn(k, m)[1] for k, m in legs(kappa, d, d2, r)]
            if not all(np.isfinite(e) and e > 0 for e in E):
                raise Invalid(f"non-finite or non-positive leg energy {E!r} at kappa={kappa}")
            v = abs(E[0] + E[1] - E[2] - E[3]) / (E[0] + E[1])
            if not np.isfinite(v):
                raise Invalid(f"non-finite quasi-energy mismatch {v!r} at kappa={kappa}")
            worst_ = max(worst_, v)
    return worst_


def walk_band(slice_):
    return lambda k, m: bsc.band(bsc.walk(k, m, slice_))


def run():
    res = {"seed": SEED, "eta": ETA, "kappas": list(KAPPAS), "mb_ratio": MB_RATIO, "g1": G1,
           "pass_slope": PASS_SLOPE, "kill_slope": KILL_SLOPE, "calibration_max": CAL_MAX,
           "control_min": CONTROL_MIN, "blind_max_slope": BLIND_MAX_SLOPE}
    cal = {v: worst(bsc.dirac_band, GAMMA[v], 0.04) for v in ("scalar", "vector")}
    res["calibration_dirac_defect"] = cal
    print("calibration (continuum Dirac): " + "  ".join(f"{k} {v:.2e}" for k, v in cal.items()))
    if not all(np.isfinite(v) and v < CAL_MAX for v in cal.values()):
        raise Invalid(f"calibration {cal!r} is not finite and below {CAL_MAX}")
    ctrl = [worst(bsc.dirac_band, GAMMA["blind"], kp, reduce=np.median) for kp in KAPPAS]
    res["blind_continuum_median_defect"] = ctrl
    print("control (continuum, blind vertex), median defect: " + "  ".join(f"{y:.3e}" for y in ctrl))
    if not all(y >= CONTROL_MIN for y in ctrl):
        raise Invalid("control did not fail: the defect cannot detect a frame-dependent vertex")
    arms = [("scalar", "scalar", False), ("vector", "vector", False),
            ("range", "scalar", True), ("blind", "blind", False)]
    for slice_ in ("half", "raw"):
        bf = walk_band(slice_)
        out = {}
        for name, g, ranged in arms:
            ys = [worst(bf, GAMMA[g], kp, ranged, require_positive=True) for kp in KAPPAS]
            s = slope(ys)
            if slice_ == "raw":
                verdict = "NOT_GRADED"
            elif name == "blind":
                ok = s < BLIND_MAX_SLOPE and min(ys) >= CONTROL_MIN
                verdict = "PREDICTION_CONFIRMED" if ok else "PREDICTION_FAILED"
            else:
                verdict = "PASS" if s >= PASS_SLOPE else ("FAIL" if s < KILL_SLOPE else "INCONCLUSIVE")
            out[name] = {"worst_defect": ys, "slope": s, "verdict": verdict}
            print(f"{slice_:4s} {name:6s} slope {s:6.3f}  {verdict:20s} "
                  + "  ".join(f"{y:.3e}" for y in ys))
        res[slice_] = out
    mis = [energy_mismatch(walk_band("half"), kp) for kp in KAPPAS]
    res["half_quasienergy_mismatch"] = mis
    print("diagnostic (not graded), half-slice relative quasi-energy mismatch in - out: "
          + "  ".join(f"{y:.3e}" for y in mis))
    res["graded"] = {n: res["half"][n]["verdict"] for n, _, _ in arms}
    return res


EXPLORATORY = {
    # Not pre-registered: candidate substrate readings of the contact (Relativity_Principle.md §6b,
    # "Which contact"). Reported, never graded.
    "euclid": np.kron(I4, I4) + sum(np.kron(a, a) for a in ALPHA),
    "pseudoscalar": np.kron(1j * BETA @ ALPHA[0] @ ALPHA[1] @ ALPHA[2],
                            1j * BETA @ ALPHA[0] @ ALPHA[1] @ ALPHA[2]),
}


def exploratory():
    out = {}
    for name, g in EXPLORATORY.items():
        cont = [worst(bsc.dirac_band, g, kp) for kp in KAPPAS]
        wk = [worst(walk_band("half"), g, kp, require_positive=True) for kp in KAPPAS]
        out[name] = {"continuum_worst": cont, "half_worst": wk, "half_slope": slope(wk)}
        print(f"exploratory {name:12s} continuum worst {cont[0]:.3e}  half slope {slope(wk):6.3f}  "
              + "  ".join(f"{y:.3e}" for y in wk))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    ap.add_argument("--exploratory", action="store_true",
                    help="also print the ungraded candidate contacts (not pre-registered)")
    a = ap.parse_args()
    try:
        res = run()
    except Invalid as e:
        print(f"INVALID, NOT_GRADED: {e}")
        raise SystemExit(2)
    if a.exploratory:
        try:
            exploratory()
        except Invalid as e:
            print(f"exploratory run INVALID: {e}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
