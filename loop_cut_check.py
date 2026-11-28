#!/usr/bin/env python3
"""Pre-registered check: stage 5, second run, with the two-step cut.

Part of the [Quantum Logical Framework (QLF)](README.md). The pre-registration is
[Relativity_Principle.md](Relativity_Principle.md) §6b, "Stage 5, second run: the two-step cut",
committed (7613ffb) before this script was written. The first run is
[loop_boost_check.py](loop_boost_check.py), whose definitions this script reuses unchanged except
for the particle/antiparticle split and the outer integration grid.

The split. A state with one-step eigenvalue e^{i theta} is a particle if its two-step quasi-energy
2 theta (mod 2 pi, in (-pi, pi]) is positive. On the forward arc (theta = w) that is w < pi/2; on
the backward arc (theta = -w) it is w > pi/2. The cut is the surface w = pi/2, where the two-step
walk is -I (walk_antiparticle_check.py, S4).

    L(E, P) = int_BZ d^3p/(2 pi)^3 [ P1(p) (x) P2(P-p) R(E - thP1 - thP2)
                                   - A1(p) (x) A2(P-p) R(E - thA1 - thA2) ].

Integration. Balls around the eight zone corners as in the first run (all eight now singular in the
particle term). Outside them, a tensor grid of Gauss-Legendre panels whose breakpoints include
every cut plane of both particles (p_i = +-pi/2 and p_i = P_i +- pi/2) and the balls' radii, so the
integrand is smooth inside each panel.

Usage: python3 loop_cut_check.py [--json data/loop_cut_check.json]
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

Invalid = lbc.Invalid
bsc = lbc.bsc
GAMMA = lbc.GAMMA
KAPPAS, PASS_SLOPE, KILL_SLOPE = lbc.KAPPAS, lbc.PASS_SLOPE, lbc.KILL_SLOPE
CAL_MAX, CONTROL_MIN, STAB_MAX = lbc.CAL_MAX, lbc.CONTROL_MIN, lbc.STAB_MAX
GATE_FRACTION = 0.2  # outside the balls, |x| >= (E - |P|)/5

# ---- integration settings (chosen by the stability gate and the calibration only) ----
SETTINGS = dict(lbc.SETTINGS, n_seg=8)
FINE = dict(lbc.FINE, n_seg=12)


def wrap(x):
    return (x + np.pi) % (2 * np.pi) - np.pi


class CutModel(lbc.Model):
    """The walk's two-particle integrand with the two-step cut."""

    def __init__(self, bands, mA, mB):
        super().__init__(bands, True, mA, mB)

    def split(self, p, m):
        w, f, b = self.bands(p, m)
        below = w < np.pi / 2
        bm = below[:, None, None]
        part = np.where(bm, f, b)
        anti = np.where(bm, b, f)
        th = np.where(below, w, -w)
        return part, anti, th

    def terms(self, p, E, P, scale=1.0):
        p1, a1, t1 = self.split(p, scale * self.mA)
        p2, a2, t2 = self.split(P[None] - p, scale * self.mB)
        return (wrap(E - t1 - t2), p1, p2), (wrap(E + t1 + t2), a1, a2)

    def x_of(self, which, p, E, P):
        return self.terms(p, E, P)[which][0]


def singular_centers(model, E, P):
    shift = P * model.mA / (model.mA + model.mB)
    out = []
    for cy in (0.0, np.pi):
        for cx in (0.0, np.pi):
            for cz in (0.0, np.pi):
                c = np.array([cy, cx, cz])
                w = model.bands(c[None], model.mA)[0][0]
                if not (abs(w - model.mA) < 1e-9 or abs(w - (np.pi - model.mA)) < 1e-9):
                    raise Invalid(f"zone corner {c} is neither a band bottom nor a band top (w = {w})")
                out.append((c + shift, 0))
    return out


def breakpoints(Pi, si, st):
    b = [-np.pi, np.pi, -np.pi / 2, np.pi / 2, Pi - np.pi / 2, Pi + np.pi / 2]
    for c in (0.0, np.pi):
        for r in (st["r1"], st["r_in"]):
            b += [c + si - r, c + si + r]
    b = np.sort(np.concatenate([wrap(np.array(b[2:])), [-np.pi, np.pi]]))
    keep = np.concatenate([[True], np.diff(b) > 1e-12])
    return b[keep]


def axis_nodes(Pi, si, st):
    xg, wg = np.polynomial.legendre.leggauss(st["n_seg"])
    b = breakpoints(Pi, si, st)
    xs, ws = [], []
    for a, c in zip(b[:-1], b[1:]):
        xs.append((c - a) / 2 * xg + (c + a) / 2)
        ws.append((c - a) / 2 * wg)
    return np.concatenate(xs), np.concatenate(ws)


def outer(model, centers, E, P, st):
    shift = P * model.mA / (model.mA + model.mB)
    ax = [axis_nodes(P[i], shift[i], st) for i in range(3)]
    g = np.stack(np.meshgrid(ax[0][0], ax[1][0], ax[2][0], indexing="ij"), axis=-1).reshape(-1, 3)
    wt = np.einsum("i,j,k->ijk", ax[0][1], ax[1][1], ax[2][1]).reshape(-1)
    chi = np.zeros(len(g))
    for c, _ in centers:
        d = (g - c[None] + np.pi) % (2 * np.pi) - np.pi
        chi += lbc._bump(np.linalg.norm(d, axis=1), st["r1"], st["r_in"])
    wt = wt * (1 - chi)
    keep = wt > 1e-15 * wt.max()
    g, wt = g[keep], wt[keep] / (2 * np.pi) ** 3
    floor = GATE_FRACTION * (E - np.linalg.norm(P))
    if not floor > 0:
        raise Invalid(f"E - |P| = {E - np.linalg.norm(P):.3e} is not positive")
    total = np.zeros((16, 16), complex)
    for ch in np.array_split(np.arange(len(g)), max(1, len(g) // 40000)):
        (xp, a1, b1), (xa, a2, b2) = model.terms(g[ch], E, P)
        if min(np.abs(xp).min(), np.abs(xa).min()) < floor:
            raise Invalid("a singular surface lies outside the integration balls")
        total += lbc._acc(wt[ch] * lbc.kern(xp, True), a1, b1)
        total -= lbc._acc(wt[ch] * lbc.kern(xa, True), a2, b2)
    return total


def loop(model, E, P, st):
    P = np.asarray(P, float)
    cen = singular_centers(model, E, P)
    tot = outer(model, cen, E, P, st)
    scale = 0.0
    for c, which in cen:
        b = lbc.ball(model, c, which, E, P, st, [(1.0, 1.0)])
        scale += float(np.abs(b).max())
        tot += b
    if not np.abs(tot).max() > 1e-8 * scale:
        raise Invalid(f"the loop vanishes to rounding (|L| = {np.abs(tot).max():.1e})")
    return tot


_CT = {}


def counterterm(model, st):
    key = (model.bands, model.mA, model.mB, id(st))
    if key not in _CT:
        E0 = model.bands(np.zeros((1, 3)), model.mA)[0][0] + \
            model.bands(np.zeros((1, 3)), model.mB)[0][0]
        _CT[key] = loop(model, E0, np.zeros(3), st)
    return _CT[key]


def slice_run(kind, kappa, st, contacts):
    out = {g: [] for g in contacts}
    bandfn = lambda k, m, s=kind: bsc.band(bsc.walk(k, m, s))
    for d, d2 in lbc.samples():
        lg, mA, mB = lbc.legs(kappa, d, d2)
        model = CutModel(lbc.walk_bands(kind), mA, mB)
        Lthr = counterterm(model, st)
        f1 = [(bandfn(k, m)[1], k, m) for k, m in lg]
        E1 = f1[0][0] + f1[1][0]
        L1 = loop(model, E1, np.zeros(3), st)
        ext1 = [(E, bandfn(k, m)[0]) for E, k, m in f1]
        for i in range(3):
            f2 = [(lambda Eb, kb: (Eb, kb, m))(*bsc.boost(E, k, i, lbc.ETA)) for E, k, m in f1]
            E2 = f2[0][0] + f2[1][0]
            P2 = np.add(f2[0][1], f2[1][1])
            L2 = loop(model, E2, P2, st)
            ext2 = [(E, bandfn(k, m)[0]) for E, k, m in f2]
            for g in contacts:
                w1 = lbc.W2(ext1, lbc.gam2(GAMMA[g], L1, Lthr))
                w2 = lbc.W2(ext2, lbc.gam2(GAMMA[g], L2, Lthr))
                out[g].append(abs(w2 - w1) / w1)
    return out


def stability_one(kind, kappa):
    d, d2 = lbc.samples()[0]
    lg, mA, mB = lbc.legs(kappa, d, d2)
    bandfn = lambda k, m, s=kind: bsc.band(bsc.walk(k, m, s))
    model = CutModel(lbc.walk_bands(kind), mA, mB)
    f1 = [(bandfn(k, m)[1], k, m) for k, m in lg]
    f2 = [(lambda Eb, kb: (Eb, kb, m))(*bsc.boost(E, k, 0, lbc.ETA)) for E, k, m in f1]
    E2, P2 = f2[0][0] + f2[1][0], np.add(f2[0][1], f2[1][1])
    vals = [lbc.gam2(GAMMA["vector"], loop(model, E2, P2, st), counterterm(model, st))
            for st in (SETTINGS, FINE)]
    return float(np.abs(vals[1] - vals[0]).max() / np.abs(vals[1]).max())


def stability(kind, pmap=map):
    """The vector Gamma_2 at the first sample and axis 0, at the largest and smallest kappa."""
    ks = (KAPPAS[0], KAPPAS[-1])
    return max(pmap(stability_one, [kind] * len(ks), ks))


def run(log=print, pmap=map):
    res = {"pre_registration": "7613ffb", "kappas": list(KAPPAS), "pass_slope": PASS_SLOPE,
           "kill_slope": KILL_SLOPE, "settings": SETTINGS, "fine": FINE}
    cal = lbc.slice_run("continuum", 0.04, lbc.SETTINGS, ["vector", "scalar"])[0]
    res["calibration_continuum_worst"] = {g: float(max(v)) for g, v in cal.items()}
    log("calibration (continuum, Pauli-Villars): " +
        "  ".join(f"{g} {max(v):.2e}" for g, v in cal.items()))
    if not all(np.isfinite(max(v)) and max(v) < CAL_MAX for v in cal.values()):
        raise Invalid(f"calibration {res['calibration_continuum_worst']!r} is not below {CAL_MAX}")
    ks = (KAPPAS[0], KAPPAS[-1])
    stab = list(pmap(stability_one, ["half", "half", "raw", "raw"], ks + ks))
    for kind, s in (("half", max(stab[:2])), ("raw", max(stab[2:]))):
        res[f"stability_{kind}"] = s
        log(f"stability ({kind}): {s:.2e}")
        if not s < STAB_MAX:
            raise Invalid(f"{kind} slice: Gamma_2 changes by {s:.2e} under finer integration")
    for kind, contacts in (("half", ["vector", "scalar", "blind"]), ("raw", ["vector"])):
        per = {g: [] for g in contacts}
        med = {g: [] for g in contacts}
        outs = list(pmap(slice_run, [kind] * len(KAPPAS), KAPPAS, [SETTINGS] * len(KAPPAS),
                         [contacts] * len(KAPPAS)))
        for kp, out in zip(KAPPAS, outs):
            for g in contacts:
                if not all(np.isfinite(v) and v > 0 for v in out[g]):
                    raise Invalid(f"non-finite or zero defect, {kind} {g} kappa={kp}")
                per[g].append(float(max(out[g])))
                med[g].append(float(np.median(out[g])))
            log(f"{kind} kappa {kp}: " + "  ".join(f"{g} {per[g][-1]:.3e}" for g in contacts))
        res[kind] = {g: {"worst_defect": per[g], "median_defect": med[g], "slope": lbc.slope(per[g])}
                     for g in contacts}
    blind_ok = min(res["half"]["blind"]["median_defect"]) >= CONTROL_MIN
    raw_ok = res["raw"]["vector"]["slope"] < KILL_SLOPE
    res["controls"] = {"blind_fails": blind_ok, "raw_fails": raw_ok}
    graded = {}
    for g in ("vector", "scalar"):
        s = res["half"][g]["slope"]
        graded[g] = lbc.verdict(s, blind_ok, raw_ok)
        log(f"graded {g}: slope {s:.3f} -> {graded[g]}")
    log(f"controls: blind fails {blind_ok}, raw fails {raw_ok} (raw slope "
        f"{res['raw']['vector']['slope']:.3f})")
    res["graded"] = graded
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    ap.add_argument("--jobs", type=int, default=1)
    a = ap.parse_args()
    try:
        if a.jobs > 1:
            from concurrent.futures import ProcessPoolExecutor
            with ProcessPoolExecutor(a.jobs) as ex:
                res = run(log=lambda s: print(s, flush=True), pmap=ex.map)
        else:
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
