#!/usr/bin/env python3
"""Pre-registered check for stage 5 of the relativity dependency chain: the one-loop contact amplitude.

Part of the [Quantum Logical Framework (QLF)](README.md). The pre-registration is
[Relativity_Principle.md](Relativity_Principle.md) §6b, "Stage 5 pre-registration", committed
(7c3102f) before this script was written. External reference: Collins, Perez, Sudarsky, Urrutia and
Vucetich, Phys. Rev. Lett. 93, 191301 (2004), arXiv:gr-qc/0403053.

Question. Stage 4b found the walk's tree-level contact vertex frame independent to O(kappa^2) for
Lorentz-scalar contacts. Collins et al. showed that Lorentz violation at the cutoff, suppressed at
tree level, can return at order one through loops. This script computes the one-loop contact
vertex of two walk particles and asks whether its frame dependence still falls as kappa^2.

The amplitude (Feynman ordering, borrowed from QFT; deriving it is stage 6):

    L(E, P) = int_BZ d^3p/(2 pi)^3 [ L1+(p) (x) L2+(P-p) R(E - w1(p) - w2(P-p))
                                   - L1-(p) (x) L2-(P-p) R(E + w1(p) + w2(P-p)) ],

R(x) = cot((x + i0)/2)/2 on the walk (energies mod 2 pi) and 1/(x + i0) in the continuum, with
L+- the band projectors and w the positive quasi-energy. The one-loop vertex is
Gamma_2 = Gamma L Gamma - c Gamma, with c the Hilbert-Schmidt component along Gamma of
Gamma L Gamma at the rest-frame threshold. The graded quantity is the stage-4b vertex proxy with
Gamma_2 in place of Gamma, and its relative change under a boost of the external legs.

Integration. Every singular surface of R (the two-particle shells, including the walk's doubler
corners, where the both-negative term wraps by 2 pi) sits inside a ball integrated in spherical
coordinates with the pole subtracted on each ray (principal value plus -i pi times the residue).
The rest of the zone is a uniform periodic grid weighted by one minus the balls' smooth bump. The
continuum is regulated by Pauli-Villars and integrated radially to a large radius.

Gates (fail closed, INVALID, nothing graded): every walk step has bands +-w with the projector
identity holding to 1e-9; every singular surface is inside a ball (checked on every outer grid
point and every ray); every W_2 is finite, real and positive; the calibration is below 1e-6; the
vector Gamma_2 is stable under a finer integration to 1e-3 relative at the largest and smallest
kappa.

Usage: python3 loop_boost_check.py [--json data/loop_boost_check.json]
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
    "vector": np.kron(I4, I4) - sum(np.kron(a, a) for a in ALPHA),
    "scalar": np.kron(BETA, BETA),
    "blind": np.kron(I4, I4),
}

# ---- pre-registered grid (Relativity_Principle.md §6b, Stage 5) ----
SEED = 20261128
N_SAMPLES = 4
MASS_RATIO = 1.0
MB_RATIO = 0.6
ETA = 0.5
KAPPAS = (0.08, 0.04, 0.02, 0.01, 0.005)
PASS_SLOPE = 1.95
KILL_SLOPE = 1.5
CAL_MAX = 1e-6
CONTROL_MIN = 1e-2
STAB_MAX = 1e-3
IMAG_TOL = 1e-10
PV_SCALES = (3.0, 4.0, 5.0, 6.0)

# ---- integration settings (chosen by convergence of L and the calibration only) ----
SETTINGS = {"n_theta": 32, "n_phi": 64, "n_gl": 24, "n_grid": 64, "r1": 0.3, "r_in": 0.6,
            "r_max": 300.0}
FINE = {"n_theta": 40, "n_phi": 80, "n_gl": 32, "n_grid": 80, "r1": 0.3, "r_in": 0.6,
        "r_max": 300.0}
# Chosen by the calibration alone (kappa = 0.04, worst vector defect): 16x32 rays, 16 nodes,
# r_max 3e3 gave 3.1e-5; 24x48 rays 1.1e-5; 24 nodes 2.0e-5; r_max 1e4 1.6e-4 (Pauli-Villars
# cancellation loses precision at large radius); 32x64 rays, 24 nodes, r_max 1e3 1.0e-5; the same
# with r_max 300, 7.3e-7.


# =============================== bands ===================================

def _real_step(T, k):
    e = np.exp(1j * k)[:, None, None]
    return e * bsc.fix(T)[None] + np.conj(e) * bsc.fix(-T)[None]


def _real_walk(ky, kx, kz):
    a, b, c = _real_step(bsc.UP, ky / 2), _real_step(bsc.LEFT, kx / 2), _real_step(bsc.SLASH, kz / 2)
    return a @ b @ c @ c @ b @ a


def _handed(p):
    ky, kx, kz = p[:, 0], p[:, 1], p[:, 2]
    r, l = _real_walk(ky, kx, kz), _real_walk(-ky, -kx, -kz)
    fr, fl = bsc.fix(bsc.SLASH), bsc.fix(-bsc.SLASH)
    return np.einsum("ij,nkl->nikjl", fr, r).reshape(-1, 4, 4) + \
        np.einsum("ij,nkl->nikjl", fl, l).reshape(-1, 4, 4)


def walk_bands(slice_):
    """Batched w(p) and projectors of the walk on a slice. p: (n, 3) in the order (ky, kx, kz)."""
    def f(p, m):
        h = _handed(p)
        if slice_ == "raw":
            u = bsc.mass_step(m)[None] @ h
        else:
            ms = bsc.mass_step(m / 2)[None]
            u = ms @ h @ ms
        c = np.real(np.trace(u, axis1=1, axis2=2)) / 4
        w = np.arccos(np.clip(c, -1, 1))
        ud = np.conj(np.transpose(u, (0, 2, 1)))
        resid = np.abs(u + ud - 2 * c[:, None, None] * I4[None]).max()
        if not resid < 1e-9:
            raise Invalid(f"walk step is not of the form exp(+-i w): residual {resid:.2e}")
        s = (u - ud) / (2j * np.sin(w))[:, None, None]
        return w, (I4[None] + s) / 2, (I4[None] - s) / 2
    return f


def dirac_bands(p, m):
    h = np.einsum("ni,ijk->njk", p, np.array(ALPHA)) + m * BETA[None]
    w = np.sqrt(np.einsum("ni,ni->n", p, p) + m * m)
    s = h / w[:, None, None]
    return w, (I4[None] + s) / 2, (I4[None] - s) / 2


# ============================ loop integral ==============================

def kern(x, lattice):
    return 0.5 / np.tan(x / 2) if lattice else 1.0 / x


def _acc(a, A, B):
    """sum_n a_n A_n (x) B_n as a 16 x 16 matrix."""
    return np.einsum("n,nij,nkl->ikjl", a, A, B).reshape(16, 16)


class Model:
    """The two-particle integrand of one slice (walk or continuum) at fixed masses."""

    def __init__(self, bands, lattice, mA, mB):
        self.bands, self.lattice, self.mA, self.mB = bands, lattice, mA, mB

    def terms(self, p, E, P, scale=1.0):
        w1, a1p, a1m = self.bands(p, scale * self.mA)
        w2, a2p, a2m = self.bands(P[None] - p, scale * self.mB)
        xpp = E - w1 - w2
        xmm = E + w1 + w2 - (2 * np.pi if self.lattice else 0.0)
        return (xpp, a1p, a2p), (xmm, a1m, a2m)

    def x_of(self, which, p, E, P):
        w1 = self.bands(p, self.mA)[0]
        w2 = self.bands(P[None] - p, self.mB)[0]
        return E - w1 - w2 if which == 0 else E + w1 + w2 - (2 * np.pi if self.lattice else 0.0)


def _bump(r, r1, r_in):
    t = np.clip((r - r1) / (r_in - r1), 0.0, 1.0)
    with np.errstate(divide="ignore", over="ignore"):
        a = np.where(t > 0, np.exp(-1.0 / np.where(t > 0, t, 1)), 0.0)
        b = np.where(t < 1, np.exp(-1.0 / np.where(t < 1, 1 - t, 1)), 0.0)
    return 1.0 - a / (a + b)


def _rays(st):
    ct, wt = np.polynomial.legendre.leggauss(st["n_theta"])
    ph = (np.arange(st["n_phi"]) + 0.5) * 2 * np.pi / st["n_phi"]
    st_ = np.sqrt(1 - ct ** 2)
    n = np.stack([np.outer(st_, np.cos(ph)), np.outer(st_, np.sin(ph)),
                  np.outer(ct, np.ones_like(ph))], axis=-1).reshape(-1, 3)
    w = np.outer(wt, np.full(st["n_phi"], 2 * np.pi / st["n_phi"])).reshape(-1)
    return n, w


def _panels(lo, hi, k):
    """k geometric panels from lo > 0 to hi."""
    b = lo * (hi / lo) ** (np.arange(k + 1) / k)
    return list(zip(b[:-1], b[1:]))


def ball(model, center, which, E, P, st, coeffs):
    """Integrate chi * F over a ball around `center`, with the pole of term `which` handled.
    coeffs: list of (scale, c) Pauli-Villars terms; only scale 1 can be singular."""
    n, wang = _rays(st)
    r1, r_in = st["r1"], st["r_in"]
    xg, wg = np.polynomial.legendre.leggauss(st["n_gl"])

    # root of the singular argument along each ray, inside r < r1
    def xs(r):
        return model.x_of(which, center[None] + r[:, None] * n, E, P)
    lo = np.full(len(n), 1e-12)
    hi = np.full(len(n), r1)
    flo, fhi = xs(lo), xs(hi)
    has = np.sign(flo) != np.sign(fhi)
    for _ in range(64):
        mid = (lo + hi) / 2
        fm = xs(mid)
        left = np.sign(fm) == np.sign(flo)
        lo = np.where(left, mid, lo)
        flo = np.where(left, fm, flo)
        hi = np.where(left, hi, mid)
    r0 = np.where(has, (lo + hi) / 2, 1e-3 * r1)
    # the singular argument must not vanish again anywhere in the ball
    rr = r1 * np.geomspace(1e-6, 1.0, 48)
    sg = np.stack([np.sign(xs(np.full(len(n), q))) for q in rr]
                  + [np.sign(xs(np.full(len(n), q))) for q in np.linspace(r1, r_in, 12)])
    if np.any(np.sum(sg[1:] != sg[:-1], axis=0) > 1):
        raise Invalid("a singular surface crosses a ray more than once, or outside r < r1")

    total = np.zeros((16, 16), complex)
    # radial panels per ray, same count for every ray
    pan = [(0.0 * r0, r0 / 2), (r0 / 2, r0)]
    geo = [(r0 * (r1 / r0) ** (i / 6), r0 * (r1 / r0) ** ((i + 1) / 6)) for i in range(6)]
    tr = [(r1 + (r_in - r1) * i / 4, r1 + (r_in - r1) * (i + 1) / 4) for i in range(4)]
    pan = pan + geo + [(np.full_like(r0, a), np.full_like(r0, b)) for a, b in tr]

    sing_h0 = None
    if np.any(has):
        dlt = 1e-6 * np.maximum(r0, 1e-3)
        xp = (xs(r0 + dlt) - xs(r0 - dlt)) / (2 * dlt)
        p0 = center[None] + r0[:, None] * n
        (xpp, a1, b1), (xmm, a2, b2) = model.terms(p0, E, P)
        A, B = (a1, b1) if which == 0 else (a2, b2)
        sgn = 1.0 if which == 0 else -1.0
        sing_h0 = (A, B, sgn * r0 ** 2 * wang / xp * has, r0, xp)

    for a, b in pan:
        for xi, wi in zip(xg, wg):
            r = (b - a) / 2 * xi + (b + a) / 2
            wr = (b - a) / 2 * wi * r ** 2 * _bump(r, r1, r_in) * wang / (2 * np.pi) ** 3
            p = center[None] + r[:, None] * n
            for scale, cj in coeffs:
                (xpp, a1, b1), (xmm, a2, b2) = model.terms(p, E, P, scale)
                total += cj * _acc(wr * kern(xpp, model.lattice), a1, b1)
                total -= cj * _acc(wr * kern(xmm, model.lattice), a2, b2)
            if sing_h0 is not None:
                A, B, coef, r0_, xp = sing_h0
                sub = coef / (r - r0_) * (b - a) / 2 * wi / (2 * np.pi) ** 3
                total -= _acc(sub, A, B)
    if sing_h0 is not None:
        A, B, coef, r0_, xp = sing_h0
        pv = coef * np.log((r_in - r0_) / r0_) / (2 * np.pi) ** 3
        im = -1j * np.pi * coef * np.sign(xp) / (2 * np.pi) ** 3
        total += _acc(pv + im, A, B)
    return total


def singular_centers(model, E, P):
    """Balls: one per point where a two-particle shell can sit (walk: the eight zone corners)."""
    shift = P * model.mA / (model.mA + model.mB)
    if not model.lattice:
        return [(shift, 0)]
    out = []
    for cy in (0.0, np.pi):
        for cx in (0.0, np.pi):
            for cz in (0.0, np.pi):
                c = np.array([cy, cx, cz])
                w = model.bands(c[None], model.mA)[0][0]
                if abs(w - model.mA) < 1e-9:
                    out.append((c + shift, 0))
                elif abs(w - (np.pi - model.mA)) < 1e-9:
                    out.append((c + shift, 1))
                else:
                    raise Invalid(f"zone corner {c} is neither a band bottom nor a band top (w = {w})")
    return out


def outer_lattice(model, centers, E, P, st):
    n = st["n_grid"]
    g = (np.arange(n) + 0.5) * 2 * np.pi / n - np.pi
    pts = np.stack(np.meshgrid(g, g, g, indexing="ij"), axis=-1).reshape(-1, 3)
    wt = np.ones(len(pts))
    for c, _ in centers:
        d = (pts - c[None] + np.pi) % (2 * np.pi) - np.pi
        wt -= _bump(np.linalg.norm(d, axis=1), st["r1"], st["r_in"])
    keep = wt > 1e-15
    pts, wt = pts[keep], wt[keep] / n ** 3
    total = np.zeros((16, 16), complex)
    for ch in np.array_split(np.arange(len(pts)), max(1, len(pts) // 40000)):
        (xpp, a1, b1), (xmm, a2, b2) = model.terms(pts[ch], E, P)
        if np.abs(np.sin(xpp / 2)).min() < 0.05 or np.abs(np.sin(xmm / 2)).min() < 0.05:
            raise Invalid("a singular surface lies outside the integration balls")
        total += _acc(wt[ch] * kern(xpp, True), a1, b1)
        total -= _acc(wt[ch] * kern(xmm, True), a2, b2)
    return total


def outer_continuum(model, center, E, P, st, coeffs):
    n, wang = _rays(st)
    xg, wg = np.polynomial.legendre.leggauss(st["n_gl"])
    r1, r_in, rmax = st["r1"], st["r_in"], st["r_max"]
    pans = [(r1 + (r_in - r1) * i / 4, r1 + (r_in - r1) * (i + 1) / 4) for i in range(4)]
    k = int(np.ceil(np.log2(rmax / r_in)))
    pans += _panels(r_in, rmax, k)
    total = np.zeros((16, 16), complex)
    for a, b in pans:
        for xi, wi in zip(xg, wg):
            r = (b - a) / 2 * xi + (b + a) / 2
            wr = (b - a) / 2 * wi * r ** 2 * (1 - _bump(r, r1, r_in)) * wang / (2 * np.pi) ** 3
            p = center[None] + r * n
            for scale, cj in coeffs:
                (xpp, a1, b1), (xmm, a2, b2) = model.terms(p, E, P, scale)
                total += cj * _acc(wr * kern(xpp, False), a1, b1)
                total -= cj * _acc(wr * kern(xmm, False), a2, b2)
    return total


def pv_coeffs():
    s = np.array(PV_SCALES)
    A = np.vstack([s ** k for k in range(4)])
    c = np.linalg.solve(A, -np.ones(4))
    return [(1.0, 1.0)] + list(zip(PV_SCALES, c))


def loop(model, E, P, st):
    P = np.asarray(P, float)
    if model.lattice:
        cen = singular_centers(model, E, P)
        tot = outer_lattice(model, cen, E, P, st)
        for c, which in cen:
            tot += ball(model, c, which, E, P, st, [(1.0, 1.0)])
        return tot
    co = pv_coeffs()
    (c, which), = singular_centers(model, E, P)
    return ball(model, c, which, E, P, st, co) + outer_continuum(model, c, E, P, st, co)


# ============================= the check =================================

def samples():
    rng = np.random.default_rng(SEED)
    v = rng.normal(size=(N_SAMPLES, 2, 3))
    return v / np.linalg.norm(v, axis=2, keepdims=True)


def legs(kappa, d, d2):
    nrm = np.sqrt(1 + MASS_RATIO ** 2)
    p, mA = kappa / nrm, kappa * MASS_RATIO / nrm
    mB = MB_RATIO * mA
    return [(tuple(p * d), mA), (tuple(-p * d), mB), (tuple(p * d2), mA), (tuple(-p * d2), mB)], mA, mB


def W2(ext, gam2):
    """ext: four (E, projector) legs."""
    pis = [E * P for E, P in ext]
    w = np.trace(np.kron(pis[2], pis[3]) @ gam2 @ np.kron(pis[0], pis[1]) @ gam2.conj().T)
    if not (np.isfinite(w) and w.real > 0 and abs(w.imag) <= IMAG_TOL * w.real):
        raise Invalid(f"W_2 is not positive real: {w!r}")
    return float(w.real)


_CT = {}


def counterterm(model, st):
    key = (model.lattice, model.bands, model.mA, model.mB, id(st))
    if key in _CT:
        return _CT[key]
    E0 = model.bands(np.zeros((1, 3)), model.mA)[0][0] + model.bands(np.zeros((1, 3)), model.mB)[0][0]
    Lt = loop(model, E0, np.zeros(3), st)
    _CT[key] = Lt
    return Lt


def gam2(gamma, L, Lthr):
    G = gamma @ L @ gamma
    Gt = gamma @ Lthr @ gamma
    c = np.vdot(gamma, Gt) / np.vdot(gamma, gamma)
    return G - c * gamma


def slice_run(kind, kappa, st, contacts):
    """All defects at one kappa for one slice; returns {contact: [defects]} and the loops."""
    out = {g: [] for g in contacts}
    loops = []
    for d, d2 in samples():
        lg, mA, mB = legs(kappa, d, d2)
        if kind == "continuum":
            bandfn, model = bsc.dirac_band, Model(dirac_bands, False, mA, mB)
        else:
            bandfn = lambda k, m, s=kind: bsc.band(bsc.walk(k, m, s))
            model = Model(walk_bands(kind), True, mA, mB)
        Lthr = counterterm(model, st)
        f1 = [(bandfn(k, m)[1], k, m) for k, m in lg]
        E1 = f1[0][0] + f1[1][0]
        L1 = loop(model, E1, np.zeros(3), st)
        ext1 = [(E, bandfn(k, m)[0]) for E, k, m in f1]
        for i in range(3):
            f2 = []
            for E, k, m in f1:
                Eb, kb = bsc.boost(E, k, i, ETA)
                f2.append((Eb, kb, m))
            E2 = f2[0][0] + f2[1][0]
            P2 = np.add(f2[0][1], f2[1][1])
            L2 = loop(model, E2, P2, st)
            loops.append((L1, L2))
            ext2 = [(E, bandfn(k, m)[0]) for E, k, m in f2]
            for g in contacts:
                w1 = W2(ext1, gam2(GAMMA[g], L1, Lthr))
                w2 = W2(ext2, gam2(GAMMA[g], L2, Lthr))
                out[g].append(abs(w2 - w1) / w1)
    return out, loops


def slope(ys):
    s = float(np.polyfit(np.log(KAPPAS), np.log(ys), 1)[0])
    if not np.isfinite(s):
        raise Invalid(f"fitted slope {s!r} is not finite")
    return s


def stability(kind):
    """The vector Gamma_2 at the first sample and axis 0, at the largest and smallest kappa."""
    worst = 0.0
    for kappa in (KAPPAS[0], KAPPAS[-1]):
        d, d2 = samples()[0]
        lg, mA, mB = legs(kappa, d, d2)
        model = Model(walk_bands(kind), True, mA, mB) if kind != "continuum" else \
            Model(dirac_bands, False, mA, mB)
        bandfn = (lambda k, m, s=kind: bsc.band(bsc.walk(k, m, s))) if kind != "continuum" \
            else bsc.dirac_band
        E1 = bandfn(lg[0][0], mA)[1] + bandfn(lg[1][0], mB)[1]
        vals = []
        for st in (SETTINGS, FINE):
            Lthr = counterterm(model, st)
            vals.append(gam2(GAMMA["vector"], loop(model, E1, np.zeros(3), st), Lthr))
        worst = max(worst, float(np.abs(vals[1] - vals[0]).max() / np.abs(vals[1]).max()))
    return worst


def run(log=print):
    res = {"seed": SEED, "eta": ETA, "kappas": list(KAPPAS), "pass_slope": PASS_SLOPE,
           "kill_slope": KILL_SLOPE, "calibration_max": CAL_MAX, "settings": SETTINGS}
    cal = slice_run("continuum", 0.04, SETTINGS, ["vector", "scalar"])[0]
    res["calibration_continuum_worst"] = {g: float(max(v)) for g, v in cal.items()}
    log("calibration (continuum, Pauli-Villars): " +
        "  ".join(f"{g} {max(v):.2e}" for g, v in cal.items()))
    if not all(np.isfinite(max(v)) and max(v) < CAL_MAX for v in cal.values()):
        raise Invalid(f"calibration {res['calibration_continuum_worst']!r} is not below {CAL_MAX}")
    for kind in ("half", "raw"):
        s = stability(kind)
        res[f"stability_{kind}"] = s
        log(f"stability ({kind}): {s:.2e}")
        if not s < STAB_MAX:
            raise Invalid(f"{kind} slice: Gamma_2 changes by {s:.2e} under finer integration")
    for kind, contacts in (("half", ["vector", "scalar", "blind"]), ("raw", ["vector"])):
        per = {g: [] for g in contacts}
        med = {g: [] for g in contacts}
        for kp in KAPPAS:
            out, _ = slice_run(kind, kp, SETTINGS, contacts)
            for g in contacts:
                if not all(np.isfinite(v) and v > 0 for v in out[g]):
                    raise Invalid(f"non-finite or zero defect, {kind} {g} kappa={kp}")
                per[g].append(float(max(out[g])))
                med[g].append(float(np.median(out[g])))
            log(f"{kind} kappa {kp}: " + "  ".join(f"{g} {per[g][-1]:.3e}" for g in contacts))
        res[kind] = {g: {"worst_defect": per[g], "median_defect": med[g], "slope": slope(per[g])}
                     for g in contacts}
    blind_ok = min(res["half"]["blind"]["median_defect"]) >= CONTROL_MIN
    raw_ok = res["raw"]["vector"]["slope"] < KILL_SLOPE
    res["controls"] = {"blind_fails": blind_ok, "raw_fails": raw_ok}
    graded = {}
    for g in ("vector", "scalar"):
        s = res["half"][g]["slope"]
        v = "PASS" if s >= PASS_SLOPE else ("FAIL" if s < KILL_SLOPE else "INCONCLUSIVE")
        if v == "PASS" and not (blind_ok and raw_ok):
            v = "INCONCLUSIVE"
        graded[g] = v
        log(f"graded {g}: slope {s:.3f} -> {v}")
    log(f"controls: blind fails {blind_ok}, raw fails {raw_ok} (raw slope "
        f"{res['raw']['vector']['slope']:.3f})")
    res["graded"] = graded
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
