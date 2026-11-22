#!/usr/bin/env python3
"""
morphogenesis_census.py — does closure alone differentiate a diverse population?

The pre-registered test of Morphogenesis.md §4. Part of the Quantum Logical Framework (QLF),
README.md. ZFA is equal and opposite quantum logical action with zero free energy.

Setup. A periodic lattice in d = 1 or 2 dimensions. Each site holds open single-twist strands,
counted by type (the eight twists ^ v < > / \\ + -). The initial population is diverse and
patternless: every site gets an independent Poisson number of each type, the same mean for all
eight. Every step, every strand hops to a uniformly random nearest neighbour. Then the closure rule
acts at every site. Three variants differ ONLY in the closure rule:

  G      the algebra. Two strands close iff their joint history is ZFA. For single twists that is
         iff they are conjugate (lean/QLF_Morphogenesis.lean, bind_iff_opposite, up_binds_down,
         up_not_binds_left). Each closure leaves the population as a receipt. By region_closes_iff
         a site is left holding exactly its ledger.
  R_all  the closure-compatibility graph, which is complete (closures_always_compatible): any two
         strands at a site close, whatever their types. This destroys the conserved ledger.
  D      no closure at all (promotion disabled).

Nothing in any rule refers to a pattern, a domain, or a target.

Statistics (fixed before any run, Morphogenesis.md §4):
  S(t)  axis segregation. For each axis a, phi_a(x) = n_{+a}(x) - n_{-a}(x). Among nearest-
        neighbour pairs with both phi_a != 0, the fraction with the same sign, minus the
        same-sign fraction expected from the site sign frequencies (p+^2 + p-^2). Averaged over
        the four axes. 0 = no spatial organisation; 0.5 = complete segregation.
  Q(t)  dominant-type agreement (the input text's statistic): among nearest-neighbour pairs of
        occupied sites, the fraction whose dominant type agrees, minus sum over types of p^2.
  rho(t) strand density, for the classical-exponent check P2.

P4 adds a source: pair creation, each site each step with probability LAMBDA, puts a conjugate
pair on an axis chosen uniformly, one strand on the site and one on a random neighbour. It
conserves the global ledger (a pair is a closure split in two, QLF_Morphogenesis.hop_flux).

Usage:
    python3 morphogenesis_census.py            # full run, writes data/morphogenesis_census.json
    python3 morphogenesis_census.py --quick    # small smoke run, no file written
"""

import argparse
import json
import math
import os
import sys

import numpy as np

CONJ = [(0, 1), (2, 3), (4, 5), (6, 7)]  # (^,v) (<,>) (/,\) (+,-)


def neighbours_shift(d):
    """The 2d nearest-neighbour displacement directions."""
    out = []
    for ax in range(d):
        for s in (1, -1):
            out.append((ax, s))
    return out


def hop(n, rng, d):
    """Lazy walk: each strand stays with probability 1/2, else hops to a random neighbour.

    Amendment A1 (Morphogenesis.md §4): with every strand hopping every step, strands on the two
    sublattices of a bipartite lattice never share a site, so the lattice splits into two
    independent populations and every nearest-neighbour bond compares them. Staying with
    probability 1/2 removes the parity.
    """
    dirs = neighbours_shift(d)
    k = len(dirs)
    moves = rng.multinomial(n, [0.5] + [0.5 / k] * k)  # shape n.shape + (k+1,)
    out = moves[..., 0].copy()
    for i, (ax, s) in enumerate(dirs, start=1):
        out += np.roll(moves[..., i], s, axis=ax)
    return out


def hop_sparse(n, rng, d):
    """The same lazy walk as `hop`, computed only on occupied cells (fast at low density).

    Same distribution as `hop` (zero-count cells draw nothing, so on test seeds it reproduces
    `hop` exactly). Used for the P2' run (Morphogenesis.md §4b).
    """
    dirs = neighbours_shift(d)
    k = len(dirs)
    idx = np.nonzero(n)
    counts = n[idx]
    moves = rng.multinomial(counts, [0.5] + [0.5 / k] * k)
    out = np.zeros_like(n)
    np.add.at(out, idx, moves[:, 0])
    shape = n.shape
    for i, (ax, s) in enumerate(dirs, start=1):
        coords = list(idx)
        coords[ax] = (coords[ax] + s) % shape[ax]
        np.add.at(out, tuple(coords), moves[:, i])
    return out


def l1_ledger(n):
    """ell^1 size of the whole lattice's ledger: sum over axes of |N_+ - N_-|."""
    tot = n.reshape(-1, 8).sum(axis=0)
    return int(sum(abs(int(tot[2 * a]) - int(tot[2 * a + 1])) for a in range(4)))


def run_p2prime(size, T, seed, times):
    """P2': d = 2, variant G, sparse hop; also checks the Lean lower bound at every sample."""
    rng = np.random.default_rng(seed)
    n = rng.poisson(1.0 / 8.0, size=(size, size, 8)).astype(np.int64)
    n = close_G(n, rng)
    floor = l1_ledger(n)
    V = size * size
    rec = {"t": [], "rho": [], "S": [], "floor_rho": floor / V, "bound_ok": True}
    tset = set(times)
    for t in range(1, T + 1):
        n = hop_sparse(n, rng, 2)
        n = close_G(n, rng)
        if t in tset:
            mass = int(n.sum())
            if mass < floor or l1_ledger(n) != floor:
                rec["bound_ok"] = False
            rec["t"].append(t)
            rec["rho"].append(mass / V)
            rec["S"].append(stat_S(n, 2))
    return rec


def close_G(n, rng):
    """The algebra: conjugate strands close pairwise; each site keeps its ledger."""
    for i, j in CONJ:
        m = np.minimum(n[..., i], n[..., j])
        n[..., i] -= m
        n[..., j] -= m
    return n


def close_Rall(n, rng):
    """Complete compatibility: any two strands close; an odd site keeps one random strand."""
    k = n.sum(axis=-1)
    odd = (k % 2) == 1
    out = np.zeros_like(n)
    if odd.any():
        counts = n[odd]                       # (m, 8)
        c = counts.cumsum(axis=-1)
        r = (rng.random(counts.shape[0]) * c[:, -1]).astype(np.int64)
        t = (r[:, None] < c).argmax(axis=-1)  # survivor type, prob proportional to counts
        surv = np.zeros_like(counts)
        surv[np.arange(counts.shape[0]), t] = 1
        out[odd] = surv
    return out


def close_D(n, rng):
    return n


RULES = {"G": close_G, "R_all": close_Rall, "D": close_D}


def pair_source(n, rng, d, lam):
    """Pair creation: a conjugate pair split across a site and a random neighbour."""
    shape = n.shape[:-1]
    born = rng.random(shape) < lam
    if not born.any():
        return n
    idx = np.argwhere(born)
    axes = rng.integers(0, 4, size=len(idx))
    dirs = neighbours_shift(d)
    which = rng.integers(0, len(dirs), size=len(idx))
    for (pos, a, w) in zip(idx, axes, which):
        p = tuple(pos)
        n[p + (2 * a,)] += 1
        ax, s = dirs[w]
        q = list(pos)
        q[ax] = (q[ax] + s) % shape[ax]
        n[tuple(q) + (2 * a + 1,)] += 1
    return n


def nn_pairs(arr, d):
    """Yield (a, b) arrays for each forward nearest-neighbour bond."""
    for ax in range(d):
        yield arr, np.roll(arr, -1, axis=ax)


def stat_S(n, d):
    vals = []
    for a in range(4):
        phi = n[..., 2 * a] - n[..., 2 * a + 1]
        sg = np.sign(phi)
        nz = sg != 0
        if nz.sum() < 2:
            continue
        pp = (sg > 0).sum() / nz.sum()
        base = pp ** 2 + (1 - pp) ** 2
        same = 0
        tot = 0
        for x, y in nn_pairs(sg, d):
            both = (x != 0) & (y != 0)
            tot += both.sum()
            same += ((x == y) & both).sum()
        if tot == 0:
            continue
        vals.append(same / tot - base)
    return float(np.mean(vals)) if vals else float("nan")


def stat_Q(n, d, rng):
    occ = n.sum(axis=-1) > 0
    if occ.sum() < 2:
        return float("nan")
    noise = rng.random(n.shape) * 0.5  # random tie-breaking, never changes a strict maximum
    dom = np.where(occ, (n + noise).argmax(axis=-1), -1)
    p = np.array([(dom == t).sum() for t in range(8)], dtype=float) / occ.sum()
    base = (p ** 2).sum()
    agree = 0
    tot = 0
    for x, y in nn_pairs(dom, d):
        both = (x >= 0) & (y >= 0)
        tot += both.sum()
        agree += ((x == y) & both).sum()
    if tot == 0:
        return float("nan")
    return float(agree / tot - base)


def run(d, size, T, rho0, rule, seed, times, lam=0.0):
    rng = np.random.default_rng(seed)
    shape = (size,) * d + (8,)
    n = rng.poisson(rho0 / 8.0, size=shape).astype(np.int64)
    n = RULES[rule](n, rng)
    V = size ** d
    rec = {"t": [], "rho": [], "S": [], "Q": []}
    tset = set(times)
    for t in range(1, T + 1):
        n = hop(n, rng, d)
        if lam > 0:
            n = pair_source(n, rng, d, lam)
        n = RULES[rule](n, rng)
        if t in tset:
            rec["t"].append(t)
            rec["rho"].append(float(n.sum() / V))
            rec["S"].append(stat_S(n, d))
            rec["Q"].append(stat_Q(n, d, rng))
    return rec


def logtimes(T, k=12):
    ts = sorted({max(1, int(round(T ** (i / (k - 1))))) for i in range(k)})
    return ts


def summarize(recs):
    keys = ["rho", "S", "Q"]
    out = {"t": recs[0]["t"]}
    for key in keys:
        arr = np.array([r[key] for r in recs], dtype=float)
        out[key + "_mean"] = np.nanmean(arr, axis=0).tolist()
        out[key + "_se"] = (np.nanstd(arr, axis=0, ddof=1) / math.sqrt(arr.shape[0])).tolist()
    return out


def slope(ts, ys, lo):
    ts = np.array(ts, float)
    ys = np.array(ys, float)
    m = (ts >= lo) & (ys > 0)
    if m.sum() < 2:
        return float("nan")
    return float(np.polyfit(np.log(ts[m]), np.log(ys[m]), 1)[0])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--p2prime", type=int, metavar="SEED",
                    help="run one seed of the P2' configuration (Morphogenesis.md §4b)")
    args = ap.parse_args()

    if args.p2prime is not None:
        size, T = (1024, 16384)
        rec = run_p2prime(size, T, 20000 + args.p2prime, logtimes(T, 15))
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data",
                            f"morphogenesis_p2prime_seed{args.p2prime}.json")
        with open(path, "w") as fh:
            json.dump(rec, fh, indent=1)
        print("wrote", path, "bound_ok", rec["bound_ok"])
        return 0

    if args.quick:
        configs = {1: (256, 256), 2: (32, 64)}
        seeds = 2
    else:
        configs = {1: (2048, 4096), 2: (128, 1024)}
        seeds = 8
    rho0 = 1.0
    LAMBDA = 0.002

    results = {"preregistration": "Morphogenesis.md §4", "rho0": rho0, "seeds": seeds,
               "runs": {}, "verdicts": {}}
    for d, (size, T) in configs.items():
        times = logtimes(T)
        for rule in ("G", "R_all", "D"):
            recs = [run(d, size, T, rho0, rule, 1000 * d + s, times) for s in range(seeds)]
            summ = summarize(recs)
            summ["rho_slope_late"] = slope(summ["t"], summ["rho_mean"], T / 16)
            results["runs"][f"d{d}_{rule}"] = summ
            print(f"d={d} {rule:5s} S={summ['S_mean'][-1]:+.3f}±{summ['S_se'][-1]:.3f} "
                  f"Q={summ['Q_mean'][-1]:+.3f}±{summ['Q_se'][-1]:.3f} "
                  f"rho={summ['rho_mean'][-1]:.4f} slope={summ['rho_slope_late']:+.3f}",
                  flush=True)
        # P4: pair source, G and D
        for rule in ("G", "D"):
            recs = [run(d, size, T, rho0, rule, 5000 + 1000 * d + s, times, lam=LAMBDA)
                    for s in range(seeds)]
            summ = summarize(recs)
            results["runs"][f"d{d}_{rule}_source"] = summ
            print(f"d={d} {rule:5s}+source S={summ['S_mean'][-1]:+.3f}±{summ['S_se'][-1]:.3f} "
                  f"Q={summ['Q_mean'][-1]:+.3f} rho={summ['rho_mean'][-1]:.4f}", flush=True)

    # Verdicts, exactly as pre-registered.
    R = results["runs"]
    V = results["verdicts"]
    for d in configs:
        g = R[f"d{d}_G"]
        sg, seg = g["S_mean"][-1], g["S_se"][-1]
        # Amendment A2: a control with no measurable bond (S = nan at every seed) is reported as
        # not measurable and left out of the comparison; the remaining control decides.
        cs = [(R[f"d{d}_{c}"]["S_mean"][-1], R[f"d{d}_{c}"]["S_se"][-1]) for c in ("R_all", "D")]
        cs = [(m, e if not math.isnan(e) else 0.0) for m, e in cs if not math.isnan(m)]
        ctrl = max(m for m, _ in cs)
        cse = max(e for _, e in cs)
        p1 = sg >= 0.2 and (sg - ctrl) > 3 * math.hypot(seg, cse)
        kill = sg < 0.1 or (sg - ctrl) <= 3 * math.hypot(seg, cse)
        V[f"P1_d{d}"] = {"S_G": sg, "S_ctrl_max": ctrl, "controls_measured": len(cs), "pass": bool(p1), "kill": bool(kill)}
        lo, hi = {1: (-0.32, -0.18), 2: (-0.60, -0.40)}[d]
        sG = g["rho_slope_late"]
        V[f"P2_G_d{d}"] = {"slope": sG, "window": [lo, hi], "pass": bool(lo <= sG <= hi)}
        if d == 1:
            sR = R["d1_R_all"]["rho_slope_late"]
            V["P2_Rall_d1"] = {"slope": sR, "window": [-0.60, -0.40],
                               "pass": bool(-0.60 <= sR <= -0.40)}
        s4 = R[f"d{d}_G_source"]
        late = s4["S_mean"][-3:]
        late_se = s4["S_se"][-3:]
        m4 = float(np.mean(late))
        se4 = float(np.mean(late_se))
        V[f"P4_d{d}"] = {"S_late": m4, "se": se4, "pass": bool(m4 >= 0.1 and m4 > 3 * se4)}
    for k, v in V.items():
        print(k, v)

    if not args.quick:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data",
                            "morphogenesis_census.json")
        with open(path, "w") as fh:
            json.dump(results, fh, indent=1, sort_keys=True)
        print("wrote", path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
