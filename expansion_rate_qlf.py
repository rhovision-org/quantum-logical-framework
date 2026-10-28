#!/usr/bin/env python3
"""
expansion_rate_qlf.py -- the pre-registered census test for the per-charge
expand/contract amplitude of Lumina_QLF.md sec 11.

Lumina_QLF.md sec 10 left one piece open: the *amplitude* of the expand/contract
term -- the ZFA interaction rate per free charge that turns the ionization-tracking
prediction from a direction into a number. QLF_ExpansionCharge (Lean, CI-green)
proved the term lives on the gauge (charge) axis and nowhere else; it is zero for
neutral matter and switched on by net charge. This script measures the amplitude
as an EXACT-INTEGER census count, not a fit, and never reads the legacy value of
anything (no cross-sections, no Thomson, no H0).

                        ---- THE MODEL ----

A free charge is one net unmatched gauge twist: `-` = a free electron (expands
future space), `+` = a free proton / positron (contracts local space). A seed of
k free charges of one sign is "-"*k or "+"*k. By QLF_ExpansionCharge every ZFA
closure must balance the gauge axis, so each free charge must recruit its opposite
partner inside a full closure. The amplitude per free charge is the free action that
one such recruitment carries.

The gauge axis is a SINGLE binary distinction (+ vs -), one axis of the four. One
free charge is therefore one binary choice = one bit. QLF_FreeEnergy proves every
ZFA closure carries dF = -log 2 (one bit, binary_kl). So the motivated prediction is

    amplitude per free charge = log 2  = Omega_Lambda   (not log 8).

the SAME log 2 that fixes the cosmological constant -- the gauge sector is binary,
the three spatial axes carry extension, not charge.

                   ---- PRE-REGISTERED KILL CONDITIONS ----
         (frozen in this commit BEFORE the script was ever run; the
          numbers below are computed by the reader, not by the author)

K1  SYMMETRY (framework check). The first-closure multiplicity and the max-excursion
    histogram from "+"*k must equal those from "-"*k EXACTLY, for k = 1,2,3. Gauge
    conjugation is an alphabet symmetry; if + and - closure censuses differ, the
    charge-expansion picture is broken at the root -> strong kill, test void.

K2  AMPLITUDE = Omega_Lambda. The per-charge gauge multiplicity factor -- the ratio
    W(k+1)/W(k) of first-closure multiplicities as one more free charge is added --
    must converge to 2, i.e. one added bit per added charge, i.e.
    amplitude = log 2 = Omega_Lambda.
      PASS  : W(k+1)/W(k) -> 2 (exact integers), so the sec-10 amplitude is log 2,
              tied to the already-established dark-energy quantum.
      FAIL  : the ratio is some other clean constant c (amplitude = log c, reported
              as the real but un-anticipated number) or does not converge (amplitude
              stays open). A FAIL is reported as a FAIL; the measured constant stands.

K1 and K2 are independent: K1 can pass while K2 fails. The SIGN of the term (- expands,
+ contracts) is NOT tested here -- by K1 the static counts are +/- symmetric, so the
sign is carried by the time arrow (closedAtHorizon_mono), not by any count. This script
tests only the MAGNITUDE.

Units: pure counts. Pure Python, reuses twist_core + qucalc_search. Depth cap 7.
"""
import math
import sys
from collections import Counter

from qucalc_search import search, max_excursion

DEPTH_CAP = 7
KMAX = 3


def census(seed: str, depth_cap: int = DEPTH_CAP):
    """First-closure (absorbing / events) census from a charged seed.
    Returns (multiplicity W, excursion-histogram Counter, min closure depth)."""
    W = 0
    exc = Counter()
    dmin = None
    for rec in search(seed, max_depth=depth_cap, limit=None, absorbing=True):
        W += 1
        exc[max_excursion(rec["history"])] += 1
        if dmin is None:
            dmin = rec["depth"]
    return W, exc, dmin


def kraft_mass(seed: str, depth_cap: int):
    """Kraft cylinder mass of a charged seed's first-closures: sum of 8^-depth over the
    absorbing (prefix-free) closures reachable within `depth_cap`. This is the conditional
    probability that a random continuation closes the seed -- depth-convergent (8^-depth
    decays), unlike the raw count. twist_kraft (QLF_KraftMeasure) bounds it by 1."""
    M = 0.0
    for rec in search(seed, max_depth=depth_cap, limit=None, absorbing=True):
        M += 8.0 ** (-rec["depth"])
    return M


def kraft_main():
    print("Per-charge amplitude -- Kraft-corrected estimator (Lumina_QLF.md sec 12)")
    print("M(k,D) = sum 8^-depth over first-closures of a k-charge seed; depth-independent.\n")

    depths = [5, 6, 7]
    print(f"Convergence of M(k,D) with depth cap D  (sign -):")
    print(f"  {'k':>2}  " + "  ".join(f"D={d:<10}" for d in depths))
    Mfinal = {}
    for k in range(1, KMAX + 1):
        row = [kraft_mass("-" * k, d) for d in depths]
        Mfinal[k] = row[-1]
        print(f"  {k:>2}  " + "  ".join(f"{m:<11.7f}" for m in row))

    # symmetry check at D = 7
    print(f"\n+/- symmetry of M at D={depths[-1]} (must match, by §11 K1):")
    sym_ok = True
    for k in range(1, KMAX + 1):
        mp = kraft_mass("+" * k, depths[-1])
        mm = Mfinal[k]
        ok = abs(mp - mm) < 1e-12
        sym_ok = sym_ok and ok
        print(f"  k={k}: M(+)={mp:.7f}  M(-)={mm:.7f}  {'match' if ok else 'DIFFER'}")

    print(f"\nPer-charge marginal surprisal  -ln[M(k+1)/M(k)]  (nats), vs ln 2 = {math.log(2):.5f}:")
    margs = []
    for k in range(1, KMAX):
        r = Mfinal[k + 1] / Mfinal[k]
        s = -math.log(r)
        margs.append(s)
        print(f"  -ln[M({k+1})/M({k})] = -ln({r:.5f}) = {s:.5f} nats")

    # reference constants
    LN2 = math.log(2)
    P4 = 0.1932015             # prime-closure mass, Closure_Walk.md
    print(f"\nReference QLF constants: ln 2 = {LN2:.5f},  p4 (prime-closure mass) = {P4:.5f},")
    print(f"  -ln p4 = {-math.log(P4):.5f},  M(1,7) itself = {Mfinal[1]:.7f}")

    print("\n" + "=" * 60)
    print("PRE-REGISTERED VERDICT (sec 12)")
    print("=" * 60)
    conv = len(margs) >= 2 and abs(margs[-1] - margs[-2]) < 0.05
    print(f"C1 (symmetry M(+)=M(-)): {'PASS' if sym_ok else 'FAIL'}")
    print(f"C2 (marginal surprisal converges): {'PASS' if conv else 'FAIL -- not settled at depth 7'}"
          f"  [last two: {[round(m,4) for m in margs[-2:]]}]")
    if conv:
        val = margs[-1]
        hit_ln2 = abs(val - LN2) < 0.03
        print(f"C3 (amplitude = ln 2 = Omega_Lambda): {'PASS' if hit_ln2 else 'FAIL'}"
              f"  (measured {val:.5f} nats = ln {math.exp(val):.4f})")
        if not hit_ln2:
            print(f"   measured per-charge amplitude = {val:.5f} nats; reported as the substrate value.")
    print()


def main():
    print("Per-charge expand/contract amplitude -- pre-registered census test")
    print(f"(Lumina_QLF.md sec 11; depth cap {DEPTH_CAP}; first-closure / events census)\n")

    plus, minus = {}, {}
    for k in range(1, KMAX + 1):
        plus[k] = census("+" * k)
        minus[k] = census("-" * k)

    print(f"{'k':>2} {'seed':>6} {'W (sign +)':>11} {'W (sign -)':>11} "
          f"{'dmin+':>6} {'dmin-':>6} {'K1 sym?':>8}")
    k1_ok = True
    for k in range(1, KMAX + 1):
        Wp, ep, dp = plus[k]
        Wm, em, dm = minus[k]
        sym = (Wp == Wm and ep == em and dp == dm)
        k1_ok = k1_ok and sym
        print(f"{k:>2} {'-'*0 + '+'*k:>6} {Wp:>11} {Wm:>11} {str(dp):>6} {str(dm):>6} "
              f"{'yes' if sym else 'NO':>8}")

    print("\nMax-excursion histograms (sign + ; sign - must match by K1):")
    for k in range(1, KMAX + 1):
        Wp, ep, dp = plus[k]
        Wm, em, dm = minus[k]
        allk = sorted(set(ep) | set(em))
        print(f"  k={k}:  + {{" + ", ".join(f'{e}:{ep[e]}' for e in allk) + "}")
        print(f"        - {{" + ", ".join(f'{e}:{em[e]}' for e in allk) + "}")

    print("\nPer-charge gauge multiplicity factor  W(k+1)/W(k)  (sign -):")
    ratios = []
    for k in range(1, KMAX):
        Wk = minus[k][0]
        Wk1 = minus[k + 1][0]
        r = Wk1 / Wk if Wk else float("nan")
        ratios.append(r)
        print(f"  W({k+1})/W({k}) = {Wk1} / {Wk} = {r:.4f}")

    print("\n" + "=" * 60)
    print("PRE-REGISTERED VERDICT")
    print("=" * 60)
    print(f"K1 (+/- symmetry, framework check): {'PASS' if k1_ok else 'FAIL -> test void, framework bug'}")

    # K2: ratio -> 2 ?
    last = ratios[-1] if ratios else float("nan")
    k2_pass = abs(last - 2.0) < 1e-9 and all(abs(r - 2.0) < 1e-9 for r in ratios)
    if k2_pass:
        print(f"K2 (amplitude = log 2 = Omega_Lambda): PASS  (ratio = 2 exactly)")
        print(f"   => per-charge expand/contract amplitude = log 2 = {math.log(2):.6f}")
    else:
        print(f"K2 (amplitude = log 2 = Omega_Lambda): FAIL")
        print(f"   measured ratio(s): {[round(r,4) for r in ratios]}")
        if ratios and all(abs(r - ratios[-1]) < 1e-9 for r in ratios) and ratios[-1] == int(ratios[-1]):
            c = int(ratios[-1])
            print(f"   converges to a clean constant c = {c}; measured amplitude = log {c} = {math.log(c):.6f}")
        else:
            print(f"   does not converge to a clean constant at this depth; amplitude stays OPEN")
    print()


if __name__ == "__main__":
    if "--kraft" in sys.argv:
        kraft_main()
    else:
        main()
