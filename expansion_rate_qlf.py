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
    main()
