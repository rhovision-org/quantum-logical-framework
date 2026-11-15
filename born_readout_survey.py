#!/usr/bin/env python3
"""Which readouts carry an unnormalized amplitude? Exact survey (Born_Readout_Criterion.md).

For a geometry (preparation word, two apparatus words) the first-closure census of
contextual_census.py gives integer branch amplitudes A_+(d), A_-(d). The unnormalized amplitude
T = sum_d A(d) 8^(-d/2) exists iff every root lambda of the sequence's *minimal linear recurrence*
has |lambda|^2 < 8 (Born_Readout_Criterion.md sec 3, Lean: QLF_ReadoutCriterion). This script finds
that recurrence exactly: Berlekamp-Massey modulo many primes, CRT lift to integers, then a check of
the lifted recurrence on every computed integer term. No float eigen-decomposition and no growth fit
decide anything; floats are used only to print root moduli, and integer |lambda|^2 = n is confirmed
by exact division by x^2 + n.

    python3 born_readout_survey.py --R 2            # the capacity-2 survey
    python3 born_readout_survey.py --R 3            # the artifact test
    python3 born_readout_survey.py --operator 2     # minimal polynomial of the transfer operator
    python3 born_readout_survey.py --geometries 2   # the seven contextual_census geometries

Needs numpy only for printing root moduli.
"""
import argparse
import itertools
import random
import sys
from collections import Counter
from multiprocessing import Pool

import contextual_census as cc

PRIMES = [(1 << 61) - 1, (1 << 31) - 1, 1000000007, 998244353, 1000000009, 2147483629,
          4294967291, (1 << 59) - 55, (1 << 62) - 57, (1 << 60) - 93, (1 << 57) - 13,
          (1 << 58) - 27, (1 << 56) - 5, (1 << 55) - 55, (1 << 54) - 33, (1 << 53) - 111]


# --------------------------------------------------------------------------- #
# exact minimal recurrence of an integer sequence
# --------------------------------------------------------------------------- #
def bm_mod(s, p):
    """Berlekamp-Massey mod p. Returns (C, L): C[0] = 1, sum_i C[i] s[n-i] = 0 for n >= L."""
    s = [x % p for x in s]
    C, B, L, m, b = [1], [1], 0, 1, 1
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            d = (d + C[i] * s[n - i]) % p
        if d == 0:
            m += 1
            continue
        coef = d * pow(b, p - 2, p) % p
        T = C[:]
        C = C + [0] * (len(B) + m - len(C))
        for i in range(len(B)):
            C[i + m] = (C[i + m] - coef * B[i]) % p
        if 2 * L <= n:
            L, B, b, m = n + 1 - L, T, d, 1
        else:
            m += 1
    return C[:L + 1] + [0] * (L + 1 - len(C)), L


def min_recurrence(seq):
    """Exact integer minimal recurrence: coefficients c (c[0] = 1, monic polynomial
    x^L + c[1] x^(L-1) + ... + c[L]) and its order L, verified on every term given.
    Raises if the sequence is too short to certify (L > len/2 - 4)."""
    if not any(seq):
        return [1], 0
    runs = [bm_mod(seq, p) for p in PRIMES]
    L = max(l for _, l in runs)
    if 2 * L + 8 > len(seq):
        raise RuntimeError(f"recurrence order {L} not certified by {len(seq)} terms")
    M, co = 1, [0] * (L + 1)
    for p, (C, l) in zip(PRIMES, runs):
        if l != L:
            continue
        for i in range(L + 1):
            t = ((C[i] - co[i]) * pow(M, -1, p)) % p
            co[i] += M * t
        M *= p
        sym = [c if c <= M // 2 else c - M for c in co]
        if all(sum(sym[i] * seq[n - i] for i in range(L + 1)) == 0 for n in range(L, len(seq))):
            return sym, L
    raise RuntimeError("CRT lift did not verify")


def divides_x2_plus(co, n):
    """Does x^2 + n divide the monic integer polynomial with coefficients co (descending)?"""
    rem = list(co)
    for i in range(len(rem) - 2):
        q = rem[i]
        rem[i + 2] -= n * q
        rem[i] = 0
    return rem[-2] == 0 and rem[-1] == 0 if len(rem) >= 2 else False


def root_moduli_sq(co):
    """|lambda|^2 of the nonzero roots, each confirmed exact when it is an integer."""
    import numpy as np
    while len(co) > 1 and co[-1] == 0:          # strip the factor x^k (finite transient)
        co = co[:-1]
    if len(co) <= 1:
        return []
    out = []
    for r in np.roots([float(c) for c in co]):
        m = abs(r) ** 2
        k = round(m)
        exact = abs(m - k) < 1e-6 and divides_x2_plus(co, k)
        out.append((k if exact else m, exact))
    return out


# --------------------------------------------------------------------------- #
# one geometry
# --------------------------------------------------------------------------- #
def classify(args):
    prep, bp, bm, R, N = args
    try:
        A, _ = cc.first_closure_census(prep, [bp, bm], R, N)
    except ValueError:
        return None
    if not any(A[0]) and not any(A[1]):
        return (prep, bp, bm, "nothing-closes", [], [])
    mods, recs = [], []
    for seq in A:
        co, L = min_recurrence(seq)
        recs.append(co)
        mods += root_moduli_sq(co)
    top = max((m for m, _ in mods), default=0.0)
    verdict = ("finite" if not mods else
               "summable" if top < 8 - 1e-9 else
               "marginal" if abs(top - 8) < 1e-9 else "divergent")
    return (prep, bp, bm, verdict, sorted(set(m for m, _ in mods), key=float),
            [all(e for _, e in mods)])


def survey(R, N, procs):
    words = [''.join(w) for L in (1, 2) for w in itertools.product(cc.ALPHABET, repeat=L)]
    jobs = []
    for prep in words:
        for bp, bm in itertools.combinations(words, 2):
            tp = tuple(-x for x in cc.imbalance(bp))
            tm = tuple(-x for x in cc.imbalance(bm))
            if tp == tm:
                continue
            jobs.append((prep, bp, bm, R, N))
    with Pool(procs) as pool:
        res = [r for r in pool.imap_unordered(classify, jobs, chunksize=64) if r is not None]
    return res


def report(res, R):
    v = Counter(r[3] for r in res)
    print(f"\n===== capacity R = {R}: {len(res)} geometries")
    for k in ("nothing-closes", "finite", "summable", "marginal", "divergent"):
        print(f"  {k:<15} {v.get(k, 0)}")
    closing = len(res) - v.get("nothing-closes", 0)
    if closing:
        print(f"  summable fraction among geometries that close: "
              f"{v.get('summable', 0) / closing:.4%}")
    spect = Counter()
    irr_low = []
    for r in res:
        if r[3] in ("summable", "marginal"):
            key = tuple(m if isinstance(m, int) else round(m, 6) for m in r[4])
            spect[(r[3], key)] += 1
            if any(not isinstance(m, int) for m in r[4]):
                irr_low.append(r[:3])
    print("  joint-support |lambda|^2 sets at or below threshold:")
    for (verdict, key), n in sorted(spect.items(), key=lambda t: (t[0][0], str(t[0][1]))):
        print(f"    {verdict:<9} {str(list(key)):<28} {n}")
    print(f"  irrational |lambda|^2 at or below threshold: {len(irr_low)}"
          + (f"  e.g. {irr_low[:3]}" if irr_low else ""))
    return v


def operator_minpoly(R, absorb=(), seed=1):
    """Minimal polynomial of the capacity-R transfer operator (absorbing at `absorb`), by
    Wiedemann's method: the minimal recurrence of u T^d v for random integer u, v."""
    rng = range(-R, R + 1)
    S = [((a, b, c, d), (p & 1, (p >> 1) & 1, (p >> 2) & 1))
         for a in rng for b in rng for c in rng for d in rng
         if abs(a) + abs(b) + abs(c) + abs(d) <= R for p in range(8)]
    idx = {s: i for i, s in enumerate(S)}
    cols = [{} if s[0] in absorb else
            {idx[t]: x for t, x in cc._step({s: 1}, R).items() if x} for s in S]
    random.seed(seed)
    u = [random.randint(-5, 5) for _ in S]
    w = [random.randint(-5, 5) for _ in S]
    seq = []
    for _ in range(2 * len(S) + 16):
        seq.append(sum(a * b for a, b in zip(u, w)))
        nw = [0] * len(S)
        for i, x in enumerate(w):
            if x:
                for j, a in cols[i].items():
                    nw[j] += a * x
        w = nw
    return len(S), min_recurrence(seq)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--R", type=int, default=0, help="run the survey at this capacity")
    ap.add_argument("--N", type=int, default=0, help="depths to compute (default 4*deg+60)")
    ap.add_argument("--procs", type=int, default=4)
    ap.add_argument("--operator", type=int, default=0, metavar="R")
    ap.add_argument("--geometries", type=int, default=0, metavar="R")
    a = ap.parse_args()
    if a.operator:
        n, (co, L) = operator_minpoly(a.operator)
        print(f"R = {a.operator}: {n} states, minimal polynomial degree {L}, coefficients {co}")
        print("  |lambda|^2 of nonzero roots:", root_moduli_sq(co))
    if a.geometries:
        for label, prep, bp, bm, _ in cc.geometries():
            r = classify((prep, bp, bm, a.geometries, 120))
            print(f"  {label:<34} {r[3] if r else 'shared target':<15} {r[4] if r else ''}")
    if a.R:
        _, (_, deg) = operator_minpoly(a.R)
        N = a.N or 4 * deg + 60
        print(f"transfer operator minimal-polynomial degree {deg}; computing {N} depths")
        report(survey(a.R, N, a.procs), a.R)


if __name__ == "__main__":
    sys.exit(main())
