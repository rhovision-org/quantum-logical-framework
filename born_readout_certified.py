#!/usr/bin/env python3
"""Certified Born readout survey: every verdict exact, at every depth (Born_Readout_Criterion.md §2).

born_readout_survey.py finds each branch sequence's recurrence from a finite prefix and classifies
roots with floating point. This module removes both gaps (review of PR #245):

1. **Annihilator, certified for all depths.** For each absorbing operator M (one per target pair) a
   candidate polynomial m is found by Wiedemann's method and then *certified*: m(M) X0 = 0, where
   X0 holds every preparation's state vector. The identity is checked modulo K primes whose product
   exceeds twice a proved bound on every entry (|(M^k x)_i| <= rho^k |x|_inf with rho the largest
   absolute row sum of M), so it holds exactly over Z. Then m(M) M^d X0 = 0 for every d, and every
   readout u.M^d.v satisfies the m-recurrence at every depth.
2. **Minimal recurrence, exactly.** m is factored over Z. The minimal recurrence of a sequence
   divides m, so it is prod f_j^{a_j}; a_j is the least a for which m / f_j^(e_j - a) annihilates the
   sequence. Annihilation of an m-recurrent sequence is decided by its first deg(m) values, each
   checked modulo the same primes under a proved bound, so a_j is exact.
3. **Disk position, exactly.** For each irreducible factor f, P(y) with P(x^2) = +-f(x)f(-x) has the
   squared roots; S(w) = P(8w). Strict stability (every |lambda|^2 < 8) is the Schur-Cohn test in
   exact rationals; "no root outside" is decided by splitting off gcd(S, S*) (S* the reciprocal),
   whose roots are on the circle iff a Chebyshev-substituted polynomial has all its roots real in
   [-2, 2] (Sturm count). No floating point decides anything; floats are printed for orientation only.

    python3 born_readout_certified.py --R 2
    python3 born_readout_certified.py --R 3
    python3 born_readout_certified.py --selftest      # disk tests on random polynomials with prescribed roots

Needs numpy (vector arithmetic modulo primes) and sympy (integer factorisation).
"""
import argparse
import itertools
import math
import random
import sys
from collections import Counter
from fractions import Fraction
from multiprocessing import Pool

import contextual_census as cc
from born_readout_survey import bm_mod


# --------------------------------------------------------------------------- #
# primes below 2^25: products of two stay below 2^50, so int64 sums of 2^13 terms cannot overflow
# --------------------------------------------------------------------------- #
def _is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


PRIMES = []
_c = (1 << 25) - 1
while len(PRIMES) < 200:
    if _is_prime(_c):
        PRIMES.append(_c)
    _c -= 2


# --------------------------------------------------------------------------- #
# exact polynomial arithmetic; coefficient lists are ASCENDING (index = power)
# --------------------------------------------------------------------------- #
def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return trim(out)


def pdivmod(a, b):
    a = [Fraction(x) for x in trim(a)]
    b = [Fraction(x) for x in trim(b)]
    if len(a) < len(b):
        return [Fraction(0)], a
    q = [Fraction(0)] * (len(a) - len(b) + 1)
    for k in range(len(a) - len(b), -1, -1):
        c = a[k + len(b) - 1] / b[-1]
        q[k] = c
        for j, y in enumerate(b):
            a[k + j] -= c * y
    return trim(q), trim(a[:len(b) - 1] or [Fraction(0)])


def pgcd(a, b):
    a, b = trim(a), trim(b)
    while any(b):
        _, r = pdivmod(a, b)
        a, b = b, r
    a = [Fraction(x) for x in a]
    return [x / a[-1] for x in a]


def pderiv(a):
    return trim([i * a[i] for i in range(1, len(a))] or [0])


def peval(a, x):
    v = 0
    for c in reversed(a):
        v = v * x + c
    return v


def is_zero(a):
    return all(x == 0 for x in a)


def schur_strict(p):
    """All roots of p (ascending, real coefficients) strictly inside |w| < 1? Schur-Cohn."""
    p = [Fraction(x) for x in trim(p)]
    while len(p) > 1:
        n = len(p) - 1
        if abs(p[0]) >= abs(p[n]):
            return False
        p = trim([p[n] * p[i + 1] - p[0] * p[n - 1 - i] for i in range(n)])
    return True


def sturm_count(r, lo, hi):
    """Number of distinct real roots of r in [lo, hi] (exact)."""
    seq = [[Fraction(x) for x in trim(r)], [Fraction(x) for x in pderiv(r)]]
    while not is_zero(seq[-1]) and len(seq[-1]) > 1:
        _, rem = pdivmod(seq[-2], seq[-1])
        seq.append([-x for x in rem])
    seq = [s for s in seq if not is_zero(s)]

    def changes(x):
        vals = [peval(s, x) for s in seq]
        vals = [v for v in vals if v != 0]
        return sum(1 for a, b in zip(vals, vals[1:]) if (a < 0) != (b < 0))

    n = changes(lo) - changes(hi)
    if peval(r, lo) == 0:
        n += 1
    return n


def all_on_circle(g):
    """Every root of g (ascending, rational) on |w| = 1?"""
    g = trim(g)
    for root in (1, -1):
        while len(g) > 1 and peval(g, root) == 0:
            g, _ = pdivmod(g, [-root, 1])
    if len(g) == 1:
        return True
    if len(g) % 2 == 0:            # odd degree with w = +-1 removed cannot be self-reciprocal
        return False
    lead = g[-1]
    g = [Fraction(x) / lead for x in g]
    m = (len(g) - 1) // 2
    if any(g[k] != g[2 * m - k] for k in range(len(g))):
        return False               # not self-reciprocal: some root r has 1/r not a root
    # w^-m g(w) = g_m + sum_k g_{m+k} (w^k + w^-k);  w^k + w^-k = D_k(t), t = w + 1/w
    D = [[Fraction(2)], [Fraction(0), Fraction(1)]]
    for k in range(2, m + 1):
        nxt = [Fraction(0)] + D[k - 1]
        for i, c in enumerate(D[k - 2]):
            nxt[i] -= c
        D.append(nxt)
    R = [Fraction(0)] * (m + 1)
    R[0] += g[m]
    for k in range(1, m + 1):
        for i, c in enumerate(D[k]):
            R[i] += g[m + k] * c
    R = trim(R)
    sq = pdivmod(R, pgcd(R, pderiv(R)))[0]
    return sturm_count(sq, -2, 2) == len(sq) - 1


def disk_position(S):
    """'inside' (all |w| < 1), 'boundary' (none outside, some on), or 'outside'."""
    S = trim(S)
    if schur_strict(S):
        return "inside"
    Sr = list(reversed(S))
    g = pgcd(S, Sr)
    h, rem = pdivmod(S, g)
    assert is_zero(rem)
    if len(g) > 1 and all_on_circle(g) and schur_strict(h):
        return "boundary"
    return "outside"


def squared_root_poly(f):
    """P with P(x^2) = +-f(x) f(-x): its roots are the lambda^2 of f's roots. Ascending."""
    fneg = [c if i % 2 == 0 else -c for i, c in enumerate(f)]
    prod = pmul(f, fneg)
    assert all(prod[i] == 0 for i in range(1, len(prod), 2))
    return trim(prod[0::2])


def factor_class(f):
    """Exact position of an irreducible integer factor's roots relative to |lambda|^2 = 8."""
    if f == [0, 1]:
        return "zero", "0"
    P = squared_root_poly(f)
    S = [c * 8 ** i for i, c in enumerate(P)]
    pos = disk_position(S)
    if len(f) == 3 and f[1] == 0:          # x^2 + n: |lambda|^2 = |n| exactly
        label = str(abs(f[0]))
    else:
        import numpy as np
        mods = sorted({round(abs(r), 6) for r in np.roots([float(c) for c in reversed(P)])})
        label = "~" + "/".join(f"{m:g}" for m in mods)
    return pos, label


# --------------------------------------------------------------------------- #
# one target pair: certified annihilator, exact minimal recurrences, exact verdicts
# --------------------------------------------------------------------------- #
_OPER = {}


def parse_rule(rule):
    """A capacity rule: which running imbalances (v, h, d, l) a horizon can hold.

    l1:R      |v|+|h|+|d|+|l| <= R   (the census's own rule, contextual_census.free_action)
    linf:R    max(|v|,|h|,|d|,|l|) <= R
    split:S,G |v|+|h|+|d| <= S and |l| <= G   (spatial and gauge capacities separately)
    Returns (allowed(imb) -> bool, box bound B with every allowed |x_a| <= B).
    """
    kind, _, arg = str(rule).partition(":")
    if not arg:                                   # a bare integer is the l1 rule
        kind, arg = "l1", kind
    if kind == "l1":
        R = int(arg)
        return (lambda imb: sum(abs(x) for x in imb) <= R), R
    if kind == "linf":
        R = int(arg)
        return (lambda imb: max(abs(x) for x in imb) <= R), R
    if kind == "split":
        Sp, G = (int(x) for x in arg.split(","))
        return (lambda imb: abs(imb[0]) + abs(imb[1]) + abs(imb[2]) <= Sp and abs(imb[3]) <= G), max(Sp, G)
    raise ValueError(f"unknown capacity rule {rule!r}")


def _install_rule(rule):
    """Route contextual_census's capacity test through `rule`: with capacity 0 the census drops
    exactly the extensions whose free action exceeds 0, and free_action is now 0 iff allowed."""
    allowed, _ = parse_rule(rule)
    cc.free_action = lambda imb: 0 if allowed(imb) else 1


def _init_oper(R):
    import numpy as np
    allowed, B = parse_rule(R)
    _install_rule(R)
    rng = range(-B, B + 1)
    S = [((a, b, c, d), (p & 1, (p >> 1) & 1, (p >> 2) & 1))
         for a in rng for b in rng for c in rng for d in rng
         if allowed((a, b, c, d)) for p in range(8)]
    idx = {s: i for i, s in enumerate(S)}
    rows, cols, vals = [], [], []
    for s, i in idx.items():
        for t, x in cc._step({s: 1}, 0).items():
            if x:
                rows.append(idx[t]); cols.append(i); vals.append(x)
    _OPER[R] = (S, idx, np.array(rows), np.array(cols), np.array(vals, dtype=np.int64))


def _matvec(r_, c_, v_, X, p):
    import numpy as np
    Y = np.zeros_like(X)
    np.add.at(Y, r_, (v_[:, None] * X[c_]) % p)
    return Y % p


def _target_set(args):
    import numpy as np
    import sympy
    R, tp, tm, pairs, preps, seed = args
    S, idx, rows, cols, vals = _OPER[R]
    keep = np.array([S[c][0] not in (tp, tm) for c in cols])
    r_, c_, v_ = rows[keep], cols[keep], vals[keep]
    n = len(S)
    rowsum = np.zeros(n, dtype=np.int64)
    np.add.at(rowsum, r_, np.abs(v_))
    rho = int(rowsum.max()) if len(r_) else 0
    rho = max(rho, 1)

    X0 = np.zeros((n, len(preps)), dtype=object)
    for k, prep in enumerate(preps):
        for s, a in cc._feed(cc.START, prep, 0).items():
            X0[idx[s], k] += a
    x0max = max(1, max(abs(int(x)) for x in X0.flat))
    words = sorted({w for pr in pairs for w in pr})
    U = {}
    for w in words:
        u = [0] * n
        tgt = tuple(-x for x in cc.imbalance(w))
        for s, i in idx.items():
            if s[0] == tgt:
                closed = cc._feed({s: 1}, w, 0)
                u[i] = sum(a for (imb, _), a in closed.items() if imb == (0, 0, 0, 0))
        U[w] = u
    umax = max(1, max(sum(abs(x) for x in u) for u in U.values()))

    # -- candidate annihilator of M on span(X0): Wiedemann with one random projection
    rnd = random.Random(seed)
    rv = [rnd.randint(-9, 9) for _ in preps]
    uv = [rnd.randint(-9, 9) for _ in range(n)]
    z0 = [sum(int(X0[i, k]) * rv[k] for k in range(len(preps))) for i in range(n)]

    def proj_seq(p, N):
        z = np.array([x % p for x in z0], dtype=np.int64)[:, None]
        uu = np.array([x % p for x in uv], dtype=np.int64)
        out = []
        for _ in range(N):
            out.append(int(uu @ z[:, 0] % p))
            z = _matvec(r_, c_, v_, z, p)
        return out

    _, D = bm_mod(proj_seq(PRIMES[0], 2 * n + 8), PRIMES[0])
    # a priori bounds: every root of M has |lambda| <= rho, so every monic divisor of m of degree
    # L has coefficient sum <= (1 + rho)^L; entries of M^k x are bounded by rho^k |x|_inf
    N = 2 * D + 2
    bound = (1 + rho) ** D * umax * x0max * rho ** N
    bits = 2 * bound.bit_length() + 8
    K, prod = 0, 1
    while prod.bit_length() <= bits:
        prod *= PRIMES[K]
        K += 1
    ps = PRIMES[:K]

    # lift m by CRT (coefficients bounded by (1+rho)^D, far inside prod/2)
    mods = []
    for p in ps:
        C, L = bm_mod(proj_seq(p, 2 * D + 8), p)
        if L != D:
            raise RuntimeError("annihilator degree differs between primes")
        mods.append(C)
    Mod, co = 1, [0] * (D + 1)
    for p, C in zip(ps, mods):
        for i in range(D + 1):
            co[i] += Mod * (((C[i] - co[i]) * pow(Mod, -1, p)) % p)
        Mod *= p
    conn = [c if c <= Mod // 2 else c - Mod for c in co]      # conn[0] = 1
    m_asc = list(reversed(conn))                              # m(x) = x^D + conn[1] x^(D-1) + ...

    # -- state vectors and branch sequences modulo every prime
    seqs = {}           # p -> array (N+1, nwords*nprep)
    cert_ok = True
    Uarr = None
    for p in ps:
        X = np.array([[int(x) % p for x in row] for row in X0], dtype=np.int64)
        Up = np.array([[x % p for x in U[w]] for w in words], dtype=np.int64)
        hist = []
        acc = np.zeros_like(X)
        for d in range(N + 1):
            if d <= D:
                acc = (acc + (m_asc[d] % p) * X) % p
            hist.append((Up @ X % p).reshape(-1))
            if d < N:
                X = _matvec(r_, c_, v_, X, p)
        if acc.any():
            cert_ok = False
        seqs[p] = np.array(hist, dtype=np.int64)
    b1 = sum(abs(c) for c in m_asc) * rho ** D * x0max
    if not cert_ok or 2 * b1 >= prod:
        # a random projection can miss a component of the Krylov space; the certificate catches
        # it, so retrying with a fresh projection is safe (nothing uncertified is ever used)
        if seed >= 1000 * 8:
            raise RuntimeError(f"annihilator certificate failed for targets {tp}, {tm}")
        return _target_set((R, tp, tm, pairs, preps, seed + 1000))

    # -- exact minimal recurrence of every sequence as a product of m's irreducible factors
    x = sympy.symbols('x')
    _, flist = sympy.factor_list(sum(sympy.Integer(c) * x ** i for i, c in enumerate(m_asc)))
    factors = [([int(c) for c in reversed(sympy.Poly(f, x).all_coeffs())], e) for f, e in flist]
    nseq = len(words) * len(preps)
    expo = [[e] * nseq for _, e in factors]

    def annihilates(g):
        """Boolean per sequence: does the integer polynomial g annihilate it, at every depth?"""
        b2 = sum(abs(c) for c in g) * umax * x0max * rho ** N
        assert 2 * b2 < prod
        ok = np.ones(nseq, dtype=bool)
        G = len(g) - 1
        for p in ps:
            gp = np.array([c % p for c in g], dtype=np.int64)
            H = np.zeros((D, N + 1), dtype=np.int64)
            for d in range(D):
                H[d, d:d + G + 1] = gp
            t = (H @ seqs[p]) % p
            ok &= ~t.any(axis=0)
        return ok

    for j, (f, e) in enumerate(factors):
        for a in range(e - 1, -1, -1):
            g = m_asc
            for _ in range(e - a):
                g, rem = pdivmod(g, f)
                assert is_zero(rem)
            g = [int(c) for c in g]
            ok = annihilates(g)
            for s in range(nseq):
                if ok[s] and expo[j][s] == a + 1:
                    expo[j][s] = a

    fclass = [factor_class(f) for f, _ in factors]
    res = []
    widx = {w: i for i, w in enumerate(words)}
    sqfree_fail = 0
    for bp, bm in pairs:
        for k, prep in enumerate(preps):
            sids = [widx[bp] * len(preps) + k, widx[bm] * len(preps) + k]
            support = [(j, max(expo[j][s] for s in sids)) for j in range(len(factors))]
            support = [(j, a) for j, a in support if a > 0]
            if not support:
                res.append((prep, bp, bm, "nothing-closes", (), False))
                continue
            nz = [(j, a) for j, a in support if fclass[j][0] != "zero"]
            if not nz:
                res.append((prep, bp, bm, "finite", (), False))
                continue
            pos = {fclass[j][0] for j, _ in nz}
            verdict = ("divergent" if "outside" in pos else
                       "marginal" if "boundary" in pos else "summable")
            repeated = any(a > 1 for _, a in nz)
            sqfree_fail += repeated
            labels = tuple(sorted({fclass[j][1] for j, _ in nz}, key=lambda s: (s[0] == "~", s)))
            res.append((prep, bp, bm, verdict, labels, repeated))
    return res, D, K


def survey(R, procs, seed=1, only=None, checkpoint=None):
    words = [''.join(w) for L in (1, 2) for w in itertools.product(cc.ALPHABET, repeat=L)]
    groups = {}
    for bp, bm in itertools.combinations(words, 2):
        tp = tuple(-x for x in cc.imbalance(bp))
        tm = tuple(-x for x in cc.imbalance(bm))
        if tp != tm:
            groups.setdefault(frozenset((tp, tm)), []).append((bp, bm))
    jobs = [(R, *sorted(key), pairs, words, seed) for key, pairs in groups.items()]
    if only is not None:
        jobs = [j for j in jobs if (j[1], j[2]) in only]
    # optional checkpoint: one JSON line per finished target pair, so a restart loses only the
    # pairs in progress. The first line is a provenance header (rule, seed, the geometry set, and
    # SHA-256 of the three source files); a checkpoint whose header does not match this run is
    # refused, so resuming can never mix rows from different code, rules or geometries.
    parts, done = [], set()
    meta = None
    if checkpoint:
        import hashlib
        import json
        import os
        here = os.path.dirname(os.path.abspath(__file__))
        meta = {"rule": str(R), "seed": seed,
                "geometries": hashlib.sha256(repr([(j[1], j[2], j[3], j[4]) for j in jobs])
                                             .encode()).hexdigest(),
                "sources": {f: hashlib.sha256(open(os.path.join(here, f), "rb").read()).hexdigest()
                            for f in ("born_readout_certified.py", "contextual_census.py",
                                      "born_readout_survey.py")}}
        if os.path.exists(checkpoint) and os.path.getsize(checkpoint):
            with open(checkpoint) as fh:
                head = json.loads(fh.readline())
                if head.get("meta") != meta:
                    raise RuntimeError(f"checkpoint {checkpoint} was written by a different "
                                       f"rule, seed, geometry set or source; refusing to resume")
                for line in fh:
                    rec = json.loads(line)
                    key = (tuple(rec["key"][0]), tuple(rec["key"][1]))
                    rows = [(a, b, c, v, tuple(lab), rep_) for a, b, c, v, lab, rep_ in rec["rows"]]
                    parts.append((rows, rec["D"], rec["K"]))
                    done.add(key)
        else:
            with open(checkpoint, "w") as fh:
                fh.write(json.dumps({"meta": meta}) + "\n")
        jobs = [j for j in jobs if (j[1], j[2]) not in done]
        print(f"checkpoint {checkpoint}: {len(done)} target pairs done, {len(jobs)} to run", flush=True)
    _init_oper(R)
    with Pool(procs, initializer=_init_oper, initargs=(R,)) as pool:
        for job, part in zip(jobs, pool.imap(_target_set, jobs)):
            parts.append(part)
            if checkpoint:
                with open(checkpoint, "a") as fh:
                    fh.write(json.dumps({"key": [job[1], job[2]], "rows": part[0],
                                         "D": part[1], "K": part[2]}) + "\n")
    rows = [r for part, _, _ in parts for r in part]
    Ds = [D for _, D, _ in parts]
    Ks = [K for _, _, K in parts]
    return rows, Ds, Ks


def report(rows, Ds, Ks, R):
    v = Counter(r[3] for r in rows)
    print(f"\n===== CERTIFIED capacity R = {R}: {len(rows)} geometries, {len(Ds)} absorbing operators, "
          f"{len(_OPER[R][0])} states")
    print(f"  certified annihilator degree: {min(Ds)}..{max(Ds)};  primes per certificate: "
          f"{min(Ks)}..{max(Ks)}")
    for k in ("nothing-closes", "finite", "summable", "marginal", "divergent"):
        print(f"  {k:<15} {v.get(k, 0)}")
    rep = Counter(r[3] for r in rows if r[5])
    print(f"  with a repeated root in the support: {dict(rep) if rep else 'none'}")
    sup = Counter((r[3], r[4]) for r in rows if r[3] in ("summable", "marginal"))
    print("  supports at or below the threshold (|lambda|^2 exact for x^2+n factors; ~ = other):")
    for (verdict, lab), c in sorted(sup.items()):
        print(f"    {verdict:<9} {str(list(lab)):<34} {c}")


def selftest(trials=3000):
    import numpy as np
    rnd = random.Random(7)
    bad = 0
    for _ in range(trials):
        deg = rnd.randint(1, 6)
        roots = []
        while len(roots) < deg:
            kind = rnd.random()
            r = rnd.choice([0.5, 1.0, 1.5]) * rnd.choice([1, -1])
            if kind < 0.3 and len(roots) <= deg - 2:
                th = rnd.choice([math.pi / 3, math.pi / 2, 2 * math.pi / 3])
                roots += [complex(r * math.cos(th), r * math.sin(th)),
                          complex(r * math.cos(th), -r * math.sin(th))]
            else:
                roots.append(complex(r, 0))
        coeffs = np.poly(roots).real
        # exact rational version of the same polynomial (roots chosen so coefficients are dyadic/rational)
        p = [Fraction(c).limit_denominator(10 ** 6) for c in reversed(coeffs)]
        if abs(peval([float(c) for c in p], 0.0) - np.polyval(coeffs, 0.0)) > 1e-9:
            continue
        # expected verdict from the roots as chosen (exact moduli 0.5, 1, 1.5), not from a float
        # root-finder: numpy misplaces repeated unit-circle roots by ~1e-8
        mods = [abs(z) for z in roots]
        want = ("inside" if max(mods) < 0.75 else
                "boundary" if max(mods) < 1.25 else "outside")
        got = disk_position(p)
        if got != want:
            bad += 1
            print("MISMATCH", p, mods, want, got)
    print(f"selftest: {trials} random polynomials, {bad} mismatches")
    return bad


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--R", default="",
                    help="capacity rule: an integer (l1), or l1:R, linf:R, split:S,G (see parse_rule)")
    ap.add_argument("--procs", type=int, default=4)
    ap.add_argument("--checkpoint", default=None,
                    help="JSON-lines file: finished target pairs are appended and skipped on rerun")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return 1 if selftest() else 0
    if a.R:
        rows, Ds, Ks = survey(a.R, a.procs, checkpoint=a.checkpoint)
        report(rows, Ds, Ks, a.R)
    return 0


if __name__ == "__main__":
    sys.exit(main())
