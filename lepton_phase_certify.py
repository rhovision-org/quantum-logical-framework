#!/usr/bin/env python3
"""
lepton_phase_certify.py -- certify the miss recorded by lepton_phase_series.py (#140).

lepton_phase_series.py pre-registered one statistic,

    P = sum_L w_L / (6 * 5^(L-1)),

the probability that a non-backtracking (NB) walk on Z^3 has an electron-like
free half-spin closure as its first return to the origin, and the hypothesis
H: Delta = P (radians), killed if 2/3 lies outside a bracket on P.  Its run gave
S_22 = 0.03999 and an ESTIMATED P ~ 0.041, but (review on PR #240) the only
certified enclosure was [S_N, S_N + (1 - F_N)] = [0.040, 0.944], which does not
exclude 2/3.  The review named the missing piece: a proved bound on the NB
walk's total return probability.  This script supplies it.

THE BOUND.  Let b_n be the number of NB walks of length n from the origin back
to the origin (closures allowed in the middle), and u_n = b_n / (6 * 5^(n-1))
the NB-measure of being at the origin at step n.  Every electron-like first
return of length n is one of those walks, so

    P - S_N  <=  sum_{n>N} u_n  =  E - U_N,      E = sum_{n>=1} u_n,

and P <= E outright.  E is the expected number of returns.

E IN CLOSED FORM.  NB walk counts on a (q+1)-regular graph obey the Chebyshev-
type recurrence A_0 = I, A_1 = A, A_2 = A^2 - (q+1) I, A_{n+1} = A A_n - q A_{n-1},
whence sum_n A_n z^n = (1 - z^2) / (1 - A z + q z^2) (standard; e.g. Alon,
Benjamini, Lubetzky, Sodin 2007; Fitzner and van der Hofstad 2013).  On Z^3,
q = 5 and A has Fourier symbol a(k) = 2(cos k1 + cos k2 + cos k3) = 6 D(k).  At
z = 1/5 the denominator is (6/5)(1 - D(k)), so

    sum_n b_n 5^-n = (4/5) G,     G = (2 pi)^-3 int dk / (1 - D(k)),

where G = 1.516386059... is Watson's integral (Watson 1939), the simple
random walk's expected visits to the origin, equal in closed form to
sqrt(6)/(32 pi^3) Gamma(1/24) Gamma(5/24) Gamma(7/24) Gamma(11/24)
(Glasser and Zucker 1977).  Hence

    E = (5/6) ((4/5) G - 1) = (2/3) G - 5/6 = 0.17759...

Exchange of sum and integral: for |a| <= 6 the roots of r^2 - a r + 5 have
modulus <= 5, so |A_n(k)| <= C (n+1) 5^n and the series converges absolutely
and uniformly for z < 1/5; b_n >= 0 gives monotone convergence on the left as
z -> 1/5, and the integrand is bounded by 1/(6 z (1 - D)), integrable in d = 3,
which gives dominated convergence on the right.

What this script checks numerically, all exact integers except G:
  1. b_n by direct enumeration agrees with the recurrence (moments of a(k) are
     the simple-walk closed-walk counts) for every n <= N;
  2. G from the Gamma-function closed form agrees with the independent Bessel
     representation G = int_0^inf e^-t I_0(t/3)^3 dt;
  3. the certified bracket on P and the verdict.

The verdict needs much less than the value of G: P <= E < 2/3 holds as soon as
G < 9/4, and Watson's integral is 1.516.

Usage: python3 lepton_phase_certify.py [N]   (default 22; uses mpmath)
"""

from __future__ import annotations

import math
import sys
from collections import defaultdict
from fractions import Fraction

from mpmath import besseli, exp, gamma, inf, mp, mpf, pi, quad, sqrt

AX = [0, 0, 1, 1, 2, 2]
SG = [1, -1, 1, -1, 1, -1]
CONJ = [1, 0, 3, 2, 5, 4]


def nb_origin_counts(n_max):
    """b_n for n = 0..n_max: NB walks of length n from 0 back to 0 (exact)."""
    b = [0] * (n_max + 1)
    b[0] = 1
    st = defaultdict(int)
    for t in range(6):
        p = [0, 0, 0]
        p[AX[t]] += SG[t]
        st[(tuple(p), t)] += 1
    for n in range(1, n_max):
        new = defaultdict(int)
        for (p, last), c in st.items():
            for t in range(6):
                if t == CONJ[last]:
                    continue
                q = list(p)
                q[AX[t]] += SG[t]
                q = tuple(q)
                if abs(q[0]) + abs(q[1]) + abs(q[2]) > n_max - n - 1:
                    continue
                new[(q, t)] += c
        st = new
        b[n + 1] = sum(c for (p, _), c in st.items() if p == (0, 0, 0))
    return b


def srw_closed(j):
    """Closed simple-random-walk paths of length j on Z^3 = constant term of a(k)^j."""
    if j % 2:
        return 0
    n = j // 2
    f = math.factorial
    return sum(
        f(2 * n) // (f(i) ** 2 * f(k) ** 2 * f(n - i - k) ** 2)
        for i in range(n + 1)
        for k in range(n - i + 1)
    )


def recurrence_counts(n_max):
    """b_n from A_{n+1} = a A_n - 5 A_{n-1}, A_2 = a^2 - 6, as polynomials in a."""

    def sub(p, q):
        r = [0] * max(len(p), len(q))
        for i, x in enumerate(p):
            r[i] += x
        for i, x in enumerate(q):
            r[i] -= x
        return r

    polys = [[1], [0, 1], [-6, 0, 1]]
    for n in range(2, n_max):
        polys.append(sub([0] + polys[n], [5 * x for x in polys[n - 1]]))
    return [sum(c * srw_closed(j) for j, c in enumerate(p)) for p in polys[: n_max + 1]]


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    mp.dps = 30

    b = nb_origin_counts(n_max)
    rec = recurrence_counts(n_max)
    assert b == rec, "enumeration and recurrence disagree"
    print(f"1. NB origin counts b_n match the recurrence for n <= {n_max}")

    G_gamma = (
        sqrt(6) / (32 * pi**3)
        * gamma(mpf(1) / 24) * gamma(mpf(5) / 24)
        * gamma(mpf(7) / 24) * gamma(mpf(11) / 24)
    )
    G_bessel = quad(lambda t: exp(-t) * besseli(0, t / 3) ** 3, [0, 1, 10, 100, inf])
    assert abs(G_gamma - G_bessel) < mpf(10) ** -12, (G_gamma, G_bessel)
    print(f"2. Watson's integral G = {mp.nstr(G_gamma, 15)} (Gamma form) "
          f"= {mp.nstr(G_bessel, 15)} (Bessel form)")

    E = mpf(2) / 3 * G_gamma - mpf(5) / 6
    U = sum(Fraction(b[n], 6 * 5 ** (n - 1)) for n in range(1, n_max + 1))
    tail = E - mpf(U.numerator) / U.denominator
    print(f"   expected NB returns E = (2/3)G - 5/6 = {mp.nstr(E, 12)}")
    print(f"   U_{n_max} = {float(U):.10f}, so sum_(n>{n_max}) u_n = {mp.nstr(tail, 10)}")

    # S_N from lepton_phase_series (exact partial sum of the pre-registered statistic)
    from lepton_phase_series import series

    w = series(n_max)
    S = sum(Fraction(w[L], 6 * 5 ** (L - 1)) for L in range(1, n_max + 1))
    lo = mpf(S.numerator) / S.denominator
    hi = lo + tail
    print(f"3. certified bracket P in [S_{n_max}, S_{n_max} + (E - U_{n_max})] = "
          f"[{mp.nstr(lo, 8)}, {mp.nstr(hi, 8)}]")
    print(f"   and P <= E = {mp.nstr(E, 8)} independently of N")
    target = mpf(2) / 3
    verdict = "FAIL (certified)" if not (lo <= target <= hi) else "UNDECIDED"
    print(f"   2/3 = {mp.nstr(target, 8)}: {verdict}")


if __name__ == "__main__":
    main()
