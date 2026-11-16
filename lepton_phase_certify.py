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

WHAT IS PROVED AND WHAT IS COMPUTED.  The reduction P <= E = (2/3) G - 5/6 is an
analytic argument (above), not machine-checked.  The numerical inequality is
certified in exact rational arithmetic, with no floating point:

    G = sum_{n>=0} u_2n,   u_2n = W_2n / 6^2n   (simple-walk return probabilities),

    u_2n = [C(2n,n)/4^n] * sum_{i+j+k=n} t(i,j,k)^2  <=  [C(2n,n)/4^n] * max t,

where t(i,j,k) = n!/(i!j!k!) 3^-n sums to 1.  The maximum is at a balanced
triple (moving one unit from i to j when i >= j+2 multiplies t by i/(j+1) > 1),
so i,j,k >= (n-2)/3.  Robbins' (1955) bounds
sqrt(2 pi m) (m/e)^m < m! < sqrt(2 pi m) (m/e)^m e^(1/(12m)), with the
relative-entropy factor <= 1, give max t <= e^(1/(12n)) sqrt(n) 3 sqrt(3) /
(2 pi (n-2)^(3/2)); with C(2n,n)/4^n <= 1/sqrt(pi n) this is, for n >= 5,

    u_2n  <=  e^(1/(12n)) * 3 sqrt(3) / (2 pi^(3/2)) * (n-2)^(-3/2)
          <   1.001 * 0.467 * (n-2)^(-3/2)        for n > 400,

using 3.14 < pi, sqrt(3) < 1.7321 and e^(1/(12n)) < 1.001 there.  (For
5 <= n <= 400 the same numerical bound is asserted directly against the exact
u_2n.)  Summing the tail n > M = 400 by the integral test,

    G  <=  S_M + 1.001 * 0.467 * 2 / sqrt(M - 2),   S_M = sum_{n<=M} u_2n exact.

The script evaluates this with Fractions (the square root is replaced by a
rational lower bound from an integer square root), asserts the term bound
against the exact u_2n for every 5 <= n <= M, and reports the rational G_hi.
Everything downstream (E_hi, the bracket, the verdict) uses G_hi.

What the script checks:
  1. b_n by direct enumeration agrees with the recurrence (moments of a(k) are
     the simple-walk closed-walk counts) for every n <= N;
  2. the rational certificate G <= G_hi < 9/4 (which alone gives P <= E < 2/3);
  3. the bracket on P from G_hi, and the verdict;
  4. if mpmath is installed, a floating-point cross-check only: Watson's value
     of G in its Gamma and Bessel forms (not part of the certificate).

Usage: python3 lepton_phase_certify.py [N]   (default 22; mpmath optional)
"""

from __future__ import annotations

import math
import sys
from collections import defaultdict
from fractions import Fraction


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


def watson_upper(m_max=400):
    """Rational upper bound G_hi >= G, exact arithmetic only (see docstring)."""
    # W_2n = (2n)! [x^2n] (sum_k x^2k / k!^2)^3, by exact convolution
    one = [Fraction(1, math.factorial(k) ** 2) for k in range(m_max + 1)]
    p = one
    for _ in range(2):
        q = [Fraction(0)] * (m_max + 1)
        for i, a in enumerate(p):
            for j in range(m_max + 1 - i):
                q[i + j] += a * one[j]
        p = q
    u = [p[n] * math.factorial(2 * n) / 6 ** (2 * n) for n in range(m_max + 1)]
    assert all(u[n] == Fraction(srw_closed(2 * n), 6 ** (2 * n)) for n in range(12))
    const = Fraction(1001, 1000) * Fraction(467, 1000)
    # term bound u_2n <= const * (n-2)^(-3/2), checked as u^2 (n-2)^3 <= const^2
    for n in range(5, m_max + 1):
        assert u[n] ** 2 * (n - 2) ** 3 <= const ** 2, n
    # rational lower bound on sqrt(m_max - 2): floor(sqrt((m_max-2) * 10^12)) / 10^6
    root_lo = Fraction(math.isqrt((m_max - 2) * 10 ** 12), 10 ** 6)
    tail = const * 2 / root_lo
    return sum(u) + tail, sum(u), tail


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 22

    b = nb_origin_counts(n_max)
    rec = recurrence_counts(n_max)
    assert b == rec, "enumeration and recurrence disagree"
    print(f"1. NB origin counts b_n match the recurrence for n <= {n_max}")

    G_hi, S_M, tail_G = watson_upper()
    assert G_hi < Fraction(9, 4)
    print(f"2. exact certificate: G <= S_400 + tail = {float(S_M):.6f} + {float(tail_G):.6f}"
          f" = {float(G_hi):.6f} < 9/4   (rational arithmetic)")

    E_hi = Fraction(2, 3) * G_hi - Fraction(5, 6)
    U = sum(Fraction(b[n], 6 * 5 ** (n - 1)) for n in range(1, n_max + 1))
    tail = E_hi - U
    print(f"   expected NB returns E <= (2/3)G_hi - 5/6 = {float(E_hi):.6f}")
    print(f"   U_{n_max} = {float(U):.10f}, so sum_(n>{n_max}) u_n <= {float(tail):.6f}")

    # S_N from lepton_phase_series (exact partial sum of the pre-registered statistic)
    from lepton_phase_series import series

    w = series(n_max)
    S = sum(Fraction(w[L], 6 * 5 ** (L - 1)) for L in range(1, n_max + 1))
    hi = S + tail
    print(f"3. bracket P in [S_{n_max}, S_{n_max} + (E_hi - U_{n_max})] = "
          f"[{float(S):.8f}, {float(hi):.8f}]")
    print(f"   and P <= E_hi = {float(E_hi):.6f} independently of N")
    target = Fraction(2, 3)
    assert E_hi < target and hi < target
    print("   2/3 lies above the bracket (exact comparison): this route does not close,"
          "\n   given the analytic reduction P <= E in the docstring")

    try:
        from mpmath import besseli, exp, gamma, inf, mp, mpf, pi, quad, sqrt
    except ImportError:
        print("4. mpmath not installed: floating-point cross-check skipped")
        return
    mp.dps = 30
    G_gamma = (
        sqrt(6) / (32 * pi**3)
        * gamma(mpf(1) / 24) * gamma(mpf(5) / 24)
        * gamma(mpf(7) / 24) * gamma(mpf(11) / 24)
    )
    G_bessel = quad(lambda t: exp(-t) * besseli(0, t / 3) ** 3, [0, 1, 10, 100, inf])
    print(f"4. cross-check (floating point, not part of the certificate): Watson's G = "
          f"{mp.nstr(G_gamma, 12)} (Gamma form), {mp.nstr(G_bessel, 12)} (Bessel form); "
          f"E = {mp.nstr(mpf(2) / 3 * G_gamma - mpf(5) / 6, 9)}")


if __name__ == "__main__":
    main()
