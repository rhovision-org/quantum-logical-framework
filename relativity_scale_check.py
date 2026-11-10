#!/usr/bin/env python3
"""Brute-force check of lean/QLF_RelativityScale.lean.

Enumerates every twist history of length L (8^L of them), reads each twist as its Minkowski
unit vector (gauge = time, spatial twists = x, y, z, as Twist.toMatrix does), and checks the
closed forms the Lean module proves:

  4 * sum x_i x_j       = delta_ij * L * 8^L        (covariance_isotropic)
  sum x_i = sum x_i^3   = 0                           (first/third_moment_zero)
  16 * sum x_i^4        = (3L^2 + L) * 8^L            (fourth_moment)
  16 * sum x_i^2 x_j^2  = (L^2 - L) * 8^L             (mixed_fourth_moment)
  anisotropy ratio      = 4 / (3L + 1)                (anisotropy_ratio)

and the step-level no-go: the gamma = 3 integer boost preserves the interval and sends e_t
(1 step) to (3,2,2,0) (7 steps); and lean/QLF_LorentzSymbol.lean: the matrix census
is H(k)^L with H = 2i*Form(sin k), det H = -4*interval(sin k). See Relativity_Principle.md.

Usage: python3 relativity_scale_check.py [--max-len 6]
"""
import argparse
import itertools
from fractions import Fraction

STEP = {  # index 0 = time, 1..3 = x, y, z
    "+": (1, 0, 0, 0), "-": (-1, 0, 0, 0),
    ">": (0, 1, 0, 0), "<": (0, -1, 0, 0),
    "^": (0, 0, 1, 0), "v": (0, 0, -1, 0),
    "/": (0, 0, 0, 1), "\\": (0, 0, 0, -1),
}


def boost(v):
    t, x, y, z = v
    return (3 * t + 2 * x + 2 * y, 2 * t + 2 * x + y, 2 * t + x + 2 * y, z)


def interval(v):
    return v[0] ** 2 - v[1] ** 2 - v[2] ** 2 - v[3] ** 2


def check_no_go():
    for v in itertools.product(range(-3, 4), repeat=4):
        assert interval(boost(v)) == interval(v)
    b = boost((1, 0, 0, 0))
    assert b == (3, 2, 2, 0) and sum(abs(c) for c in b) == 7
    print("no-go: boost preserves the interval on [-3,3]^4; e_t (1 step) -> (3,2,2,0) (7 steps)")


def check_moments(max_len):
    for L in range(0, max_len + 1):
        N = 8 ** L
        m1 = [0] * 4
        m2 = [[0] * 4 for _ in range(4)]
        m3 = [0] * 4
        m4 = [0] * 4
        q = [[0] * 4 for _ in range(4)]
        for word in itertools.product(STEP.values(), repeat=L):
            d = [sum(s[i] for s in word) for i in range(4)]
            for i in range(4):
                m1[i] += d[i]
                m3[i] += d[i] ** 3
                m4[i] += d[i] ** 4
                for j in range(4):
                    m2[i][j] += d[i] * d[j]
                    q[i][j] += d[i] ** 2 * d[j] ** 2
        for i in range(4):
            assert m1[i] == 0 and m3[i] == 0
            assert 16 * m4[i] == (3 * L * L + L) * N
            for j in range(4):
                assert 4 * m2[i][j] == (L * N if i == j else 0)
                if i != j:
                    assert 16 * q[i][j] == (L * L - L) * N
        ratio = Fraction(m4[0] - 3 * q[0][1], m4[0]) if L else None
        if L:
            assert ratio == Fraction(4, 3 * L + 1)
        print(f"L={L}: {N} histories, all moment identities hold"
              + (f", anisotropy ratio = {ratio}" if L else ""))


def check_matrix_symbol(max_len=4, trials=3):
    """census_symbol / symbol_eq_form / symbol_det of lean/QLF_LorentzSymbol.lean."""
    import cmath
    import math
    import random
    I2 = [[1, 0], [0, 1]]
    sx = [[0, 1], [1, 0]]
    sy = [[0, -1j], [1j, 0]]
    sz = [[1, 0], [0, -1]]
    neg = lambda A: [[-a for a in r] for r in A]
    MAT = {"+": I2, "-": neg(I2), ">": sx, "<": neg(sx), "^": sy, "v": neg(sy),
           "/": sz, "\\": neg(sz)}
    mul = lambda A, B: [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    rng = random.Random(1)
    for _ in range(trials):
        k = [rng.uniform(-3, 3) for _ in range(4)]
        st = [math.sin(c) for c in k]
        H = [[2j * (st[0] + st[3]), 2j * (st[1] - 1j * st[2])],
             [2j * (st[1] + 1j * st[2]), 2j * (st[0] - st[3])]]
        det = H[0][0] * H[1][1] - H[0][1] * H[1][0]
        assert abs(det + 4 * (st[0] ** 2 - st[1] ** 2 - st[2] ** 2 - st[3] ** 2)) < 1e-9
        P = [[1, 0], [0, 1]]
        for L in range(max_len + 1):
            S = [[0j, 0j], [0j, 0j]]
            for word in itertools.product(STEP.keys(), repeat=L):
                d = [sum(STEP[t][i] for t in word) for i in range(4)]
                ph = cmath.exp(1j * sum(k[i] * d[i] for i in range(4)))
                F = [[1, 0], [0, 1]]
                for t in reversed(word):
                    F = mul(MAT[t], F)
                for i in range(2):
                    for j in range(2):
                        S[i][j] += ph * F[i][j]
            assert all(abs(S[i][j] - P[i][j]) < 1e-6 for i in range(2) for j in range(2)), (L, k)
            P = mul(H, P)
    print(f"matrix census = H(k)^L with H = 2i*Form(sin k), det H = -4*interval(sin k): "
          f"checked to L={max_len} at {trials} random momenta")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-len", type=int, default=6)
    args = ap.parse_args()
    check_no_go()
    check_moments(args.max_len)
    check_matrix_symbol()
