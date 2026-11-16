#!/usr/bin/env python3
"""Reference implementation and test vectors for the MrE update (issue #221).

Spec: MrE_Update.md. Lean: lean/QLF_MrEUpdate.lean.

The update itself is exact rational arithmetic (Fraction), so every node computes the same
posterior bit for bit. Logarithms appear only in the information quantities, which are reported
as floats for checking, never fed back into the update.

    python3 mre_update.py            # check every invariant, print the vectors
    python3 mre_update.py --write    # also write data/mre_test_vectors.json
"""
import json
import sys
from fractions import Fraction as F
from math import log

LOG2 = log(2)


def evidence(p, a, b):
    return p * a + (1 - p) * b


def posterior(p, a, b):
    m = evidence(p, a, b)
    if m == 0:
        raise ValueError("observation has probability 0 under the prior")
    return p * a / m


def xlogy_ratio(x, y):
    """x * log(x / y) with 0 * log 0 = 0 (Lean's Real.log convention)."""
    return 0.0 if x == 0 else float(x) * log(float(x) / float(y))


def binary_kl(q, r):
    return xlogy_ratio(q, r) + xlogy_ratio(1 - q, 1 - r)


def h(q):
    return -(xlogy_ratio(q, 1)) - xlogy_ratio(1 - q, 1)


def eig(p, a, b):
    """Expected information gain = I(H; E), in nats."""
    return h(evidence(p, a, b)) - float(p) * h(a) - float(1 - p) * h(b)


def eig_kl_form(p, a, b):
    m = evidence(p, a, b)
    out = 0.0
    if m > 0:
        out += float(m) * binary_kl(posterior(p, a, b), p)
    if m < 1:
        out += float(1 - m) * binary_kl(posterior(p, 1 - a, 1 - b), p)
    return out


def mre_divergence(s, p, a, b):
    """Relative entropy to the prior joint of the candidate (s on H&E, 1-s on ~H&E).

    Support-aware: +inf if the candidate puts mass where the prior joint has none
    (Lean: Admissible / mre_update_unique_on_support). The naive real-valued formula returns a
    finite number there and is wrong (unrestricted_objective_fails).
    """
    out = 0.0
    for mass, ref in ((s, p * a), (1 - s, (1 - p) * b)):
        if mass == 0:
            continue
        if ref == 0:
            return float("inf")
        out += float(mass) * log(float(mass) / float(ref))
    return out


CASES = [
    # name, prior, P(E|H), P(E|~H)
    ("aria_counterexample", F(1, 100), F(1), F(1, 9801)),
    ("uniform_perfect", F(1, 2), F(1), F(0)),
    ("uniform_perfect_flipped", F(1, 2), F(0), F(1)),
    ("uniform_noisy", F(1, 2), F(9, 10), F(1, 10)),
    ("skewed_perfect", F(1, 10), F(1), F(0)),
    ("uninformative", F(3, 10), F(2, 5), F(2, 5)),
    ("boundary_b_zero", F(1, 4), F(3, 5), F(0)),
    ("boundary_a_zero", F(1, 4), F(0), F(3, 5)),
    ("identity_login_ok", F(19, 20), F(99, 100), F(1, 20)),
    ("presence_beacon", F(4, 5), F(9, 10), F(3, 10)),
    ("security_alert", F(1, 50), F(7, 10), F(1, 100)),
    ("privacy_leak_check", F(1, 5), F(1, 2), F(1, 10)),
]


def vector(name, p, a, b):
    m = evidence(p, a, b)
    q = posterior(p, a, b)
    pointwise = binary_kl(q, p)
    e = eig(p, a, b)
    return {
        "name": name,
        "prior": str(p), "p_E_given_H": str(a), "p_E_given_notH": str(b),
        "evidence": str(m),
        "posterior_given_E": str(q),
        "posterior_given_notE": str(posterior(p, 1 - a, 1 - b)) if m < 1 else None,
        "kl_posterior_given_E_from_prior_nats": round(pointwise, 12),
        "expected_information_gain_nats": round(e, 12),
        "pointwise_exceeds_log2": pointwise > LOG2,
        "expected_within_log2": e <= LOG2 + 1e-12,
    }


def check():
    vs = []
    for name, p, a, b in CASES:
        v = vector(name, p, a, b)
        e = eig(p, a, b)
        assert -1e-12 <= e <= LOG2 + 1e-12, name                     # eig_nonneg, eig_le_log_two
        assert abs(e - eig_kl_form(p, a, b)) < 1e-12, name           # eig_eq_expected_kl
        sat = p == F(1, 2) and {a, b} == {F(0), F(1)}
        assert (abs(e - LOG2) < 1e-12) == sat, name                  # eig_eq_log_two_iff
        vs.append(v)
    aria = vs[0]
    assert aria["posterior_given_E"] == "99/100"                     # pointwise_bound_false
    assert aria["pointwise_exceeds_log2"]
    assert abs(aria["kl_posterior_given_E_from_prior_nats"] - 0.98 * log(99)) < 1e-9
    assert posterior(F(3, 10), F(2, 5), F(2, 5)) == F(3, 10)         # uninformative_posterior
    # mre_update_unique_on_support: on a grid, the support-aware objective is minimised only at
    # the Bayes posterior, boundary likelihoods included.
    grid = [F(i, 200) for i in range(201)]
    for name, p, a, b in CASES:
        q = posterior(p, a, b)
        best = mre_divergence(q, p, a, b)
        assert best < float("inf"), name
        for s in grid:
            d = mre_divergence(s, p, a, b)
            assert d >= best - 1e-12, name
            assert s == q or d > best + 1e-15, name
    assert posterior(F(1, 4), F(3, 5), F(0)) == 1                    # posterior_zero_right
    assert posterior(F(1, 4), F(0), F(3, 5)) == 0                    # posterior_zero_left
    # unrestricted_objective_fails: the zero-support candidate must score +inf, not 0
    assert mre_divergence(F(0), F(1, 2), F(1), F(0)) == float("inf")
    assert abs(mre_divergence(F(1), F(1, 2), F(1), F(0)) - LOG2) < 1e-12
    # impossible observation (a = b = 0): the update is rejected, not computed
    try:
        posterior(F(1, 2), F(0), F(0))
        raise AssertionError("impossible observation accepted")
    except ValueError:
        pass
    # sequential_update: two conditionally independent observations
    p, a1, b1, a2, b2 = F(1, 3), F(4, 5), F(1, 5), F(2, 3), F(1, 4)
    assert posterior(posterior(p, a1, b1), a2, b2) == posterior(p, a1 * a2, b1 * b2)
    return vs


if __name__ == "__main__":
    vs = check()
    for v in vs:
        print(f'{v["name"]:26s} post={v["posterior_given_E"]:>10s} '
              f'KL(E)={v["kl_posterior_given_E_from_prior_nats"]:.6f} '
              f'EIG={v["expected_information_gain_nats"]:.6f}')
    print(f"log 2 = {LOG2:.6f}; all invariants hold")
    if "--write" in sys.argv:
        with open("data/mre_test_vectors.json", "w") as f:
            json.dump({"spec": "MrE_Update.md", "lean": "lean/QLF_MrEUpdate.lean",
                       "units": "nats", "arithmetic": "update exact rational; logs float64",
                       "boundary_policy": {
                           "impossible_observation": "P(E) = 0: reject, no update",
                           "zero_likelihood": "candidate with mass off the prior support has "
                                              "divergence +inf; posterior is 0 or 1",
                           "naive_objective_counterexample": {
                               "prior": "1/2", "p_E_given_H": "1", "p_E_given_notH": "0",
                               "candidate": "0", "naive_value": 0.0,
                               "correct_value": "+inf"}},
                       "vectors": vs}, f, indent=2)
            f.write("\n")
        print("wrote data/mre_test_vectors.json")
