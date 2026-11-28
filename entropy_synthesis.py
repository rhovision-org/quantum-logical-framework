#!/usr/bin/env python3
"""Finite entropy synthesis for the one-law QLF framing.

This is a **census**, not a new physical law.  It makes three finite points
explicit:

1. The number of ZFA closures grows, while the forward record carried by a
   closure's sign is at most one bit.
2. A record partition obeys the exact identity
       H(history) = H(record) + H(history | record)
   for the uniform measure on the enumerated histories.
3. Two distinct balanced histories can have the same fold and the same future
   closure behaviour, so the route is not recoverable from the closure record.

The script deliberately does not claim that half of all information is
permanently lost to space, that the sign is a physical entropy, or that the
QLF free-energy quantum is thermodynamic work in joules.  Those are bridges.

Run:
    python3 entropy_synthesis.py --self-test
    python3 entropy_synthesis.py --run
"""

from __future__ import annotations

import argparse
import collections
import itertools
import json
import math
from pathlib import Path
from typing import Iterable

from twist_core import TWISTS, calculate_action, is_pauli_closed, pauli_fold

OUTPUT = Path("data/entropy_synthesis.json")


def zfa_closures(length: int) -> tuple[str, ...]:
    """All count-balanced Pauli-closed words of exactly ``length`` twists."""
    out = []
    for word in itertools.product(TWISTS, repeat=length):
        history = "".join(word)
        if all(component == 0 for component in calculate_action(history)) and \
                is_pauli_closed(history):
            out.append(history)
    return tuple(out)


def sign(history: str) -> int:
    """The scalar sign of a closed history's Pauli fold."""
    value = pauli_fold(history)[0]
    if abs(value.imag) > 1e-9 or abs(value.real) < 1e-9:
        raise ValueError(f"not a real scalar closure: {history!r}")
    return 1 if value.real > 0 else -1


def shannon_bits(weights: Iterable[float]) -> float:
    """Shannon entropy in bits for non-negative weights."""
    values = [float(weight) for weight in weights]
    total = sum(values)
    if total <= 0:
        return 0.0
    entropy = -sum((w / total) * math.log2(w / total) for w in values if w > 0)
    return 0.0 if abs(entropy) < 1e-15 else entropy


def census(length: int) -> dict[str, object]:
    words = zfa_closures(length)
    counts = collections.Counter(sign(word) for word in words)
    total = len(words)
    h_total = math.log2(total) if total else 0.0
    h_sign = shannon_bits(counts.values())
    return {
        "length": length,
        "closures": total,
        "plus": counts[1],
        "minus": counts[-1],
        "H_total_bits": h_total,
        "H_sign_bits": h_sign,
        "forgotten_bits": h_total - h_sign,
        "sign_is_at_most_one_bit": h_sign <= 1.0 + 1e-12,
    }


def route_erasure_witness() -> dict[str, object]:
    """Two distinct closures with the same fold and the same future law."""
    a, b = "^v", "v^"
    fa, fb = pauli_fold(a), pauli_fold(b)
    return {
        "a": a,
        "b": b,
        "distinct": a != b,
        "both_closed": is_pauli_closed(a) and is_pauli_closed(b),
        "same_fold": all(abs(x - y) < 1e-12 for x, y in zip(fa, fb)),
        "future_rule": (
            "after a balanced prefix, count-balanced continuations are the same "
            "and the fold is multiplied by the one sign of the prefix"
        ),
        "lean_anchor": "QLF_ClosureRenewal.closure_renewal",
    }


def build_summary() -> dict[str, object]:
    rows = [census(length) for length in (2, 4, 6)]
    return {
        "meta": {
            "generator": "entropy_synthesis.py",
            "version": 1,
            "framing": (
                "one law: equal and opposite logical action; entropy is derived "
                "record bookkeeping, not a second premise"
            ),
            "measure": "uniform over enumerated ZFA closures",
            "units": "bits in the finite census; physical nats require the QLF map",
        },
        "sign_census": rows,
        "route_erasure": route_erasure_witness(),
        "pair_account": {
            "global": "singlet: pure, S(AB) = 0",
            "local_each": "S(A) = S(B) = log 2 nats",
            "lean_anchors": [
                "QLF_HolographicCompletion.singlet_reduced",
                "QLF_HolographicCompletion.entropy_half_half",
                "QLF_HolographicCompletion.cutEntropy_eq_vonNeumann",
            ],
            "scope": (
                "local accessibility, not a proof of permanent loss; the pair may "
                "re-interact and the 50% rule is not a theorem"
            ),
        },
        "proof_obligations": [
            "derive permanent local loss relative to an admissible continuation domain",
            "derive thermodynamic work in joules from the dimensionless log 2 quantum",
            "derive horizon entropy normalization from closure counting",
            "derive the GR thermodynamic bridge from closure locality and flux",
        ],
        "not_claimed": [
            "that half of all information is permanently lost to space",
            "that a qubit pair physically destroys a qubit",
            "that the sign entropy is thermodynamic entropy",
            "that the finite census proves the area law or GR",
        ],
    }


def self_test() -> None:
    rows = build_summary()["sign_census"]
    assert rows[0]["closures"] == 8  # type: ignore[index]
    assert rows[1]["closures"] == 168  # type: ignore[index]
    assert rows[2]["closures"] == 5120  # type: ignore[index]
    for row in rows:  # type: ignore[union-attr]
        total = row["H_sign_bits"] + row["forgotten_bits"]
        assert abs(total - row["H_total_bits"]) < 1e-12
        assert row["sign_is_at_most_one_bit"]
    witness = route_erasure_witness()
    assert witness["distinct"] and witness["both_closed"] and witness["same_fold"]
    print("self-test: OK")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--run", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if args.run:
        summary = build_summary()
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {OUTPUT}")
        for row in summary["sign_census"]:  # type: ignore[union-attr]
            print(
                f"L={row['length']:>2}  closures={row['closures']:>5}  "
                f"H_total={row['H_total_bits']:.6f}  H_sign={row['H_sign_bits']:.6f}  "
                f"forgotten={row['forgotten_bits']:.6f}"
            )
        return 0
    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
