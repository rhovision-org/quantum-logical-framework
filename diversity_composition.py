#!/usr/bin/env python3
"""D8a: a primitive cross-type composition witness for QLF diversity (#290).

The provisional structural type is the oriented net-action vector `net(word)`.
Composition is concatenation. A pair is admissible when both constituents are
open (not ZFA-closed) and their concatenation is ZFA-closed.

This proves D8a only: at least one cross-type composition exists. It does not
claim D8b (a genuinely novel outcome unreachable by homogeneous composition) or
D8c (a measured diversity advantage).
"""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
from typing import Sequence

from assembly_index import TWISTS, fold, is_closed, net

OUTPUT = Path("data/diversity_d8a_census.json")


def is_zfa(word: str) -> bool:
    """Count-balanced and Pauli-scalar-closed."""
    return is_closed(word) and fold(word) is not None


def kind(word: str) -> tuple[int, int, int, int]:
    """Provisional structural type: oriented net action on the four axes."""
    return net(word)


def compose(a: str, b: str) -> str:
    return a + b


def admissible_composition(a: str, b: str) -> bool:
    """Two open histories whose concatenation is ZFA-closed.

    The relation uses only the primitive net/closure algebra, not a distance,
    a Penrose matching rule, or a desired emergent pattern.
    """
    return bool(a) and bool(b) and not is_zfa(a) and not is_zfa(b) and is_zfa(compose(a, b))


def has_cross_composition() -> bool:
    return any(
        admissible_composition(a, b) and kind(a) != kind(b)
        for a in TWISTS
        for b in TWISTS
    )


def words_upto(max_length: int) -> list[str]:
    return [
        "".join(chars)
        for length in range(1, max_length + 1)
        for chars in product(TWISTS, repeat=length)
    ]


def census(max_length: int = 2) -> dict[str, object]:
    words = words_upto(max_length)
    open_words = [word for word in words if not is_zfa(word)]
    admissible: list[tuple[str, str, str]] = []
    for a in open_words:
        for b in open_words:
            if admissible_composition(a, b):
                admissible.append((a, b, compose(a, b)))
    cross = [
        (a, b, c)
        for a, b, c in admissible
        if kind(a) != kind(b)
    ]
    same = [
        (a, b, c)
        for a, b, c in admissible
        if kind(a) == kind(b)
    ]
    zero_outcomes = {
        kind(c)
        for _a, _b, c in admissible
    }
    return {
        "max_length": max_length,
        "words": len(words),
        "open_words": len(open_words),
        "admissible_compositions": len(admissible),
        "cross_type_compositions": len(cross),
        "same_type_compositions": len(same),
        "cross_type_witness": {
            "a": "^",
            "b": "v",
            "composite": "^v",
            "kind_a": kind("^"),
            "kind_b": kind("v"),
            "kind_composite": kind("^v"),
            "a_open": not is_zfa("^"),
            "b_open": not is_zfa("v"),
            "composite_closed": is_zfa("^v"),
            "composite_fold": fold("^v"),
        },
        "examples": [
            {
                "a": a,
                "b": b,
                "composite": c,
                "kind_a": kind(a),
                "kind_b": kind(b),
                "kind_composite": kind(c),
            }
            for a, b, c in cross[:5]
        ],
        "distinct_composite_kinds": len(zero_outcomes),
        "note": (
            "D8a only: a finite cross-type witness. D8b (novel outcome) and "
            "D8c (measured advantage) are not claimed."
        ),
    }


def build_summary() -> dict[str, object]:
    return {
        "meta": {
            "generator": "diversity_composition.py",
            "version": 1,
            "issue": 290,
            "gate": "D8a",
            "pre_registration": "Diversity_Composition_QLF.md",
        },
        "census": census(),
        "gates": {
            "D8a_cross_composition": "pass: explicit primitive witness ^ + v -> ^v",
            "D8b_novel_outcome": "open; not attempted",
            "D8c_measured_advantage": "open; no measure/comparison",
        },
    }


def self_test() -> None:
    assert is_zfa("^v")
    assert fold("^v") is not None
    assert not is_zfa("^")
    assert not is_zfa("v")
    assert kind("^") != kind("v")
    assert kind("^v") == (0, 0, 0, 0)
    assert admissible_composition("^", "v")
    assert has_cross_composition()
    result = census()
    assert result["cross_type_compositions"] > 0
    assert result["cross_type_witness"]["composite_closed"]
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    result = summary["census"]  # type: ignore[index]
    print("\nfinite census:")
    print(
        f"  words={result['words']} open={result['open_words']} "
        f"admissible={result['admissible_compositions']} "
        f"cross={result['cross_type_compositions']} "
        f"same={result['same_type_compositions']}"
    )
    print(f"  witness={result['cross_type_witness']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--json", type=Path, default=OUTPUT)
    args = parser.parse_args(argv)
    if args.self_test:
        self_test()
        if not args.run:
            return 0
    summary = build_summary()
    print_summary(summary)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
