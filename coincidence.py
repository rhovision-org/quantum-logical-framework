#!/usr/bin/env python3
"""Co-incidence first slice: CO0 triviality + CO1/CO2 provenance schedule.

Frozen semantics are in ``Coincidence_QLF.md`` and issue #283.

CO0: without typed provenance and a pre-existing schedule, every closed word of
length >= 2 is a co-incidence by the trivial first-twist split.

CO1/CO2: origins are fixed in the event record; projections are taken at each
prefix; the first prefix whose projections jointly close is the co-incidence.

CO3 (universality/census) is deliberately not implemented here.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Sequence

from assembly_index import TWISTS, fold, is_closed

OUTPUT = Path("data/coincidence_census.json")
MAX_TRIVIALITY_LENGTH = 6


@dataclass(frozen=True)
class ProvEvent:
    """A twist tagged with its origin *before* any closure is observed."""

    origin: str
    twist: str

    def __post_init__(self) -> None:
        if not self.origin:
            raise ValueError("origin must be non-empty")
        if self.twist not in TWISTS:
            raise ValueError(f"unknown twist {self.twist!r}")


def is_zfa(word: str) -> bool:
    """QLF closure: count balance plus a Pauli scalar fold."""
    return is_closed(word) and fold(word) is not None


def origins(run: Sequence[ProvEvent]) -> tuple[str, ...]:
    """Origins in first-appearance order."""
    seen: list[str] = []
    for event in run:
        if event.origin not in seen:
            seen.append(event.origin)
    return tuple(seen)


def project(run: Sequence[ProvEvent], origin: str, n: int) -> str:
    """History belonging to *origin* in the first *n* events."""
    return "".join(event.twist for event in run[:n] if event.origin == origin)


def first_joint_closure(
    run: Sequence[ProvEvent], origin_a: str, origin_b: str
) -> int | None:
    """First prefix length n where both projections are non-empty and jointly close."""
    if origin_a == origin_b:
        return None
    for n in range(1, len(run) + 1):
        a = project(run, origin_a, n)
        b = project(run, origin_b, n)
        if a and b and is_zfa(a + b):
            return n
    return None


def product_sector(a: str, b: str) -> bool:
    """True when each side folds to a Pauli scalar on its own.

    This is the product-sector reading used by ``gauge_pair_is_product_sector``.
    It is distinct from ZFA closure: a word can fold to a scalar and still be
    count-imbalanced.
    """
    return fold(a) is not None and fold(b) is not None


def coincides(
    run: Sequence[ProvEvent], origin_a: str, origin_b: str
) -> dict[str, object] | None:
    """CO1/CO2: first shared closure of two separately sourced open projections."""
    n = first_joint_closure(run, origin_a, origin_b)
    if n is None:
        return None
    a = project(run, origin_a, n)
    b = project(run, origin_b, n)
    if not a or not b:
        return None
    if is_zfa(a) or is_zfa(b):
        return None
    product = product_sector(a, b)
    return {
        "origin_a": origin_a,
        "origin_b": origin_b,
        "first_joint_closure": n,
        "a": a,
        "b": b,
        "joint": a + b,
        "product_sector": product,
        "strong": not product,
    }


def triviality_census(max_length: int = MAX_TRIVIALITY_LENGTH) -> dict[str, object]:
    """CO0 finite check: the bare first-twist split is always available."""
    checked = 0
    failures: list[dict[str, object]] = []
    for length in range(2, max_length + 1):
        for chars in product(TWISTS, repeat=length):
            word = "".join(chars)
            if not is_zfa(word):
                continue
            checked += 1
            a = word[0]
            b = word[1:]
            if is_zfa(a) or is_zfa(b) or not is_zfa(a + b):
                failures.append({"word": word, "a": a, "b": b})
    return {
        "max_length": max_length,
        "closed_words_checked": checked,
        "failures": failures,
        "all_pass": not failures,
        "note": (
            "This is a finite check of the CO0 proof sketch, not a Lean theorem. "
            "The analytic argument covers arbitrary length."
        ),
    }


def build_summary() -> dict[str, object]:
    primordial = [ProvEvent("A", "^"), ProvEvent("B", "v")]
    gauge = [ProvEvent("A", "+"), ProvEvent("B", "-")]
    same_origin = [ProvEvent("A", "^"), ProvEvent("A", "v")]
    early = [ProvEvent("A", "^"), ProvEvent("B", "v"), ProvEvent("A", "v"), ProvEvent("B", "^")]
    return {
        "meta": {
            "generator": "coincidence.py",
            "version": 1,
            "issue": 283,
            "pre_registration": "Coincidence_QLF.md",
        },
        "co0": triviality_census(),
        "co1_co2": {
            "primordial": coincides(primordial, "A", "B"),
            "gauge_pair": coincides(gauge, "A", "B"),
            "same_origin": coincides(same_origin, "A", "B"),
            "early_joint_closure": coincides(early, "A", "B"),
        },
        "gates": {
            "CO0_triviality": "finite check; bare split is vacuous",
            "CO1_typed_origins": "origins fixed in the event record",
            "CO2_first_joint_closure": "first prefix with joint closure",
            "CO3_universality": "interaction-event census open; not implemented here",
            "CO4_law_of_exceptions": "open bridge; finite resolver not claimed universal",
            "strong_coincidence": "non-product-sector witness",
        },
    }


def self_test() -> None:
    first = coincides([ProvEvent("A", "^"), ProvEvent("B", "v")], "A", "B")
    assert first is not None
    assert first["a"] == "^" and first["b"] == "v"
    assert first["first_joint_closure"] == 2
    assert first["strong"] is True, "^v should be a strong co-incidence"

    gauge = coincides([ProvEvent("A", "+"), ProvEvent("B", "-")], "A", "B")
    assert gauge is not None
    assert gauge["product_sector"] is True, "+- should be product-sector"
    assert gauge["strong"] is False, "+- should not be a strong co-incidence"

    assert coincides([ProvEvent("A", "^"), ProvEvent("A", "v")], "A", "B") is None
    early = coincides(
        [ProvEvent("A", "^"), ProvEvent("B", "v"), ProvEvent("A", "v"), ProvEvent("B", "^")],
        "A",
        "B",
    )
    assert early is not None and early["first_joint_closure"] == 2

    census = triviality_census()
    assert census["all_pass"] is True, census["failures"]
    assert int(census["closed_words_checked"]) > 0
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    co0 = summary["co0"]  # type: ignore[index]
    print("\nCO0 triviality census:")
    print(f"  max_length={co0['max_length']} checked={co0['closed_words_checked']}")
    print(f"  all_pass={co0['all_pass']} failures={len(co0['failures'])}")
    print("\nCO1/CO2 examples:")
    for name, result in summary["co1_co2"].items():  # type: ignore[union-attr]
        if result is None:
            print(f"  {name}: no co-incidence")
            continue
        print(
            f"  {name}: n={result['first_joint_closure']} "
            f"{result['a']} | {result['b']} strong={result['strong']}"
        )


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
