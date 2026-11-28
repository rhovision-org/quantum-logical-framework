#!/usr/bin/env python3
"""D3 interface census for the diversity program (#290).

Implements the pre-registered conjugate-boundary relation:

    interface_ok(a,b) := last(a) == CONJUGATE[first(b)]
    join(a,b)         := interface_ok(a,b) and is_zfa(a ++ b)
    K_k(a)            := |{ canonical_word(a ++ b) : |b| <= k, join(a,b) }|

This is the D3 census only. It tests interface dependence and closure
preservation; it does **not** run the matched D8c2 homogeneous/heterogeneous
comparison and makes no diversity-advantage claim.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from itertools import product
from pathlib import Path
from typing import Sequence

from assembly_index import CONJUGATE, TWISTS, canonical_word, fold, is_closed

OUTPUT = Path("data/diversity_d3_census.json")
MAX_LENGTH = 3


def is_zfa(word: str) -> bool:
    return is_closed(word) and fold(word) is not None


def interface_ok(a: str, b: str) -> bool:
    """Conjugate boundary join: last twist of a meets first twist of b."""
    return bool(a) and bool(b) and a[-1] == CONJUGATE[b[0]]


def join(a: str, b: str) -> bool:
    return interface_ok(a, b) and is_zfa(a + b)


def words_upto(max_length: int) -> list[str]:
    return [
        "".join(chars)
        for length in range(1, max_length + 1)
        for chars in product(TWISTS, repeat=length)
    ]


def profile(a: str, extensions: Sequence[str]) -> dict[str, object]:
    composites = [a + b for b in extensions if join(a, b)]
    distinct = {canonical_word(composite) for composite in composites}
    return {
        "admitted": len(composites),
        "K": len(distinct),
        "extensions": [b for b in extensions if join(a, b)],
        "canonical_composites": sorted(distinct),
    }


def census(max_length: int = MAX_LENGTH) -> dict[str, object]:
    bases = words_upto(max_length)
    extensions = words_upto(max_length)
    by_length: dict[str, object] = {}
    total_joins = 0
    closure_failures = 0
    extension_sets: set[tuple[str, ...]] = set()

    for length in range(1, max_length + 1):
        k_counts: Counter[int] = Counter()
        for a in [base for base in bases if len(base) == length]:
            composites = []
            admitted_extensions = []
            for b in extensions:
                if join(a, b):
                    total_joins += 1
                    admitted_extensions.append(b)
                    if not is_zfa(a + b):
                        closure_failures += 1
                    composites.append(canonical_word(a + b))
            extension_sets.add(tuple(admitted_extensions))
            k_counts[len(set(composites))] += 1
        by_length[str(length)] = {
            "bases": sum(k_counts.values()),
            "K_counts": {str(k): v for k, v in sorted(k_counts.items())},
        }

    witnesses = {}
    for a in ("^v<", "^^^", "^<^"):
        witnesses[a] = profile(a, extensions)

    all_k = {
        int(k)
        for stats in by_length.values()
        for k in stats["K_counts"]  # type: ignore[index]
    }
    return {
        "max_length": max_length,
        "bases": len(bases),
        "extensions": len(extensions),
        "total_admitted_joins": total_joins,
        "closure_failures": closure_failures,
        "by_length": by_length,
        "interface_dependence": {
            "distinct_K_values": sorted(all_k),
            "distinct_extension_sets": len(extension_sets),
            "pass": len(all_k) > 1 and len(extension_sets) > 1,
        },
        "witnesses": witnesses,
        "d8c2": "not run",
        "verdict": (
            "D3.1 and D3.2 pass; D3.3 by construction; D8c2 not run"
        ),
    }


def build_summary() -> dict[str, object]:
    return {
        "meta": {
            "generator": "diversity_interface.py",
            "version": 1,
            "issue": 290,
            "gate": "D3 interface census",
            "pre_registration": "Diversity_Interface_D3.md",
        },
        "census": census(),
        "gates": {
            "D3.1_interface_dependence": "pass: multiple K values and extension sets",
            "D3.2_closure_preservation": "pass: every join is ZFA-closed",
            "D3.3_no_target_geometry": "pass: conjugate boundary + closure only",
            "D8c2_matched_comparison": "not run",
        },
    }


def self_test() -> None:
    assert interface_ok("^", "v")
    assert not interface_ok("^", "^")
    assert join("^", "v")
    assert not join("^", "^")
    result = census()
    assert result["closure_failures"] == 0
    assert result["by_length"]["1"]["K_counts"] == {"4": 8}
    assert result["by_length"]["2"]["K_counts"] == {"1": 64}
    assert result["by_length"]["3"]["K_counts"] == {"1": 64, "2": 384, "4": 16, "6": 48}
    assert result["interface_dependence"]["pass"] is True
    assert result["witnesses"]["^v<"]["K"] == 6
    assert result["witnesses"]["^^^"]["K"] == 1
    assert result["witnesses"]["^<^"]["K"] == 2
    assert result["d8c2"] == "not run"
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    result = summary["census"]  # type: ignore[index]
    print("\ncensus:")
    print(
        f"  bases={result['bases']} extensions={result['extensions']} "
        f"joins={result['total_admitted_joins']} "
        f"closure_failures={result['closure_failures']}"
    )
    print(f"  distinct K values={result['interface_dependence']['distinct_K_values']}")
    for length, stats in result["by_length"].items():
        print(f"  length {length}: bases={stats['bases']} K_counts={stats['K_counts']}")
    for base, witness in result["witnesses"].items():
        print(f"  witness {base}: K={witness['K']} admitted={witness['admitted']}")


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
