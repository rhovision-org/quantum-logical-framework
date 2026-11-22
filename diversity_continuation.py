#!/usr/bin/env python3
"""D8c pilot: can naive continuation counting distinguish axis diversity? (#290)

For a closed base word `w`, append every nonempty closed extension `e` of length
<= 2 and count:

  admitted(w) = # { e : is_zfa(w ++ e) }
  distinct(w) = # { canonical_word(w ++ e) }

Because `w` is already closed, `w ++ e` closes exactly when `e` closes. The
admissible extension set is therefore independent of `w`; every base has the
same eight extensions. Raw continuation counting cannot support D8c.

Distinct canonical composites do vary by axis support, but that is reported as
an exploratory structural metric, not a measured diversity advantage.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
from typing import Sequence

from assembly_index import AXIS, TWISTS, canonical_word, fold, is_closed

OUTPUT = Path("data/diversity_d8c_census.json")
BASE_LENGTH = 6
MAX_EXTENSION_LENGTH = 2


def is_zfa(word: str) -> bool:
    return is_closed(word) and fold(word) is not None


def spatial_axes(word: str) -> tuple[int, ...]:
    return tuple(sorted({AXIS[ch] for ch in word if AXIS[ch] != 3}))


def support_size(word: str) -> int:
    return len(spatial_axes(word))


def words_of_length(length: int) -> list[str]:
    return ["".join(chars) for chars in product(TWISTS, repeat=length)]


def closed_extensions(max_length: int = MAX_EXTENSION_LENGTH) -> list[str]:
    return [
        "".join(chars)
        for length in range(1, max_length + 1)
        for chars in product(TWISTS, repeat=length)
        if is_zfa("".join(chars))
    ]


def profile(word: str, extensions: Sequence[str]) -> dict[str, object]:
    admitted = [word + ext for ext in extensions if is_zfa(word + ext)]
    distinct = {canonical_word(composite) for composite in admitted}
    return {
        "admitted": len(admitted),
        "distinct": len(distinct),
        "canonical": sorted(distinct),
    }


def census(
    base_length: int = BASE_LENGTH,
    max_extension_length: int = MAX_EXTENSION_LENGTH,
) -> dict[str, object]:
    closed = [word for word in words_of_length(base_length) if is_zfa(word)]
    extensions = closed_extensions(max_extension_length)
    groups: dict[int, list[str]] = defaultdict(list)
    for word in closed:
        groups[support_size(word)].append(word)

    group_stats: dict[str, object] = {}
    for size in sorted(groups):
        words = groups[size]
        admitted_counts: Counter[int] = Counter()
        distinct_counts: Counter[int] = Counter()
        for word in words:
            p = profile(word, extensions)
            admitted_counts[int(p["admitted"])] += 1
            distinct_counts[int(p["distinct"])] += 1
        total_distinct = sum(k * v for k, v in distinct_counts.items())
        group_stats[str(size)] = {
            "bases": len(words),
            "admitted_counts": {str(k): v for k, v in sorted(admitted_counts.items())},
            "distinct_type_counts": {str(k): v for k, v in sorted(distinct_counts.items())},
            "mean_distinct_types": total_distinct / len(words),
        }

    all_admitted = {
        count
        for stats in group_stats.values()
        for count in stats["admitted_counts"]  # type: ignore[index]
    }
    return {
        "base_length": base_length,
        "max_extension_length": max_extension_length,
        "closed_bases": len(closed),
        "closed_extensions": len(extensions),
        "extension_words": extensions,
        "groups": group_stats,
        "raw_continuation_counts_identical": len(all_admitted) == 1,
        "verdict": (
            "negative_on_raw_continuation; canonical-composite variation is exploratory only"
        ),
        "note": (
            "w is closed, so w++e closes exactly when e closes. The admitted "
            "extension set is independent of w; raw continuation count cannot "
            "distinguish axis support. Distinct canonical composites are not a "
            "matched measure and do not pass D8c."
        ),
    }


def build_summary() -> dict[str, object]:
    return {
        "meta": {
            "generator": "diversity_continuation.py",
            "version": 1,
            "issue": 290,
            "gate": "D8c pilot",
            "pre_registration": "Diversity_Continuation_D8c.md",
        },
        "census": census(),
        "gates": {
            "D8c0_raw_continuation": "fail as a diversity metric: admitted count is invariant",
            "D8c1_canonical_variety": "exploratory only; unmatched and not independent",
            "D8c2_matched_measure": "open; requires a richer D3 composition relation",
        },
    }


def self_test() -> None:
    extensions = closed_extensions()
    assert len(extensions) == 8
    assert all(is_zfa(word) for word in extensions)
    result = census()
    assert result["closed_bases"] == 5120
    assert result["raw_continuation_counts_identical"] is True
    for stats in result["groups"].values():
        assert list(stats["admitted_counts"].keys()) == ["8"]
    assert result["groups"]["3"]["mean_distinct_types"] == 7.0
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    result = summary["census"]  # type: ignore[index]
    print("\ncensus:")
    print(
        f"  closed_bases={result['closed_bases']} "
        f"closed_extensions={result['closed_extensions']} "
        f"raw_identical={result['raw_continuation_counts_identical']}"
    )
    for size, stats in result["groups"].items():
        print(
            f"  support={size} bases={stats['bases']} "
            f"admitted={stats['admitted_counts']} "
            f"mean_distinct={stats['mean_distinct_types']:.3f}"
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
