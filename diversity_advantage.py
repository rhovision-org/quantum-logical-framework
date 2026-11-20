#!/usr/bin/env python3
"""D8c2a screen: does axis-support diversity increase interface continuations? (#290)

Using the frozen D3 conjugate-boundary relation, compare the mean number of
distinct continuation classes K for bases grouped by spatial-axis support.

The screen is deliberately simple and pre-declared:

  homogeneous  = bases with exactly one spatial axis
  heterogeneous = bases with two or three spatial axes
  fixed        = base length L and extension bound k
  endpoint     = mean K per base

It is a base-level screen, not the full matched population test. A negative
result blocks the full D8c2 test under this relation/measure.

The null model replaces ZFA closure with net-action zero but keeps the
conjugate boundary and canonicalization. If the null matches exactly, the
effect is not ZFA-specific.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Sequence

from assembly_index import AXIS, CONJUGATE, TWISTS, canonical_word, fold, is_closed, net

OUTPUT = Path("data/diversity_d8c2a_screen.json")
BASE_LENGTHS = (3, 4, 5)
EXTENSION_BOUND = 3


def is_zfa(word: str) -> bool:
    return is_closed(word) and fold(word) is not None


def spatial_axes(word: str) -> tuple[int, ...]:
    return tuple(sorted({AXIS[ch] for ch in word if AXIS[ch] != 3}))


def support_size(word: str) -> int:
    return len(spatial_axes(word))


def interface_ok(a: str, b: str) -> bool:
    return bool(a) and bool(b) and a[-1] == CONJUGATE[b[0]]


def join(a: str, b: str, null: bool = False) -> bool:
    if not interface_ok(a, b):
        return False
    if null:
        return net(a + b) == (0, 0, 0, 0)
    return is_zfa(a + b)


def continuation_classes(a: str, extensions: Sequence[str], null: bool = False) -> frozenset[str]:
    return frozenset(
        canonical_word(a + b)
        for b in extensions
        if join(a, b, null=null)
    )


def extensions_upto(bound: int = EXTENSION_BOUND) -> list[str]:
    return [
        "".join(chars)
        for length in range(1, bound + 1)
        for chars in product(TWISTS, repeat=length)
    ]


@lru_cache(maxsize=8)
def screen(lengths: Sequence[int] = BASE_LENGTHS, bound: int = EXTENSION_BOUND) -> dict[str, object]:
    extensions = extensions_upto(bound)
    by_length: dict[str, object] = {}
    null_differences = 0
    total_bases = 0

    for length in lengths:
        groups: dict[int, list[int]] = defaultdict(list)
        for chars in product(TWISTS, repeat=length):
            a = "".join(chars)
            total_bases += 1
            zfa_classes = continuation_classes(a, extensions, null=False)
            null_classes = continuation_classes(a, extensions, null=True)
            if zfa_classes != null_classes:
                null_differences += 1
            groups[support_size(a)].append(len(zfa_classes))

        group_stats = {}
        for support in sorted(groups):
            values = groups[support]
            group_stats[str(support)] = {
                "bases": len(values),
                "mean_K": sum(values) / len(values),
                "K_counts": {str(k): v for k, v in sorted(Counter(values).items())},
            }

        hom = groups.get(1, [])
        het = groups.get(2, []) + groups.get(3, [])
        mean_hom = sum(hom) / len(hom) if hom else None
        mean_het = sum(het) / len(het) if het else None
        by_length[str(length)] = {
            "groups": group_stats,
            "homogeneous_support_1": {
                "bases": len(hom),
                "mean_K": mean_hom,
            },
            "heterogeneous_support_2_3": {
                "bases": len(het),
                "mean_K": mean_het,
            },
            "heterogeneous_advantage": (
                mean_hom is not None and mean_het is not None and mean_het > mean_hom
            ),
        }

    advantages = [
        stats["heterogeneous_advantage"]  # type: ignore[index]
        for stats in by_length.values()
    ]
    return {
        "base_lengths": list(lengths),
        "extension_bound": bound,
        "total_bases": total_bases,
        "null_differences": null_differences,
        "null_matches_exactly": null_differences == 0,
        "by_length": by_length,
        "screen_advantages": advantages,
        "verdict": (
            "negative_no_heterogeneous_advantage"
            if not any(advantages)
            else "candidate_signal_requires_matched_population_test"
        ),
        "d8c2": "not run; base-level screen blocks it under this relation/measure",
        "note": (
            "Homogeneous and heterogeneous groups are not population-size matched; "
            "this is a screen, not the full D8c2 test. No post-hoc subgroup was used."
        ),
    }


def build_summary() -> dict[str, object]:
    return {
        "meta": {
            "generator": "diversity_advantage.py",
            "version": 1,
            "issue": 290,
            "gate": "D8c2a base-level screen",
            "pre_registration": "Diversity_Advantage_D8c2a.md",
        },
        "screen": screen(),
        "gates": {
            "D8c2a_heterogeneous_advantage": "fail: no length shows higher mean K for support 2/3",
            "D8c2a_null_separation": "fail: null continuation sets match ZFA exactly",
            "D8c2_matched_population": "not run; blocked by the screen",
        },
    }


def self_test() -> None:
    assert interface_ok("^", "v")
    assert join("^", "v")
    assert not join("^", "^")
    result = screen()
    assert result["total_bases"] == 512 + 4096 + 32768
    assert result["null_matches_exactly"] is True
    assert result["verdict"] == "negative_no_heterogeneous_advantage"
    for stats in result["by_length"].values():
        assert stats["heterogeneous_advantage"] is False
    assert result["by_length"]["3"]["homogeneous_support_1"]["mean_K"] == 2.5
    assert result["by_length"]["5"]["homogeneous_support_1"]["mean_K"] > result["by_length"]["5"]["heterogeneous_support_2_3"]["mean_K"]
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    result = summary["screen"]  # type: ignore[index]
    print("\nscreen:")
    print(
        f"  total_bases={result['total_bases']} "
        f"null_differences={result['null_differences']} "
        f"verdict={result['verdict']}"
    )
    for length, stats in result["by_length"].items():
        hom = stats["homogeneous_support_1"]
        het = stats["heterogeneous_support_2_3"]
        print(
            f"  L={length}: hom mean K={hom['mean_K']:.3f} (n={hom['bases']}) "
            f"het mean K={het['mean_K']:.3f} (n={het['bases']}) "
            f"advantage={stats['heterogeneous_advantage']}"
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
