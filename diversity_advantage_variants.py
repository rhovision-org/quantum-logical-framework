#!/usr/bin/env python3
"""D8c2b revision synthesis: two candidate rescues both fail (#290).

Candidate 1 — phase-labelled closure classes:
    K_phase(a) = |{ (canonical_word(a++b), fold(a++b)) : join(a,b) }|
The phase label adds no new classes in the tested range.

Candidate 2 — two-interface continuation:
    a -> b -> c with join(a,b) and join(a++b,c)
The heterogeneous support groups remain below the one-axis group, and the
net-zero null model matches the ZFA continuation sets exactly.

This is a negative synthesis, not another D8c2 attempt. A further test
requires a genuinely different relation derived from the primitive algebra.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Sequence

from assembly_index import AXIS, CONJUGATE, TWISTS, canonical_word, fold, is_closed, net

OUTPUT = Path("data/diversity_d8c2b_revision.json")
PHASE_LENGTHS = (3, 4, 5)
TWO_INTERFACE_LENGTHS = (3, 4)
EXTENSION_BOUND = 2


def is_zfa(word: str) -> bool:
    return is_closed(word) and fold(word) is not None


def support_size(word: str) -> int:
    return len({AXIS[ch] for ch in word if AXIS[ch] != 3})


def extensions_upto(bound: int = EXTENSION_BOUND) -> list[str]:
    return [
        "".join(chars)
        for length in range(1, bound + 1)
        for chars in product(TWISTS, repeat=length)
    ]


def interface_ok(a: str, b: str) -> bool:
    return bool(a) and bool(b) and a[-1] == CONJUGATE[b[0]]


def join(a: str, b: str, null: bool = False) -> bool:
    if not interface_ok(a, b):
        return False
    if null:
        return net(a + b) == (0, 0, 0, 0)
    return is_zfa(a + b)


def phase_profile(a: str, extensions: Sequence[str]) -> tuple[int, int]:
    canonical = set()
    phase_labelled = set()
    for b in extensions:
        if not join(a, b):
            continue
        composite = a + b
        canonical.add(canonical_word(composite))
        phase_labelled.add((canonical_word(composite), fold(composite)))
    return len(canonical), len(phase_labelled)


def phase_census(lengths: Sequence[int] = PHASE_LENGTHS) -> dict[str, object]:
    extensions = extensions_upto(EXTENSION_BOUND)
    by_length = {}
    added = 0
    total = 0
    for length in lengths:
        diffs = 0
        bases = 0
        for chars in product(TWISTS, repeat=length):
            a = "".join(chars)
            k, kp = phase_profile(a, extensions)
            bases += 1
            total += 1
            if kp != k:
                diffs += 1
                added += kp - k
        by_length[str(length)] = {"bases": bases, "phase_added_classes": diffs}
    return {
        "lengths": list(lengths),
        "total_bases": total,
        "bases_with_added_classes": added,
        "by_length": by_length,
        "verdict": "phase_label_adds_no_classes" if added == 0 else "phase_label_changes_classes",
    }


def two_interface_profile(a: str, extensions: Sequence[str], null: bool = False) -> frozenset[str]:
    classes = set()
    for b in extensions:
        if not join(a, b, null=null):
            continue
        ab = a + b
        for c in extensions:
            if join(ab, c, null=null):
                classes.add(canonical_word(ab + c))
    return frozenset(classes)


@lru_cache(maxsize=8)
def two_interface_census(lengths: tuple[int, ...] = TWO_INTERFACE_LENGTHS) -> dict[str, object]:
    extensions = extensions_upto()
    by_length = {}
    null_differences = 0
    total = 0
    for length in lengths:
        groups: dict[int, list[int]] = defaultdict(list)
        for chars in product(TWISTS, repeat=length):
            a = "".join(chars)
            total += 1
            zfa_classes = two_interface_profile(a, extensions, null=False)
            null_classes = two_interface_profile(a, extensions, null=True)
            if zfa_classes != null_classes:
                null_differences += 1
            groups[support_size(a)].append(len(zfa_classes))
        stats = {}
        for support, values in sorted(groups.items()):
            stats[str(support)] = {
                "bases": len(values),
                "mean_K2": sum(values) / len(values),
            }
        hom = groups.get(1, [])
        het = groups.get(2, []) + groups.get(3, [])
        mean_hom = sum(hom) / len(hom) if hom else None
        mean_het = sum(het) / len(het) if het else None
        by_length[str(length)] = {
            "groups": stats,
            "homogeneous_mean_K2": mean_hom,
            "heterogeneous_mean_K2": mean_het,
            "heterogeneous_advantage": (
                mean_hom is not None and mean_het is not None and mean_het > mean_hom
            ),
        }
    advantages = [stats["heterogeneous_advantage"] for stats in by_length.values()]
    return {
        "lengths": list(lengths),
        "total_bases": total,
        "null_differences": null_differences,
        "null_matches_exactly": null_differences == 0,
        "by_length": by_length,
        "verdict": (
            "negative_no_two_interface_advantage"
            if not any(advantages)
            else "candidate_signal_requires_new_relation_test"
        ),
    }


def build_summary() -> dict[str, object]:
    return {
        "meta": {
            "generator": "diversity_advantage_variants.py",
            "version": 1,
            "issue": 290,
            "gate": "D8c2b revision synthesis",
            "pre_registration": "Diversity_Revision_D8c2b.md",
        },
        "phase": phase_census(),
        "two_interface": two_interface_census(),
        "gates": {
            "D8c2b_phase_revision": "fail: phase label adds no classes",
            "D8c2b_two_interface": "fail: no advantage; null matches ZFA exactly",
            "D8c2": "not passed; a genuinely new relation is required",
        },
    }


def self_test() -> None:
    assert phase_census()["bases_with_added_classes"] == 0
    two = two_interface_census()
    assert two["null_matches_exactly"] is True
    assert two["verdict"] == "negative_no_two_interface_advantage"
    for stats in two["by_length"].values():
        assert stats["heterogeneous_advantage"] is False
    assert two["by_length"]["3"]["homogeneous_mean_K2"] == 0.21428571428571427
    assert two["by_length"]["4"]["homogeneous_mean_K2"] == 0.55
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    phase = summary["phase"]  # type: ignore[index]
    print(
        f"\nphase: bases={phase['total_bases']} "
        f"with_added_classes={phase['bases_with_added_classes']}"
    )
    two = summary["two_interface"]  # type: ignore[index]
    print(
        f"two-interface: bases={two['total_bases']} "
        f"null_differences={two['null_differences']}"
    )
    for length, stats in two["by_length"].items():
        print(
            f"  L={length}: hom={stats['homogeneous_mean_K2']:.3f} "
            f"het={stats['heterogeneous_mean_K2']:.3f} "
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
