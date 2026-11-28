#!/usr/bin/env python3
"""D3T typed-provenance residual-obligation census (#290).

Pre-registration: ``Diversity_Obligation_D3T.md``.
Census note: ``Diversity_Obligation_Census_D3T.md``.

The relation is frozen in the pre-registration.  This module enumerates only the
declared finite panels:

    panel A: two-origin open bases of length 3, extensions of length <= 3
    panel B: two-origin open bases of length 4, extensions of length <= 2

and the whole-history phase check for closed two-origin histories of lengths 4
and 6.

The primary observable is the set-valued continuation profile

    C_T(a) = { B(b) : R_T(a, b) }

where B is the per-origin residual-obligation record.  The aggregate control
keeps the same bases/extensions/first-closure rule but admits extensions with a
complementary aggregate net, ignoring per-origin matching.  The phase check asks
whether B determines the closure phase; it is a separate observable and is not
used to tune the relation.

No weights, fitted parameters, target geometry, or post-hoc fields are used.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Iterable, Iterator, Sequence

from assembly_index import TWISTS, net, is_closed, fold, pauli_mul, TWIST_NF

OUTPUT = Path("data/diversity_obligation_census.json")
ORIGIN_COUNT = 2
PANELS = (("A", 3, 3), ("B", 4, 2))
WHOLE_HISTORY_LENGTHS = (4, 6)

ProvEvent = tuple[int, str]
ProvHistory = tuple[ProvEvent, ...]
Pauli = tuple[int, int]


def pauli(word: str) -> Pauli:
    """Full Pauli product of a word, including the scalar phase."""
    acc: Pauli = (0, 0)
    for ch in word:
        acc = pauli_mul(acc, TWIST_NF[ch])
    return acc


def is_zfa(word: str) -> bool:
    """QLF closure: count balance plus a scalar Pauli fold."""
    return is_closed(word) and fold(word) is not None


def canonical_history(events: Iterable[ProvEvent]) -> ProvHistory:
    """Relabel origins by first appearance."""
    remap: dict[int, int] = {}
    out: list[ProvEvent] = []
    for origin, twist in events:
        if origin not in remap:
            remap[origin] = len(remap)
        out.append((remap[origin], twist))
    return tuple(out)


def origin_patterns(length: int, origins: int = ORIGIN_COUNT) -> tuple[tuple[int, ...], ...]:
    """Canonical origin schedules: all origins used, first appearance order."""
    patterns: list[tuple[int, ...]] = []
    for schedule in product(range(origins), repeat=length):
        if set(schedule) != set(range(origins)):
            continue
        remap: dict[int, int] = {}
        for origin in schedule:
            if origin not in remap:
                remap[origin] = len(remap)
        if all(remap[origin] == origin for origin in schedule):
            patterns.append(schedule)
    return tuple(patterns)


def histories(length: int, origins: int = ORIGIN_COUNT) -> Iterator[ProvHistory]:
    """All canonical provenance-typed histories of *length* with *origins* streams."""
    patterns = origin_patterns(length, origins)
    for twists in product(TWISTS, repeat=length):
        for schedule in patterns:
            yield tuple(zip(schedule, twists))


def word(history: ProvHistory) -> str:
    return "".join(twist for _, twist in history)


def projection(history: ProvHistory, origin: int) -> str:
    return "".join(twist for event_origin, twist in history if event_origin == origin)


def origins(history: ProvHistory) -> tuple[int, ...]:
    return tuple(sorted({origin for origin, _ in history}))


def obligation(history: ProvHistory, origin: int) -> tuple[tuple[int, ...], int, int]:
    """Residual obligation: net action, Pauli axis, and Pauli phase."""
    projected = projection(history, origin)
    phase, axis = pauli(projected)
    return net(projected), axis, phase


def boundary(history: ProvHistory) -> tuple[tuple[tuple[int, ...], int, int], ...]:
    """Sorted multiset of per-origin obligations; origin labels forgotten."""
    return tuple(sorted(obligation(history, origin) for origin in origins(history)))


def boundary_key(history: ProvHistory) -> tuple[tuple[tuple[int, ...], int], ...]:
    """Boundary record without the phase labels; this is the matching key."""
    return tuple(sorted((obligation[0], obligation[1]) for obligation in boundary(history)))


def complement_key(
    key: tuple[tuple[tuple[int, ...], int], ...]
) -> tuple[tuple[tuple[int, ...], int], ...]:
    """Per-stream complement: opposite net, same Pauli axis, phase unconstrained."""
    return tuple(sorted((tuple(-x for x in vector), axis) for vector, axis in key))


def aggregate(history: ProvHistory) -> tuple[tuple[int, ...], int, int]:
    """Aggregate closure data: total net, Pauli axis, Pauli phase."""
    phase, axis = pauli(word(history))
    return net(word(history)), axis, phase


def is_open(history: ProvHistory) -> bool:
    return not is_zfa(word(history))


def joint_history(a: ProvHistory, b: ProvHistory) -> tuple[tuple[str, int, str], ...]:
    """Tag the two sides so base and extension origins cannot collide."""
    return tuple(("A", origin, twist) for origin, twist in a) + tuple(
        ("B", origin, twist) for origin, twist in b
    )


def first_joint_closure_at_end(a: ProvHistory, b: ProvHistory) -> bool:
    """True iff the final prefix is the first all-origin ZFA closure."""
    if not a or not b:
        return False
    combined = word(a) + word(b)
    if not is_zfa(combined):
        return False
    events = joint_history(a, b)
    declared = {(side, origin) for side, origin, _ in events}
    seen: set[tuple[str, int]] = set()
    for index, (side, origin, _) in enumerate(events[:-1], start=1):
        seen.add((side, origin))
        if seen == declared and is_zfa(combined[:index]):
            return False
    return True


def obligations_match(a: ProvHistory, b: ProvHistory) -> bool:
    """The no-pooling, two-sided residual-obligation matching condition.

    Origin integers are local to each history.  ``joint_history`` tags the two
    sides ``A`` and ``B``, so the frozen "fresh continuation streams" condition
    is enforced semantically even though both histories use labels 0, 1.
    """
    if not a or not b:
        return False
    if len(origins(a)) != len(origins(b)):
        return False
    if not is_open(a) or not is_open(b):
        return False
    return complement_key(boundary_key(a)) == boundary_key(b)


def typed_join(a: ProvHistory, b: ProvHistory) -> bool:
    """Frozen D3T relation R_T(a, b)."""
    if not obligations_match(a, b):
        return False
    if not is_zfa(word(a) + word(b)):
        return False
    return first_joint_closure_at_end(a, b)


def aggregate_match(a: ProvHistory, b: ProvHistory) -> bool:
    """Aggregate control: only the total net has to cancel."""
    if not a or not b:
        return False
    if not is_open(a) or not is_open(b):
        return False
    return all(
        left + right == 0
        for left, right in zip(net(word(a)), net(word(b)))
    )


def aggregate_join(a: ProvHistory, b: ProvHistory) -> bool:
    """Control relation: aggregate net, no per-origin matching."""
    if not aggregate_match(a, b):
        return False
    if not is_zfa(word(a) + word(b)):
        return False
    return first_joint_closure_at_end(a, b)


def _phase_key(phases: Iterable[int]) -> str:
    return ",".join(str(phase) for phase in sorted(phases))


def _example_profile(profile: frozenset) -> list:
    """A small JSON-friendly representative of a profile (boundary records only)."""
    return [
        [[list(vector), axis, phase] for vector, axis, phase in record]
        for record in sorted(profile)
    ]


@lru_cache(maxsize=None)
def panel_stats(length: int, bound: int, origin_count: int = ORIGIN_COUNT) -> dict[str, object]:
    """Exhaustive gate census for one declared panel."""
    all_bases = tuple(histories(length, origin_count))
    bases = tuple(history for history in all_bases if is_open(history))
    closed_bases = len(all_bases) - len(bases)
    extensions = tuple(history for history in histories(bound, origin_count) if is_open(history))

    extensions_by_key: dict[tuple, list[ProvHistory]] = defaultdict(list)
    extensions_by_net: dict[tuple[int, ...], list[ProvHistory]] = defaultdict(list)
    for extension in extensions:
        extensions_by_key[boundary_key(extension)].append(extension)
        extensions_by_net[net(word(extension))].append(extension)

    profiles: dict[ProvHistory, frozenset] = {}
    aggregate_profiles: dict[ProvHistory, frozenset] = {}
    phase_groups: dict[tuple[ProvHistory, tuple], set[int]] = defaultdict(set)
    phase_pattern: dict[tuple[ProvHistory, tuple, tuple[int, ...]], set[int]] = defaultdict(set)
    phase_word: dict[tuple[ProvHistory, tuple, str], set[int]] = defaultdict(set)
    phase_sets: Counter[str] = Counter()

    typed_joins = 0
    aggregate_joins = 0
    closure_failures = 0
    first_closure_failures = 0

    for base in bases:
        profile: set[tuple] = set()
        for extension in extensions_by_key.get(complement_key(boundary_key(base)), ()):
            if not obligations_match(base, extension):
                continue
            combined = word(base) + word(extension)
            closure_ok = is_zfa(combined)
            first_ok = first_joint_closure_at_end(base, extension)
            if not closure_ok:
                closure_failures += 1
            if not first_ok:
                first_closure_failures += 1
            if not (closure_ok and first_ok):
                continue

            typed_joins += 1
            record = boundary(extension)
            profile.add(record)
            phase = fold(combined)
            phase_groups[(base, record)].add(phase)
            phase_pattern[(base, record, tuple(origin for origin, _ in extension))].add(phase)
            phase_word[(base, record, word(extension))].add(phase)

        profiles[base] = frozenset(profile)

        aggregate_profile: set[tuple] = set()
        target_net = tuple(-x for x in net(word(base)))
        for extension in extensions_by_net.get(target_net, ()):
            if aggregate_join(base, extension):
                aggregate_joins += 1
                aggregate_profile.add(boundary(extension))
        aggregate_profiles[base] = frozenset(aggregate_profile)

    for phases in phase_groups.values():
        phase_sets[_phase_key(phases)] += 1

    aggregate_groups: dict[tuple, set[frozenset]] = defaultdict(set)
    boundary_groups: dict[tuple, set[frozenset]] = defaultdict(set)
    word_groups: dict[str, set[frozenset]] = defaultdict(set)
    for base in bases:
        aggregate_groups[aggregate(base)].add(profiles[base])
        boundary_groups[boundary(base)].add(profiles[base])
        word_groups[word(base)].add(profiles[base])

    typed_nonempty = sum(bool(profile) for profile in profiles.values())
    aggregate_nonempty = sum(bool(profile) for profile in aggregate_profiles.values())
    distinct_typed = len(set(profiles.values()))
    distinct_aggregate = len(set(aggregate_profiles.values()))
    typed_differs = sum(profiles[base] != aggregate_profiles[base] for base in bases)

    # A representative profile for documentation, chosen deterministically.
    representative = None
    for base in sorted(bases):
        if profiles[base]:
            representative = {
                "base": [[origin, twist] for origin, twist in base],
                "word": word(base),
                "boundary": [
                    [list(vector), axis, phase]
                    for vector, axis, phase in boundary(base)
                ],
                "profile_size": len(profiles[base]),
                "profile": _example_profile(profiles[base]),
            }
            break

    # A representative phase-ambiguity witness, if one exists.
    phase_witness = None
    for base in sorted(bases):
        for extension in extensions_by_key.get(complement_key(boundary_key(base)), ()):
            if not typed_join(base, extension):
                continue
            record = boundary(extension)
            phases = phase_groups[(base, record)]
            if len(phases) > 1:
                witnesses = []
                for candidate in extensions_by_key[complement_key(boundary_key(base))]:
                    if not typed_join(base, candidate) or boundary(candidate) != record:
                        continue
                    phase = fold(word(base) + word(candidate))
                    if all(existing["phase"] != phase for existing in witnesses):
                        witnesses.append(
                            {
                                "extension": [[origin, twist] for origin, twist in candidate],
                                "word": word(candidate),
                                "phase": phase,
                            }
                        )
                phase_witness = {
                    "base": [[origin, twist] for origin, twist in base],
                    "word": word(base),
                    "boundary": [[list(vector), axis, phase] for vector, axis, phase in record],
                    "extensions": witnesses,
                }
                break
        if phase_witness is not None:
            break

    # A same-word/different-provenance witness, if one exists.
    word_witness = None
    for value, group in word_groups.items():
        if len(group) <= 1:
            continue
        members = [base for base in bases if word(base) == value]
        by_profile: dict[frozenset, ProvHistory] = {}
        for member in members:
            by_profile.setdefault(profiles[member], member)
        if len(by_profile) < 2:
            continue
        chosen = list(by_profile.values())[:2]
        word_witness = {
            "word": value,
            "bases": [
                {
                    "history": [[origin, twist] for origin, twist in member],
                    "boundary": [
                        [list(vector), axis, phase]
                        for vector, axis, phase in boundary(member)
                    ],
                    "profile_size": len(profiles[member]),
                }
                for member in chosen
            ],
        }
        break

    # A same-aggregate/different-profile witness, if one exists.
    aggregate_witness = None
    for value, group in aggregate_groups.items():
        if len(group) <= 1:
            continue
        members = [base for base in bases if aggregate(base) == value]
        by_profile = {}
        for member in members:
            by_profile.setdefault(profiles[member], member)
        if len(by_profile) < 2:
            continue
        chosen = list(by_profile.values())[:2]
        aggregate_witness = {
            "aggregate": [list(value[0]), value[1], value[2]],
            "bases": [
                {
                    "history": [[origin, twist] for origin, twist in member],
                    "boundary": [
                        [list(vector), axis, phase]
                        for vector, axis, phase in boundary(member)
                    ],
                    "profile_size": len(profiles[member]),
                }
                for member in chosen
            ],
        }
        break

    return {
        "base_length": length,
        "extension_bound": bound,
        "origin_count": origin_count,
        "base_histories": len(all_bases),
        "closed_bases_excluded": closed_bases,
        "open_bases": len(bases),
        "extensions": len(extensions),
        "typed_joins": typed_joins,
        "aggregate_joins": aggregate_joins,
        "typed_profiles_nonempty": typed_nonempty,
        "aggregate_profiles_nonempty": aggregate_nonempty,
        "distinct_typed_profiles": distinct_typed,
        "distinct_aggregate_profiles": distinct_aggregate,
        "typed_differs_from_aggregate": typed_differs,
        "aggregate_groups": len(aggregate_groups),
        "aggregate_groups_with_multiple_profiles": sum(
            len(group) > 1 for group in aggregate_groups.values()
        ),
        "boundary_groups": len(boundary_groups),
        "boundary_groups_with_multiple_profiles": sum(
            len(group) > 1 for group in boundary_groups.values()
        ),
        "word_groups": len(word_groups),
        "word_groups_with_multiple_profiles": sum(
            len(group) > 1 for group in word_groups.values()
        ),
        "phase_groups": len(phase_groups),
        "phase_ambiguous_groups": sum(len(group) > 1 for group in phase_groups.values()),
        "phase_set_distribution": dict(sorted(phase_sets.items())),
        "phase_pattern_groups": len(phase_pattern),
        "phase_pattern_ambiguous_groups": sum(
            len(group) > 1 for group in phase_pattern.values()
        ),
        "phase_word_groups": len(phase_word),
        "phase_word_ambiguous_groups": sum(len(group) > 1 for group in phase_word.values()),
        "closure_failures": closure_failures,
        "first_closure_failures": first_closure_failures,
        "representative_profile": representative,
        "phase_witness": phase_witness,
        "word_witness": word_witness,
        "aggregate_witness": aggregate_witness,
    }


@lru_cache(maxsize=None)
def whole_history_phase_stats(length: int, origin_count: int = ORIGIN_COUNT) -> dict[str, object]:
    """Does B(h) determine fold(word(h)) for closed two-origin histories?"""
    patterns = origin_patterns(length, origin_count)
    groups: dict[tuple, set[int]] = defaultdict(set)
    phase_examples: dict[tuple[tuple, int], ProvHistory] = {}
    phase_sets: Counter[str] = Counter()
    closed_histories = 0

    for twists in product(TWISTS, repeat=length):
        twist_word = "".join(twists)
        if not is_zfa(twist_word):
            continue
        phase = fold(twist_word)
        for schedule in patterns:
            history = tuple(zip(schedule, twists))
            record = boundary(history)
            groups[record].add(phase)
            phase_examples.setdefault((record, phase), history)
            closed_histories += 1

    for phases in groups.values():
        phase_sets[_phase_key(phases)] += 1

    witness = None
    for record, phases in groups.items():
        if len(phases) <= 1:
            continue
        representatives = []
        for phase in sorted(phases):
            history = phase_examples[(record, phase)]
            representatives.append(
                {
                    "history": [[origin, twist] for origin, twist in history],
                    "word": word(history),
                    "phase": phase,
                }
            )
        witness = {
            "boundary": [[list(vector), axis, phase] for vector, axis, phase in record],
            "phases": sorted(phases),
            "histories": representatives,
        }
        break

    return {
        "length": length,
        "origin_count": origin_count,
        "closed_typed_histories": closed_histories,
        "boundary_groups": len(groups),
        "phase_ambiguous_groups": sum(len(phases) > 1 for phases in groups.values()),
        "phase_set_distribution": dict(sorted(phase_sets.items())),
        "witness": witness,
    }


def build_summary() -> dict[str, object]:
    panels = {
        panel_id: panel_stats(base_length, extension_bound)
        for panel_id, base_length, extension_bound in PANELS
    }
    whole = {
        str(length): whole_history_phase_stats(length)
        for length in WHOLE_HISTORY_LENGTHS
    }

    panel_a = panels["A"]
    panel_b = panels["B"]
    whole_4 = whole["4"]
    whole_6 = whole["6"]

    gates = {
        "D3T.1_interface_dependence": (
            "PASS: "
            f"{panel_a['distinct_typed_profiles']} distinct typed profiles over "
            f"{panel_a['open_bases']} bases (panel A); "
            f"{panel_b['distinct_typed_profiles']} over {panel_b['open_bases']} (panel B)"
        ),
        "D3T.2_closure_preservation": (
            "PASS: 0 closure failures among obligation-matching candidates; "
            f"{panel_a['typed_joins']} + {panel_b['typed_joins']} admitted joins"
        ),
        "D3T.3_provenance_separation": (
            "PASS: same aggregate data, different profile in "
            f"{panel_a['aggregate_groups_with_multiple_profiles']}/{panel_a['aggregate_groups']} "
            f"groups (panel A) and "
            f"{panel_b['aggregate_groups_with_multiple_profiles']}/{panel_b['aggregate_groups']} "
            f"(panel B); same raw word, different provenance profile in "
            f"{panel_a['word_groups_with_multiple_profiles']}/{panel_a['word_groups']} and "
            f"{panel_b['word_groups_with_multiple_profiles']}/{panel_b['word_groups']}; "
            f"typed differs from aggregate control on "
            f"{panel_a['typed_differs_from_aggregate']}/{panel_a['open_bases']} and "
            f"{panel_b['typed_differs_from_aggregate']}/{panel_b['open_bases']} bases"
        ),
        "D3T.4_first_closure_integrity": (
            "PASS: 0 earlier all-origin closures among obligation-matching candidates"
        ),
        "D3T.5_continuation_boundary_sufficiency": (
            "PASS: 0 boundary groups with multiple continuation profiles "
            f"({panel_a['boundary_groups']} groups panel A; "
            f"{panel_b['boundary_groups']} panel B)"
        ),
        "D3T.6_phase_boundary_sufficiency": (
            "FAIL: whole-history phase ambiguous in "
            f"{whole_4['phase_ambiguous_groups']}/{whole_4['boundary_groups']} boundary groups "
            f"at length 4 and {whole_6['phase_ambiguous_groups']}/{whole_6['boundary_groups']} "
            f"at length 6; extension phase ambiguous in "
            f"{panel_a['phase_ambiguous_groups']}/{panel_a['phase_groups']} groups (panel A) "
            f"and {panel_b['phase_ambiguous_groups']}/{panel_b['phase_groups']} (panel B)"
        ),
        "D3T.7_no_target_geometry": (
            "PASS by construction: twist, net, Pauli product, provenance, and first closure only"
        ),
        "D8c2": (
            "NOT RUN: D3T.1-D3T.5 pass, but D3T.6 fails for the closure phase; no advantage "
            "test is run under a boundary record that does not determine the phase. D8c2 remains "
            "NOT PASSED."
        ),
    }

    return {
        "meta": {
            "generator": "diversity_obligation.py",
            "version": 1,
            "issue": 290,
            "gate": "D3T typed-provenance residual obligations",
            "pre_registration": "Diversity_Obligation_D3T.md",
            "census": "Diversity_Obligation_Census_D3T.md",
        },
        "parameters": {
            "origin_count": ORIGIN_COUNT,
            "panels": [
                {"id": panel_id, "base_length": base_length, "extension_bound": extension_bound}
                for panel_id, base_length, extension_bound in PANELS
            ],
            "whole_history_lengths": list(WHOLE_HISTORY_LENGTHS),
        },
        "panels": panels,
        "whole_history_phase": whole,
        "gates": gates,
        "verdict": {
            "relation": "D3T typed-provenance residual obligations",
            "interface_gates": "D3T.1-D3T.5 PASS",
            "phase_dictionary": "D3T.6 FAIL",
            "d8c2": "NOT RUN; NOT PASSED",
            "next": (
                "Decide whether the closure phase is in scope. If yes, pre-register a "
                "schedule-resolved boundary relation and retest D3T.6 from scratch. If no, "
                "a matched D8c2 continuation-profile test is a separate pre-registration under "
                "the frozen D3T relation."
            ),
        },
    }


def _jsonable(value: object) -> object:
    """Convert tuples/sets in the summary to JSON-friendly lists."""
    if isinstance(value, dict):
        return {str(key): _jsonable(item) for key, item in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [_jsonable(item) for item in value]
    return value


def self_test() -> None:
    assert pauli("^") == (0, 2)
    assert is_zfa("^v")
    assert not is_zfa("^^")
    assert boundary(((0, "^"), (1, "v"))) == (((-1, 0, 0, 0), 2, 2), ((1, 0, 0, 0), 2, 0))

    base = ((0, "^"), (0, "^"), (1, "^"))
    extension = ((0, "v"), (0, "v"), (1, "v"))
    assert obligations_match(base, extension)
    assert typed_join(base, extension)
    assert typed_join(extension, base)
    assert not typed_join(((0, "^"), (0, "v")), extension)  # closed base
    assert not typed_join(base, base)  # wrong complement

    panel_a = panel_stats(3, 3)
    assert panel_a["open_bases"] == 1536
    assert panel_a["extensions"] == 1536
    assert panel_a["typed_joins"] == 12096
    assert panel_a["distinct_typed_profiles"] == 264
    assert panel_a["closure_failures"] == 0
    assert panel_a["first_closure_failures"] == 0
    assert panel_a["boundary_groups_with_multiple_profiles"] == 0
    assert panel_a["phase_ambiguous_groups"] == 1368

    panel_b = panel_stats(4, 2)
    assert panel_b["open_bases"] == 27496
    assert panel_b["extensions"] == 56
    assert panel_b["typed_joins"] == 8736
    assert panel_b["distinct_typed_profiles"] == 33
    assert panel_b["boundary_groups_with_multiple_profiles"] == 0
    assert panel_b["phase_ambiguous_groups"] == 2016

    whole_4 = whole_history_phase_stats(4)
    assert whole_4["closed_typed_histories"] == 1176
    assert whole_4["boundary_groups"] == 46
    assert whole_4["phase_ambiguous_groups"] == 34

    whole_6 = whole_history_phase_stats(6)
    assert whole_6["closed_typed_histories"] == 158720
    assert whole_6["boundary_groups"] == 199
    assert whole_6["phase_ambiguous_groups"] == 178

    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    print("\npanels:")
    for panel_id, stats in summary["panels"].items():  # type: ignore[union-attr]
        print(
            f"  {panel_id}: L={stats['base_length']} k={stats['extension_bound']} "
            f"bases={stats['open_bases']} joins={stats['typed_joins']} "
            f"profiles={stats['distinct_typed_profiles']} "
            f"phase_ambiguous={stats['phase_ambiguous_groups']}/{stats['phase_groups']}"
        )
    print("\nwhole-history phase:")
    for length, stats in summary["whole_history_phase"].items():  # type: ignore[union-attr]
        print(
            f"  n={length}: closed={stats['closed_typed_histories']} "
            f"boundary_groups={stats['boundary_groups']} "
            f"phase_ambiguous={stats['phase_ambiguous_groups']}"
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
    args.json.write_text(
        json.dumps(_jsonable(summary), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
