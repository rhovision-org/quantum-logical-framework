#!/usr/bin/env python3
"""Listener equivalence — finite reference implementation for #274.

Definitions are frozen in ``Listener_Equivalence_QLF.md``:

  * a finite deterministic observed transition system ``(S, A, step, obs, closed)``;
  * listener equivalence ``s ~_B t`` is the greatest bisimulation of the
    observed transition system, computed by partition refinement;
  * ``W_micro`` is the number of first-completion paths;
  * ``W_B`` is the number of listener classes among their endpoints;
  * the uniform measure is an explicit default; ``path_weights`` supplies mu(c);
  * a self-model square is faithful when it commutes up to the model bisimulation;
  * L6 checks nondecreasing levels only.  It does not exclude same-level loops.

The script is a finite check, not the general N-body theorem.  It does not modify
QKB storage and makes no consciousness/qualia claim.

Run:

    python3 listener_equivalence.py --self-test
    python3 listener_equivalence.py --run
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence

OUTPUT = Path("data/listener_equivalence_census.json")


@dataclass(frozen=True)
class ListenerSystem:
    """A finite deterministic observed transition system."""

    name: str
    states: tuple[str, ...]
    alphabet: tuple[str, ...]
    step: dict[str, dict[str, str]]
    obs: dict[str, str]
    closed: frozenset[str]

    def next(self, state: str, token: str) -> str:
        return self.step[state][token]

    def next_path(self, start: str, path: tuple[str, ...]) -> str:
        state = start
        for token in path:
            state = self.next(state, token)
        return state


# ---------------------------------------------------------------------------
# Partition refinement / greatest bisimulation
# ---------------------------------------------------------------------------

def refine(system: ListenerSystem) -> dict[str, int]:
    """Compute the greatest bisimulation by Moore partition refinement."""
    by_obs: dict[str, set[str]] = {}
    for state in system.states:
        by_obs.setdefault(system.obs[state], set()).add(state)
    ordered = sorted(by_obs.values(), key=lambda block: sorted(block))
    block = {state: i for i, states in enumerate(ordered) for state in states}
    while True:
        signatures: dict[str, tuple[object, ...]] = {}
        for state in system.states:
            signatures[state] = (
                system.obs[state],
                tuple(block[system.next(state, token)] for token in system.alphabet),
            )
        groups: dict[tuple[object, ...], set[str]] = {}
        for state in system.states:
            groups.setdefault(signatures[state], set()).add(state)
        if len(groups) == len(set(block.values())):
            return block
        ordered = sorted(groups.values(), key=lambda block: sorted(block))
        block = {state: i for i, states in enumerate(ordered) for state in states}


def blocks_of(block: dict[str, int]) -> tuple[frozenset[str], ...]:
    grouped: dict[int, set[str]] = {}
    for state, cls in block.items():
        grouped.setdefault(cls, set()).add(state)
    return tuple(frozenset(grouped[i]) for i in sorted(grouped))


def is_equivalence(block: dict[str, int], states: Iterable[str]) -> bool:
    states = tuple(states)
    reflexive = all(block[s] == block[s] for s in states)
    symmetric = all(
        (block[s] == block[t]) == (block[t] == block[s]) for s in states for t in states
    )
    transitive = all(
        not (block[s] == block[t] and block[t] == block[u]) or block[s] == block[u]
        for s in states
        for t in states
        for u in states
    )
    return reflexive and symmetric and transitive


def is_right_congruence(system: ListenerSystem, block: dict[str, int]) -> bool:
    for s in system.states:
        for t in system.states:
            if block[s] != block[t]:
                continue
            for token in system.alphabet:
                if block[system.next(s, token)] != block[system.next(t, token)]:
                    return False
    return True


def all_partitions(items: tuple[str, ...]) -> Iterator[tuple[frozenset[str], ...]]:
    """Enumerate every set partition of a small tuple (Bell number growth)."""
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for part in all_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + (part[i] | {first},) + part[i + 1 :]
        yield part + (frozenset({first}),)


def is_bisimulation_partition(
    system: ListenerSystem, part: tuple[frozenset[str], ...]
) -> bool:
    where = {state: i for i, block in enumerate(part) for state in block}
    for block in part:
        observations = {system.obs[s] for s in block}
        if len(observations) != 1:
            return False
    for s in system.states:
        for t in system.states:
            if where[s] != where[t]:
                continue
            for token in system.alphabet:
                if where[system.next(s, token)] != where[system.next(t, token)]:
                    return False
    return True


def coarsest_bisimulation(system: ListenerSystem) -> tuple[frozenset[str], ...]:
    valid = [
        part
        for part in all_partitions(system.states)
        if is_bisimulation_partition(system, part)
    ]
    return min(valid, key=lambda part: (len(part), sorted(map(sorted, part))))


# ---------------------------------------------------------------------------
# First completions and listener uncertainty
# ---------------------------------------------------------------------------

def first_completions(
    system: ListenerSystem, start: str, horizon: int
) -> tuple[tuple[str, ...], ...]:
    """First-completion token paths of at most ``horizon`` steps."""
    if start not in system.states:
        raise ValueError(f"unknown start {start!r}")
    out: list[tuple[str, ...]] = []

    def rec(state: str, path: tuple[str, ...], depth: int) -> None:
        if state in system.closed:
            out.append(path)
            return
        if depth == horizon:
            return
        for token in system.alphabet:
            rec(system.next(state, token), path + (token,), depth + 1)

    rec(start, (), 0)
    return tuple(out)


def listener_uncertainty(
    system: ListenerSystem,
    start: str,
    horizon: int,
    block: dict[str, int],
    path_weights: dict[tuple[str, ...], float] | None = None,
) -> dict[str, object]:
    """Listener-relative completion weights.

    ``path_weights`` supplies mu(c) for every first-completion path.  When it
    is omitted the measure is explicitly uniform, ``mu(c) = 1``.  Keeping this
    parameter separate prevents the uniform specialization from silently
    standing in for the general weighted formula.
    """
    paths = first_completions(system, start, horizon)
    endpoints = [system.next_path(start, path) for path in paths]
    classes = [block[endpoint] for endpoint in endpoints]
    class_states: dict[int, list[str]] = {}
    for state, cls in block.items():
        class_states.setdefault(cls, []).append(state)

    def label(cls: int) -> str:
        return "|".join(sorted(class_states[cls]))

    labels = [label(cls) for cls in classes]
    if path_weights is None:
        path_weight_values = [1.0] * len(paths)
        measure_name = "uniform"
    else:
        missing = [path for path in paths if path not in path_weights]
        if missing:
            raise ValueError(f"path_weights missing first-completion path {missing[0]!r}")
        path_weight_values = [float(path_weights[path]) for path in paths]
        if any(weight < 0 for weight in path_weight_values):
            raise ValueError("path_weights must be nonnegative")
        measure_name = "explicit"

    total_weight = sum(path_weight_values)
    if paths and total_weight <= 0:
        raise ValueError("path_weights must have positive total mass")

    counts: dict[str, int] = {}
    weighted: dict[str, float] = {}
    for cls_label, weight in zip(labels, path_weight_values):
        counts[cls_label] = counts.get(cls_label, 0) + 1
        weighted[cls_label] = weighted.get(cls_label, 0.0) + weight

    return {
        "start": start,
        "horizon": horizon,
        "measure": measure_name,
        "W_micro": len(paths),
        "W_B": sum(1 for weight in weighted.values() if weight > 0),
        "class_counts": dict(sorted(counts.items())),
        "weights": {
            cls_label: weight / total_weight
            for cls_label, weight in sorted(weighted.items())
            if weight > 0
        }
        if total_weight
        else {},
    }


# ---------------------------------------------------------------------------
# QKB toy: microscopic ways vs listener-distinguishable ways
# ---------------------------------------------------------------------------

def qkb_concept_demo() -> dict[str, object]:
    closures = ("c1", "c2", "c3", "c4")
    listener_obs = {"c1": "blue", "c2": "blue", "c3": "red", "c4": "red"}
    ways = len(set(closures))
    listener_ways = len({listener_obs[c] for c in closures})
    return {
        "closures": list(closures),
        "ways": ways,
        "listener_obs": listener_obs,
        "listener_ways": listener_ways,
    }


# ---------------------------------------------------------------------------
# Self-model square
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SelfModelToy:
    system_states: tuple[str, ...]
    system_next: dict[str, str]
    model_states: tuple[str, ...]
    model_next: dict[str, str]
    compress: dict[str, str]
    level: dict[str, int]


def good_model() -> SelfModelToy:
    return SelfModelToy(
        system_states=("s0", "s1", "s2", "s3"),
        system_next={"s0": "s2", "s1": "s3", "s2": "s2", "s3": "s3"},
        model_states=("m0", "m1"),
        model_next={"m0": "m1", "m1": "m1"},
        compress={"s0": "m0", "s1": "m0", "s2": "m1", "s3": "m1"},
        level={"s0": 0, "s1": 0, "s2": 1, "s3": 1, "m0": 0, "m1": 1},
    )


def bad_model() -> SelfModelToy:
    good = good_model()
    return SelfModelToy(
        system_states=good.system_states,
        system_next=good.system_next,
        model_states=good.model_states,
        model_next={"m0": "m0", "m1": "m1"},
        compress=good.compress,
        level=good.level,
    )


def square_commutes(toy: SelfModelToy) -> bool:
    return all(
        toy.compress[toy.system_next[s]] == toy.model_next[toy.compress[s]]
        for s in toy.system_states
    )


def levels_nondecreasing(toy: SelfModelToy) -> bool:
    """The finite monotonicity check, not an event-loop exclusion theorem.

    A transition that stays at the same level, including a self-loop, passes
    this check.  The name says exactly what is verified.
    """
    return all(
        toy.level[toy.system_next[s]] >= toy.level[s] for s in toy.system_states
    ) and all(
        toy.level[toy.model_next[m]] >= toy.level[m] for m in toy.model_states
    )


def self_loop_states(toy: SelfModelToy) -> tuple[str, ...]:
    """States whose one-step successor is themselves, in system or model.

    This is the counterexample witness: ``bad_model`` has ``m0 -> m0`` at a
    constant level, so a passing monotonicity check is not a no-loop proof.
    """
    loops = [s for s in toy.system_states if toy.system_next[s] == s]
    loops += [m for m in toy.model_states if toy.model_next[m] == m]
    return tuple(loops)


# ---------------------------------------------------------------------------
# Concrete systems and summary
# ---------------------------------------------------------------------------

def uncertainty_system(obs_c2: str = "blue") -> ListenerSystem:
    states = ("s", "a", "b", "c1", "c2")
    alphabet = ("x", "y")
    step = {
        "s": {"x": "a", "y": "b"},
        "a": {"x": "c1", "y": "c1"},
        "b": {"x": "c2", "y": "c2"},
        "c1": {"x": "c1", "y": "c1"},
        "c2": {"x": "c2", "y": "c2"},
    }
    obs = {"s": "start", "a": "midA", "b": "midB", "c1": "blue", "c2": obs_c2}
    return ListenerSystem(
        name="uncertainty",
        states=states,
        alphabet=alphabet,
        step=step,
        obs=obs,
        closed=frozenset({"c1", "c2"}),
    )


def build_summary() -> dict[str, object]:
    coarse = uncertainty_system("blue")
    fine = uncertainty_system("cyan")
    coarse_block = refine(coarse)
    fine_block = refine(fine)
    coarse_w = listener_uncertainty(coarse, "s", 2, coarse_block)
    fine_w = listener_uncertainty(fine, "s", 2, fine_block)
    toy_good = good_model()
    toy_bad = bad_model()
    qkb = qkb_concept_demo()
    return {
        "meta": {
            "generator": "listener_equivalence.py",
            "version": 1,
            "issue": 274,
            "pre_registration": "Listener_Equivalence_QLF.md",
            "listener_equivalence": (
                "s ~_B t iff same observation and all one-token successors remain equivalent"
            ),
            "W_micro": "number of first-completion paths",
            "W_B": "number of listener classes among completion endpoints",
        },
        "partition": {
            "coarse_blocks": [sorted(block) for block in blocks_of(coarse_block)],
            "fine_blocks": [sorted(block) for block in blocks_of(fine_block)],
            "coarse_right_congruence": is_right_congruence(coarse, coarse_block),
            "fine_right_congruence": is_right_congruence(fine, fine_block),
            "coarse_coarsest_blocks": [
                sorted(block) for block in coarsest_bisimulation(coarse)
            ],
            "fine_coarsest_blocks": [
                sorted(block) for block in coarsest_bisimulation(fine)
            ],
        },
        "uncertainty": {
            "coarse": coarse_w,
            "fine": fine_w,
        },
        "qkb": qkb,
        "self_model": {
            "good_square": square_commutes(toy_good),
            "bad_square": square_commutes(toy_bad),
            "good_levels_nondecreasing": levels_nondecreasing(toy_good),
            "bad_levels_nondecreasing": levels_nondecreasing(toy_bad),
            "good_self_loops": list(self_loop_states(toy_good)),
            "bad_self_loops": list(self_loop_states(toy_bad)),
            "bad_has_m0_self_loop": "m0" in self_loop_states(toy_bad),
        },
        "gates": {
            "L0_definition": "frozen",
            "L1_equivalence_right_congruence": "finite pass",
            "L2_coarsest_lossless": (
                "finite brute-force pass; two-body Lean theorem cited; N-body open"
            ),
            "L3_uncertainty_factorization": (
                "finite pass; uniform default made explicit and mu(c) parameterized; general theorem open"
            ),
            "L4_qkb_concept_quotient": "prototype only; storage unchanged",
            "L5_self_model_square": "toy pass; general theorem open",
            "L6_level_monotonicity": (
                "finite pass only; same-level self-loop counterexample retained; no event-loop theorem"
            ),
        },
    }


def self_test() -> None:
    coarse = uncertainty_system("blue")
    fine = uncertainty_system("cyan")
    cb = refine(coarse)
    fb = refine(fine)

    assert is_equivalence(cb, coarse.states), "refinement must be an equivalence"
    assert is_right_congruence(coarse, cb), "refinement must be a right congruence"
    assert is_equivalence(fb, fine.states), "refinement must be an equivalence"
    assert is_right_congruence(fine, fb), "refinement must be a right congruence"

    coarse_coarsest = coarsest_bisimulation(coarse)
    fine_coarsest = coarsest_bisimulation(fine)
    assert set(blocks_of(cb)) == set(coarse_coarsest), (
        "refinement is not the coarsest bisimulation"
    )
    assert set(blocks_of(fb)) == set(fine_coarsest), (
        "refinement is not the coarsest bisimulation"
    )

    cw = listener_uncertainty(coarse, "s", 2, cb)
    fw = listener_uncertainty(fine, "s", 2, fb)
    assert cw["W_micro"] == 4, f"expected 4 microscopic completions, got {cw['W_micro']}"
    assert cw["W_B"] == 1, f"expected one coarse listener class, got {cw['W_B']}"
    assert fw["W_B"] == 2, f"expected two fine listener classes, got {fw['W_B']}"
    assert cw["W_B"] <= cw["W_micro"], "listener classes exceeded microscopic paths"
    assert cw["measure"] == "uniform", "default measure must be labelled uniform"
    assert abs(sum(cw["weights"].values()) - 1.0) < 1e-12, "weights must sum to one"

    fw_weighted = listener_uncertainty(
        fine,
        "s",
        2,
        fb,
        {
            ("x", "x"): 1.0,
            ("x", "y"): 0.0,
            ("y", "x"): 1.0,
            ("y", "y"): 3.0,
        },
    )
    assert fw_weighted["measure"] == "explicit"
    assert fw_weighted["W_B"] == 2
    assert abs(fw_weighted["weights"]["c1"] - 0.2) < 1e-12
    assert abs(fw_weighted["weights"]["c2"] - 0.8) < 1e-12

    qkb = qkb_concept_demo()
    assert qkb["listener_ways"] <= qkb["ways"], "listener ways exceeded microscopic ways"

    good = good_model()
    bad = bad_model()
    assert square_commutes(good), "good model square should commute"
    assert not square_commutes(bad), "bad model square should fail"
    assert levels_nondecreasing(good), "good model levels should be nondecreasing"
    assert levels_nondecreasing(bad), (
        "the monotonicity check must not silently become a no-loop theorem"
    )
    assert "m0" not in self_loop_states(good)
    assert "m0" in self_loop_states(bad), "bad model must retain its m0 self-loop witness"

    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    print("\npartition:")
    print(f"  coarse blocks: {summary['partition']['coarse_blocks']}")  # type: ignore[index]
    print(f"  fine blocks:   {summary['partition']['fine_blocks']}")  # type: ignore[index]
    print("\nuncertainty:")
    print(f"  coarse: {summary['uncertainty']['coarse']}")  # type: ignore[index]
    print(f"  fine:   {summary['uncertainty']['fine']}")  # type: ignore[index]
    print("\nQKB concept:")
    print(f"  ways = {summary['qkb']['ways']}, listener_ways = {summary['qkb']['listener_ways']}")  # type: ignore[index]
    print("\nself-model square:")
    print(f"  good = {summary['self_model']['good_square']}, bad = {summary['self_model']['bad_square']}")  # type: ignore[index]


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
