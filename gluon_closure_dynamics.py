#!/usr/bin/env python3
"""Gluon closure dynamics first slice (#286).

GL2 is made concrete as **vertex gluing**:

    choose two non-collinear gluon labels q, r in a colour state;
    replace them by the third vertex leg p = -(q + r).

The move is defined from the F3^2 colour algebra and `symp(q, r) != 0`; it never
consults the distance to a singlet.  `d_G` is then the shortest number of
vertex-gluing moves to total colour zero.

This is a finite toy, not full QCD: no quark emission/absorption, no kinematics,
no coupling, no string tension, and no physical spatial distance.  GL7/GL8 stay
open.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, deque
from itertools import combinations, combinations_with_replacement
from pathlib import Path
from typing import Sequence

OUTPUT = Path("data/gluon_closure_dynamics_census.json")
MAX_STATE_SIZE = 4
MAX_SEARCH_SIZE = 5

Colour = tuple[int, int]
State = tuple[Colour, ...]

LABELS: tuple[Colour, ...] = tuple(
    (a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)
)


def add(u: Colour, v: Colour) -> Colour:
    return ((u[0] + v[0]) % 3, (u[1] + v[1]) % 3)


def neg(u: Colour) -> Colour:
    return ((-u[0]) % 3, (-u[1]) % 3)


def symp(u: Colour, v: Colour) -> int:
    return (u[0] * v[1] - u[1] * v[0]) % 3


def total(state: State) -> Colour:
    x = y = 0
    for a, b in state:
        x = (x + a) % 3
        y = (y + b) % 3
    return (x, y)


def is_singlet(state: State) -> bool:
    return total(state) == (0, 0)


def create_moves(state: State) -> set[State]:
    """Vertex creation: add the third leg p = -(q + r) for non-collinear q, r.

    Defined independently of `d_G`.
    """
    out: set[State] = set()
    for i, j in combinations(range(len(state)), 2):
        q, r = state[i], state[j]
        if symp(q, r) == 0:
            continue
        p = neg(add(q, r))
        out.add(tuple(sorted(state + (p,))))
    return out


def glue_moves(state: State) -> set[State]:
    """Vertex gluing: replace q, r by p = -(q + r) for non-collinear q, r.

    The reverse channel of :func:`create_moves`; both are defined independently
    of `d_G`.
    """
    out: set[State] = set()
    for i, j in combinations(range(len(state)), 2):
        q, r = state[i], state[j]
        if symp(q, r) == 0:
            continue
        p = neg(add(q, r))
        rest = list(state)
        rest.pop(j)
        rest.pop(i)
        rest.append(p)
        out.add(tuple(sorted(rest)))
    return out


def all_moves(state: State) -> set[State]:
    return create_moves(state) | glue_moves(state)


def distance_to_singlet(state: State, max_size: int = MAX_SEARCH_SIZE) -> int | None:
    """Shortest path to a colour singlet using creation + gluing, or None."""
    if is_singlet(state):
        return 0
    queue = deque([(state, 0)])
    seen = {state}
    while queue:
        current, depth = queue.popleft()
        if len(current) >= max_size:
            continue
        for nxt in all_moves(current):
            if nxt in seen:
                continue
            if is_singlet(nxt):
                return depth + 1
            seen.add(nxt)
            queue.append((nxt, depth + 1))
    return None


def enumerate_states(max_size: int = MAX_STATE_SIZE) -> list[State]:
    states: list[State] = []
    for n in range(1, max_size + 1):
        states.extend(combinations_with_replacement(LABELS, n))
    return states


def binding_period(periods: Sequence[int]) -> int:
    if not periods:
        raise ValueError("at least one period is required")
    if any(period <= 0 for period in periods):
        raise ValueError("periods must be positive")
    return min(periods)


def binding_frequency(periods: Sequence[int]) -> float:
    return 1.0 / binding_period(periods)


def census(max_size: int = MAX_STATE_SIZE) -> dict[str, object]:
    states = enumerate_states(max_size)
    distances = {state: distance_to_singlet(state) for state in states}
    classes: dict[str, Counter[str]] = {"create": Counter(), "glue": Counter()}
    first_singlet: dict[str, Counter[str]] = {"create": Counter(), "glue": Counter()}
    examples: dict[str, dict[str, object]] = {"create": {}, "glue": {}}
    for state in states:
        d = distances[state]
        if d is None:
            continue
        for kind, moves in (("create", create_moves(state)), ("glue", glue_moves(state))):
            for nxt in moves:
                if is_singlet(nxt):
                    d_next = 0
                elif nxt in distances:
                    d_next = distances[nxt]
                else:
                    d_next = distance_to_singlet(nxt)
                if d_next is None:
                    cls = "blocked"
                elif d_next < d:
                    cls = "distance_reducing"
                elif d_next == d:
                    cls = "distance_neutral"
                else:
                    cls = "distance_increasing"
                classes[kind][cls] += 1
                if is_singlet(nxt):
                    first_singlet[kind][cls] += 1
                examples[kind].setdefault(
                    cls,
                    {
                        "before": state,
                        "after": nxt,
                        "d_before": d,
                        "d_after": d_next,
                    },
                )
    return {
        "max_state_size": max_size,
        "max_search_size": MAX_SEARCH_SIZE,
        "states": len(states),
        "with_distance": sum(1 for d in distances.values() if d is not None),
        "without_distance": sum(1 for d in distances.values() if d is None),
        "distance_counts": dict(Counter(str(d) for d in distances.values())),
        "move_classes": {kind: dict(counter) for kind, counter in classes.items()},
        "first_singlet_moves": {
            kind: dict(counter) for kind, counter in first_singlet.items()
        },
        "examples": examples,
        "note": (
            "Two-channel vertex toy: creation adds p = -(q+r); gluing replaces "
            "q, r by p. Both are defined from symp != 0 and p + q + r = 0, "
            "independently of d_G. Not full QCD."
        ),
    }


def worked_examples() -> dict[str, object]:
    open_pair = ((1, 0), (0, 1))
    gluing_state = ((0, 1), (1, 0), (1, 1))
    return {
        "open_pair": {
            "state": open_pair,
            "d": distance_to_singlet(open_pair),
            "create_moves": sorted(create_moves(open_pair)),
            "glue_moves": sorted(glue_moves(open_pair)),
        },
        "gluing_to_singlet": {
            "state": gluing_state,
            "d": distance_to_singlet(gluing_state),
            "create_moves": sorted(create_moves(gluing_state)),
            "glue_moves": sorted(glue_moves(gluing_state)),
        },
        "two_gluon_singlet": {
            "state": ((1, 0), (2, 0)),
            "d": distance_to_singlet(((1, 0), (2, 0))),
            "create_moves": sorted(create_moves(((1, 0), (2, 0)))),
            "glue_moves": sorted(glue_moves(((1, 0), (2, 0)))),
        },
        "harmonic": {
            "periods": [5, 3],
            "T_bind": binding_period([5, 3]),
            "f_bind": binding_frequency([5, 3]),
            "f_parts": [1 / 5, 1 / 3],
        },
    }


def build_summary() -> dict[str, object]:
    return {
        "meta": {
            "generator": "gluon_closure_dynamics.py",
            "version": 1,
            "issue": 286,
            "pre_registration": "Gluon_Closure_Dynamics.md",
        },
        "census": census(),
        "worked": worked_examples(),
        "gates": {
            "GL0_definition": "finite; d_G, T, f, tau_event separated",
            "GL1_confinement": "cited charged_not_closed / singlet_closure",
            "GL2_gluon_move": "vertex creation + gluing: p + q + r = 0, symp(q,r) != 0",
            "GL3_distance_effect": "finite census; both channels reduce, neutral, increase",
            "GL4_first_closure": "first singlet is d=0; commit atomic",
            "GL5_harmonic": "T_bind = min(T_parts); f_bind >= each f_part",
            "GL6_atomic": "tau_event = 0, cited #281",
            "GL7_spatial": "open bridge; no physical distance claim",
            "GL8_string_tension": "open; not claimed",
        },
    }


def self_test() -> None:
    assert len(LABELS) == 8
    assert symp((1, 0), (0, 1)) == 1
    assert symp((1, 0), (2, 0)) == 0
    assert total(((1, 0), (0, 1))) == (1, 1)
    assert is_singlet(((1, 0), (2, 0)))
    assert glue_moves(((1, 0), (0, 1))) == {((2, 2),)}
    assert create_moves(((1, 0), (0, 1))) == {((0, 1), (1, 0), (2, 2))}
    assert distance_to_singlet(((1, 0), (0, 1))) == 1
    assert distance_to_singlet(((0, 1), (1, 0), (1, 1))) == 1
    assert distance_to_singlet(((1, 0), (2, 0))) == 0
    result = census()
    for kind in ("create", "glue"):
        assert result["move_classes"][kind].get("distance_reducing", 0) > 0
        assert result["move_classes"][kind].get("distance_neutral", 0) > 0
        assert result["move_classes"][kind].get("distance_increasing", 0) > 0
        assert result["first_singlet_moves"][kind].get("distance_reducing", 0) > 0
    assert binding_period([5, 3]) == 3
    assert binding_frequency([5, 3]) > 1 / 5
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    result = summary["census"]  # type: ignore[index]
    print("\ncensus:")
    print(
        f"  states={result['states']} with_distance={result['with_distance']} "
        f"without_distance={result['without_distance']}"
    )
    print(f"  move_classes={result['move_classes']}")
    print(f"  first_singlet_moves={result['first_singlet_moves']}")
    print("\nworked:")
    for name, example in summary["worked"].items():  # type: ignore[union-attr]
        print(f"  {name}: {example}")


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
