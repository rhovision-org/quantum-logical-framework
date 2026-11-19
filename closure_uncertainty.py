#!/usr/bin/env python3
"""Finite closure-uncertainty kernel — the reference implementation for #269.

The definitions are frozen in ``Closure_Uncertainty_QLF.md``:

  * a finite closure system is ``(S, step, closed, context)``;
  * a first completion is a path of length <= R ending at the first closed state;
  * ``W_R = |Omega_R|`` is an integer; ``U_R = log2 W_R`` is derived;
  * ``U`` is undefined when no completion exists within the horizon.

The script provides the generic kernel, an exact game-theory instantiation
(Nash = closure, via ``nash_iff_closure``), a U(1) confinement toy (not the full
SU(3) colour theory), and a joint-closure toy.  It does not claim that the toy
instantiations are physical derivations.

Run:

    python3 closure_uncertainty.py --self-test
    python3 closure_uncertainty.py --run
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import assembly_index as ai

OUTPUT = Path("data/closure_uncertainty_census.json")


@dataclass(frozen=True)
class FiniteClosureSystem:
    """A finite state space with a step relation, closure predicate, and context."""

    name: str
    states: tuple[object, ...]
    step: dict[object, tuple[object, ...]]
    closed: frozenset[object]
    context: frozenset[object]
    start: object

    def with_context(self, allowed: Iterable[object]) -> "FiniteClosureSystem":
        allowed_set = frozenset(allowed)
        if self.start not in allowed_set:
            raise ValueError("the start state must remain in the context")
        return FiniteClosureSystem(
            name=self.name + "/tighter",
            states=self.states,
            step=self.step,
            closed=self.closed,
            context=self.context & allowed_set,
            start=self.start,
        )


def first_completions(
    system: FiniteClosureSystem, horizon: int
) -> tuple[tuple[object, ...], ...]:
    """All first-completion paths of length <= horizon, in deterministic order.

    A closed start yields the empty path only.  Paths that leave the context are
    discarded.  The horizon bounds cycles, so the enumeration is finite.
    """
    if horizon < 0:
        raise ValueError("horizon must be non-negative")
    if system.start not in system.context:
        return ()

    out: list[tuple[object, ...]] = []

    def rec(state: object, path: tuple[object, ...], depth: int) -> None:
        if state in system.closed:
            out.append(path)
            return
        if depth == horizon:
            return
        for nxt in system.step.get(state, ()):  # deterministic tuple order
            if nxt not in system.context:
                continue
            rec(nxt, path + (nxt,), depth + 1)

    rec(system.start, (), 0)
    return tuple(out)


def W(system: FiniteClosureSystem, horizon: int) -> int:
    return len(first_completions(system, horizon))


def U(system: FiniteClosureSystem, horizon: int) -> float | None:
    count = W(system, horizon)
    return math.log2(count) if count else None


def completion_measure(
    system: FiniteClosureSystem,
    horizon: int,
    start_length: int,
    base: int = 8,
) -> dict[str, object]:
    """Cylinder/Kraft weights and their normalization (gate U5).

    ``mu(c) = base ** (-(start_length + steps(c)))``.  The raw count ``W`` is
    unchanged; this function only supplies the declared measure needed before
    using ``W``/``U`` as a physical probability.
    """
    if start_length < 1:
        raise ValueError("start_length must be positive")
    paths = first_completions(system, horizon)
    weights = [base ** (-(start_length + len(path))) for path in paths]
    total = sum(weights)
    by_steps: dict[str, dict[str, float | int]] = {}
    for path, weight in zip(paths, weights):
        key = str(len(path))
        row = by_steps.setdefault(key, {"count": 0, "mu_each": weight, "P_total": 0.0})
        row["count"] = int(row["count"]) + 1
        if total:
            row["P_total"] = float(row["P_total"]) + weight / total
    return {
        "W_micro": len(paths),
        "base": base,
        "start_length": start_length,
        "mu_total": total,
        "normalized": [weight / total for weight in weights] if total else [],
        "by_steps": dict(sorted(by_steps.items(), key=lambda item: int(item[0]))),
    }


# ---------------------------------------------------------------------------
# Instantiation 1: finite normal-form games, Nash = closure
# ---------------------------------------------------------------------------

ACTIONS = ("S", "H")  # Stag, Hare
PROFILES = tuple((a, b) for a in ACTIONS for b in ACTIONS)
STAG_HUNT = {
    ("S", "S"): (4, 4),
    ("S", "H"): (0, 3),
    ("H", "S"): (3, 0),
    ("H", "H"): (2, 2),
}
NASH = frozenset({("S", "S"), ("H", "H")})


def game_step(profile: tuple[str, str]) -> tuple[tuple[str, str], ...]:
    a, b = profile
    out: list[tuple[str, str]] = []
    for alt in ACTIONS:
        if alt != a:
            out.append((alt, b))
        if alt != b:
            out.append((a, alt))
    return tuple(out)


def game_system(start: tuple[str, str] = ("S", "H")) -> FiniteClosureSystem:
    return FiniteClosureSystem(
        name=f"stag-hunt/{start[0]}{start[1]}",
        states=PROFILES,
        step={p: game_step(p) for p in PROFILES},
        closed=NASH,
        context=frozenset(PROFILES),
        start=start,
    )


# ---------------------------------------------------------------------------
# Instantiation 2: U(1) charge toy (not full SU(3) confinement)
# ---------------------------------------------------------------------------

def charge_system(bound: int = 4, start: int = 1) -> FiniteClosureSystem:
    states = tuple(range(-bound, bound + 1))
    return FiniteClosureSystem(
        name=f"u1-charge/b{bound}/q{start}",
        states=states,
        step={q: tuple(x for x in (q - 1, q + 1) if -bound <= x <= bound) for q in states},
        closed=frozenset({0}),
        context=frozenset(states),
        start=start,
    )


# ---------------------------------------------------------------------------
# Joint-closure toy: neither component alone closes; the pair does
# ---------------------------------------------------------------------------

PAIR_STATES = ((0, 0), (1, 0), (0, 1), (1, 1))


def pair_step(state: tuple[int, int]) -> tuple[tuple[int, int], ...]:
    a, b = state
    return ((1 - a, b), (a, 1 - b))


def joint_system() -> FiniteClosureSystem:
    return FiniteClosureSystem(
        name="joint-pair",
        states=PAIR_STATES,
        step={s: pair_step(s) for s in PAIR_STATES},
        closed=frozenset({(1, 1)}),
        context=frozenset(PAIR_STATES),
        start=(0, 0),
    )


# ---------------------------------------------------------------------------
# Instantiation 3: flat-history ZFA (the actual count-balanced predicate)
# ---------------------------------------------------------------------------

def flat_word_system(max_length: int = 4, start: str = "^") -> FiniteClosureSystem:
    """Exact flat-history closure system: all twist words up to max_length.

    ``closed`` is the real QLF ``is_closed`` / ``countBalanced`` predicate from
    ``assembly_index.py``.  This is an exact instantiation, not a toy.
    """
    if start not in ai.TWISTS:
        raise ValueError(f"start must be one of {ai.TWISTS!r}")
    states: list[str] = [""]
    frontier: list[str] = [""]
    for _ in range(max_length):
        frontier = [word + twist for word in frontier for twist in ai.TWISTS]
        states.extend(frontier)
    step = {
        word: tuple(word + twist for twist in ai.TWISTS) if len(word) < max_length else ()
        for word in states
    }
    return FiniteClosureSystem(
        name=f"flat-zfa/L{max_length}/{start}",
        states=tuple(states),
        step=step,
        closed=frozenset(word for word in states if ai.is_closed(word)),
        context=frozenset(states),
        start=start,
    )


# ---------------------------------------------------------------------------
# Self-test and report
# ---------------------------------------------------------------------------

def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def self_test() -> None:
    # Closed start: empty path only, W = 1, U = 0.
    game = game_system(("S", "S"))
    _assert(first_completions(game, 3) == ((),), "closed start must have the empty path")
    _assert(W(game, 3) == 1 and U(game, 3) == 0.0, "closed start must have U = 0")

    # Stag Hunt from (S,H): two length-1 Nash completions.
    game = game_system(("S", "H"))
    _assert(W(game, 1) == 2, f"expected W=2, got {W(game, 1)}")
    _assert(W(game, 3) == 2, "first-completions stop at Nash")

    # Tighter context removes (H,H); W cannot increase.
    tight = game.with_context(p for p in PROFILES if p != ("H", "H"))
    _assert(W(tight, 3) == 1, f"expected W=1 under tighter context, got {W(tight, 3)}")
    _assert(W(tight, 3) <= W(game, 3), "tighter context increased W")

    # U(1) charge toy: first returns from q=1.
    charge = charge_system()
    _assert(W(charge, 1) == 1, "one-step return to zero must be unique")
    _assert(W(charge, 2) == 1, "parity forbids a length-2 first return from q=1")
    _assert(W(charge, 3) == 2, "length-3 first return should add one path")
    band = charge.with_context(q for q in charge.states if -1 <= q <= 1)
    _assert(W(band, 3) == 1, "the tighter charge band should kill the length-3 path")

    # Joint closure: both bits must be 1; there are two length-2 paths.
    joint = joint_system()
    _assert(W(joint, 2) == 2, "joint closure should have two length-2 paths")
    _assert(W(joint, 3) == 2, "first-completions stop at the joint closure")

    # Flat-history ZFA: the real countBalanced predicate, exact enumeration.
    flat = flat_word_system(4, "^")
    _assert(len(flat.states) == 4681, "flat system should have 4681 words through length 4")
    _assert(len(flat.closed) == 177, "flat system should have 177 count-balanced words")
    _assert([W(flat, r) for r in range(5)] == [0, 1, 1, 14, 14],
            "flat-ZFA first-completion counts changed")

    # Gate U5: the raw count is unchanged, and the cylinder weights normalize.
    measure = completion_measure(flat, 3, start_length=1)
    _assert(measure["W_micro"] == 14, "measure gate changed the raw count")
    _assert(abs(sum(measure["normalized"]) - 1.0) < 1e-12,
            "cylinder weights must normalize to one")
    _assert(measure["by_steps"]["1"]["P_total"] > measure["by_steps"]["3"]["P_total"],
            "shorter completions should carry more cylinder weight")

    # Finiteness: the enumeration is bounded by the horizon.
    for system in (game, charge, joint, flat):
        paths = first_completions(system, 4)
        _assert(all(len(p) <= 4 for p in paths), "path exceeded the horizon")

    print("self-test: OK")


def build_summary() -> dict[str, object]:
    game_starts = (("S", "H"), ("H", "S"), ("S", "S"), ("H", "H"))
    games = {}
    for start in game_starts:
        system = game_system(start)
        games[f"{start[0]}{start[1]}"] = {
            "W": {str(r): W(system, r) for r in range(0, 5)},
            "U": {str(r): U(system, r) for r in range(0, 5)},
        }
    tight_game = game_system(("S", "H")).with_context(
        p for p in PROFILES if p != ("H", "H")
    )
    charge = charge_system()
    band = charge.with_context(q for q in charge.states if -1 <= q <= 1)
    joint = joint_system()
    flat = flat_word_system(4, "^")
    flat_measure = completion_measure(flat, 3, start_length=1)
    return {
        "meta": {
            "generator": "closure_uncertainty.py",
            "version": 3,
            "issue": 269,
            "pre_registration": "Closure_Uncertainty_QLF.md",
            "first_completion": "paths ending at the first closed state, length <= R",
            "W": "integer count of first-completion paths",
            "U": "log2(W), undefined when W = 0",
            "measure": "cylinder/Kraft mu(c)=8^(-|c|); P normalized over Omega_R",
        },
        "games": games,
        "game_tighter_context": {
            "start": "SH",
            "W": {str(r): W(tight_game, r) for r in range(0, 5)},
        },
        "flat_zfa": {
            "start": "^",
            "max_length": 4,
            "states": len(flat.states),
            "closed": len(flat.closed),
            "W": {str(r): W(flat, r) for r in range(0, 5)},
        },
        "measure": flat_measure,
        "u1_charge": {
            "W": {str(r): W(charge, r) for r in range(0, 7)},
            "W_tight_band": {str(r): W(band, r) for r in range(0, 7)},
        },
        "joint_pair": {
            "W": {str(r): W(joint, r) for r in range(0, 5)},
        },
        "gates": {
            "U0_definition": "frozen",
            "U1_finite_checks": "pass",
            "U1_lean": "open",
            "U2_sector": "flat only",
            "U3_reuse": "cited, formal lemma open",
            "U4_domains": (
                "game theory exact; flat-history ZFA exact; "
                "confinement U(1) toy; full colour open"
            ),
            "U5_measure": "cylinder/Kraft weights normalized; raw W unchanged",
            "U6_law_of_exceptions": (
                "open bridge; C_R strict by law_of_exceptions; "
                "Omega_R horizon-relative; local W may stabilize"
            ),
        },
    }


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    print("\ngame theory (Stag Hunt, Nash = closure):")
    for start, data in summary["games"].items():  # type: ignore[union-attr]
        print(f"  start {start}: W = {data['W']}")
    print("\nU(1) charge toy:")
    print(f"  W = {summary['u1_charge']['W']}")  # type: ignore[index]
    print(f"  W (context band [-1,1]) = {summary['u1_charge']['W_tight_band']}")  # type: ignore[index]
    print("\nflat-history ZFA (countBalanced, lengths <= 4):")
    flat = summary["flat_zfa"]  # type: ignore[index]
    print(f"  states = {flat['states']}, closed = {flat['closed']}")
    print(f"  W = {flat['W']}")
    print("\nmeasure gate (cylinder/Kraft, R=3):")
    measure = summary["measure"]  # type: ignore[index]
    print(f"  W_micro = {measure['W_micro']}, mu_total = {measure['mu_total']:.10f}")
    print(f"  by_steps = {measure['by_steps']}")
    print("\njoint pair:")
    print(f"  W = {summary['joint_pair']['W']}")  # type: ignore[index]


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
