#!/usr/bin/env python3
"""Finite toy model for the strange-loop / Markov-blanket bridge question.

This is a model of underdetermination, not evidence for QLF or for a physical
Born/Malus rule. It asks whether a pure MO2 closure walk reproduces the
three-polarizer 1/8, or whether the operational re-preparation/probability map
is doing the work.

The answer is deliberately negative:

* a pure MO2 meet walk blocks at the second polarizer (inf(az, ax) = bot);
* a re-preparation walk gives 1/8 only when the branch weights are assumed
  uniform (or supplied by the operational Malus map);
* the same lattice pass/block pattern with different weights gives a different
  transmission;
* a blanket that integrates only the first two stages gives a different result.

Run:
    python3 tools/strange_loop_observer.py
    python3 tools/strange_loop_observer.py --json verification/strange-loop/strange_loop_observer.json
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from mo2_finite_audit import E, inf  # noqa: E402


@dataclass(frozen=True)
class Screen:
    """One polarizer stage in the toy apparatus."""

    label: str
    element: str
    malus_weight: float


@dataclass(frozen=True)
class Observer:
    """A finite Markov blanket with a lattice state."""

    blanket: frozenset[str]
    state: str = "top"

    def can_integrate(self, screen: Screen) -> bool:
        return screen.element in self.blanket


SCREENS = (
    Screen("0 deg", "az", 0.5),                 # unpolarized input -> first polarizer
    Screen("45 deg", "ax", math.cos(math.radians(45)) ** 2),
    Screen("90 deg", "azp", math.cos(math.radians(45)) ** 2),
)
ALL_ELEMENTS = frozenset(E)


def _result(transmission: float, passed: int, **extra: object) -> dict:
    out = {
        "transmission": round(float(transmission), 12),
        "passed_stages": passed,
    }
    out.update(extra)
    return out


def meet_walk(observer: Observer, screens: tuple[Screen, ...] = SCREENS) -> dict:
    """Pure lattice meet: state <- inf(state, screen). No re-preparation."""
    state = observer.state
    passed = 0
    for i, screen in enumerate(screens, start=1):
        if not observer.can_integrate(screen):
            return _result(0.0, passed, unintegrated_at=i, reason="stage outside blanket")
        nxt = inf(state, screen.element)
        if nxt == "bot":
            return _result(
                0.0,
                passed,
                blocked_at=i,
                state_before=state,
                screen_element=screen.element,
                reason=f"inf({state}, {screen.element}) = bot",
            )
        state = nxt
        passed += 1
    return _result(1.0, passed, final_state=state, reason="all stages pass the lattice meet")


def reprepare_walk(
    observer: Observer,
    screens: tuple[Screen, ...] = SCREENS,
    weights: tuple[float, ...] | None = None,
) -> dict:
    """Operational re-preparation: each screen resets the state and multiplies a weight.

    This is the extra assumption the pure lattice does not supply. With no weights,
    each screen's Malus weight is used.
    """
    if weights is None:
        weights = tuple(s.malus_weight for s in screens)
    if len(weights) != len(screens):
        raise ValueError("weights must match screens")
    weight = 1.0
    passed = 0
    state = observer.state
    for i, (screen, w) in enumerate(zip(screens, weights), start=1):
        if not observer.can_integrate(screen):
            return _result(weight, passed, unintegrated_at=i, reason="stage outside blanket")
        if not 0.0 <= w <= 1.0:
            raise ValueError("weights must lie in [0, 1]")
        weight *= w
        state = screen.element
        passed += 1
    return _result(weight, passed, final_state=state, reason="operational re-preparation")


def self_reference_check(observer: Observer, screens: tuple[Screen, ...] = SCREENS) -> dict:
    """Apply the final record as its own screen; the toy loop is idempotent."""
    run = reprepare_walk(observer, screens)
    final_state = run.get("final_state")
    if final_state is None:
        return {"fixed_point": False, "reason": "no final state"}
    returned = inf(final_state, final_state)
    return {
        "fixed_point": returned == final_state,
        "final_state": final_state,
        "returned_state": returned,
        "reason": "a lattice state used as its own screen returns itself; this is a toy fixed point, not a physical bridge",
    }


def run_model() -> dict:
    all_blanket = Observer(ALL_ELEMENTS)
    first_two = Observer(frozenset({"az", "ax"}))

    malus = reprepare_walk(all_blanket)
    meet = meet_walk(all_blanket)
    uniform = reprepare_walk(all_blanket, weights=(0.5, 0.5, 0.5))
    biased = reprepare_walk(all_blanket, weights=(0.6, 0.6, 0.6))
    truncated = reprepare_walk(first_two, weights=(0.5, 0.5, 0.5))
    self_check = self_reference_check(all_blanket)

    outputs = {
        "operational_malus": malus["transmission"],
        "pure_meet": meet["transmission"],
        "reprepare_uniform": uniform["transmission"],
        "reprepare_biased_0_6": biased["transmission"],
        "blanket_first_two_stages": truncated["transmission"],
    }
    distinct = sorted({round(v, 12) for v in outputs.values()})
    return {
        "model": "finite MO2 / Markov-blanket toy",
        "scope": "underdetermination demonstration only; not QLF evidence, not a detector model, not a physical probability derivation",
        "angles_deg": [0, 45, 90],
        "screen_elements": [s.element for s in SCREENS],
        "malus_weights": [round(s.malus_weight, 12) for s in SCREENS],
        "outputs": outputs,
        "details": {
            "operational_malus": malus,
            "pure_meet": meet,
            "reprepare_uniform": uniform,
            "reprepare_biased_0_6": biased,
            "blanket_first_two_stages": truncated,
            "self_reference": self_check,
        },
        "distinct_transmissions": distinct,
        "underdetermined": len(distinct) > 1,
        "conclusion": (
            "The pure MO2 meet walk gives 0, not 1/8: inf(az, ax) = bot. "
            "A re-preparation walk gives 1/8 only with uniform or Malus-supplied weights; "
            "the same lattice pass/block pattern with different weights gives a different transmission. "
            "The lattice alone therefore does not select the optical law; the operational map is the missing premise."
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=None, help="write the result JSON to this path")
    args = parser.parse_args(argv)
    result = run_model()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text)
        print(f"wrote {args.json}")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
