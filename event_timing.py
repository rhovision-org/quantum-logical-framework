#!/usr/bin/env python3
"""Event timing — finite reference implementation for #280.

Frozen semantics are in ``Event_Timing_QLF.md``:

  * listening takes time: tau_listen > 0;
  * a ZFA closure event is atomic: tau_event = 0;
  * recurrence frequency f=1/T and event priority argmin d are distinct.

Run:

    python3 event_timing.py --self-test
    python3 event_timing.py --run
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

OUTPUT = Path("data/event_timing_census.json")


@dataclass(frozen=True)
class Candidate:
    name: str
    period: int
    distance: int
    eligible: bool = True


CANDIDATES = (
    Candidate("fast_recurrent", period=1, distance=5),
    Candidate("slow_near", period=10, distance=1),
    Candidate("percept", period=2, distance=2),
)

TRACE_CANDIDATE = Candidate("slow_trace", period=10, distance=3)


def frequency(candidate: Candidate) -> float:
    return 1.0 / max(1, candidate.period)


def next_trigger(
    candidates: Iterable[Candidate] = CANDIDATES,
) -> dict[str, object] | None:
    pool = [candidate for candidate in candidates if candidate.eligible]
    if not pool:
        return None
    winner = min(
        pool,
        key=lambda candidate: (candidate.distance, -frequency(candidate), candidate.name),
    )
    return {
        "name": winner.name,
        "period": winner.period,
        "frequency": frequency(winner),
        "distance": winner.distance,
    }


def highest_frequency(
    candidates: Iterable[Candidate] = CANDIDATES,
) -> dict[str, object] | None:
    pool = [candidate for candidate in candidates if candidate.eligible]
    if not pool:
        return None
    winner = max(pool, key=lambda candidate: (frequency(candidate), -candidate.distance, candidate.name))
    return {
        "name": winner.name,
        "period": winner.period,
        "frequency": frequency(winner),
        "distance": winner.distance,
    }


def listening_trace(candidate: Candidate, max_steps: int = 10) -> dict[str, object]:
    """Reduce distance by one per listening step; emit CLOSE at zero."""
    if candidate.distance > max_steps:
        raise ValueError("distance exceeds the listening horizon")
    trace = []
    distance = candidate.distance
    step = 0
    while True:
        trace.append(
            {
                "step": step,
                "distance": distance,
                "event": "CLOSE" if distance == 0 else "listening",
            }
        )
        if distance == 0:
            break
        distance -= 1
        step += 1
    return {
        "candidate": candidate.name,
        "tau_listen": candidate.distance,
        "tau_event": 0,
        "atomic": True,
        "trace": trace,
    }


def build_summary() -> dict[str, object]:
    priority = next_trigger(CANDIDATES)
    fastest = highest_frequency(CANDIDATES)
    trace = listening_trace(TRACE_CANDIDATE)
    return {
        "meta": {
            "generator": "event_timing.py",
            "version": 1,
            "issue": 280,
            "pre_registration": "Event_Timing_QLF.md",
            "rule": "listening takes time; closure does not",
        },
        "race": [
            {
                "name": candidate.name,
                "period": candidate.period,
                "frequency": frequency(candidate),
                "distance": candidate.distance,
                "eligible": candidate.eligible,
            }
            for candidate in CANDIDATES
        ],
        "priority_next": priority,
        "highest_frequency": fastest,
        "separation": {
            "priority": priority["name"] if priority else None,
            "fastest": fastest["name"] if fastest else None,
            "distinct": bool(priority and fastest and priority["name"] != fastest["name"]),
        },
        "trace": trace,
        "gates": {
            "ET0_definition": "frozen",
            "ET1_timing": "tau_listen>0; tau_event=0",
            "ET2_separation": "frequency and priority are distinct",
            "ET3_no_backward_causation": "event steps increase; cited",
            "ET4_dependencies": "#271, #272, #275, #277, #279",
        },
    }


def self_test() -> None:
    priority = next_trigger(CANDIDATES)
    fastest = highest_frequency(CANDIDATES)
    assert priority is not None and priority["name"] == "slow_near"
    assert fastest is not None and fastest["name"] == "fast_recurrent"
    assert priority["name"] != fastest["name"], "frequency and priority were conflated"

    fast = next(candidate for candidate in CANDIDATES if candidate.name == "fast_recurrent")
    slow = next(candidate for candidate in CANDIDATES if candidate.name == "slow_near")
    assert frequency(fast) > frequency(slow), "fast_recurrent should recur faster"
    assert slow.distance < fast.distance, "slow_near should be nearer to trigger"

    trace = listening_trace(TRACE_CANDIDATE)
    assert trace["tau_listen"] == 3, "listening should take three steps"
    assert trace["tau_event"] == 0, "the closure event must be atomic"
    assert trace["trace"][-1]["event"] == "CLOSE"
    assert trace["trace"][-1]["distance"] == 0
    assert all(
        trace["trace"][i]["step"] < trace["trace"][i + 1]["step"]
        for i in range(len(trace["trace"]) - 1)
    ), "event steps must increase"

    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    print("\nrace:")
    for row in summary["race"]:  # type: ignore[union-attr]
        print(
            f"  {row['name']}: T={row['period']} f={row['frequency']:.3f} "
            f"d={row['distance']} eligible={row['eligible']}"
        )
    print(f"\nnext trigger (min d): {summary['priority_next']}")  # type: ignore[index]
    print(f"highest frequency (max f): {summary['highest_frequency']}")  # type: ignore[index]
    print(f"distinct: {summary['separation']['distinct']}")  # type: ignore[index]
    print("\ntrace:")
    for row in summary["trace"]["trace"]:  # type: ignore[index]
        print(f"  step {row['step']}: d={row['distance']} {row['event']}")
    print(f"tau_listen={summary['trace']['tau_listen']}, tau_event={summary['trace']['tau_event']}")  # type: ignore[index]


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
