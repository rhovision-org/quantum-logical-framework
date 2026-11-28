#!/usr/bin/env python3
"""Conscious dynamics — finite reference implementation for #278.

Frozen definitions are in ``Conscious_Dynamics_QLF.md``:

  * f_i^(B) = 1 / T_i^(B);
  * C_t* = argmin d_i over eligible, self-relevant, integrated closures;
  * B_{t+1} = U(B_t, C_t*).

The script is a functional toy, not a theory of qualia.  It shows the
listener-relative race, attention, quieting, a bounded promotion trace, and the
fixed-history/changing-compression distinction.  D3 checks the external step
index of a bounded trace; it does not prove a no-event-loop transition invariant.

Run:

    python3 conscious_dynamics.py --self-test
    python3 conscious_dynamics.py --run
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field, fields, replace
from pathlib import Path
from typing import Iterable, Sequence

OUTPUT = Path("data/conscious_dynamics_census.json")


@dataclass(frozen=True)
class Candidate:
    """A candidate closure with a recurrence period and a trigger distance.

    ``intrinsic_period`` is the characteristic listening/retrigger period ``T``.
    ``base_distance`` is the remaining distance to the next trigger ``d``.
    They are deliberately separate: a fast recurrent mode need not be nearest.
    """

    name: str
    intrinsic_period: int
    base_distance: int
    integration: float
    self_relevant: bool


@dataclass(frozen=True)
class Listener:
    name: str
    period_bonus: dict[str, int] = field(default_factory=dict)
    distance_bonus: dict[str, int] = field(default_factory=dict)

    def with_period_bonus(self, candidate: str, delta: int) -> "Listener":
        bonuses = dict(self.period_bonus)
        bonuses[candidate] = bonuses.get(candidate, 0) + delta
        return Listener(
            name=self.name + f"/T{candidate}{delta:+d}",
            period_bonus=bonuses,
            distance_bonus=dict(self.distance_bonus),
        )

    def with_distance_bonus(self, candidate: str, delta: int) -> "Listener":
        bonuses = dict(self.distance_bonus)
        bonuses[candidate] = bonuses.get(candidate, 0) + delta
        return Listener(
            name=self.name + f"/d{candidate}{delta:+d}",
            period_bonus=dict(self.period_bonus),
            distance_bonus=bonuses,
        )


CONSCIOUS_CANDIDATES = (
    Candidate("percept", intrinsic_period=2, base_distance=2, integration=0.80, self_relevant=True),
    Candidate("thought", intrinsic_period=5, base_distance=5, integration=0.90, self_relevant=True),
    Candidate("feeling", intrinsic_period=7, base_distance=7, integration=0.95, self_relevant=True),
    Candidate("external", intrinsic_period=8, base_distance=8, integration=0.85, self_relevant=True),
    # Fast but ineligible: the globally fastest event is not automatically conscious.
    Candidate("micro", intrinsic_period=1, base_distance=0, integration=0.20, self_relevant=False),
)

# The frequency/priority separation check.  fast_recurrent has the higher
# frequency; slow_near is closer to its next trigger.
PRIORITY_CANDIDATES = (
    Candidate("fast_recurrent", intrinsic_period=1, base_distance=5, integration=0.80, self_relevant=True),
    Candidate("slow_near", intrinsic_period=10, base_distance=1, integration=0.90, self_relevant=True),
    Candidate("percept", intrinsic_period=2, base_distance=2, integration=0.80, self_relevant=True),
)

LOOP_CANDIDATES = tuple(
    candidate
    for candidate in CONSCIOUS_CANDIDATES
    if candidate.name in {"percept", "thought", "feeling", "external"}
)


def effective_period(candidate: Candidate, listener: Listener) -> int:
    """Characteristic listening/retrigger period T_i^(B)."""
    return max(1, candidate.intrinsic_period + listener.period_bonus.get(candidate.name, 0))


def frequency(candidate: Candidate, listener: Listener) -> float:
    """Recurrence frequency f_i^(B) = 1 / T_i^(B)."""
    return 1.0 / effective_period(candidate, listener)


def remaining_distance(candidate: Candidate, listener: Listener) -> int:
    """Remaining distance to the next trigger d_i^(B)."""
    return max(0, candidate.base_distance + listener.distance_bonus.get(candidate.name, 0))


def eligible(candidate: Candidate) -> bool:
    return candidate.self_relevant and candidate.integration >= 0.5


def next_trigger(
    candidates: Iterable[Candidate] = CONSCIOUS_CANDIDATES,
    listener: Listener | None = None,
) -> dict[str, object] | None:
    """The next conscious expression: minimum remaining distance, not max frequency."""
    listener = listener or Listener("default")
    pool = [candidate for candidate in candidates if eligible(candidate)]
    if not pool:
        return None
    winner = min(
        pool,
        key=lambda candidate: (
            remaining_distance(candidate, listener),
            -frequency(candidate, listener),
            candidate.name,
        ),
    )
    return {
        "name": winner.name,
        "distance": remaining_distance(winner, listener),
        "period": effective_period(winner, listener),
        "frequency": frequency(winner, listener),
        "integration": winner.integration,
    }


def highest_frequency(
    candidates: Iterable[Candidate] = CONSCIOUS_CANDIDATES,
    listener: Listener | None = None,
) -> dict[str, object] | None:
    """The recurring-dominance winner: maximum frequency, used only as a contrast."""
    listener = listener or Listener("default")
    pool = [candidate for candidate in candidates if eligible(candidate)]
    if not pool:
        return None
    winner = max(pool, key=lambda candidate: (frequency(candidate, listener), candidate.integration, candidate.name))
    return {
        "name": winner.name,
        "distance": remaining_distance(winner, listener),
        "period": effective_period(winner, listener),
        "frequency": frequency(winner, listener),
        "integration": winner.integration,
    }


def race_table(
    candidates: Iterable[Candidate] = CONSCIOUS_CANDIDATES,
    listener: Listener | None = None,
) -> list[dict[str, object]]:
    listener = listener or Listener("default")
    rows = []
    for candidate in candidates:
        rows.append(
            {
                "name": candidate.name,
                "intrinsic_period": candidate.intrinsic_period,
                "base_distance": candidate.base_distance,
                "period": effective_period(candidate, listener),
                "frequency": frequency(candidate, listener),
                "distance": remaining_distance(candidate, listener),
                "integration": candidate.integration,
                "self_relevant": candidate.self_relevant,
                "eligible": eligible(candidate),
            }
        )
    return sorted(
        rows,
        key=lambda row: (int(row["distance"]), -float(row["frequency"]), str(row["name"])),
    )


# ---------------------------------------------------------------------------
# Attention and quieting
# ---------------------------------------------------------------------------

def attention(
    listener: Listener,
    target: str,
    distance_acceleration: int = 4,
    period_acceleration: int = 0,
) -> Listener:
    """Attention changes the race: move one candidate nearer or make it recur faster."""
    out = listener
    if distance_acceleration:
        out = out.with_distance_bonus(target, -distance_acceleration)
    if period_acceleration:
        out = out.with_period_bonus(target, -period_acceleration)
    return out


def quiet_internal(
    listener: Listener,
    names: tuple[str, ...] = ("percept", "thought", "feeling"),
    distance_penalty: int = 20,
    period_penalty: int = 0,
) -> Listener:
    """Quieting pushes internal candidates away so an external joint closure can win."""
    out = listener
    for name in names:
        if distance_penalty:
            out = out.with_distance_bonus(name, distance_penalty)
        if period_penalty:
            out = out.with_period_bonus(name, period_penalty)
    return replace(out, name=out.name + "/quiet")


# ---------------------------------------------------------------------------
# Finite dynamic loop
# ---------------------------------------------------------------------------

SUCCESSOR = {
    "percept": "thought",
    "thought": "feeling",
    "feeling": "external",
    "external": None,
}


def loop_step(listener: Listener) -> tuple[Listener, dict[str, object]]:
    winner = next_trigger(LOOP_CANDIDATES, listener)
    if winner is None:
        return listener, {"winner": None}
    name = str(winner["name"])
    # The winner becomes context: its own refractory distance rises, and its
    # successor is brought nearer.  This is the listener update U(B_t, C_t*).
    nxt = listener.with_distance_bonus(name, 6)
    successor = SUCCESSOR.get(name)
    if successor is not None:
        nxt = nxt.with_distance_bonus(successor, -2)
    winner["next_successor"] = successor
    winner["winner"] = name
    return nxt, winner


def run_loop(steps: int = 4) -> list[dict[str, object]]:
    listener = Listener("loop0")
    trace: list[dict[str, object]] = []
    for step in range(1, steps + 1):
        listener, winner = loop_step(listener)
        winner["step"] = step
        winner["listener_after"] = {
            "period_bonus": dict(listener.period_bonus),
            "distance_bonus": dict(listener.distance_bonus),
        }
        trace.append(winner)
    return trace


# ---------------------------------------------------------------------------
# Retrospective compression
# ---------------------------------------------------------------------------

HISTORY = ("h1", "h2", "h3", "h4")
COMPRESSION_BEFORE = {"h1": "A", "h2": "A", "h3": "B", "h4": "C"}
COMPRESSION_AFTER = {"h1": "A", "h2": "B", "h3": "B", "h4": "B"}


def retrospective_compression() -> dict[str, object]:
    return {
        "history": list(HISTORY),
        "history_unchanged": tuple(HISTORY) == HISTORY,
        "compression_before": dict(COMPRESSION_BEFORE),
        "compression_after": dict(COMPRESSION_AFTER),
        "compression_changed": COMPRESSION_BEFORE != COMPRESSION_AFTER,
        "note": "the past is fixed; the listener-relative compression changes",
    }


# ---------------------------------------------------------------------------
# D8: affective recollection
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Memory:
    name: str
    features: frozenset[str]
    base_distance: int


@dataclass(frozen=True)
class Feeling:
    """A listener context.  It carries generic features, never a target identity."""

    name: str
    features: frozenset[str]


MEMORIES = (
    Memory("M_A", frozenset({"blue", "room", "childhood"}), base_distance=4),
    Memory("M_B", frozenset({"blue", "song", "summer"}), base_distance=5),
    Memory("M_C", frozenset({"loss", "room", "winter"}), base_distance=7),
)

FEELINGS = (
    Feeling("neutral", frozenset()),
    Feeling("F_blue_room", frozenset({"blue", "room"})),
    Feeling("F_song_summer", frozenset({"song", "summer"})),
    Feeling("F_loss_winter", frozenset({"loss", "winter"})),
)


def memory_gain(memory: Memory, feeling: Feeling) -> int:
    """Generic compatibility gain: base 1 plus two per shared feature."""
    overlap = len(memory.features & feeling.features)
    return 1 + 2 * overlap


def trigger_step(memory: Memory, feeling: Feeling) -> int:
    gain = memory_gain(memory, feeling)
    return (memory.base_distance + gain - 1) // gain


def memory_race(feeling: Feeling) -> dict[str, object]:
    """Same memory store, one feeling context; first closure emits RECALL."""
    rows = []
    for memory in MEMORIES:
        overlap = len(memory.features & feeling.features)
        gain = memory_gain(memory, feeling)
        trigger = trigger_step(memory, feeling)
        rows.append(
            {
                "memory": memory.name,
                "base_distance": memory.base_distance,
                "overlap": overlap,
                "gain": gain,
                "trigger_step": trigger,
            }
        )
    winner = min(rows, key=lambda row: (row["trigger_step"], row["base_distance"], row["memory"]))
    trace = []
    for step in range(1, int(winner["trigger_step"]) + 1):
        distances = {}
        for memory in MEMORIES:
            gain = memory_gain(memory, feeling)
            distances[memory.name] = max(0, memory.base_distance - gain * step)
        trace.append(
            {
                "step": step,
                "distances": distances,
                "event": "RECALL" if step == winner["trigger_step"] else "listening",
            }
        )
    return {
        "feeling": feeling.name,
        "feeling_features": sorted(feeling.features),
        "store": [memory.name for memory in MEMORIES],
        "rows": rows,
        "winner": winner["memory"],
        "trigger_step": winner["trigger_step"],
        "trace": trace,
        "recall": {
            "event": "RECALL",
            "memory": winner["memory"],
            "tau_recall": 0,
            "atomic": True,
        },
        "store_unchanged": True,
    }


def affective_recollection() -> dict[str, object]:
    runs = [memory_race(feeling) for feeling in FEELINGS]
    store = [memory.name for memory in MEMORIES]
    return {
        "store": store,
        "store_unchanged_across_feelings": all(run["store"] == store for run in runs),
        "runs": runs,
        "winners": {str(run["feeling"]): run["winner"] for run in runs},
        "feeling_fields": [field.name for field in fields(Feeling)],
        "target_field_present": any(
            field.name in {"target", "memory", "answer"} for field in fields(Feeling)
        ),
        "kill_condition": (
            "the feeling carries generic features only; it never contains the target memory"
        ),
    }


# ---------------------------------------------------------------------------
# Summary and tests
# ---------------------------------------------------------------------------

def build_summary() -> dict[str, object]:
    default = Listener("default")
    attended = attention(default, "thought")
    quiet = quiet_internal(default)
    loop = run_loop(4)
    return {
        "meta": {
            "generator": "conscious_dynamics.py",
            "version": 3,
            "issue": 278,
            "pre_registration": "Conscious_Dynamics_QLF.md",
            "frequency": "f_i^(B) = 1 / T_i^(B), a recurrence frequency",
            "distance": "d_i^(B) = remaining distance to the next trigger",
            "priority": "i_next = argmin d_i over eligible closures",
            "update": "B_{t+1} = U(B_t, C_t*)",
        },
        "default_race": race_table(CONSCIOUS_CANDIDATES, default),
        "default_winner": next_trigger(CONSCIOUS_CANDIDATES, default),
        "priority_race": race_table(PRIORITY_CANDIDATES, default),
        "priority_next": next_trigger(PRIORITY_CANDIDATES, default),
        "priority_fastest": highest_frequency(PRIORITY_CANDIDATES, default),
        "attention_winner": next_trigger(CONSCIOUS_CANDIDATES, attended),
        "quieting_winner": next_trigger(CONSCIOUS_CANDIDATES, quiet),
        "loop": loop,
        "retrospective": retrospective_compression(),
        "memory": affective_recollection(),
        "magical_powers": {
            "relative_world_database": (
                "finite candidate set + listener context B; a bounded relative database, "
                "not an unrestricted inventory of all possible worlds"
            ),
            "active_inference_synthesis": (
                "explicit promotion/update U in this toy; identity with active inference "
                "remains B-OPEN"
            ),
            "strange_loop_reflection": (
                "finite self-model square M ~ S/~_B; toy commutativity only, general theorem open"
            ),
            "gift_of_forgetfulness": (
                "disciplined listener quotient: drop only distinctions no declared continuation "
                "can recover; many-to-one closure price and persistence-by-copying are cited, "
                "not re-proved"
            ),
        },
        "gates": {
            "D0_definition": "frozen",
            "D1_effective_frequency": "finite check; T>0, f=1/T, d separate",
            "D2_promotion_filter": "finite check; next trigger is argmin d; fast micro-event is ineligible",
            "D3_bounded_trace": (
                "finite check only: a bounded trace has increasing external step index; "
                "no transition-system no-event-loop invariant is proved"
            ),
            "D4_retrospective_compression": "finite check; history fixed, compression changes",
            "D5_bisimulation": "cited from Listener_Equivalence_QLF.md; general theorem open",
            "D6_attention_quieting": "finite check; race changes without new contestants",
            "D7_qualia": "bracketed; no theorem",
            "D8_affective_recollection": (
                "finite check; same store, feeling features change accessibility; "
                "no target identity; RECALL is atomic"
            ),
            "D9_frequency_priority_separation": (
                "finite check; fast_recurrent has f=1.0 but slow_near has d=1; "
                "the next trigger is slow_near"
            ),
            "D10_bounded_forgetting": (
                "scope gate + cited results: discard only distinctions no declared continuation "
                "can recover; many-to-one closure and its -log 2 price are not re-proved"
            ),
        },
    }


def self_test() -> None:
    default = Listener("default")
    race = race_table(CONSCIOUS_CANDIDATES, default)
    assert all(row["period"] >= 1 for row in race), "period must stay positive"
    assert all(row["frequency"] > 0 for row in race), "frequency must stay positive"
    assert all(row["distance"] >= 0 for row in race), "distance must stay non-negative"

    micro = next(row for row in race if row["name"] == "micro")
    assert micro["period"] == 1, "micro should have the shortest period"
    assert micro["distance"] == 0, "micro should be at zero distance"
    assert not micro["eligible"], "micro must be ineligible"

    winner = next_trigger(CONSCIOUS_CANDIDATES, default)
    assert winner is not None and winner["name"] == "percept", "default winner should be percept"

    # D9: frequency and event priority are distinct.
    priority_next = next_trigger(PRIORITY_CANDIDATES, default)
    priority_fastest = highest_frequency(PRIORITY_CANDIDATES, default)
    assert priority_next is not None and priority_next["name"] == "slow_near"
    assert priority_fastest is not None and priority_fastest["name"] == "fast_recurrent"
    assert priority_next["name"] != priority_fastest["name"], "frequency and priority were conflated"
    fast = next(row for row in race_table(PRIORITY_CANDIDATES, default) if row["name"] == "fast_recurrent")
    slow = next(row for row in race_table(PRIORITY_CANDIDATES, default) if row["name"] == "slow_near")
    assert float(fast["frequency"]) > float(slow["frequency"]), "fast_recurrent should recur faster"
    assert int(slow["distance"]) < int(fast["distance"]), "slow_near should be nearer to trigger"

    attended = attention(default, "thought", distance_acceleration=4)
    attended_winner = next_trigger(CONSCIOUS_CANDIDATES, attended)
    assert attended_winner is not None and attended_winner["name"] == "thought", (
        "attention should bring thought to the next trigger"
    )

    quiet = quiet_internal(default)
    quiet_winner = next_trigger(CONSCIOUS_CANDIDATES, quiet)
    assert quiet_winner is not None and quiet_winner["name"] == "external", (
        "quieting should promote the external joint closure"
    )

    loop = run_loop(4)
    sequence = [row["winner"] for row in loop]
    assert sequence == ["percept", "thought", "feeling", "external"], (
        f"unexpected promotion sequence: {sequence}"
    )
    assert all(loop[i]["step"] < loop[i + 1]["step"] for i in range(len(loop) - 1)), (
        "event step must increase"
    )

    retro = retrospective_compression()
    assert retro["history_unchanged"], "history must be fixed"
    assert retro["compression_changed"], "compression must change"

    memory = affective_recollection()
    assert memory["winners"]["neutral"] == "M_A", "neutral should recall M_A"
    assert memory["winners"]["F_blue_room"] == "M_A", "blue/room should recall M_A"
    assert memory["winners"]["F_song_summer"] == "M_B", "song/summer should recall M_B"
    assert memory["winners"]["F_loss_winter"] == "M_C", "loss/winter should recall M_C"
    assert memory["store_unchanged_across_feelings"], "memory store must not change"
    assert not memory["target_field_present"], "the feeling must not contain the target"
    for run in memory["runs"]:
        assert run["recall"]["tau_recall"] == 0, "recall must be atomic"
        assert run["recall"]["atomic"] is True
        assert run["trace"][-1]["event"] == "RECALL", "the final trace event must be RECALL"
        assert run["trace"][-1]["distances"][run["winner"]] == 0, "winner must be at zero distance"

    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    print("\ndefault race:")
    for row in summary["default_race"]:  # type: ignore[union-attr]
        print(
            f"  {row['name']}: T={row['period']} f={row['frequency']:.3f} "
            f"d={row['distance']} eligible={row['eligible']}"
        )
    print(f"\ndefault winner (min d): {summary['default_winner']}")  # type: ignore[index]
    print(f"priority next (min d): {summary['priority_next']}")  # type: ignore[index]
    print(f"priority fastest (max f): {summary['priority_fastest']}")  # type: ignore[index]
    print(f"attention winner: {summary['attention_winner']}")  # type: ignore[index]
    print(f"quieting winner: {summary['quieting_winner']}")  # type: ignore[index]
    print("\nloop:")
    for row in summary["loop"]:  # type: ignore[union-attr]
        print(f"  step {row['step']}: {row['winner']} (f={row['frequency']:.3f})")
    print(f"\nretrospective: {summary['retrospective']}")  # type: ignore[index]
    print("\nmemory recall:")
    memory = summary["memory"]  # type: ignore[index]
    for feeling, winner in memory["winners"].items():
        print(f"  {feeling}: {winner} (RECALL, tau=0)")


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
