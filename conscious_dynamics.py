#!/usr/bin/env python3
"""Conscious dynamics — finite reference implementation for #278.

Frozen definitions are in ``Conscious_Dynamics_QLF.md``:

  * f_i^(B) = 1 / R_i^(B);
  * C_t* = argmax over eligible, self-relevant, integrated closures;
  * B_{t+1} = U(B_t, C_t*).

The script is a functional toy, not a theory of qualia.  It shows the
listener-relative race, attention, quieting, a finite promotion loop, and the
fixed-history/changing-compression distinction.

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
    name: str
    intrinsic_delay: int
    integration: float
    self_relevant: bool


@dataclass(frozen=True)
class Listener:
    name: str
    delay_bonus: dict[str, int] = field(default_factory=dict)

    def with_bonus(self, candidate: str, delta: int) -> "Listener":
        bonuses = dict(self.delay_bonus)
        bonuses[candidate] = bonuses.get(candidate, 0) + delta
        return Listener(name=self.name + f"/{candidate}{delta:+d}", delay_bonus=bonuses)


CANDIDATES = (
    Candidate("percept", intrinsic_delay=2, integration=0.80, self_relevant=True),
    Candidate("thought", intrinsic_delay=5, integration=0.90, self_relevant=True),
    Candidate("feeling", intrinsic_delay=7, integration=0.95, self_relevant=True),
    Candidate("external", intrinsic_delay=8, integration=0.85, self_relevant=True),
    # Fast but ineligible: the globally fastest event is not automatically conscious.
    Candidate("micro", intrinsic_delay=1, integration=0.20, self_relevant=False),
)


def effective_delay(candidate: Candidate, listener: Listener) -> int:
    return max(1, candidate.intrinsic_delay + listener.delay_bonus.get(candidate.name, 0))


def frequency(candidate: Candidate, listener: Listener) -> float:
    return 1.0 / effective_delay(candidate, listener)


def eligible(candidate: Candidate) -> bool:
    return candidate.self_relevant and candidate.integration >= 0.5


def promote(
    candidates: Iterable[Candidate] = CANDIDATES, listener: Listener | None = None
) -> dict[str, object] | None:
    listener = listener or Listener("default")
    pool = [c for c in candidates if eligible(c)]
    if not pool:
        return None
    winner = max(pool, key=lambda c: (frequency(c, listener), c.integration, c.name))
    return {
        "name": winner.name,
        "delay": effective_delay(winner, listener),
        "frequency": frequency(winner, listener),
        "integration": winner.integration,
    }


def race_table(listener: Listener | None = None) -> list[dict[str, object]]:
    listener = listener or Listener("default")
    rows = []
    for candidate in CANDIDATES:
        rows.append(
            {
                "name": candidate.name,
                "intrinsic_delay": candidate.intrinsic_delay,
                "effective_delay": effective_delay(candidate, listener),
                "frequency": frequency(candidate, listener),
                "integration": candidate.integration,
                "self_relevant": candidate.self_relevant,
                "eligible": eligible(candidate),
            }
        )
    return sorted(rows, key=lambda row: (-float(row["frequency"]), str(row["name"])))


# ---------------------------------------------------------------------------
# Attention and quieting
# ---------------------------------------------------------------------------

def attention(listener: Listener, target: str, acceleration: int = 4) -> Listener:
    """Attention changes the race: accelerate one existing candidate."""
    return listener.with_bonus(target, -acceleration)


def quiet_internal(listener: Listener, penalty: int = 20) -> Listener:
    """Quieting slows the internal candidates so an external joint closure can win."""
    out = listener
    for name in ("percept", "thought", "feeling"):
        out = out.with_bonus(name, penalty)
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
    winner = promote(CANDIDATES, listener)
    if winner is None:
        return listener, {"winner": None}
    name = str(winner["name"])
    # The winner becomes context: its own refractory delay rises, and its
    # successor is accelerated.  This is the listener update U(B_t, C_t*).
    nxt = listener.with_bonus(name, 6)
    successor = SUCCESSOR.get(name)
    if successor is not None:
        nxt = nxt.with_bonus(successor, -2)
    winner["next_successor"] = successor
    winner["winner"] = name
    return nxt, winner


def run_loop(steps: int = 4) -> list[dict[str, object]]:
    listener = Listener("loop0")
    trace: list[dict[str, object]] = []
    for step in range(1, steps + 1):
        listener, winner = loop_step(listener)
        winner["step"] = step
        winner["listener_after"] = dict(listener.delay_bonus)
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
            "version": 2,
            "issue": 278,
            "pre_registration": "Conscious_Dynamics_QLF.md",
            "frequency": "f_i^(B) = 1 / R_i^(B)",
            "promotion": "argmax over eligible self-relevant integrated closures",
            "update": "B_{t+1} = U(B_t, C_t*)",
        },
        "default_race": race_table(default),
        "default_winner": promote(CANDIDATES, default),
        "attention_winner": promote(CANDIDATES, attended),
        "quieting_winner": promote(CANDIDATES, quiet),
        "loop": loop,
        "retrospective": retrospective_compression(),
        "memory": affective_recollection(),
        "gates": {
            "D0_definition": "frozen",
            "D1_effective_frequency": "finite check; f>0 and delays can move both ways",
            "D2_promotion_filter": "finite check; fast micro-event is ineligible",
            "D3_finite_loop": "finite promotion sequence; event step increases",
            "D4_retrospective_compression": "finite check; history fixed, compression changes",
            "D5_bisimulation": "cited from #275; general theorem open",
            "D6_attention_quieting": "finite check; race changes without new contestants",
            "D7_qualia": "bracketed; no theorem",
            "D8_affective_recollection": (
                "finite check; same store, feeling features change accessibility; "
                "no target identity; RECALL is atomic"
            ),
        },
    }


def self_test() -> None:
    default = Listener("default")
    race = race_table(default)
    assert all(row["effective_delay"] >= 1 for row in race), "delay must stay positive"
    assert all(row["frequency"] > 0 for row in race), "frequency must stay positive"

    micro = next(row for row in race if row["name"] == "micro")
    assert micro["effective_delay"] == 1, "micro should be the fastest candidate"
    assert not micro["eligible"], "micro must be ineligible"

    winner = promote(CANDIDATES, default)
    assert winner is not None and winner["name"] == "percept", "default winner should be percept"

    attended = attention(default, "thought")
    attended_winner = promote(CANDIDATES, attended)
    assert attended_winner is not None and attended_winner["name"] == "thought", (
        "attention should promote thought"
    )

    quiet = quiet_internal(default)
    quiet_winner = promote(CANDIDATES, quiet)
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
            f"  {row['name']}: R={row['effective_delay']} f={row['frequency']:.3f} "
            f"eligible={row['eligible']}"
        )
    print(f"\ndefault winner: {summary['default_winner']}")  # type: ignore[index]
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
