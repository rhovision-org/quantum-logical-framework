#!/usr/bin/env python3
"""Spatial response first slice: independent ΔS and Δd.

Issue #287.  This is a finite *ledger* test, not a physical model:

  * S is the orientation-ledger netSpace from QLF_MagneticOrientation;
  * d is a separate Hamming distance in a small closure automaton;
  * an event appends an orientation pair and independently flips (or does not
    flip) one closure bit.

The point is to test whether "binding" (Δd < 0) implies "contraction" (ΔS < 0)
without defining one in terms of the other.  A negative result is useful: it
means the physical bridge cannot be assumed.

No gravity, 3D metric, or string-tension claim is made.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Sequence

OUTPUT = Path("data/spatial_response_census.json")


def joint_space(p: bool, q: bool) -> int:
    """The QLF orientation ledger: like -> +2, opposite -> -2."""
    return 2 if p == q else -2


def net_space(history: Sequence[tuple[bool, bool]]) -> int:
    return sum(joint_space(p, q) for p, q in history)


def closure_distance(bits: Sequence[bool]) -> int:
    """Hamming distance to the all-False target; independent of netSpace."""
    return sum(1 for bit in bits if bit)


@dataclass(frozen=True)
class Event:
    kind: str  # "like" or "opposite"
    flip: int | None = None

    def __post_init__(self) -> None:
        if self.kind not in ("like", "opposite"):
            raise ValueError(f"unknown event kind {self.kind!r}")


@dataclass(frozen=True)
class Config:
    history: tuple[tuple[bool, bool], ...]
    bits: tuple[bool, ...]


def apply_event(config: Config, event: Event) -> Config:
    pair = (True, True) if event.kind == "like" else (True, False)
    bits = list(config.bits)
    if event.flip is not None:
        bits[event.flip] = not bits[event.flip]
    return Config(history=config.history + (pair,), bits=tuple(bits))


def enumerate_configs(max_history: int = 2, n_bits: int = 2) -> list[Config]:
    histories: list[tuple[tuple[bool, bool], ...]] = [()]
    for _ in range(max_history):
        histories.extend(
            history + (pair,)
            for history in list(histories)
            for pair in ((True, True), (True, False))
        )
    # Deduplicate while preserving deterministic order.
    unique_histories = sorted(set(histories), key=lambda h: (len(h), h))
    return [
        Config(history=history, bits=bits)
        for history in unique_histories
        for bits in product((False, True), repeat=n_bits)
    ]


def transitions(max_history: int = 2, n_bits: int = 2) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    configs = enumerate_configs(max_history, n_bits)
    for config in configs:
        before_s = net_space(config.history)
        before_d = closure_distance(config.bits)
        for kind in ("like", "opposite"):
            for flip in (None, *range(n_bits)):
                event = Event(kind, flip)
                after = apply_event(config, event)
                if len(after.history) > max_history:
                    continue
                ds = net_space(after.history) - before_s
                dd = closure_distance(after.bits) - before_d
                rows.append(
                    {
                        "kind": kind,
                        "flip": flip,
                        "before_s": before_s,
                        "after_s": net_space(after.history),
                        "delta_s": ds,
                        "before_d": before_d,
                        "after_d": closure_distance(after.bits),
                        "delta_d": dd,
                        "binding": dd < 0,
                        "contraction": ds < 0,
                        "expansion": ds > 0,
                    }
                )
    return rows


def census(max_history: int = 2, n_bits: int = 2) -> dict[str, object]:
    rows = transitions(max_history, n_bits)
    binding = [row for row in rows if row["binding"]]
    binding_contraction = [row for row in binding if row["contraction"]]
    binding_expansion = [row for row in binding if row["expansion"]]
    binding_neutral = [row for row in binding if int(row["delta_s"]) == 0]
    categories = {
        "binding_and_contraction": len(binding_contraction),
        "binding_and_expansion": len(binding_expansion),
        "binding_and_neutral": len(binding_neutral),
    }
    return {
        "max_history": max_history,
        "n_bits": n_bits,
        "events": len(rows),
        "binding_events": len(binding),
        "binding_implies_contraction": len(binding_contraction) == len(binding) and len(binding) > 0,
        "categories": categories,
        "examples": {
            "binding_contraction": binding_contraction[0] if binding_contraction else None,
            "binding_expansion": binding_expansion[0] if binding_expansion else None,
            "binding_neutral": binding_neutral[0] if binding_neutral else None,
        },
        "note": (
            "A finite independence test, not a physical spatial model. "
            "S uses only orientation pairs; d uses only closure bits."
        ),
    }


def build_summary() -> dict[str, object]:
    return {
        "meta": {
            "generator": "spatial_response.py",
            "version": 1,
            "issue": 287,
            "pre_registration": "Spatial_Response_QLF.md",
        },
        "ledger": census(),
        "gates": {
            "SR0_definition": "finite; S and d independently defined",
            "SR1_pauli_expansion": "orientation ledger cite; physical reading interpreted",
            "SR2_binding_contraction": "orientation ledger cite; physical reading interpreted",
            "SR3_independence": "finite test; binding does not automatically imply contraction",
            "SR4_gravity": "open; no coarse-graining or curvature claim",
            "SR5_propagation": "open wording split: free propagation vs joint interaction",
            "SR6_timing": "cited #281; d and f separate",
            "SR7_3d": "open; boolean ledger is not a 3D metric",
        },
    }


def self_test() -> None:
    assert joint_space(True, True) == 2
    assert joint_space(True, False) == -2
    assert net_space([(True, True), (True, True)]) == 4
    assert net_space([(True, False), (True, False)]) == -4
    assert net_space([(True, True), (True, False)]) == 0
    assert closure_distance((False, False)) == 0
    assert closure_distance((True, False)) == 1
    result = census()
    assert result["binding_events"] > 0
    assert result["binding_implies_contraction"] is False, (
        "the toy decoupling should expose both signs"
    )
    assert result["categories"]["binding_and_contraction"] > 0
    assert result["categories"]["binding_and_expansion"] > 0
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    ledger = summary["ledger"]  # type: ignore[index]
    print("\nfinite ledger:")
    print(
        f"  events={ledger['events']} binding={ledger['binding_events']} "
        f"binding=>contraction={ledger['binding_implies_contraction']}"
    )
    print(f"  categories={ledger['categories']}")
    for name, example in ledger["examples"].items():
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
