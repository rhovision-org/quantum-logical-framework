#!/usr/bin/env python3
"""Cosmic closure — finite reference implementation for #276.

Definitions are frozen in ``Cosmic_Closure_QLF.md``:

  * G1: the minimal count-balanced ZFA word is a logical origin, not a metric
    singularity;
  * G2: a closed binary distinction has a one-bit reading, not an
    information-energy identity;
  * G3: a holographic listener is a compression that preserves the claimed
    closure observable;
  * G4: raw path counts become probabilities only after a declared measure;
  * G5: every realized horizon is finite, and balanced extensions are unbounded;
  * G6: the numerical cosmic age waits on an independent derivation of N.

This is a finite sanity check, not a derivation of the observed universe.

Run:

    python3 cosmic_closure.py --self-test
    python3 cosmic_closure.py --run
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, Sequence

OUTPUT = Path("data/cosmic_closure_census.json")

TWISTS = ("^", "v", ">", "<", "/", "\\", "+", "-")
AXIS = {
    "^": ("y", 1),
    "v": ("y", -1),
    ">": ("x", 1),
    "<": ("x", -1),
    "/": ("z", 1),
    "\\": ("z", -1),
    "+": ("g", 1),
    "-": ("g", -1),
}


def net(word: str) -> tuple[int, int, int, int]:
    counts = {"y": 0, "x": 0, "z": 0, "g": 0}
    for char in word:
        axis, sign = AXIS[char]
        counts[axis] += sign
    return counts["y"], counts["x"], counts["z"], counts["g"]


def is_closed(word: str) -> bool:
    return all(value == 0 for value in net(word))


def first_completions(start: str = "^", max_length: int = 4) -> tuple[str, ...]:
    """Count-balanced first completions of ``start`` through ``max_length``."""
    if not start or any(char not in AXIS for char in start):
        raise ValueError("start must be a nonempty twist word")
    out: list[str] = []

    def rec(word: str) -> None:
        if is_closed(word):
            out.append(word)
            return
        if len(word) >= max_length:
            return
        for twist in TWISTS:
            rec(word + twist)

    rec(start)
    return tuple(out)


def measure(completions: Iterable[str], base: int = 8) -> dict[str, object]:
    """Cylinder/Kraft weights for the completion words (gate G4).

    A length-sensitive cylinder measure requires an integer base greater than
    one.  ``base=1`` would erase length discrimination; non-positive or
    non-integer bases are not a coherent measure for this interpretation.
    """
    if isinstance(base, bool) or not isinstance(base, int) or base <= 1:
        raise ValueError("measure base must be an integer greater than 1")
    words = tuple(completions)
    weights = [base ** (-len(word)) for word in words]
    total = sum(weights)
    by_length: dict[str, dict[str, float | int]] = {}
    for word, weight in zip(words, weights):
        key = str(len(word))
        row = by_length.setdefault(
            key, {"count": 0, "mu_each": weight, "P_total": 0.0}
        )
        row["count"] = int(row["count"]) + 1
        if total:
            row["P_total"] = float(row["P_total"]) + weight / total
    return {
        "W_micro": len(words),
        "base": base,
        "mu_total": total,
        "normalized": [weight / total for weight in weights] if total else [],
        "by_length": dict(sorted(by_length.items(), key=lambda item: int(item[0]))),
    }


# ---------------------------------------------------------------------------
# G3: holographic compression toy
# ---------------------------------------------------------------------------

INTERIORS = ("h1", "h2", "h3", "h4", "h5", "h6")
SAFE_BOUNDARY = {
    "h1": "A",
    "h2": "A",
    "h3": "A",
    "h4": "B",
    "h5": "B",
    "h6": "C",
}
LOSSY_BOUNDARY = {
    "h1": "A",
    "h2": "A",
    "h3": "B",  # merges h3 (obs1) with h4 (obs2)
    "h4": "B",
    "h5": "B",
    "h6": "C",
}
OBSERVABLE = {
    "h1": "obs1",
    "h2": "obs1",
    "h3": "obs1",
    "h4": "obs2",
    "h5": "obs2",
    "h6": "obs3",
}


def compression_preserves(
    boundary: dict[str, str], observable: dict[str, str]
) -> bool:
    """A boundary compression is lossless for the observable iff equal boundary
    classes imply equal observable values."""
    for a in boundary:
        for b in boundary:
            if boundary[a] == boundary[b] and observable[a] != observable[b]:
                return False
    return True


def compression_stats(boundary: dict[str, str]) -> dict[str, object]:
    classes: dict[str, list[str]] = {}
    for interior, cls in boundary.items():
        classes.setdefault(cls, []).append(interior)
    return {
        "interiors": len(boundary),
        "boundary_classes": len(classes),
        "ratio": len(classes) / len(boundary),
        "classes": {cls: sorted(members) for cls, members in sorted(classes.items())},
    }


# ---------------------------------------------------------------------------
# G5: finite horizons and unbounded possible extension
# ---------------------------------------------------------------------------

def extension_witnesses(n_max: int = 6) -> tuple[dict[str, object], ...]:
    """Constructive witnesses ``(^v)^n`` of unbounded balanced extension."""
    out = []
    for n in range(1, n_max + 1):
        word = "^v" * n
        out.append({"n": n, "word": word, "length": len(word), "closed": is_closed(word)})
    return tuple(out)


def time_gate(n_max: int = 6) -> dict[str, object]:
    witnesses = extension_witnesses(n_max)
    return {
        "finite_at_every_witness": all(w["closed"] for w in witnesses),
        "unbounded_witness_family": "for every n, (^v)^n is count-balanced",
        "witnesses": witnesses,
        "physical_eternal": "interpretation, not proved",
        "status": "unbounded possible extension proved; physical eternity open",
    }


# ---------------------------------------------------------------------------
# G6: cosmic clock
# ---------------------------------------------------------------------------

def clock_gate() -> dict[str, object]:
    return {
        "relation": "t0 = N * tau_Planck",
        "N_derived": False,
        "numerical_age_claim": None,
        "status": (
            "N is not independently derived; the numerical age is calibrated "
            "through H0/expansion history (AgeOfUniverse.md)"
        ),
    }


def build_summary() -> dict[str, object]:
    completions = first_completions("^", 4)
    measured = measure(completions)
    safe_stats = compression_stats(SAFE_BOUNDARY)
    lossy_stats = compression_stats(LOSSY_BOUNDARY)
    return {
        "meta": {
            "generator": "cosmic_closure.py",
            "version": 1,
            "issue": 276,
            "pre_registration": "Cosmic_Closure_QLF.md",
        },
        "logical_origin": {
            "minimal_closures": ["+-", "^v"],
            "minimal_closure_closed": is_closed("+-") and is_closed("^v"),
            "stale_triangle_word": "^<v",
            "stale_triangle_closed": is_closed("^<v"),
            "stale_triangle_net": net("^<v"),
        },
        "measure": measured,
        "holography": {
            "safe": {
                "preserves": compression_preserves(SAFE_BOUNDARY, OBSERVABLE),
                **safe_stats,
            },
            "lossy": {
                "preserves": compression_preserves(LOSSY_BOUNDARY, OBSERVABLE),
                **lossy_stats,
            },
        },
        "time": time_gate(),
        "clock": clock_gate(),
        "gates": {
            "G1_logical_origin": "theorem cited; no metric singularity",
            "G2_information": "one-bit interpretation; no information-energy identity",
            "G3_holographic_compression": (
                "finite toy; safe vs lossy checked; general N-body open"
            ),
            "G4_measure": "candidate cylinder/Kraft weight; raw W vs P checked",
            "G5_time": "unbounded extension witnessed; physical eternity interpretation",
            "G6_cosmic_clock": "N not derived; no numerical age claim",
        },
    }


def self_test() -> None:
    assert is_closed("+-"), "the minimal [+,-] closure must close"
    assert is_closed("^v"), "the up/down conjugate must close"
    assert not is_closed("^<v"), "the stale 3-twist triangle must not be balanced"
    assert net("^<v") == (0, -1, 0, 0), "the stale triangle should leave net x = -1"

    completions = first_completions("^", 4)
    assert len(completions) == 14, f"expected 14 completions, got {len(completions)}"
    measured = measure(completions)
    assert measured["W_micro"] == 14, "measure changed the raw count"
    assert abs(sum(measured["normalized"]) - 1.0) < 1e-12, "weights must normalize"
    assert measured["by_length"]["2"]["P_total"] > measured["by_length"]["4"]["P_total"], (
        "shorter completions should carry more cylinder weight"
    )

    assert compression_preserves(SAFE_BOUNDARY, OBSERVABLE), "safe compression failed"
    assert not compression_preserves(LOSSY_BOUNDARY, OBSERVABLE), "lossy compression passed"
    assert compression_stats(SAFE_BOUNDARY)["boundary_classes"] == 3
    assert compression_stats(SAFE_BOUNDARY)["interiors"] == 6

    time = time_gate()
    assert time["finite_at_every_witness"], "extension witness failed to close"
    assert len(time["witnesses"]) == 6
    assert time["physical_eternal"] == "interpretation, not proved"

    clock = clock_gate()
    assert clock["N_derived"] is False
    assert clock["numerical_age_claim"] is None

    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print("gates:")
    for key, value in summary["gates"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")
    print("\nlogical origin:")
    origin = summary["logical_origin"]  # type: ignore[index]
    print(f"  minimal closures closed: {origin['minimal_closure_closed']}")
    print(f"  stale ^<v closed: {origin['stale_triangle_closed']} (net {origin['stale_triangle_net']})")
    print("\nmeasure:")
    measured = summary["measure"]  # type: ignore[index]
    print(f"  W_micro = {measured['W_micro']}, mu_total = {measured['mu_total']:.10f}")
    print(f"  by_length = {measured['by_length']}")
    print("\nholography:")
    print(f"  safe: {summary['holography']['safe']}")  # type: ignore[index]
    print(f"  lossy: {summary['holography']['lossy']}")  # type: ignore[index]
    print("\nclock:")
    print(f"  {summary['clock']}")  # type: ignore[index]


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
