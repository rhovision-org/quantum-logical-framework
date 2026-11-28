#!/usr/bin/env python3
"""Cooperative ZFA assembly transport — the pre-registered #267 screen.

The model is frozen in ``Cooperative_Assembly_QLF.md``; this script implements that
specification and nothing else.  It is deliberately small:

  * universe: all canonical count-balanced words of even length 2..8 (1442 classes);
  * state: a normalized population over the cumulative library of classes;
  * bottom-up: concatenate representative words of any two library classes whose
    lengths sum to at most 2(k+1), canonicalize, and add the product multiplicity;
  * persistence: carry the previous library forward with weight 1;
  * top-down: keep only classes with ``a_ZFA <= max(1, 2k-2)`` (the blanket capacity);
  * mass: ``M_L(k) = sum n * 8^{-len}`` (primary) and
    ``M_A(k) = sum n * 8^{-a_ZFA}`` (secondary);
  * transfer: ``W(k) = M(k+1)/M(k)``.

A candidate plateau is only a screen: with four scales there are three ratios.
The floor diagnostic rejects a plateau carried by the length-2 classes.  The scalar
ablation uses the raw closure-count census with no assembly memory.

Run:

    python3 assembly_transport.py --self-test
    python3 assembly_transport.py --run
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

import assembly_index as ai

MAX_LENGTH = 8
MAX_SCALE = MAX_LENGTH // 2
OUTPUT = Path("data/assembly_transport_census.json")


@dataclass(frozen=True)
class AssemblyClass:
    word: str
    length: int
    orbit: int
    a: int
    a_zfa: int
    fold: int
    prime: bool


def build_classes() -> list[AssemblyClass]:
    classes: list[AssemblyClass] = []
    for length in range(2, MAX_LENGTH + 1, 2):
        for word in ai.iter_canonical_words(length):
            phase = ai.fold(word)
            if phase is None:
                raise AssertionError(f"canonical class {word!r} is not closed")
            classes.append(
                AssemblyClass(
                    word=word,
                    length=length,
                    orbit=ai.orbit_size(word),
                    a=ai.assembly_index(word),
                    a_zfa=ai.assembly_index_closed(word),
                    fold=phase,
                    prime=ai.is_prime_closure(word),
                )
            )
    return classes


def build_transitions(
    classes: Sequence[AssemblyClass],
) -> tuple[list[tuple[int, int, int]], dict[str, int]]:
    by_word = {c.word: i for i, c in enumerate(classes)}
    by_length: dict[int, list[int]] = defaultdict(list)
    for i, c in enumerate(classes):
        by_length[c.length].append(i)

    transitions: list[tuple[int, int, int]] = []
    for lx in range(2, MAX_LENGTH + 1, 2):
        for ly in range(2, MAX_LENGTH + 1, 2):
            if lx + ly > MAX_LENGTH:
                continue
            for i in by_length[lx]:
                for j in by_length[ly]:
                    parent_word = ai.canonical_word(classes[i].word + classes[j].word)
                    k = by_word.get(parent_word)
                    if k is None:
                        raise AssertionError(
                            f"join {classes[i].word!r} + {classes[j].word!r} "
                            f"canonicalized to {parent_word!r}, not in the class table"
                        )
                    if classes[k].length != lx + ly:
                        raise AssertionError("parent length mismatch")
                    transitions.append((i, j, k))
    return transitions, by_word


def capacity(scale: int, mode: str) -> int:
    if mode == "none":
        return 2 * scale - 1
    if mode == "tight":
        return max(1, 2 * scale - 2)
    raise ValueError(f"unknown capacity mode {mode!r}")


def mass(n: dict[int, float], classes: Sequence[AssemblyClass], kind: str) -> float:
    if kind == "length":
        return sum(pop * 8.0 ** (-classes[i].length) for i, pop in n.items())
    if kind == "assembly":
        return sum(pop * 8.0 ** (-classes[i].a_zfa) for i, pop in n.items())
    raise ValueError(f"unknown mass kind {kind!r}")


def state_diagnostics(
    n: dict[int, float], classes: Sequence[AssemblyClass]
) -> dict[str, float]:
    m_len = mass(n, classes, "length")
    floor = sum(
        pop * 8.0 ** (-2) for i, pop in n.items() if classes[i].length == 2
    )
    return {
        "M_L": m_len,
        "M_A": mass(n, classes, "assembly"),
        "floor_fraction": floor / m_len if m_len else 0.0,
        "mean_length": sum(pop * classes[i].length for i, pop in n.items()),
        "total": sum(n.values()),
    }


def run_model(
    classes: Sequence[AssemblyClass],
    transitions: Sequence[tuple[int, int, int]],
    by_word: dict[str, int],
    filter_mode: str,
    capacity_mode: str,
) -> list[dict[str, float]]:
    """Run the frozen library recursion through MAX_SCALE."""
    seed = by_word[ai.canonical_word("^v")]
    n: dict[int, float] = {seed: 1.0}
    history: list[dict[str, float]] = []

    for scale in range(1, MAX_SCALE + 1):
        diag = state_diagnostics(n, classes)
        history.append({"scale": scale, **diag})
        if scale == MAX_SCALE:
            break

        next_n: dict[int, float] = defaultdict(float)
        for idx, pop in n.items():
            next_n[idx] += pop  # persistence
        for i, j, k in transitions:
            if classes[k].length > 2 * (scale + 1):
                continue
            pi = n.get(i)
            pj = n.get(j)
            if pi is None or pj is None:
                continue
            next_n[k] += pi * pj

        cap = capacity(scale + 1, capacity_mode)
        filtered: dict[int, float] = {}
        for idx, pop in next_n.items():
            c = classes[idx]
            if c.length > 2 * (scale + 1):
                continue
            metric = c.a_zfa if filter_mode == "zfa" else c.a
            if metric <= cap:
                filtered[idx] = pop
        total = sum(filtered.values())
        if total <= 0:
            history.append(
                {
                    "scale": scale + 1,
                    "M_L": 0.0,
                    "M_A": 0.0,
                    "floor_fraction": 0.0,
                    "mean_length": 0.0,
                    "total": 0.0,
                    "collapsed": 1.0,
                }
            )
            break
        n = {idx: pop / total for idx, pop in filtered.items()}

    return history


def ratios(history: Sequence[dict[str, float]], key: str) -> list[float]:
    return [
        history[i + 1][key] / history[i][key]
        for i in range(len(history) - 1)
        if history[i][key] > 0
    ]


def plateau(ws: Sequence[float]) -> bool:
    if len(ws) < 2:
        return False
    a, b = ws[-2], ws[-1]
    return abs(b - a) / max(a, b) < 0.05 and 0.5 <= a <= 2.0 and 0.5 <= b <= 2.0


def scalar_history() -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for scale in range(1, MAX_SCALE + 1):
        length = 2 * scale
        count = ai.balanced_word_count(length)
        out.append(
            {
                "scale": scale,
                "balanced_words": count,
                "M_L": count * 8.0 ** (-length),
                "M_A": None,
                "floor_fraction": 1.0 if scale == 1 else 0.0,
                "mean_length": float(length),
                "total": 1.0,
            }
        )
    return out


def max_relative_difference(a: Sequence[float], b: Sequence[float]) -> float:
    if len(a) != len(b):
        return float("inf")
    if not a:
        return 0.0
    return max(abs(x - y) / max(abs(x), abs(y), 1e-300) for x, y in zip(a, b))


def build_summary() -> dict[str, object]:
    classes = build_classes()
    transitions, by_word = build_transitions(classes)

    models: dict[str, dict[str, object]] = {}
    for label, filter_mode, capacity_mode in (
        ("full", "zfa", "tight"),
        ("ordinary", "a", "tight"),
        ("no_filter", "zfa", "none"),
    ):
        hist = run_model(classes, transitions, by_word, filter_mode, capacity_mode)
        wl = ratios(hist, "M_L")
        wa = ratios(hist, "M_A")
        floor_values = [h["floor_fraction"] for h in hist[1:]]
        models[label] = {
            "history": hist,
            "W_L": wl,
            "W_A": wa,
            "plateau_L": plateau(wl),
            "plateau_A": plateau(wa),
            "floor_ok": all(v <= 0.5 for v in floor_values),
            "candidate_plateau_L": plateau(wl) and all(v <= 0.5 for v in floor_values),
        }

    scalar = scalar_history()
    scalar_w = ratios(scalar, "M_L")
    models["scalar"] = {
        "history": scalar,
        "W_L": scalar_w,
        "W_A": [],
        "plateau_L": plateau(scalar_w),
        "plateau_A": False,
        "floor_ok": True,
        "candidate_plateau_L": False,
    }

    full_w = models["full"]["W_L"]  # type: ignore[index]
    comparisons = {
        "full_vs_scalar_W_L": max_relative_difference(full_w, scalar_w),
        "full_vs_no_filter_W_L": max_relative_difference(
            full_w, models["no_filter"]["W_L"]  # type: ignore[index]
        ),
        "full_vs_ordinary_W_L": max_relative_difference(
            full_w, models["ordinary"]["W_L"]  # type: ignore[index]
        ),
    }
    verdict = {
        "candidate_plateau_full": models["full"]["candidate_plateau_L"],
        "assembly_memory_changes_transfer": any(
            comparisons[k] > 1e-9
            for k in ("full_vs_scalar_W_L", "full_vs_no_filter_W_L", "full_vs_ordinary_W_L")
        ),
        "full_vs_scalar_identical": comparisons["full_vs_scalar_W_L"] <= 1e-9,
        "full_vs_no_filter_identical": comparisons["full_vs_no_filter_W_L"] <= 1e-9,
        "full_vs_ordinary_identical": comparisons["full_vs_ordinary_W_L"] <= 1e-9,
    }
    if verdict["candidate_plateau_full"]:
        verdict["status"] = "screening_positive"
    else:
        verdict["status"] = "negative_no_candidate_plateau"

    return {
        "meta": {
            "generator": "assembly_transport.py",
            "version": 1,
            "pre_registration": "Cooperative_Assembly_QLF.md",
            "issue": 267,
            "max_length": MAX_LENGTH,
            "max_scale": MAX_SCALE,
            "universe": "canonical count-balanced words, even length 2..8",
            "capacity": "A_k = max(1, 2k-2); no_filter uses 2k-1",
            "mass_primary": "M_L = sum n * 8^(-length)",
            "mass_secondary": "M_A = sum n * 8^(-a_ZFA)",
            "plateau_rule": "last two ratios within 5%, both in [0.5,2], floor_fraction <= 0.5",
        },
        "classes": {
            "count": len(classes),
            "orbit_weight_sum": sum(c.orbit for c in classes),
            "transitions": len(transitions),
        },
        "models": models,
        "comparisons": comparisons,
        "verdict": verdict,
    }


def self_test() -> None:
    classes = build_classes()
    transitions, by_word = build_transitions(classes)
    expected_classes = 1 + 6 + 70 + 1365
    expected_words = 8 + 168 + 5120 + 190120
    if len(classes) != expected_classes:
        raise AssertionError(f"class count {len(classes)} != {expected_classes}")
    if sum(c.orbit for c in classes) != expected_words:
        raise AssertionError("orbit weights do not reproduce the balanced-word count")
    for c in classes:
        if not (c.a <= c.a_zfa <= c.length - 1):
            raise AssertionError(f"{c.word!r}: index sandwich failed")
    if not transitions:
        raise AssertionError("no transitions built")
    for _ in (0, 1, 2):
        for label, fm, cm in (
            ("full", "zfa", "tight"),
            ("ordinary", "a", "tight"),
            ("no_filter", "zfa", "none"),
        ):
            hist = run_model(classes, transitions, by_word, fm, cm)
            if len(hist) != MAX_SCALE:
                raise AssertionError(f"{label}: incomplete history")
            for h in hist:
                if h["total"] <= 0 or not math.isfinite(h["M_L"]):
                    raise AssertionError(f"{label}: invalid state at scale {h['scale']}")
    print("self-test: OK")


def print_summary(summary: dict[str, object]) -> None:
    print(
        f"classes {summary['classes']['count']}  "
        f"orbit weights {summary['classes']['orbit_weight_sum']}  "
        f"transitions {summary['classes']['transitions']}"
    )
    for label in ("full", "ordinary", "no_filter", "scalar"):
        model = summary["models"][label]  # type: ignore[index]
        print(f"\n[{label}]  plateau_L={model['plateau_L']}  "
              f"candidate={model['candidate_plateau_L']}  floor_ok={model['floor_ok']}")
        for h in model["history"]:  # type: ignore[union-attr]
            wl = h.get("M_L", 0.0)
            ma = h.get("M_A")
            ma_text = "—" if ma is None else f"{ma:.6e}"
            print(
                f"  k={h['scale']}  M_L={wl:.6e}  "
                f"M_A={ma_text}  "
                f"floor={h['floor_fraction']:.3f}  "
                f"mean_len={h['mean_length']:.3f}"
            )
        if model["W_L"]:  # type: ignore[index]
            print("  W_L = " + ", ".join(f"{w:.4f}" for w in model["W_L"]))  # type: ignore[index]
        if model["W_A"]:  # type: ignore[index]
            print("  W_A = " + ", ".join(f"{w:.4f}" for w in model["W_A"]))  # type: ignore[index]
    print("\ncomparisons (max relative difference of W_L):")
    for key, value in summary["comparisons"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value:.3e}")
    print("\nverdict:")
    for key, value in summary["verdict"].items():  # type: ignore[union-attr]
        print(f"  {key}: {value}")


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
