#!/usr/bin/env python3
"""Exact census of three-axis closures by junction baryon number.

Part of the Quantum Logical Framework (QLF), see README.md and Colour_Closure.md.

The alphabet is the six spatial twists ``> < ^ v / \\`` (the three colour axes, no
gauge).  A history closes when it is count balanced (its walk on Z^3 returns to the
origin); Pauli closure then follows by ``count_balanced_pauli_closed``.  Baryon number
is the signed three-axis winding of ``QLF_BaryonWinding`` (on a gauge-free word the
junction is the word, ``junctionBaryon_eq_of_noGauge``).

Two layers are counted, exactly, by a transfer recursion over the state
``(position, last two axes, winding, has-returned)``:

* ``all``   every closed history of length L (possibilities);
* ``first`` histories whose first return to the origin is at L (the absorbing,
            first-closure census: a closure is an event, so the run stops there).

Status: exact computational.  The Lean side (``QLF_ColourClosure``,
``QLF_Manifestation.short_closures_unwound``) proves the structural statements;
this script reports the value distribution, which Lean does not.

Usage::

    python3 borromean_census.py --max-len 12          # print and write the JSON
    python3 borromean_census.py --self-test           # brute-force cross-check to L=8
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter, defaultdict
from pathlib import Path

OUTPUT = Path("data/borromean_census.json")

TWISTS = {  # symbol: (axis, sign)
    ">": (0, 1), "<": (0, -1),
    "^": (1, 1), "v": (1, -1),
    "/": (2, 1), "\\": (2, -1),
}
CYCLIC = {(0, 1, 2): 1, (1, 2, 0): 1, (2, 0, 1): 1,
          (0, 2, 1): -1, (2, 1, 0): -1, (1, 0, 2): -1}


def winding(word: str) -> int:
    ax = [TWISTS[c][0] for c in word]
    return sum(CYCLIC.get((ax[i], ax[i + 1], ax[i + 2]), 0) for i in range(len(ax) - 2))


def census(max_len: int) -> dict[int, dict[str, Counter]]:
    """Exact counts by length and winding for all closures and first closures."""
    # state: (pos, prev2, prev1, B, returned) -> count ; prev axes are -1 when absent
    layer: dict[tuple, int] = {((0, 0, 0), -1, -1, 0, False): 1}
    out: dict[int, dict[str, Counter]] = {}
    for L in range(1, max_len + 1):
        nxt: dict[tuple, int] = defaultdict(int)
        allc: Counter = Counter()
        first: Counter = Counter()
        for (pos, p2, p1, b, ret), n in layer.items():
            for a, s in TWISTS.values():
                q = list(pos)
                q[a] += s
                q = tuple(q)
                nb = b + (CYCLIC.get((p2, p1, a), 0) if p2 >= 0 else 0)
                closed = q == (0, 0, 0)
                if closed:
                    allc[nb] += n
                    if not ret:
                        first[nb] += n
                nxt[(q, p1, a, nb, ret or closed)] += n
        layer = nxt
        if allc:
            out[L] = {"all": allc, "first": first}
    return out


def brute(max_len: int) -> dict[int, dict[str, Counter]]:
    out: dict[int, dict[str, Counter]] = {}
    for L in range(2, max_len + 1, 2):
        allc: Counter = Counter()
        first: Counter = Counter()
        for w in itertools.product(TWISTS, repeat=L):
            pos = [0, 0, 0]
            early = False
            for i, c in enumerate(w):
                a, s = TWISTS[c]
                pos[a] += s
                if pos == [0, 0, 0] and i < L - 1:
                    early = True
            if pos != [0, 0, 0]:
                continue
            b = winding("".join(w))
            allc[b] += 1
            if not early:
                first[b] += 1
        out[L] = {"all": allc, "first": first}
    return out


def minimal_census() -> dict:
    """The 720 orderings of one conjugate pair per spatial axis: wound counts, all and first."""
    words = ["".join(p) for p in itertools.permutations(">^/<\\v")]
    first = [w for w in words if first_closure(w)]
    return {"orderings": len(words), "wound": sum(winding(w) != 0 for w in words),
            "first_closures": len(first), "first_wound": sum(winding(w) != 0 for w in first)}


def first_closure(word: str) -> bool:
    pos = [0, 0, 0]
    for i, c in enumerate(word):
        a, s = TWISTS[c]
        pos[a] += s
        if pos == [0, 0, 0] and i < len(word) - 1:
            return False
    return pos == [0, 0, 0]


def summarise(data: dict[int, dict[str, Counter]]) -> dict:
    rows = {}
    for L, d in sorted(data.items()):
        row = {}
        for layer in ("all", "first"):
            c = d[layer]
            total = sum(c.values())
            wound = total - c.get(0, 0)
            row[layer] = {
                "total": total,
                "wound": wound,
                "wound_fraction": wound / total if total else 0.0,
                "max_abs_B": max((abs(k) for k in c if c[k]), default=0),
                "missing_B_values": [k for k in range(-max(map(abs, c)), max(map(abs, c)) + 1)
                                     if c.get(k, 0) == 0],
                "by_B": {str(k): c[k] for k in sorted(c)},
            }
        rows[str(L)] = row
    return rows


def self_test() -> None:
    fast = census(8)
    slow = brute(8)
    for L in slow:
        for layer in ("all", "first"):
            assert +fast[L][layer] == +slow[L][layer], (L, layer)
    # Lean anchors: short_closures_unwound, protonWord_baryon, B odd under conjugation (mirror)
    for L in (2, 4):
        assert set(fast[L]["all"]) == {0}
    assert winding(">^/<\\v") == 1
    assert minimal_census() == {"orderings": 720, "wound": 576, "first_closures": 480, "first_wound": 384}
    for L, d in fast.items():
        for k, n in d["all"].items():
            assert d["all"][-k] == n
    print("self-test passed: transfer recursion = brute force to L = 8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-len", type=int, default=12)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--minimal", action="store_true", help="the 720 minimal three-axis orderings")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return 0
    if args.minimal:
        print(json.dumps(minimal_census()))
        return 0
    rows = summarise(census(args.max_len))
    for L, row in rows.items():
        a, f = row["all"], row["first"]
        print(f"L={L:>2}  closures {a['total']:>12}  wound {a['wound_fraction']:.4f}  "
              f"max|B| {a['max_abs_B']}  missing {a['missing_B_values']}  |  "
              f"first {f['total']:>11}  wound {f['wound_fraction']:.4f}")
    OUTPUT.parent.mkdir(exist_ok=True)
    OUTPUT.write_text(json.dumps({
        "meta": {"alphabet": "six spatial twists", "closure": "count balance",
                 "B": "signed three-axis winding (junction baryon number)",
                 "status": "exact computational", "max_len": args.max_len},
        "census": rows}, indent=2) + "\n")
    print(f"wrote {OUTPUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
