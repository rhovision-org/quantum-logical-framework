#!/usr/bin/env python3
"""Equal-size library diversity census for closure-constrained assembly (#264, #290).

Pre-registration: ``Library_Diversity_Assembly_Prereg.md`` (committed in 69a09ef,
before this file existed).  Results: ``Library_Diversity_Assembly.md``.

Question: at equal library size, do closed one-axis parts spread over several axes
(diverse) lower the closure-constrained assembly cost of balanced words more than
parts on one axis (homogeneous)?

* Saving ``S(w | L) = a_ZFA(w) - a_ZFA(w | L)``; library parts are available at zero
  cost and, being closed, are reusable (``libIndex`` in ``lean/QLF_AssemblyIndex.lean``).
* Strata: (panel, k, shape multiset, target length n); 28 in all.
* Primary: Delta = unweighted mean over strata of (mean saving, diverse) - (homogeneous).
* N1: the same with the ordinary assembly index (every object reusable).
* Coverage qualifier: the same with savings averaged over covered targets only.
* Descriptors: coverage and synergy ``S(w|L) - sum_p S(w|{p})``.

Exact rationals throughout.  Means over libraries use the symmetry group of the
alphabet (axis permutations and per-axis conjugation, 384 maps): every index here
depends only on which letters are equal and which are conjugate, so a library and
its image under the group have the same target-averaged statistics, and each orbit
is computed once and weighted by its size.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path
from typing import Iterable

from assembly_index import (
    CONJUGATE,
    INF,
    _splits,
    _substrings,
    assembly_index,
    assembly_index_closed,
    is_closed,
)

OUTPUT = Path("data/library_diversity_census.json")
AXES: tuple[tuple[str, str], ...] = (("^", "v"), ("<", ">"), ("/", "\\"), ("+", "-"))
TARGET_LENGTHS = (6, 8)


# ---------------------------------------------------------------------------
# Indices relative to a library
# ---------------------------------------------------------------------------

def ordinary_index_from(word: str, library: frozenset[str]) -> int:
    """Ordinary assembly index when the parts of ``library`` cost nothing."""
    n = len(word)
    if n <= 1 or word in library:
        return 0
    splits = _splits(_substrings(word))
    best = n - 1

    def free(s: str) -> bool:
        return len(s) <= 1 or s in library

    def dfs(chosen: frozenset[str], assigned: frozenset[str]) -> None:
        nonlocal best
        if len(chosen) >= best:
            return
        pending = chosen - assigned
        if not pending:
            best = len(chosen)
            return
        s = min(pending, key=lambda t: (len(splits[t]), -len(t)))
        for u, v in splits[s]:
            new_chosen = chosen
            if not free(u) and u not in new_chosen:
                new_chosen = new_chosen | {u}
            if not free(v) and v not in new_chosen:
                new_chosen = new_chosen | {v}
            if len(new_chosen) >= best:
                continue
            dfs(new_chosen, assigned | {s})

    dfs(frozenset({word}), frozenset())
    return best


def closed_index_from(word: str, library: frozenset[str]) -> int:
    """Closure-constrained index when the (closed) parts of ``library`` cost nothing.

    Same search as ``assembly_index.assembly_index_closed``, started with the library
    parts in the set of built reusable objects.
    """
    n = len(word)
    if n <= 1 or word in library:
        return 0
    subs = _substrings(word)
    splits = _splits(subs)
    closed = {s for s in subs if is_closed(s)}
    memo: dict[tuple, int] = {}

    def solve(req: Counter[str], built: frozenset[str], budget: int) -> int:
        req = Counter({s: c for s, c in req.items() if c > 0 and len(s) > 1 and s not in built})
        if not req:
            return 0
        if len(req) > budget:
            return INF
        key = (tuple(sorted(req.items())), built)
        if key in memo:
            return memo[key]
        s = min(req, key=lambda t: (0 if t in closed else 1, -req[t], len(splits[t])))
        share = s in closed
        best_local = INF
        for u, v in splits[s]:
            new_req = req.copy()
            new_req[s] -= 1
            if new_req[s] <= 0:
                del new_req[s]
            if len(u) > 1:
                new_req[u] += 1
            if len(v) > 1:
                new_req[v] += 1
            new_built = built
            if share:
                new_req = Counter({t: c for t, c in new_req.items() if t != s})
                new_built = built | {s}
            sub_budget = min(budget - 1, best_local - 1)
            if sub_budget < 0:
                continue
            value = 1 + solve(new_req, new_built, sub_budget)
            if value < best_local:
                best_local = value
        if best_local <= budget:
            memo[key] = best_local
        return best_local

    built0 = frozenset(p for p in library if p in subs)
    return solve(Counter({word: 1}), built0, n - 1)


# ---------------------------------------------------------------------------
# Parts, libraries, symmetry
# ---------------------------------------------------------------------------

SHAPES_A = {"D": (0, 1)}
SHAPES_B = {"B": (0, 0, 1, 1), "A": (0, 1, 0, 1), "N": (0, 1, 1, 0)}


def parts(panel: str) -> dict[str, tuple[int, str]]:
    """part word -> (axis index, shape name), both orientations."""
    shapes = SHAPES_A if panel == "A" else SHAPES_B
    out: dict[str, tuple[int, str]] = {}
    for ax, pair in enumerate(AXES):
        for name, pattern in shapes.items():
            for flip in (0, 1):
                out["".join(pair[b ^ flip] for b in pattern)] = (ax, name)
    return out


def group_maps() -> list[dict[str, str]]:
    maps = []
    for perm in itertools.permutations(range(4)):
        for flips in itertools.product((0, 1), repeat=4):
            m: dict[str, str] = {}
            for ax, pair in enumerate(AXES):
                img = AXES[perm[ax]]
                for b in (0, 1):
                    m[pair[b]] = img[b ^ flips[ax]]
            maps.append(m)
    return maps


GROUP = group_maps()


def apply(m: dict[str, str], w: str) -> str:
    return "".join(m[c] for c in w)


def canonical(library: Iterable[str]) -> tuple[str, ...]:
    lib = tuple(library)
    return min(tuple(sorted(apply(m, p) for p in lib)) for m in GROUP)


def libraries(panel: str, k: int) -> dict[tuple, dict[str, Counter]]:
    """stratum shape multiset -> group -> Counter(canonical library -> number of libraries)."""
    table = parts(panel)
    out: dict[tuple, dict[str, Counter]] = defaultdict(lambda: {"homogeneous": Counter(),
                                                                 "diverse": Counter()})
    for lib in itertools.combinations(sorted(table), k):
        axes = [table[p][0] for p in lib]
        if len(set(axes)) == 1:
            group = "homogeneous"
        elif len(set(axes)) == k:
            group = "diverse"
        else:
            continue
        shapes = tuple(sorted(table[p][1] for p in lib))
        out[shapes][group][canonical(lib)] += 1
    return out


# ---------------------------------------------------------------------------
# Targets
# ---------------------------------------------------------------------------

def balanced_words(n: int) -> list[str]:
    letters = [c for pair in AXES for c in pair]
    return ["".join(w) for w in itertools.product(letters, repeat=n) if is_closed("".join(w))]


def _base(word: str) -> tuple[str, int, int]:
    return word, assembly_index_closed(word), assembly_index(word)


def _lib_row(args: tuple[str, tuple[str, ...]]) -> tuple[str, int, int]:
    word, lib = args
    lib_set = frozenset(lib)
    return word, closed_index_from(word, lib_set), ordinary_index_from(word, lib_set)


class Engine:
    def __init__(self, n: int, jobs: int) -> None:
        self.n = n
        self.jobs = jobs
        self.targets = balanced_words(n)
        with ProcessPoolExecutor(jobs) as ex:
            rows = list(ex.map(_base, self.targets, chunksize=512))
        self.base_closed = {w: c for w, c, _ in rows}
        self.base_ord = {w: o for w, _, o in rows}
        self.cache: dict[tuple[str, ...], dict[str, tuple[int, int]]] = {}

    def savings(self, lib: tuple[str, ...]) -> dict[str, tuple[int, int]]:
        """covered target -> (closed saving, ordinary saving)."""
        if lib in self.cache:
            return self.cache[lib]
        covered = [w for w in self.targets if any(p in w for p in lib)]
        with ProcessPoolExecutor(self.jobs) as ex:
            rows = list(ex.map(_lib_row, [(w, lib) for w in covered], chunksize=256))
        out = {w: (self.base_closed[w] - c, self.base_ord[w] - o) for w, c, o in rows}
        self.cache[lib] = out
        return out

    def stats(self, lib: tuple[str, ...]) -> dict[str, Fraction]:
        sv = self.savings(lib)
        total = len(self.targets)
        cov = len(sv)
        s_closed = sum(c for c, _ in sv.values())
        s_ord = sum(o for _, o in sv.values())
        singles = Counter()
        for p in lib:
            for w, (c, _) in self.savings((p,)).items():
                singles[w] += c
        synergy = s_closed - sum(singles.values())
        return {
            "S": Fraction(s_closed, total),
            "S_ord": Fraction(s_ord, total),
            "S_cov": Fraction(s_closed, cov) if cov else Fraction(0),
            "coverage": Fraction(cov, total),
            "synergy": Fraction(synergy, total),
        }


# ---------------------------------------------------------------------------
# Census
# ---------------------------------------------------------------------------

def fr(x: Fraction | None) -> str | None:
    if x is None:
        return None
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)


def sign(x: Fraction) -> int:
    return (x > 0) - (x < 0)


def build(jobs: int) -> dict[str, object]:
    designs = [("A", 2), ("B", 2), ("B", 3)]
    strata = []
    for n in TARGET_LENGTHS:
        engine = Engine(n, jobs)
        for panel, k in designs:
            for shapes, groups in sorted(libraries(panel, k).items()):
                if not groups["homogeneous"] or not groups["diverse"]:
                    continue
                row: dict[str, object] = {"panel": panel, "k": k, "shapes": list(shapes), "n": n}
                means: dict[str, dict[str, Fraction]] = {}
                for g in ("homogeneous", "diverse"):
                    libs = groups[g]
                    count = sum(libs.values())
                    acc: dict[str, Fraction] = defaultdict(Fraction)
                    for lib, mult in libs.items():
                        for key, val in engine.stats(lib).items():
                            acc[key] += mult * val
                    means[g] = {key: val / count for key, val in acc.items()}
                    row[g] = {"libraries": count, "orbits": len(libs),
                              **{key: fr(val) for key, val in means[g].items()}}
                for key in ("S", "S_ord", "S_cov"):
                    d = means["diverse"][key] - means["homogeneous"][key]
                    row[f"delta_{key}"] = fr(d)
                    row[f"sign_{key}"] = sign(d)
                strata.append((row, means))
                print(panel, k, shapes, n, row["delta_S"], row["delta_S_ord"], row["delta_S_cov"],
                      flush=True)

    def overall(key: str) -> Fraction:
        ds = [m["diverse"][key] - m["homogeneous"][key] for _, m in strata]
        return sum(ds, Fraction(0)) / len(ds)

    delta, delta_ord, delta_cov = overall("S"), overall("S_ord"), overall("S_cov")
    signs = [r["sign_S"] for r, _ in strata]
    if delta <= 0:
        verdict = "FAIL"
    elif any(s < 0 for s in signs):
        verdict = "MIXED"
    else:
        same = all(r["sign_S_ord"] == r["sign_S"] for r, _ in strata)
        verdict = "PASS, NOT ZFA-SPECIFIC" if (delta_ord > 0 and same) else "PASS (ZFA)"
        if delta_cov <= 0:
            verdict += ", coverage-only"
    return {
        "prereg": "Library_Diversity_Assembly_Prereg.md @ 69a09ef",
        "strata_count": len(strata),
        "delta": fr(delta), "delta_float": float(delta),
        "delta_N1_ordinary": fr(delta_ord), "delta_N1_float": float(delta_ord),
        "delta_coverage": fr(delta_cov), "delta_coverage_float": float(delta_cov),
        "stratum_signs": {"+": signs.count(1), "0": signs.count(0), "-": signs.count(-1)},
        "verdict": verdict,
        "strata": [r for r, _ in strata],
    }


def self_test() -> None:
    for w in ["^v<>", "^^vv^^vv", "^<v>^<v>", "<>^v<>", "^v^v^v"]:
        assert closed_index_from(w, frozenset()) == assembly_index_closed(w), w
        assert ordinary_index_from(w, frozenset()) == assembly_index(w), w
    assert closed_index_from("^v^v", frozenset({"^v"})) == 1
    assert closed_index_from("^v^v", frozenset({"^v^v"})) == 0
    assert closed_index_from("^vv^", frozenset({"^v", "v^"})) == 1
    assert closed_index_from("<>^v", frozenset({"^v"})) == 2
    # Group sanity: 384 maps, the balanced set is invariant.
    assert len(GROUP) == 384
    w6 = set(balanced_words(4))
    assert all(apply(m, w) in w6 for m in GROUP[:20] for w in w6)
    print("self-test ok")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    self_test()
    if args.self_test:
        return 0
    data = build(args.jobs)
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(data["verdict"], data["delta"], data["delta_N1_ordinary"], data["delta_coverage"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
