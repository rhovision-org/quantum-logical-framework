#!/usr/bin/env python3
"""Exact assembly index for ZFA twist histories.

This module implements the *ordinary* Assembly-Theory assembly index for words over
the eight-twist alphabet, and a separate *closure-constrained* variant in which only
count-balanced (closed) intermediate objects may be freely reused.

Object semantics are frozen here:

  * an object is a raw word over the eight twists ``^ v < > / \\ + -``;
  * the primitives are the eight one-letter words;
  * a join concatenates two available objects, ``(u, v) -> u + v``;
  * a constructed object may be reused according to the mode below.

The ordinary assembly index ``a(x)`` is the minimum number of joins needed to build
``x`` when every constructed object may be reused without limit.  This is the
minimum number of nonterminals in a straight-line program (SLP) for ``x``.

The closure-constrained index ``a_ZFA(x)`` allows unlimited reuse only of objects
whose word is count-balanced (``countBalanced`` in QLF), i.e. every conjugate pair
``^/v``, ``</>``, ``/\\``, ``+/-`` occurs equally often.  A non-closed object may be
built and used, but it has fan-out one: it is consumed by the single join that uses
it.  This is the formal content of ``isolated_iff_closed`` and
``closed_insertion_is_phase`` as a restriction on an assembly space.

The code is dependency-free.  The exact solvers are branch-and-bound searches over
the substrings of the target; both are cross-checked against independent
breadth-first searches in ``--self-test`` and in ``tests/test_assembly_index.py``.
The companion design memo is ``Assembly_Index_QLF.md``.

Usage:

    python3 assembly_index.py --word '^v^v'
    python3 assembly_index.py --max-length 10 --jobs 4 \
        --json data/assembly_index_census.json
    python3 assembly_index.py --self-test
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import zlib
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence

# ---------------------------------------------------------------------------
# The eight-twist alphabet
# ---------------------------------------------------------------------------

TWISTS: tuple[str, ...] = ("^", "v", "<", ">", "/", "\\", "+", "-")

CONJUGATE: dict[str, str] = {
    "^": "v", "v": "^",
    "<": ">", ">": "<",
    "/": "\\", "\\": "/",
    "+": "-", "-": "+",
}

# Four signed axes: 0 = up/down, 1 = left/right, 2 = slash/backslash, 3 = plus/minus.
AXIS: dict[str, int] = {
    "^": 0, "v": 0,
    "<": 1, ">": 1,
    "/": 2, "\\": 2,
    "+": 3, "-": 3,
}
SIGN: dict[str, int] = {
    "^": 1, "v": -1,
    "<": -1, ">": 1,
    "/": 1, "\\": -1,
    "+": 1, "-": -1,
}

# Canonical symbols for the four axes, positive and negative.  Axis 0 is ^/v,
# axis 1 is >/<, axis 2 is /\\, axis 3 is +/-.
PLUS_SYMBOL: tuple[str, ...] = ("^", ">", "/", "+")
MINUS_SYMBOL: tuple[str, ...] = ("v", "<", "\\", "-")

# Pauli axes, in the order used by lean/QLF_TwistAlphabet.lean: I, X, Y, Z.
AXIS_I, AXIS_X, AXIS_Y, AXIS_Z = 0, 1, 2, 3

# Twist -> (Pauli phase, Pauli axis), with phase 0,1,2,3 = +1, +i, -1, -i.
# This mirrors Twist.toMatrix in lean/QLF_TwistAlphabet.lean:
#   up = +sigma_y, down = -sigma_y, left = -sigma_x, right = +sigma_x,
#   slash = +sigma_z, backslash = -sigma_z, plus = +1, minus = -1.
TWIST_NF: dict[str, tuple[int, int]] = {
    "^": (0, AXIS_Y),
    "v": (2, AXIS_Y),
    "<": (2, AXIS_X),
    ">": (0, AXIS_X),
    "/": (0, AXIS_Z),
    "\\": (2, AXIS_Z),
    "+": (0, AXIS_I),
    "-": (2, AXIS_I),
}

# Klein four-group law on axes (commutative): X*Y = Z, Y*Z = X, Z*X = Y.
AXIS_MUL: dict[tuple[int, int], int] = {}
for _a in range(4):
    for _b in range(4):
        if _a == AXIS_I:
            AXIS_MUL[(_a, _b)] = _b
        elif _b == AXIS_I:
            AXIS_MUL[(_a, _b)] = _a
        elif _a == _b:
            AXIS_MUL[(_a, _b)] = AXIS_I
        else:
            AXIS_MUL[(_a, _b)] = 6 - _a - _b  # X+Y+Z = 6, I = 0

# Cocycle phase of axisMatrix(a) * axisMatrix(b), from the sigma-product identities.
# X*Y = +iZ, Y*X = -iZ, Y*Z = +iX, Z*Y = -iX, Z*X = +iY, X*Z = -iY.
COCYCLE: dict[tuple[int, int], int] = {}
for _a in range(4):
    for _b in range(4):
        if _a == AXIS_I or _b == AXIS_I or _a == _b:
            COCYCLE[(_a, _b)] = 0
        elif (_a, _b) in ((AXIS_X, AXIS_Y), (AXIS_Y, AXIS_Z), (AXIS_Z, AXIS_X)):
            COCYCLE[(_a, _b)] = 1
        else:
            COCYCLE[(_a, _b)] = 3


def validate_word(word: str) -> str:
    """Raise ValueError unless *word* uses only the eight twists."""
    bad = sorted({ch for ch in word if ch not in CONJUGATE})
    if bad:
        raise ValueError(
            f"word contains non-twist characters {bad!r}; allowed: {''.join(TWISTS)!r}"
        )
    return word


def net(word: str) -> tuple[int, int, int, int]:
    """Signed action vector: net count on each of the four axis pairs."""
    counts = [0, 0, 0, 0]
    for ch in word:
        counts[AXIS[ch]] += SIGN[ch]
    return tuple(counts)  # type: ignore[return-value]


def is_closed(word: str) -> bool:
    """QLF count balance: every conjugate pair occurs equally often."""
    return all(c == 0 for c in net(word))


def pauli_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    """Multiply two Pauli-group elements represented as (phase, axis)."""
    p1, a1 = left
    p2, a2 = right
    return ((p1 + p2 + COCYCLE[(a1, a2)]) % 4, AXIS_MUL[(a1, a2)])


def fold(word: str) -> int | None:
    """Pauli scalar phase of a closed word, or None if the word is not closed.

    Returns 0,1,2,3 for +1, +i, -1, -i respectively.
    """
    acc = (0, AXIS_I)
    for ch in word:
        acc = pauli_mul(acc, TWIST_NF[ch])
    phase, axis = acc
    return phase if axis == AXIS_I else None


# ---------------------------------------------------------------------------
# Canonical forms and the QLF symmetry group
# ---------------------------------------------------------------------------

GROUP_ORDER = 384  # S_4 axis permutations times 2^4 per-axis sign flips


def canonical_word(word: str) -> str:
    """Canonical representative under axis permutations and per-axis sign flips.

    Axes are numbered by first appearance, and each axis's first occurrence is
    made positive by flipping that axis if necessary.  This is a unique
    representative of the orbit under the 384-element group that preserves
    count balance.
    """
    axis_id: dict[int, int] = {}
    first_sign: dict[int, int] = {}
    out: list[str] = []
    for ch in word:
        a = AXIS[ch]
        if a not in axis_id:
            axis_id[a] = len(axis_id)
            first_sign[a] = SIGN[ch]
        b = axis_id[a]
        s = SIGN[ch] * first_sign[a]
        out.append(PLUS_SYMBOL[b] if s == 1 else MINUS_SYMBOL[b])
    return "".join(out)


def equality_pattern(word: str) -> str:
    """Canonical form under arbitrary permutations of the eight symbols.

    The ordinary assembly index depends only on this pattern.
    """
    label: dict[str, int] = {}
    out: list[int] = []
    for ch in word:
        if ch not in label:
            label[ch] = len(label)
        out.append(label[ch])
    return ",".join(str(x) for x in out)


def orbit_size(word: str) -> int:
    """Number of words in the word's orbit under the 384-element QLF group.

    If k of the four axes occur, the stabilizer has size (4-k)! * 2^(4-k):
    unused axes may be permuted and their signs flipped freely, while used axes
    are fixed (each used axis has both signs in a balanced word).
    """
    k = len({AXIS[ch] for ch in word})
    stab = 1
    for i in range(1, 5 - k):
        stab *= i
    stab *= 2 ** (4 - k)
    return GROUP_ORDER // stab


def iter_canonical_words(length: int) -> Iterator[str]:
    """Yield every balanced canonical word of *length* exactly once.

    A canonical word uses axes 0,1,... in first-appearance order and each axis's
    first occurrence is positive.  Balance is enforced at the leaf, with a
    necessary-condition prune on the remaining number of steps.
    """
    if length <= 0 or length % 2:
        return
    plus: list[int] = []
    minus: list[int] = []
    buf: list[str] = []

    def rec(pos: int) -> Iterator[str]:
        remaining = length - pos
        if sum(abs(p - m) for p, m in zip(plus, minus)) > remaining:
            return
        if pos == length:
            if all(p == m for p, m in zip(plus, minus)):
                yield "".join(buf)
            return
        k = len(plus)
        for a in range(k):
            plus[a] += 1
            buf.append(PLUS_SYMBOL[a])
            yield from rec(pos + 1)
            buf.pop()
            plus[a] -= 1
            minus[a] += 1
            buf.append(MINUS_SYMBOL[a])
            yield from rec(pos + 1)
            buf.pop()
            minus[a] -= 1
        if k < 4:
            plus.append(1)
            minus.append(0)
            buf.append(PLUS_SYMBOL[k])
            yield from rec(pos + 1)
            buf.pop()
            plus.pop()
            minus.pop()

    yield from rec(0)


# ---------------------------------------------------------------------------
# Exact assembly indices
# ---------------------------------------------------------------------------

INF = 10**9


def _substrings(word: str) -> list[str]:
    return sorted({word[i:j] for i in range(len(word)) for j in range(i + 2, len(word) + 1)})


def _splits(substrings: Sequence[str]) -> dict[str, list[tuple[str, str]]]:
    out: dict[str, list[tuple[str, str]]] = {}
    for s in substrings:
        pairs = [(s[:k], s[k:]) for k in range(1, len(s))]
        # Balanced halves first: they tend to reach reuse early.
        pairs.sort(key=lambda uv: (abs(len(uv[0]) - len(uv[1])), -max(len(uv[0]), len(uv[1]))))
        out[s] = pairs
    return out


def assembly_index(word: str) -> int:
    """Exact ordinary assembly index: minimum joins with unrestricted reuse."""
    word = validate_word(word)
    n = len(word)
    if n <= 1:
        return 0
    subs = _substrings(word)
    splits = _splits(subs)
    best = n - 1  # linear assembly is always available

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
            if len(u) > 1 and u not in new_chosen:
                new_chosen = new_chosen | {u}
            if len(v) > 1 and v not in new_chosen:
                new_chosen = new_chosen | {v}
            if len(new_chosen) >= best:
                continue
            dfs(new_chosen, assigned | {s})

    dfs(frozenset({word}), frozenset())
    return best


def assembly_index_closed(word: str) -> int:
    """Exact assembly index when only count-balanced objects may be reused.

    Non-closed constructed objects have fan-out one; closed objects have
    unlimited fan-out.  The search is over a multiset of required objects plus
    the set of already-built closed objects.
    """
    word = validate_word(word)
    n = len(word)
    if n <= 1:
        return 0
    subs = _substrings(word)
    splits = _splits(subs)
    closed = {s for s in subs if is_closed(s)}
    memo: dict[tuple[tuple[tuple[str, int], ...], frozenset[str]], int] = {}

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
                # One copy satisfies every occurrence; the object is now reusable.
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

    return solve(Counter({word: 1}), frozenset(), n - 1)


# ---------------------------------------------------------------------------
# Baselines and descriptors
# ---------------------------------------------------------------------------

def linear_index(word: str) -> int:
    """Joins in the naive left-to-right assembly: |word| - 1."""
    return max(0, len(word) - 1)


def lz78_phrases(word: str) -> int:
    """Number of phrases in the standard longest-prefix LZ78 parse."""
    dictionary: set[str] = set()
    i = 0
    phrases = 0
    n = len(word)
    while i < n:
        j = i
        while j < n and word[i:j + 1] in dictionary:
            j += 1
        if j == n:
            phrases += 1
            break
        dictionary.add(word[i:j + 1])
        phrases += 1
        i = j + 1
    return phrases


def zlib_bytes(word: str) -> int:
    """Length in bytes of zlib's default-compression output (a generic baseline)."""
    return len(zlib.compress(word.encode("utf-8"), 9))


def distinct_substring_count(word: str) -> int:
    return len({word[i:j] for i in range(len(word)) for j in range(i + 1, len(word) + 1)})


def is_prime_closure(word: str) -> bool:
    """True if a closed word is not a concatenation of two nonempty closed words."""
    if not is_closed(word):
        return False
    for k in range(2, len(word) - 1, 2):
        if is_closed(word[:k]):
            return False
    return True


# ---------------------------------------------------------------------------
# Counting balanced words and fold classes
# ---------------------------------------------------------------------------

def balanced_word_count(length: int) -> int:
    """Number of words of *length* with zero net action on all four axes."""
    dp: dict[tuple[int, int, int, int], int] = {(0, 0, 0, 0): 1}
    for _ in range(length):
        nxt: dict[tuple[int, int, int, int], int] = defaultdict(int)
        for state, count in dp.items():
            for a in range(4):
                for s in (1, -1):
                    new = list(state)
                    new[a] += s
                    nxt[tuple(new)] += count  # type: ignore[index]
        dp = dict(nxt)
    return dp.get((0, 0, 0, 0), 0)


def fold_class_counts(length: int) -> dict[int, int]:
    """Number of balanced words of *length* in each Pauli-scalar fold class.

    State is (net action vector, Pauli phase, Pauli axis).  At the end we keep
    net = 0 and axis = I; count balance forces the axis to I, so the phase is the
    fold.  States that cannot return to the origin are pruned.
    """
    dp: dict[tuple[tuple[int, int, int, int], int, int], int] = {
        ((0, 0, 0, 0), 0, AXIS_I): 1
    }
    for step in range(length):
        remaining = length - step
        nxt: dict[tuple[tuple[int, int, int, int], int, int], int] = defaultdict(int)
        for (state, phase, axis), count in dp.items():
            if sum(abs(x) for x in state) > remaining:
                continue
            for ch in TWISTS:
                new_state = list(state)
                new_state[AXIS[ch]] += SIGN[ch]
                new_phase, new_axis = pauli_mul((phase, axis), TWIST_NF[ch])
                nxt[(tuple(new_state), new_phase, new_axis)] += count  # type: ignore[index]
        dp = dict(nxt)
    out: Counter[int] = Counter()
    for (state, phase, axis), count in dp.items():
        if state == (0, 0, 0, 0) and axis == AXIS_I:
            out[phase] += count
    return dict(out)


# ---------------------------------------------------------------------------
# Independent brute-force validators (used by --self-test and the unit tests)
# ---------------------------------------------------------------------------

def _all_available(built: frozenset[str]) -> set[str]:
    return set(TWISTS) | set(built)


def brute_force_assembly_index(word: str) -> int:
    """BFS over built-object sets: exact ordinary index for short words."""
    word = validate_word(word)
    if len(word) <= 1:
        return 0
    substrings = set(_substrings(word)) | {word}
    start: frozenset[str] = frozenset()
    frontier = {start}
    seen = {start}
    depth = 0
    while frontier:
        depth += 1
        nxt: set[frozenset[str]] = set()
        for built in frontier:
            available = _all_available(built)
            for u in available:
                for v in available:
                    joined = u + v
                    if joined not in substrings:
                        continue
                    if joined == word:
                        return depth
                    new_built = frozenset(set(built) | {joined})
                    if new_built not in seen:
                        seen.add(new_built)
                        nxt.add(new_built)
        frontier = nxt
    raise AssertionError("linear assembly should always reach the target")


def brute_force_assembly_index_closed(word: str) -> int:
    """BFS over the closure-constrained assembly process for short words.

    State: (set of built closed objects, sorted counts of built non-closed
    objects with one remaining use).  Primitives and built closed objects are
    available without limit; a non-closed object is consumed when used.
    """
    word = validate_word(word)
    if len(word) <= 1:
        return 0
    substrings = set(_substrings(word)) | {word}
    start: tuple[frozenset[str], tuple[tuple[str, int], ...]] = (frozenset(), ())
    frontier = {start}
    seen = {start}
    depth = 0
    while frontier:
        depth += 1
        nxt: set[tuple[frozenset[str], tuple[tuple[str, int], ...]]] = set()
        for closed_built, nonclosed in frontier:
            available: list[tuple[str, bool]] = [(t, True) for t in TWISTS]
            available.extend((s, True) for s in closed_built)
            available.extend((s, False) for s, c in nonclosed for _ in range(c))
            for i, (u, u_free) in enumerate(available):
                for j, (v, v_free) in enumerate(available):
                    if not u_free and not v_free and i == j:
                        continue
                    joined = u + v
                    if joined not in substrings:
                        continue
                    if joined == word:
                        return depth
                    new_closed = set(closed_built)
                    remaining = dict(nonclosed)
                    if not u_free:
                        remaining[u] -= 1
                        if remaining[u] == 0:
                            del remaining[u]
                    if not v_free:
                        remaining[v] -= 1
                        if remaining[v] == 0:
                            del remaining[v]
                    if is_closed(joined):
                        new_closed.add(joined)
                    else:
                        remaining[joined] = remaining.get(joined, 0) + 1
                    state = (frozenset(new_closed), tuple(sorted(remaining.items())))
                    if state not in seen:
                        seen.add(state)
                        nxt.add(state)
        frontier = nxt
    raise AssertionError("linear assembly should always reach the target")


# ---------------------------------------------------------------------------
# Weighted statistics
# ---------------------------------------------------------------------------

def weighted_entropy(pairs: Iterable[tuple[object, int]]) -> float:
    counts: Counter[object] = Counter()
    total = 0
    for value, weight in pairs:
        counts[value] += weight
        total += weight
    if total == 0:
        return 0.0
    return -sum((w / total) * math.log2(w / total) for w in counts.values())


def conditional_entropy(records: Sequence["Record"], target: str, *conditions: str) -> float:
    groups: dict[tuple[object, ...], list[Record]] = defaultdict(list)
    for r in records:
        groups[tuple(getattr(r, c) for c in conditions)].append(r)
    total = sum(r.weight for r in records)
    if total == 0:
        return 0.0
    return sum(
        (sum(r.weight for r in group) / total)
        * weighted_entropy((getattr(r, target), r.weight) for r in group)
        for group in groups.values()
    )


def _weighted_ranks(values: Sequence[tuple[object, int]]) -> dict[object, float]:
    weight_by_value: Counter[object] = Counter()
    for value, weight in values:
        weight_by_value[value] += weight
    ranks: dict[object, float] = {}
    cumulative = 0
    for value in sorted(weight_by_value):
        w = weight_by_value[value]
        # Average rank of the block occupying positions cumulative+1 .. cumulative+w.
        ranks[value] = cumulative + (w + 1) / 2.0
        cumulative += w
    return ranks


def weighted_spearman(records: Sequence["Record"], x: str, y: str) -> float:
    xr = _weighted_ranks([(getattr(r, x), r.weight) for r in records])
    yr = _weighted_ranks([(getattr(r, y), r.weight) for r in records])
    total = sum(r.weight for r in records)
    if total == 0:
        return 0.0
    mean_x = sum(xr[getattr(r, x)] * r.weight for r in records) / total
    mean_y = sum(yr[getattr(r, y)] * r.weight for r in records) / total
    cov = sum(
        r.weight
        * (xr[getattr(r, x)] - mean_x)
        * (yr[getattr(r, y)] - mean_y)
        for r in records
    )
    var_x = sum(r.weight * (xr[getattr(r, x)] - mean_x) ** 2 for r in records)
    var_y = sum(r.weight * (yr[getattr(r, y)] - mean_y) ** 2 for r in records)
    if var_x == 0 or var_y == 0:
        return 0.0
    return cov / math.sqrt(var_x * var_y)


# ---------------------------------------------------------------------------
# Census
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Record:
    length: int
    word: str
    weight: int
    a: int
    a_zfa: int
    lz78: int
    zlib_bytes: int
    distinct_substrings: int
    prime: bool
    fold: int | None
    fold_class_size: int


def _measure(args: tuple[int, str]) -> tuple[int, str, int, int, int, int, int, int, bool, int | None]:
    length, word = args
    return (
        length,
        word,
        orbit_size(word),
        assembly_index(word),
        assembly_index_closed(word),
        lz78_phrases(word),
        zlib_bytes(word),
        distinct_substring_count(word),
        is_prime_closure(word),
        fold(word),
    )


def build_records(max_length: int, jobs: int = 1) -> tuple[list[Record], dict[str, object]]:
    records: list[Record] = []
    validation: dict[str, object] = {"per_length": [], "totals": {}}
    for length in range(2, max_length + 1, 2):
        words = list(iter_canonical_words(length))
        args = [(length, w) for w in words]
        if jobs > 1:
            with ProcessPoolExecutor(max_workers=jobs) as pool:
                measured = list(pool.map(_measure, args, chunksize=64))
        else:
            measured = [_measure(a) for a in args]
        fold_counts = fold_class_counts(length)
        for (n, word, weight, a, az, lz, zb, ds, prime, ph) in measured:
            records.append(
                Record(
                    length=n,
                    word=word,
                    weight=weight,
                    a=a,
                    a_zfa=az,
                    lz78=lz,
                    zlib_bytes=zb,
                    distinct_substrings=ds,
                    prime=prime,
                    fold=ph,
                    fold_class_size=fold_counts.get(ph, 0) if ph is not None else 0,
                )
            )
        expected = balanced_word_count(length)
        observed = sum(r.weight for r in records if r.length == length)
        if observed != expected:
            raise AssertionError(
                f"length {length}: canonical orbit weights sum to {observed}, "
                f"expected {expected}"
            )
        validation["per_length"].append(  # type: ignore[union-attr]
            {
                "length": length,
                "balanced_words": expected,
                "canonical_classes": len(words),
                "orbit_weight_sum": observed,
                "fold_classes": {str(k): v for k, v in sorted(fold_counts.items())},
            }
        )
    validation["totals"] = {
        "balanced_words": sum(r.weight for r in records),
        "canonical_classes": len(records),
        "lengths": list(range(2, max_length + 1, 2)),
    }
    return records, validation


def _distribution(records: Sequence[Record], field: str) -> dict[str, int]:
    out: Counter[int] = Counter()
    for r in records:
        out[getattr(r, field)] += r.weight
    return {str(k): v for k, v in sorted(out.items())}


def _bucket_variation(
    records: Sequence[Record], target: str, *conditions: str
) -> dict[str, object]:
    groups: dict[tuple[object, ...], Counter[int]] = defaultdict(Counter)
    for r in records:
        groups[tuple(getattr(r, c) for c in conditions)][getattr(r, target)] += r.weight
    total = sum(r.weight for r in records)
    mixed = {k: v for k, v in groups.items() if len(v) > 1}
    mixed_weight = sum(sum(v.values()) for v in mixed.values())
    return {
        "buckets": len(groups),
        "mixed_buckets": len(mixed),
        "mixed_weight_fraction": mixed_weight / total if total else 0.0,
        "max_values_in_bucket": max((len(v) for v in groups.values()), default=0),
    }


def _examples(records: Sequence[Record]) -> list[dict[str, object]]:
    examples: list[dict[str, object]] = []

    def add(label: str, r: Record) -> None:
        examples.append(
            {
                "label": label,
                "length": r.length,
                "word": r.word,
                "weight": r.weight,
                "a": r.a,
                "a_zfa": r.a_zfa,
                "gap": r.a_zfa - r.a,
                "lz78": r.lz78,
            }
        )

    gapped = [r for r in records if r.a_zfa > r.a]
    if gapped:
        add("smallest word with a_ZFA > a", min(gapped, key=lambda r: (r.length, r.word)))
        add("largest gap", max(gapped, key=lambda r: (r.a_zfa - r.a, -r.length)))
        deepest = max(r.length for r in gapped)
        add(
            "largest gap at maximum length",
            max((r for r in gapped if r.length == deepest), key=lambda r: (r.a_zfa - r.a, r.word)),
        )

    # A same-length, same-LZ78 pair with different ordinary indices.
    by_key: dict[tuple[int, int], list[Record]] = defaultdict(list)
    for r in records:
        by_key[(r.length, r.lz78)].append(r)
    for key in sorted(by_key):
        group = by_key[key]
        vals = {r.a for r in group}
        if len(vals) > 1:
            group = sorted(group, key=lambda r: (r.a, r.word))
            add(f"same length/LZ78, different a (n={key[0]}, lz78={key[1]})", group[0])
            add(f"same length/LZ78, different a (n={key[0]}, lz78={key[1]})", group[-1])
            break

    # A same-length, same-a pair with different closure-constrained indices.
    by_key2: dict[tuple[int, int], list[Record]] = defaultdict(list)
    for r in records:
        by_key2[(r.length, r.a)].append(r)
    for key in sorted(by_key2):
        group = by_key2[key]
        vals = {r.a_zfa for r in group}
        if len(vals) > 1:
            group = sorted(group, key=lambda r: (r.a_zfa, r.word))
            add(f"same length/a, different a_ZFA (n={key[0]}, a={key[1]})", group[0])
            add(f"same length/a, different a_ZFA (n={key[0]}, a={key[1]})", group[-1])
            break
    return examples


def census(max_length: int = 10, jobs: int = 1) -> dict[str, object]:
    records, validation = build_records(max_length, jobs)
    lengths = list(range(2, max_length + 1, 2))

    per_length: list[dict[str, object]] = []
    for n in lengths:
        group = [r for r in records if r.length == n]
        total = sum(r.weight for r in group)
        gaps = [r.a_zfa - r.a for r in group]
        per_length.append(
            {
                "length": n,
                "balanced_words": total,
                "canonical_classes": len(group),
                "mean_a": sum(r.a * r.weight for r in group) / total,
                "mean_a_zfa": sum(r.a_zfa * r.weight for r in group) / total,
                "max_a": max(r.a for r in group),
                "max_a_zfa": max(r.a_zfa for r in group),
                "words_with_gap": sum(r.weight for r in group if r.a_zfa > r.a),
                "max_gap": max(gaps),
                "prime_words": sum(r.weight for r in group if r.prime),
                "a_distribution": _distribution(group, "a"),
                "a_zfa_distribution": _distribution(group, "a_zfa"),
                "gap_distribution": {str(k): sum(r.weight for r in group if r.a_zfa - r.a == k) for k in range(max(gaps) + 1)},
            }
        )

    entropy = {
        "H_a": weighted_entropy((r.a, r.weight) for r in records),
        "H_a_given_length": conditional_entropy(records, "a", "length"),
        "H_a_given_length_lz78": conditional_entropy(records, "a", "length", "lz78"),
        "H_a_given_length_zlib": conditional_entropy(records, "a", "length", "zlib_bytes"),
        "H_a_zfa": weighted_entropy((r.a_zfa, r.weight) for r in records),
        "H_a_zfa_given_length": conditional_entropy(records, "a_zfa", "length"),
        "H_a_zfa_given_length_a": conditional_entropy(records, "a_zfa", "length", "a"),
        "H_a_zfa_given_length_a_lz78": conditional_entropy(
            records, "a_zfa", "length", "a", "lz78"
        ),
        "H_a_zfa_given_length_a_zlib": conditional_entropy(
            records, "a_zfa", "length", "a", "zlib_bytes"
        ),
        "H_a_zfa_given_length_a_lz78_zlib": conditional_entropy(
            records, "a_zfa", "length", "a", "lz78", "zlib_bytes"
        ),
        "H_a_zfa_given_length_lz78": conditional_entropy(
            records, "a_zfa", "length", "lz78"
        ),
    }
    variation = {
        "a_given_length_lz78": _bucket_variation(records, "a", "length", "lz78"),
        "a_given_length_zlib": _bucket_variation(records, "a", "length", "zlib_bytes"),
        "a_zfa_given_length_a": _bucket_variation(records, "a_zfa", "length", "a"),
        "a_zfa_given_length_a_lz78": _bucket_variation(
            records, "a_zfa", "length", "a", "lz78"
        ),
        "a_zfa_given_length_a_zlib": _bucket_variation(
            records, "a_zfa", "length", "a", "zlib_bytes"
        ),
        "a_zfa_given_length_a_lz78_zlib": _bucket_variation(
            records, "a_zfa", "length", "a", "lz78", "zlib_bytes"
        ),
        "a_zfa_given_length_lz78": _bucket_variation(
            records, "a_zfa", "length", "lz78"
        ),
    }
    correlations = {
        f"spearman_{x}_{y}": weighted_spearman(records, x, y)
        for x, y in (
            ("a", "a_zfa"),
            ("a", "lz78"),
            ("a", "zlib_bytes"),
            ("a_zfa", "lz78"),
            ("a_zfa", "zlib_bytes"),
            ("a", "length"),
            ("a_zfa", "length"),
            ("a", "distinct_substrings"),
            ("a_zfa", "distinct_substrings"),
        )
    }
    fold_table = {
        str(item["length"]): item["fold_classes"]  # type: ignore[index]
        for item in validation["per_length"]  # type: ignore[union-attr]
    }
    return {
        "meta": {
            "generator": "assembly_index.py",
            "version": 1,
            "max_length": max_length,
            "object_semantics": (
                "raw twist words over ^ v < > / \\ + -; primitives are the eight "
                "single twists; a join is concatenation; previously constructed "
                "objects may be reused"
            ),
            "ordinary_index": "minimum joins, unrestricted reuse (SLP size)",
            "closure_constrained_index": (
                "minimum joins; only count-balanced objects have unlimited reuse; "
                "non-closed objects have fan-out one"
            ),
            "symmetry_group_order": GROUP_ORDER,
        },
        "validation": validation,
        "per_length": per_length,
        "entropy_bits": entropy,
        "conditional_variation": variation,
        "correlations": correlations,
        "fold_classes": fold_table,
        "examples": _examples(records),
        "distributions": {
            "a": _distribution(records, "a"),
            "a_zfa": _distribution(records, "a_zfa"),
            "gap": {
                str(k): sum(r.weight for r in records if r.a_zfa - r.a == k)
                for k in range(max(r.a_zfa - r.a for r in records) + 1)
            },
        },
    }


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

def _assert_example(word: str, ordinary: int, closed: int) -> None:
    got_a = assembly_index(word)
    got_az = assembly_index_closed(word)
    if (got_a, got_az) != (ordinary, closed):
        raise AssertionError(
            f"{word!r}: expected a={ordinary}, a_ZFA={closed}; got {got_a}, {got_az}"
        )


def self_test() -> None:
    # Known small values.
    _assert_example("<>", 1, 1)
    _assert_example("^v^v", 2, 2)
    _assert_example("<><>", 2, 2)
    _assert_example("^^^^", 2, 3)
    _assert_example("^^^^vvvv", 5, 7)

    # Brute-force cross-checks on every canonical class through length 4.
    for n in (2, 4):
        for word in iter_canonical_words(n):
            bf_a = brute_force_assembly_index(word)
            bf_az = brute_force_assembly_index_closed(word)
            if assembly_index(word) != bf_a:
                raise AssertionError(f"{word!r}: ordinary {assembly_index(word)} != brute {bf_a}")
            if assembly_index_closed(word) != bf_az:
                raise AssertionError(f"{word!r}: closed {assembly_index_closed(word)} != brute {bf_az}")

    # Ordinary brute force on all canonical classes through length 6.
    for word in iter_canonical_words(6):
        if assembly_index(word) != brute_force_assembly_index(word):
            raise AssertionError(f"{word!r}: ordinary mismatch at length 6")

    # Canonical enumeration and orbit weights.
    for n in (2, 4, 6, 8):
        weights = sum(orbit_size(w) for w in iter_canonical_words(n))
        if weights != balanced_word_count(n):
            raise AssertionError(f"length {n}: orbit weights {weights} != {balanced_word_count(n)}")

    # Fold classes partition the balanced words.
    for n in (2, 4, 6):
        if sum(fold_class_counts(n).values()) != balanced_word_count(n):
            raise AssertionError(f"length {n}: fold classes do not partition the census")

    # Invariants on examples.
    for word in ("<>", "^v^v", "^^^^", "^^^^vvvv", "^v<>"):
        a, az = assembly_index(word), assembly_index_closed(word)
        if not (a <= az <= len(word) - 1):
            raise AssertionError(f"{word!r}: expected a <= a_ZFA <= n-1, got {a}, {az}")

    print("self-test: OK")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _print_word(word: str) -> None:
    a = assembly_index(word)
    az = assembly_index_closed(word)
    print(f"word              {word!r}")
    print(f"length            {len(word)}")
    print(f"net               {net(word)}")
    print(f"count-balanced    {is_closed(word)}")
    print(f"fold              {fold(word)}")
    print(f"a (ordinary)      {a}")
    print(f"a_ZFA             {az}")
    print(f"linear upper      {linear_index(word)}")
    print(f"LZ78 phrases      {lz78_phrases(word)}")
    print(f"zlib bytes        {zlib_bytes(word)}")
    print(f"prime closure     {is_prime_closure(word)}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--word", action="append", help="inspect one word (repeatable)")
    parser.add_argument(
        "--max-length",
        type=int,
        default=10,
        help="largest even length in the exhaustive canonical census (default 10)",
    )
    parser.add_argument("--jobs", type=int, default=1, help="worker processes for the census")
    parser.add_argument("--json", type=Path, help="write the census summary to this path")
    parser.add_argument("--self-test", action="store_true", help="run brute-force cross-checks")
    args = parser.parse_args(argv)

    if args.self_test:
        self_test()
        if not args.word and not args.json:
            return 0

    if args.word:
        for word in args.word:
            _print_word(validate_word(word))
        if not args.json:
            return 0

    if args.max_length < 2 or args.max_length % 2:
        parser.error("--max-length must be an even integer >= 2")

    summary = census(args.max_length, max(1, args.jobs))
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote {args.json}")

    totals = summary["validation"]["totals"]  # type: ignore[index]
    print(json.dumps(
        {
            "lengths": totals["lengths"],
            "balanced_words": totals["balanced_words"],
            "canonical_classes": totals["canonical_classes"],
            "entropy_bits": summary["entropy_bits"],
            "conditional_variation": summary["conditional_variation"],
            "examples": summary["examples"],
        },
        indent=2,
        sort_keys=True,
    ))
    return 0


if __name__ == "__main__":
    sys.exit(main())
