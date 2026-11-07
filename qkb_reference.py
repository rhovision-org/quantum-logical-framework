"""
qkb_reference.py — executable specification of the quantum logical knowledge base (QKB).

The Rholang contract `rholang/QKB.rho` is the deployable form; this file is the
same semantics in Python, so every rule the contract enforces can be checked
against the repo's canonical engines (`twist_core.py`, `qucalc_search.py`)
without a node. Design and rationale: Quantum_Knowledge_Base.md.

Run `python3 qkb_reference.py` to execute the self-checks (seconds).

Encoding: twists are the integers 0..7 that rholo's `rho:qucalc:*` natives use
    0 ^   1 v   2 >   3 <   4 /   5 \\   6 +   7 -
so axis(t) = t // 2 (0 = y, 1 = x, 2 = z, 3 = gauge) and sign(t) = + iff t is even.
(Note: twist_core.TWISTS orders x as '<','>' — indices 2 and 3 are swapped
relative to rholo. Only the symbol mapping below is used, so nothing depends on it.)

Five layers, one store:
  1. closures  — a record is admitted only if it is a ZFA closure (per-axis count
                 balance; Pauli closure then follows by `count_balanced_pauli_closed`).
  2. ways      — a concept (name) is the set of distinct closures filed under it;
                 its size is the concept's multiplicity (frequency IS multiplicity).
  3. records   — each closure carries the set of independent attesters that hold
                 it; that count is its redundancy R (Memetics_QLF.md §5: a closure
                 is a meme to the degree its record is held by third parties).
  4. questions — an open strand (seed) asked in a context; answers are
                 continuations that close it; `solve` picks the first closure by
                 the same cascade as qucalc_search.solve.
  5. logic     — propositions are (context, sign) atoms of the orthomodular
                 lattice MO3 over the three spatial axes; the gauge axis is a
                 classical (Boolean) block. Compatibility is computed from the
                 Pauli fold, not declared.
"""
from __future__ import annotations

import hashlib
import itertools
from dataclasses import dataclass, field
from typing import Optional

from twist_core import pauli_fold

SYMBOLS = "^v></\\+-"          # rholo integer t -> symbol SYMBOLS[t]
AXES = ("y", "x", "z", "g")    # axis index 0..3
MIN_LEN = 4                    # length-2 closures t t† all fold to -I: no bit to record
PHASE_RANK = {"+1": 0, "-1": 1, "+i": 2, "-i": 3}   # qucalc_search._PHASE_RANK


# --------------------------------------------------------------------------- #
# 1. the closure gate
# --------------------------------------------------------------------------- #
def to_str(ts: list[int]) -> str:
    return "".join(SYMBOLS[t] for t in ts)


def from_str(s: str) -> list[int]:
    return [SYMBOLS.index(c) for c in s]


def action(ts: list[int]) -> tuple[int, int, int, int]:
    """Signed action vector per axis (y, x, z, g)."""
    v = [0, 0, 0, 0]
    for t in ts:
        v[t // 2] += 1 if t % 2 == 0 else -1
    return tuple(v)


def phase(ts: list[int]) -> Optional[str]:
    """'+1' / '-1' / '+i' / '-i' if the Pauli fold is a scalar, else None."""
    a, b, c, d = pauli_fold(to_str(ts))
    if abs(b) > 1e-9 or abs(c) > 1e-9 or abs(a - d) > 1e-9:
        return None
    for z, name in ((1, "+1"), (-1, "-1"), (1j, "+i"), (-1j, "-i")):
        if abs(a - z) < 1e-9:
            return name
    return None


def is_closure(ts: list[int]) -> bool:
    """The KB's admission rule: per-axis count balance, length >= MIN_LEN.
    Pauli closure is entailed (count_balanced_pauli_closed) and asserted in self-check."""
    return len(ts) >= MIN_LEN and action(ts) == (0, 0, 0, 0)


def rholo_native_zfa(ts: list[int]) -> bool:
    """What rholo's `rho:qucalc:zfa` accepts today (qucalc/src/lib.rs `achieves_zfa`):
    Pauli-closed AND #even == #odd. The aggregate count is weaker than per-axis
    balance, so the contract must not use this bit as its gate."""
    pos = sum(1 for t in ts if t % 2 == 0)
    return phase(ts) is not None and pos == len(ts) - pos


def excursion(ts: list[int]) -> int:
    """Max over prefixes of |v|+|h|+|d|+|l| (qucalc_search.max_excursion)."""
    v = [0, 0, 0, 0]
    m = 0
    for t in ts:
        v[t // 2] += 1 if t % 2 == 0 else -1
        m = max(m, sum(abs(x) for x in v))
    return m


def content_id(ts: list[int]) -> str:
    """Content address: blake2b-256 of the twist bytes, as rho:qucalc:grant hashes
    them. (rholo wraps the digest into a registry uri; the digest is what matters:
    the same closure from two attesters lands on the same record.)"""
    return hashlib.blake2b(bytes(ts), digest_size=32).hexdigest()


# --------------------------------------------------------------------------- #
# 5. the logic layer: MO3 over spatial contexts, gauge classical
# --------------------------------------------------------------------------- #
BOT, TOP = "bot", "top"
Prop = object   # BOT | TOP | (axis:int, sign:int)


def compl(p):
    if p == BOT:
        return TOP
    if p == TOP:
        return BOT
    a, s = p
    return (a, -s)


def le(p, q) -> bool:
    return p == BOT or q == TOP or p == q


def meet(p, q):
    if p == TOP:
        return q
    if q == TOP:
        return p
    return p if p == q else BOT


def join(p, q):
    if p == BOT:
        return q
    if q == BOT:
        return p
    return p if p == q else TOP


def commute(a: int, b: int) -> bool:
    """Do the axis-a and axis-b twists commute? Read off the plaquette
    a b a† b† (a closure): its fold is +I iff they commute, -I (π flux,
    Closure_Walk.md) iff they anticommute. This is what the contract computes
    with one rho:qucalc:zfa call."""
    return phase([2 * a, 2 * b, 2 * a + 1, 2 * b + 1]) == "+1"


def commute_matrix(a: int, b: int) -> bool:
    """Independent check: compare the two orders of the 2x2 product directly."""
    return pauli_fold(SYMBOLS[2 * a] + SYMBOLS[2 * b]) == pauli_fold(SYMBOLS[2 * b] + SYMBOLS[2 * a])


def compatible(p, q) -> bool:
    if p in (BOT, TOP) or q in (BOT, TOP):
        return True
    return commute(p[0], q[0])


def conjoin(p, q):
    """Conjunction the KB will actually assert. Same-context atoms use the
    lattice meet; incompatible atoms are refused (None), never silently ⊥ —
    a client must not read 'incompatible' as 'contradictory'. A gauge atom is
    compatible with everything, so its conjunction is the classical pair."""
    if not compatible(p, q):
        return None
    if p in (BOT, TOP) or q in (BOT, TOP) or p[0] == q[0]:
        return meet(p, q)
    return ("and", p, q)        # commuting, different blocks: Boolean product


SPATIAL_ATOMS = [(a, s) for a in range(3) for s in (1, -1)]
MO3 = [BOT, TOP] + SPATIAL_ATOMS


# --------------------------------------------------------------------------- #
# 2–4. the store
# --------------------------------------------------------------------------- #
@dataclass
class Record:
    twists: list[int]
    phase: str
    excursion: int
    attesters: set = field(default_factory=set)


@dataclass
class Question:
    seed: list[int]
    context: int
    answers: set = field(default_factory=set)     # content ids of closed histories


class KB:
    def __init__(self) -> None:
        self.records: dict[str, Record] = {}
        self.names: dict[str, set[str]] = {}
        self.questions: dict[str, Question] = {}

    # -- layer 1–3 ----------------------------------------------------------
    def assert_closure(self, name: str, ts: list[int], attester) -> dict:
        if not is_closure(ts):
            return {"ok": False, "residual": tuple(-x for x in action(ts))}
        cid = content_id(ts)
        rec = self.records.get(cid)
        if rec is None:
            rec = self.records[cid] = Record(list(ts), phase(ts), excursion(ts))
        rec.attesters.add(attester)
        self.names.setdefault(name, set()).add(cid)
        return {"ok": True, "id": cid, "ways": len(self.names[name]),
                "redundancy": len(rec.attesters)}

    def ways(self, name: str) -> int:
        return len(self.names.get(name, ()))

    def redundancy(self, cid: str) -> int:
        r = self.records.get(cid)
        return len(r.attesters) if r else 0

    def _cascade(self, cids):
        def key(c):
            r = self.records[c]
            return (r.excursion, len(r.twists), PHASE_RANK[r.phase], to_str(r.twists))
        return sorted(cids, key=key)

    def first(self, name: str) -> Optional[str]:
        """Priority: the closure reached first (least excursion → shortest → phase → lex)."""
        c = self._cascade(self.names.get(name, ()))
        return c[0] if c else None

    def most_held(self, name: str) -> Optional[str]:
        """The closure under `name` held by the most attesters (a different statistic)."""
        c = self.names.get(name)
        if not c:
            return None
        return max(sorted(c), key=lambda x: len(self.records[x].attesters))

    # -- layer 4 ------------------------------------------------------------
    def ask(self, q: str, seed: list[int], context: int) -> dict:
        self.questions[q] = Question(list(seed), context)
        return {"residual": tuple(-x for x in action(seed))}

    def answer(self, q: str, cont: list[int], attester) -> dict:
        qq = self.questions[q]
        res = self.assert_closure(q, qq.seed + cont, attester)
        if res["ok"]:
            qq.answers.add(res["id"])
        return res

    def solve(self, q: str) -> Optional[list[int]]:
        """The continuation of the first-reached recorded closure.

        No prefix-freeness filter is needed: if a recorded answer's continuation
        has a recorded closing prefix, that prefix has excursion <= and length <,
        so the cascade already ranks it first. The minimum over all answers is
        the minimum over events (qucalc_search mode=events)."""
        qq = self.questions[q]
        best = self._cascade(qq.answers)
        return self.records[best[0]].twists[len(qq.seed):] if best else None


# --------------------------------------------------------------------------- #
# self-checks — each one is a check the construction could fail
# --------------------------------------------------------------------------- #
def _selfcheck() -> None:
    import qucalc_search as qs

    # (a) gate: every per-axis-balanced history of length 4 is Pauli-closed
    #     (count_balanced_pauli_closed), so the gate never admits a non-scalar fold.
    n_bal = 0
    for ts in itertools.product(range(8), repeat=4):
        if is_closure(list(ts)):
            n_bal += 1
            assert phase(list(ts)) in ("+1", "-1"), ts
    assert n_bal == 168, n_bal              # Fredkin_QLF.md: 168 of 4096 close
    print(f"(a) gate: {n_bal}/4096 length-4 histories admitted, all fold to ±I")

    # (b) the native rholo bit admits histories the gate rejects
    weak = [ts for ts in itertools.product(range(8), repeat=4)
            if rholo_native_zfa(list(ts)) and not is_closure(list(ts))]
    assert [0, 0, 3, 3] in [list(w) for w in weak]           # ^^<< : y=+2, x=-2
    print(f"(b) rho:qucalc:zfa over-admits {len(weak)} length-4 histories, e.g. "
          f"{to_str([0, 0, 3, 3])} with action {action([0, 0, 3, 3])}")

    # (c) logic: MO3 is orthomodular and NOT distributive; incompatibility is the fold's.
    for p, q in itertools.product(MO3, repeat=2):
        if le(p, q):
            assert q == join(p, meet(compl(p), q)), (p, q)
        assert meet(p, compl(p)) == BOT and join(p, compl(p)) == TOP
    bad = [(p, q, r) for p, q, r in itertools.product(MO3, repeat=3)
           if meet(p, join(q, r)) != join(meet(p, q), meet(p, r))]
    assert bad
    assert [commute(a, b) for a in range(3) for b in range(3) if a != b] == [False] * 6
    assert all(commute(3, b) for b in range(4))
    assert all(commute(a, b) == commute_matrix(a, b) for a in range(4) for b in range(4))
    print(f"(c) MO3 orthomodular; {len(bad)} distributivity failures; "
          f"spatial axes pairwise non-commuting, gauge commutes with all (read from the fold)")
    assert conjoin((0, 1), (1, 1)) is None
    assert conjoin((0, 1), (3, 1)) == ("and", (0, 1), (3, 1))

    # (d) ways and redundancy are different statistics
    kb = KB()
    alice, bob, carol = object(), object(), object()
    r1 = kb.assert_closure("plaquette", from_str("^<v>"), alice)
    kb.assert_closure("plaquette", from_str("^<v>"), bob)      # same closure, new holder
    kb.assert_closure("plaquette", from_str("^>v<"), carol)    # a second way
    assert kb.ways("plaquette") == 2 and kb.redundancy(r1["id"]) == 2
    assert kb.most_held("plaquette") == r1["id"]
    assert not kb.assert_closure("bad", from_str("^^<<"), alice)["ok"]
    print("(d) ways=2 (two closures), redundancy=2 (two holders of one), ^^<< refused")

    # (e) solve agrees with qucalc_search.solve when every short event is recorded
    for seed in ["^", "^>", "+^", "^<", "/+"]:
        kb2 = KB()
        kb2.ask("q", from_str(seed), context=0)
        for rec in qs.search(seed, max_depth=5, limit=None, absorbing=False):
            kb2.answer("q", from_str(rec["cont"]), alice)
        ref = qs.solve(seed, max_depth=4)
        got = kb2.solve("q")
        assert ref["solved"] and to_str(got) == ref["cont"], (seed, got, ref["cont"])
    print("(e) solve over all possibilities (non-events included) matches qucalc_search.solve on 5 seeds")
    print("all self-checks passed")


if __name__ == "__main__":
    _selfcheck()
