"""
qkb_reference.py — executable specification of the quantum logical knowledge base (QKB).

The Rholang contract `rholang/QKB.rho` is the deployable form; this file is the
same semantics in Python, so every rule the contract enforces can be checked
against the repo's canonical engines (`twist_core.py`, `qucalc_search.py`)
without a node. The contract has also been parsed and executed on an isolated
rnode; that evidence is in `verification/qkb/rholo_acceptance.md`. Design and
rationale: Quantum_Knowledge_Base.md.

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
MAX_LEN = 64                   # bound on any submitted history (seed ++ continuation)
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


def valid_twists(ts) -> bool:
    """Fail closed: a list of plain ints in 0..7, at most MAX_LEN long.
    (bool is excluded explicitly: Python's True is an int, Rholang's is not.)"""
    return (isinstance(ts, list) and len(ts) <= MAX_LEN
            and all(type(t) is int and 0 <= t <= 7 for t in ts))


def question_id(seed: list[int], context: int) -> tuple:
    """A question IS its (seed, context): content-addressed, so re-asking it is a
    no-op and no two parties can bind one id to different questions. The contract
    uses the pair itself as the map key."""
    return (tuple(seed), context)


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


def _atom(p) -> bool:
    return (isinstance(p, tuple) and len(p) == 2
            and type(p[0]) is int and 0 <= p[0] <= 3
            and type(p[1]) is int and p[1] in (1, -1))


def valid_prop(p) -> bool:
    """'bot', 'top', an atom (axis, sign) with axis an int in 0..3 and sign in
    {1, -1}, or a conjunction ("and", spatial atom, gauge atom), which is what
    conjoin returns for two compatible atoms in different blocks. Checked before
    any native call: an axis of 4 would build twist 8."""
    if p in (BOT, TOP) or _atom(p):
        return True
    return (isinstance(p, tuple) and len(p) == 3 and p[0] == "and"
            and _atom(p[1]) and p[1][0] < 3 and _atom(p[2]) and p[2][0] == 3)


def _parts(p):
    """A valid proposition as (spatial part, gauge part), each BOT/TOP/atom.
    The lattice is MO3 (spatial) smashed with the gauge Boolean block: the
    gauge twists are ±I, so they commute with everything, and a conjunction
    with either part ⊥ is ⊥."""
    if p in (BOT, TOP):
        return (p, p)
    if p[0] == "and":
        return (p[1], p[2])
    return (TOP, p) if p[0] == 3 else (p, TOP)


def _from_parts(sp, g):
    if BOT in (sp, g):
        return BOT
    if g == TOP:
        return sp
    if sp == TOP:
        return g
    return ("and", sp, g)


def compatible(p, q) -> Optional[bool]:
    """True / False, or None for a malformed proposition (the contract answers
    "invalid proposition"). Only the spatial parts can clash."""
    if not (valid_prop(p) and valid_prop(q)):
        return None
    a, b = _parts(p)[0], _parts(q)[0]
    if a in (BOT, TOP) or b in (BOT, TOP):
        return True
    return commute(a[0], b[0])


def conjoin(p, q):
    """Conjunction the KB will actually assert, closed under its own output:
    every result is again a valid proposition. Incompatible spatial atoms are
    refused ("incompatible"), never silently ⊥ — a client must not read
    'incompatible' as 'contradictory'. Otherwise the meet is taken part by part."""
    c = compatible(p, q)
    if c is None:
        return "invalid proposition"
    if not c:
        return "incompatible"
    (s1, g1), (s2, g2) = _parts(p), _parts(q)
    return _from_parts(meet(s1, s2), meet(g1, g2))


SPATIAL_ATOMS = [(a, s) for a in range(3) for s in (1, -1)]
MO3 = [BOT, TOP] + SPATIAL_ATOMS


# --------------------------------------------------------------------------- #
# 2–4. the store
# --------------------------------------------------------------------------- #
class DeployerId:
    """Model of rho:rchain:deployerId: an unforgeable name that the node binds to
    the deploy's verified secp256k1 key. Client code cannot construct one; a
    fresh `new` name is a different kind of name."""
    __slots__ = ("_pk",)

    def __init__(self, pk: bytes) -> None:
        self._pk = pk


def pub_key_bytes(attester) -> Optional[bytes]:
    """rho:rchain:deployerId:ops "pubKeyBytes": the signing key of a genuine
    deployerId, Nil for any other name. Attester sets hold these keys, so R
    counts distinct signing keys. (One person holding many funded keys is a
    Sybil question that no contract can settle; see the design doc §3a.)"""
    return attester._pk if isinstance(attester, DeployerId) else None


@dataclass
class Record:
    twists: list[int]
    phase: str
    excursion: int
    attesters: set = field(default_factory=set)


def valid_question(q) -> bool:
    return (isinstance(q, tuple) and len(q) == 2 and isinstance(q[0], tuple)
            and valid_twists(list(q[0])) and type(q[1]) is int and 0 <= q[1] <= 3)


class KB:
    def __init__(self) -> None:
        self.records: dict[str, Record] = {}
        self.names: dict[str, set[str]] = {}
        self.asked: set = set()                      # questions registered by ask
        self.answers: dict[tuple, set[str]] = {}     # q -> ids; never mixed with names

    # -- layer 1–3 ----------------------------------------------------------
    def _admit(self, ts, attester) -> dict:
        """Gate + record + attester, without filing under any name."""
        if not valid_twists(ts):
            return {"ok": False, "error": "invalid twists"}
        pk = pub_key_bytes(attester)
        if pk is None:
            return {"ok": False, "error": "attester is not a deployerId"}
        if not is_closure(ts):
            return {"ok": False, "residual": tuple(-x for x in action(ts))}
        cid = content_id(ts)
        rec = self.records.get(cid)
        if rec is None:
            rec = self.records[cid] = Record(list(ts), phase(ts), excursion(ts))
        rec.attesters.add(pk)
        return {"ok": True, "id": cid, "redundancy": len(rec.attesters)}

    def assert_closure(self, name: str, ts: list[int], attester) -> dict:
        res = self._admit(ts, attester)
        if res["ok"]:
            self.names.setdefault(name, set()).add(res["id"])
            res["ways"] = len(self.names[name])
        return res

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
    def ask(self, seed: list[int], context: int) -> dict:
        """Grow-only: the id is the question's content, so a replayed ask finds
        the same entry and leaves its answers alone."""
        q = (tuple(seed), context) if isinstance(seed, list) else None
        if q is None or not valid_question(q):
            return {"ok": False, "error": "invalid question"}
        self.asked.add(q)
        return {"ok": True, "q": q, "residual": tuple(-x for x in action(seed))}

    def answer(self, q, cont: list[int], attester) -> dict:
        """A question is its content, so any well-formed q can be answered,
        before or after it is asked: the answer is checked against q's own seed.
        That keeps answers order-independent across shards (ask registers q
        for listing; it is not a precondition)."""
        if not valid_question(q):
            return {"ok": False, "error": "invalid question"}
        if not valid_twists(cont):
            return {"ok": False, "error": "invalid twists"}
        res = self._admit(list(q[0]) + cont, attester)
        if res["ok"]:
            self.answers.setdefault(q, set()).add(res["id"])
        return res

    def solve(self, q) -> Optional[list[int]]:
        """The continuation of the first-reached recorded answer.

        No prefix-freeness filter is needed: if a recorded answer's continuation
        has a recorded closing prefix, that prefix has excursion <= and length <,
        so the cascade already ranks it first. The minimum over all answers is
        the minimum over events (qucalc_search mode=events)."""
        if not valid_question(q):
            return None
        best = self._cascade(self.answers.get(q, ()))
        return self.records[best[0]].twists[len(q[0]):] if best else None


# --------------------------------------------------------------------------- #
# sharding: two roles, grow-only state, no cross-shard transaction
# --------------------------------------------------------------------------- #
def cascade_key(ts: list[int]) -> tuple:
    """The /solve total order, computable from the closure alone."""
    return (excursion(ts), len(ts), PHASE_RANK[phase(ts)], to_str(ts))


def shard_of(key, k: int) -> int:
    key = key if isinstance(key, str) else repr(key)
    return int(hashlib.blake2b(key.encode(), digest_size=8).hexdigest(), 16) % k


class RecordShard:
    """Holds closures by content id: id -> (twists, attesters). Grow-only."""
    def __init__(self) -> None:
        self.recs: dict[str, tuple[list[int], set]] = {}

    def put(self, cid: str, ts: list[int], attester) -> None:      # idempotent
        self.recs.setdefault(cid, (list(ts), set()))[1].add(attester)


class IndexShard:
    """Holds name -> {(cascade_key, id)} and question -> seed. Grow-only.
    Carrying the key beside the id makes ways / first / solve local to one shard."""
    def __init__(self) -> None:
        self.names: dict[str, set] = {}
        self.answers: dict[tuple, set] = {}          # separate from names
        self.asked: set = set()

    def put(self, name: str, key: tuple, cid: str) -> None:        # idempotent
        self.names.setdefault(name, set()).add((key, cid))

    def put_answer(self, q: tuple, key: tuple, cid: str) -> None:  # idempotent
        self.answers.setdefault(q, set()).add((key, cid))


class ShardedKB:
    """k record shards (by content id) + k index shards (by name).

    A write is two idempotent legs, record first, then index. Every piece of
    state is a grow-only set, so legs commute, re-delivery is harmless, and
    shards never need to agree on an order (no 2PC). A crash between the legs
    leaves an orphan record (held, unnamed), never a dangling name: the index
    only ever points at a record that already exists. (Delivered out of order,
    an index entry can briefly precede its record; ways / first / solve read
    the index alone, so only redundancy waits for the record leg.)"""
    def __init__(self, k: int) -> None:
        self.k = k
        self.rec = [RecordShard() for _ in range(k)]
        self.idx = [IndexShard() for _ in range(k)]

    # legs, exposed separately so a test can deliver them in any order, twice
    def _record_leg(self, ts, attester):
        """Snapshot first, then validate, address and key the snapshot. Both legs
        capture only these fixed values, so mutating the caller's list after the
        legs are built (before delivery, or between them) cannot change what is
        stored. (In Rholang every value is immutable, so the contract cannot
        hit this; a client library in a mutable language can.)"""
        if not isinstance(ts, list):
            return None
        snap = tuple(ts)
        pk = pub_key_bytes(attester)
        if not valid_twists(list(snap)) or pk is None or not is_closure(list(snap)):
            return None                                           # stateless gate
        cid, key = content_id(list(snap)), cascade_key(list(snap))
        r = self.rec[shard_of(cid, self.k)]
        return cid, key, (lambda: r.put(cid, list(snap), pk))

    def legs(self, name, ts: list[int], attester):
        got = self._record_leg(ts, attester)
        if got is None:
            return []
        cid, key, leg = got
        i = self.idx[shard_of(name, self.k)]
        return [leg, lambda: i.put(name, key, cid)]

    def assert_closure(self, name, ts, attester) -> None:
        for leg in self.legs(name, ts, attester):
            leg()

    def ways(self, name: str) -> int:
        return len(self.idx[shard_of(name, self.k)].names.get(name, ()))

    def redundancy(self, cid: str) -> int:
        r = self.rec[shard_of(cid, self.k)].recs.get(cid)
        return len(r[1]) if r else 0

    def first(self, name: str) -> Optional[str]:
        e = self.idx[shard_of(name, self.k)].names.get(name)
        return min(e)[1] if e else None

    def ask(self, seed: list[int], context: int) -> dict:
        q = (tuple(seed), context) if isinstance(seed, list) else None
        if q is None or not valid_question(q):
            return {"ok": False, "error": "invalid question"}
        self.idx[shard_of(q, self.k)].asked.add(q)
        return {"ok": True, "q": q, "residual": tuple(-x for x in action(seed))}

    def answer_legs(self, q, cont: list[int], attester):
        if not valid_question(q) or not valid_twists(cont):
            return []
        ts = list(q[0]) + list(cont)
        got = self._record_leg(ts, attester)
        if got is None:
            return []
        cid, key, leg = got
        i = self.idx[shard_of(q, self.k)]
        return [leg, lambda: i.put_answer(q, key, cid)]

    def solve(self, q) -> Optional[list[int]]:
        if not valid_question(q):
            return None
        e = self.idx[shard_of(q, self.k)].answers.get(q)
        if not e:
            return None
        key, _ = min(e)                  # the key carries the history: no record-shard read
        return from_str(key[3])[len(q[0]):]

    def merged(self) -> "ShardedKB":
        """Union of all shards into one: what a full replica would hold."""
        m = ShardedKB(1)
        for r in self.rec:
            for cid, (ts, att) in r.recs.items():
                for a in att:
                    m.rec[0].put(cid, ts, a)
        for i in self.idx:
            for n, es in i.names.items():
                for key, cid in es:
                    m.idx[0].put(n, key, cid)
            for q, es in i.answers.items():
                for key, cid in es:
                    m.idx[0].put_answer(q, key, cid)
            m.idx[0].asked |= i.asked
        return m


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
    assert conjoin((0, 1), (1, 1)) == "incompatible"
    assert conjoin((0, 1), (3, 1)) == ("and", (0, 1), (3, 1))

    # (d) ways and redundancy are different statistics
    kb = KB()
    alice, bob, carol = DeployerId(b"A" * 33), DeployerId(b"B" * 33), DeployerId(b"C" * 33)
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
        q = kb2.ask(from_str(seed), 0)["q"]
        for rec in qs.search(seed, max_depth=5, limit=None, absorbing=False):
            kb2.answer(q, from_str(rec["cont"]), alice)
        ref = qs.solve(seed, max_depth=4)
        got = kb2.solve(q)
        assert ref["solved"] and to_str(got) == ref["cont"], (seed, got, ref["cont"])
    print("(e) solve over all possibilities (non-events included) matches qucalc_search.solve on 5 seeds")

    # (f) sharding: random workload, legs delivered shuffled and duplicated, k = 1..7 shards;
    #     every query equals the single-store KB, and a full merge of the shards equals k = 1.
    import random
    rng = random.Random(20261107)
    people = [DeployerId(bytes([i]) * 33) for i in range(6)]
    pool = [list(t) for t in itertools.product(range(8), repeat=4) if is_closure(list(t))]
    seeds = ["^", "^>", "+^", "^<", "/+"]
    work = [("n%d" % rng.randrange(12), rng.choice(pool), rng.choice(people)) for _ in range(400)]
    answers = []
    for sd in seeds:
        for rec in qs.search(sd, max_depth=4, limit=None, absorbing=False):
            answers.append((sd, from_str(rec["cont"]), rng.choice(people)))
    ref = KB()
    for n, ts, a in work:
        ref.assert_closure(n, ts, a)
    for sd in seeds:
        ref.ask(from_str(sd), 0)
    for sd, c, a in answers:
        ref.answer(question_id(from_str(sd), 0), c, a)
    for k in range(1, 8):
        kb3 = ShardedKB(k)
        for sd in seeds:
            kb3.ask(from_str(sd), 0)
        legs = [l for n, ts, a in work for l in kb3.legs(n, ts, a)]
        legs += [l for sd, c, a in answers for l in kb3.answer_legs(question_id(from_str(sd), 0), c, a)]
        legs = legs + rng.sample(legs, len(legs) // 3)            # re-delivery
        rng.shuffle(legs)                                          # any order across shards
        for leg in legs:
            leg()
        for kbx in (kb3, kb3.merged()):
            for n in ref.names:
                assert kbx.ways(n) == ref.ways(n) and kbx.first(n) == ref.first(n), (k, n)
            for cid in ref.records:
                assert kbx.redundancy(cid) == ref.redundancy(cid), (k, cid)
            for sd in seeds:
                qid = question_id(from_str(sd), 0)
                assert kbx.solve(qid) == ref.solve(qid), (k, sd)
    print(f"(f) sharded k=1..7, {len(work) + len(answers)} writes shuffled + 1/3 re-delivered: "
          f"ways, redundancy, first, solve all equal the single store")

    # (g) review fixes: questions are grow-only, malformed input fails closed with an answer.
    kb4 = KB()
    seed = from_str("^>")
    q = kb4.ask(seed, 0)["q"]
    kb4.answer(q, from_str("<v"), alice)
    before = kb4.solve(q)
    again = kb4.ask(seed, 0)                                   # replayed ask
    assert again["q"] == q and kb4.solve(q) == before and len(kb4.answers[q]) == 1
    q2 = kb4.ask(seed, 1)["q"]                                 # same seed, other context:
    assert q2 != q and kb4.solve(q2) is None and kb4.solve(q) == before   # a different question
    bad = [[8], [-1], [0, 1, True, 2], [0.0, 1, 2, 3], "^v<>", None, (0, 1, 2, 3),
           [0, 1] * (MAX_LEN // 2) + [0, 1]]
    for b in bad:
        r = kb4.assert_closure("x", b, alice)
        assert r == {"ok": False, "error": "invalid twists"}, (b, r)
        assert kb4.answer(q, b, alice)["ok"] is False
        assert kb4.ask(b, 0)["ok"] is False
    assert kb4.ask(seed, 4)["ok"] is False and kb4.ask(seed, "0")["ok"] is False
    assert kb4.answer(("nope",), from_str("<v"), alice)["error"] == "invalid question"
    assert kb4.solve(q) == before and "x" not in kb4.names
    print(f"(g) replayed ask keeps its answers; {len(bad)} malformed inputs refused on "
          f"assert/ask/answer; state unchanged")

    # (h) second review: attesters are signing keys; propositions are validated.
    kb5 = KB()
    plaq = from_str("^<v>")
    fresh = [object() for _ in range(5)]                  # names a single caller can mint
    for f in fresh:
        r = kb5.assert_closure("p", plaq, f)
        assert r == {"ok": False, "error": "attester is not a deployerId"}, r
    assert kb5.records == {} and kb5.names == {}
    r = None
    for _ in range(5):                                     # one deployer, five attestations
        r = kb5.assert_closure("p", plaq, alice)
    assert r["redundancy"] == 1
    assert kb5.assert_closure("p", plaq, DeployerId(b"A" * 33))["redundancy"] == 1  # same key
    assert kb5.assert_closure("p", plaq, bob)["redundancy"] == 2
    sh = ShardedKB(3)
    for f in fresh:
        assert sh.legs("p", plaq, f) == []
    bad_props = [(4, 1), (-1, 1), (0, 0), (0, 2), (0, True), (True, 1), (0.0, 1),
                 (0, 1, 2), [0, 1], "x", None, (0,)]
    for b in bad_props:
        for p_, q_ in ((b, (0, 1)), ((0, 1), b), (b, b)):
            assert compatible(p_, q_) is None, (p_, q_)
            assert conjoin(p_, q_) == "invalid proposition", (p_, q_)
    assert all(compatible(p_, q_) is not None for p_ in MO3 + [(3, 1), (3, -1)]
               for q_ in MO3 + [(3, 1), (3, -1)])
    print(f"(h) 5 fresh names refused as attesters, 5 repeats by one key give R=1; "
          f"{len(bad_props)} malformed propositions refused before any fold")

    # (i) third review: answers are their own namespace, conjoin is closed, the
    #     sharded model validates questions like the single store, and answers
    #     may arrive before (or without) the ask that registers the question.
    q = question_id(from_str("^>"), 0)
    for model in (KB(), ShardedKB(3)):
        model.ask(from_str("^>"), 0)
        run = (model.answer_legs if isinstance(model, ShardedKB) else None)
        if run:
            for leg in run(q, from_str("<v"), alice):
                leg()
            model.assert_closure(q, from_str("+-+-"), alice)   # unrelated closure filed under q
        else:
            model.answer(q, from_str("<v"), alice)
            model.assert_closure(q, from_str("+-+-"), alice)
        assert model.solve(q) == from_str("<v"), (type(model).__name__, model.solve(q))
    props = (MO3 + [(3, 1), (3, -1)]
             + [("and", sa, g) for sa in SPATIAL_ATOMS for g in ((3, 1), (3, -1))])
    n_ok = 0
    for p_, q_ in itertools.product(props, repeat=2):
        r = conjoin(p_, q_)
        assert r == "incompatible" or valid_prop(r), (p_, q_, r)
        if r != "incompatible":
            n_ok += 1
            assert conjoin(r, TOP) == r and conjoin(r, r) == r       # closed, idempotent
            assert conjoin(q_, p_) == r                              # commutative
    for p_, q_, r_ in itertools.product(props, repeat=3):            # associative where defined
        a1, b1 = conjoin(p_, q_), conjoin(q_, r_)
        if "incompatible" not in (a1, b1):
            assert conjoin(a1, r_) == conjoin(p_, b1) or "incompatible" in (
                conjoin(a1, r_), conjoin(p_, b1)), (p_, q_, r_)
    assert conjoin(("and", (0, 1), (3, 1)), (1, 1)) == "incompatible"
    assert conjoin(("and", (0, 1), (3, 1)), (3, -1)) == BOT
    assert not valid_prop(("and", (3, 1), (0, 1))) and not valid_prop(("and", (0, 1), (1, 1)))
    single, sharded = KB(), ShardedKB(4)
    for bad_q in (([8], 0), ([0], 4), ([0, 1], True), ("^v", 0)):
        assert single.ask(*bad_q) == sharded.ask(*bad_q) == {"ok": False, "error": "invalid question"}
    for qq in (("nope",), ((8,), 0), ((0,), 4)):
        assert single.answer(qq, [1], alice)["error"] == "invalid question"
        assert sharded.answer_legs(qq, [1], alice) == [] and sharded.solve(qq) is None
    for order in range(20):                        # ask anywhere among the answer legs
        sk, ref2 = ShardedKB(3), KB()
        conts = [from_str(c) for c in ("<v", "v<", "<v+-", "/v<\\")]
        steps = [l for c in conts for l in sk.answer_legs(q, c, people[order % 6])]
        steps.append(lambda: sk.ask(from_str("^>"), 0))
        random.Random(order).shuffle(steps)
        for st in steps:
            st()
        for c in conts:
            ref2.answer(q, c, people[order % 6])     # single store, never asked
        assert sk.solve(q) == ref2.solve(q) == from_str("<v") and q in sk.merged().idx[0].asked
    print(f"(i) non-answer under the question id ignored by solve in both models; "
          f"conjoin closed on {len(props)} propositions ({n_ok} defined pairs); "
          f"questions validated alike; answer-before-ask converges")

    # (j) fourth review: a queued leg carries a snapshot, not the caller's list.
    def integrity(sk):
        for shard in sk.rec:
            for cid, (ts_, _) in shard.recs.items():
                assert content_id(ts_) == cid, (cid, ts_)             # content address holds
        for shard in sk.idx:
            for table in (shard.names, shard.answers):
                for es in table.values():
                    for key, cid in es:
                        rec = sk.rec[shard_of(cid, sk.k)].recs[cid]
                        assert key == cascade_key(rec[0]), (key, rec[0])   # index agrees
    for mutate_at in ("before", "between"):
        for make in ("assert", "answer"):
            sk = ShardedKB(3)
            buf = from_str("^<v>") if make == "assert" else from_str("<v")
            lg = (sk.legs("n", buf, alice) if make == "assert"
                  else sk.answer_legs(question_id(from_str("^>"), 0), buf, alice))
            if mutate_at == "before":
                buf[:] = from_str("+-+-")
            lg[0]()
            if mutate_at == "between":
                buf[:] = from_str("+-+-")
            lg[1]()
            integrity(sk)
            want = from_str("^<v>") if make == "assert" else from_str("^><v")
            stored = [ts_ for sh in sk.rec for ts_, _ in sh.recs.values()]
            assert stored == [want], (mutate_at, make, stored)
    assert ShardedKB(2).legs("n", tuple(from_str("^<v>")), alice) == []    # not a list
    print("(j) caller mutation before delivery or between legs changes nothing: "
          "content ids and index keys match the stored history")
    print("all self-checks passed")


if __name__ == "__main__":
    _selfcheck()
