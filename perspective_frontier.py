"""Bounded three-body record and nested-face accounting audit (#296)."""
from functools import lru_cache
from itertools import product
import json

import twist_core
from territory_return import ledger, fold, balanced
from perspective_holography import factor_reconstruction


@lru_cache(maxsize=None)
def body_record(word):
    return ledger(word), fold(word)


def run():
    tokens = tuple(product("ABC", twist_core.TWISTS))
    words = list(w for n in range(4) for w in product(tokens, repeat=n))
    records = {k: [] for k in ("A", "C", "AB", "BC", "B_fold", "ABC")}
    b_ledgers, b_zfa, global_zfa = [], [], []
    restrictions = True
    for word in words:
        projections = {b: "".join(t for owner, t in word if owner == b) for b in "ABC"}
        for view in ("A", "C", "AB", "BC", "ABC"):
            # Compute each view solely from its own tagged projection.
            records[view].append(tuple(body_record("".join(
                t for owner, t in word if owner == b)) for b in view))
        records["B_fold"].append(fold(projections["B"]))
        b_ledgers.append(ledger(projections["B"]))
        b_zfa.append(balanced(projections["B"]))
        global_zfa.append(all(balanced(w) for w in projections.values()))
        abc = records["ABC"][-1]
        restrictions &= abc[:2] == records["AB"][-1] and abc[1:] == records["BC"][-1]

    def audit(view, observable):
        a = factor_reconstruction(records[view], observable)
        result = {"reconstructible": a.reconstructible}
        if not a.reconstructible:
            result["witness"] = [words[i] for i in a.counterexample_indices]
            result["observable_values"] = a.observable_values
        return result

    checks = {
        "AB_B_ledger": audit("AB", b_ledgers),
        "BC_B_ledger": audit("BC", b_ledgers),
        "AB_B_zfa": audit("AB", b_zfa),
        "BC_B_zfa": audit("BC", b_zfa),
        "A_B_ledger": audit("A", b_ledgers),
        "C_B_ledger": audit("C", b_ledgers),
        "AB_global_zfa": audit("AB", global_zfa),
        "BC_global_zfa": audit("BC", global_zfa),
        "B_fold_B_zfa": audit("B_fold", b_zfa),
    }
    expected = {name: name in ("AB_B_ledger", "BC_B_ledger", "AB_B_zfa", "BC_B_zfa")
                for name in checks}
    frontiers = (frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2}))
    increments = [frontiers[0]] + [b - a for a, b in zip(frontiers, frontiers[1:])]
    union = frozenset().union(*increments)
    accounting = {"cumulative_sum": sum(map(len, frontiers)),
                  "increment_sum": sum(map(len, increments)),
                  "terminal_count": len(frontiers[-1]),
                  "partition_valid": union == frontiers[-1] and
                  all(not a & b for i, a in enumerate(increments) for b in increments[i+1:])}
    assert all(checks[k]["reconstructible"] == v for k, v in expected.items())
    assert restrictions and accounting["partition_valid"]
    assert accounting["increment_sum"] == accounting["terminal_count"] != accounting["cumulative_sum"]
    return {"histories": len(words), "max_length": 3, "checks": checks,
            "nested_record_restrictions": restrictions, "face_accounting": accounting,
            "scope": "finite tagged surrogate; physical bridge B-OPEN"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
