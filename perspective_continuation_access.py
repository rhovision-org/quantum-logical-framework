"""Finite continuation-language audit; physical accessibility is not assumed."""
from functools import lru_cache
import json
from twist_core import (TWISTS, PAULI_MAP, get_successor_twists, calculate_action,
                        pauli_fold, is_zfa, _mat_mul)
from perspective_holography import factor_reconstruction

ALL = tuple(TWISTS)
A = tuple(t for t in ALL if t in "^v<>+-")
B = tuple(t for t in ALL if t in "<>/\\+-")
SHARED = tuple(t for t in A if t in B)
MASKS = {"full": ALL, "A": A, "B": B, "shared": SHARED}
DELTAS = {t: calculate_action(t) for t in ALL}


def prefixes():
    level = [""]
    for _ in range(3):
        level = [h + t for h in level for t in get_successor_twists(h[-1:] or "")]
        yield from level


def terminal_phase(fold):
    a, b, c, d = fold
    if b == c == 0 and a == d and a in (1, -1, 1j, -1j):
        return (int(a.real), int(a.imag))
    return None


def direct(prefix, mask, horizon=3):
    out = set()

    def visit(suffix, remaining):
        history = prefix + suffix
        if is_zfa(history):
            out.add((suffix, terminal_phase(pauli_fold(history))))
            return
        if remaining:
            for t in get_successor_twists(history[-1]):
                if t in mask:
                    visit(suffix + t, remaining - 1)

    visit("", horizon)
    return frozenset(out)


@lru_cache(maxsize=None)
def from_record(action, fold, last, length, mask, remaining):
    phase = terminal_phase(fold)
    if length >= 4 and action == (0, 0, 0, 0) and phase is not None:
        return frozenset({("", phase)})
    if not remaining:
        return frozenset()
    out = set()
    for t in get_successor_twists(last):
        if t in mask:
            new_action = tuple(a + b for a, b in zip(action, DELTAS[t]))
            new_fold = _mat_mul(fold, PAULI_MAP[t])
            out.update((t + suffix, p) for suffix, p in
                       from_record(new_action, new_fold, t, length + 1, mask, remaining - 1))
    return frozenset(out)


def run():
    words = list(prefixes())
    bases, languages = [], []
    loss = None
    total_terminals = {name: 0 for name in MASKS}
    for h in words:
        action, fold = calculate_action(h), pauli_fold(h)
        bases.append((is_zfa(h), action, fold, len(h)))
        records = {name: direct(h, mask) for name, mask in MASKS.items()}
        for name, mask in MASKS.items():
            assert records[name] == from_record(action, fold, h[-1], len(h), mask, 3), (h, name)
            total_terminals[name] += len(records[name])
        assert records["A"] & records["B"] == records["shared"], h
        assert records["A"] <= records["full"] and records["B"] <= records["full"]
        if loss is None and records["full"] - records["A"]:
            loss = {"prefix": h, "view": "A", "missing_terminal": sorted(records["full"] - records["A"])[0]}
        languages.append(records["full"])
    result = factor_reconstruction(bases, languages)
    assert not result.reconstructible and loss is not None
    i, j = result.counterexample_indices
    difference = sorted(languages[i] ^ languages[j])
    return {"prefixes": len(words), "mask_comparisons": len(words) * len(MASKS),
            "base_reconstructs": False,
            "collision": {"histories": [words[i], words[j]],
                          "same_record": True, "differing_terminal": difference[0],
                          "terminal_counts": [len(languages[i]), len(languages[j])]},
            "augmented_record_matches_all": True, "overlap_matches_all": True,
            "view_loss": loss, "terminal_counts": total_terminals,
            "scope": "finite successor policy; physical causal accessibility B-OPEN"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
