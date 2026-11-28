"""Prefix-reachability identity audit for #296; no physical observer is assumed."""
from collections import defaultdict
from itertools import combinations
import json

from twist_core import calculate_action, pauli_fold, is_zfa, get_successor_twists
from perspective_continuation_access import ALL, prefixes, from_record, terminal_phase
from perspective_holography import factor_reconstruction


def run():
    words = list(prefixes())
    indexed = {w: set() for w in words}
    leaf_count = 0

    def walk(word):
        nonlocal leaf_count
        if word and is_zfa(word):
            leaf_count += 1
            phase = terminal_phase(pauli_fold(word))
            assert phase is not None
            for length in range(1, min(3, len(word)) + 1):
                if len(word) - length <= 3:
                    indexed[word[:length]].add((word, phase))
            return
        if len(word) < 6:
            for token in get_successor_twists(word[-1:]):
                walk(word + token)

    walk("")
    groups = defaultdict(list)
    states, absolute, relative = [], [], {}
    for w in words:
        state = (calculate_action(w), pauli_fold(w), w[-1], len(w))
        suffixes = from_record(*state, ALL, 3)
        expected = frozenset(indexed[w])
        assert expected == frozenset((w + s, p) for s, p in suffixes), w
        states.append(state)
        absolute.append(expected)
        relative[w] = suffixes
        groups[state].append(w)

    result = factor_reconstruction(states, absolute)
    witness = None
    pairs = nonempty_pairs = 0
    for members in groups.values():
        for a, b in combinations(members, 2):
            pairs += 1
            assert relative[a] == relative[b], (a, b)
            if not indexed[a]:
                assert not indexed[b]
                continue
            nonempty_pairs += 1
            assert indexed[a].isdisjoint(indexed[b]), (a, b)
            if witness is None:
                suffix, phase = sorted(relative[a])[0]
                witness = {"prefixes": [a, b], "common_suffix": suffix,
                           "phase": phase, "absolute_events": [a + suffix, b + suffix]}
    repaired = factor_reconstruction([(w, relative[w]) for w in words], absolute)
    assert repaired.reconstructible
    assert result.reconstructible == (nonempty_pairs == 0)
    return {"prefixes": len(words), "first_closure_leaves": leaf_count,
            "absolute_comparisons": len(words), "tree_matches": True,
            "reduced_state_classes": len(groups),
            "same_state_pairs": pairs, "nonempty_same_state_pairs": nonempty_pairs,
            "reduced_state_reconstructs_absolute": result.reconstructible,
            "collision": witness, "prefix_identity_repairs": repaired.reconstructible,
            "scope": "bounded word identity and first closure; physical accessibility B-OPEN"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
