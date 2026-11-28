"""Replication of the frozen eight-count record in dee8efc; no physical bridge."""
from collections import Counter
from itertools import product
from functools import lru_cache
import unittest

import twist_core
from territory_return import AXIS, SIGN, fold, ledger
from perspective_holography import factor_reconstruction


class FrozenEightCountTest(unittest.TestCase):
    def test_full_frozen_domain(self):
        alphabet = tuple(twist_core.TWISTS)
        self.assertEqual(len(alphabet), 8)
        tokens = tuple(product("ABC", alphabet))
        words = [w for n in range(4) for w in product(tokens, repeat=n)]
        self.assertEqual(len(words), 14425)

        @lru_cache(None)
        def record(w):
            counts = Counter(w)
            return tuple(counts[t] for t in alphabet), fold(w)

        def net(counts):
            return tuple(sum(n * SIGN[t] for t, n in zip(alphabet, counts)
                             if AXIS[t] == axis) for axis in range(4))

        views = {v: [] for v in ("A", "C", "AB", "BC", "ABC", "B_fold", "B_net_fold")}
        b_counts, b_zfa, global_zfa = [], [], []
        for w in words:
            # Each observer builds only its own view from tagged input.
            for v in ("A", "C", "AB", "BC", "ABC"):
                views[v].append(tuple(record("".join(t for owner, t in w if owner == b))
                                      for b in v))
            projections = {b: "".join(t for owner, t in w if owner == b) for b in "ABC"}
            counts, f = record(projections["B"])
            for p in projections.values():
                self.assertEqual(net(record(p)[0]), ledger(p))
            views["B_fold"].append(f)
            views["B_net_fold"].append((net(counts), f))
            b_counts.append(counts)
            b_zfa.append(net(counts) == (0, 0, 0, 0))
            global_zfa.append(all(net(record(p)[0]) == (0, 0, 0, 0)
                                  for p in projections.values()))
            self.assertEqual(views["ABC"][-1][:2], views["AB"][-1])
            self.assertEqual(views["ABC"][-1][1:], views["BC"][-1])
        for v, observable in (("AB", b_counts), ("BC", b_counts),
                              ("AB", b_zfa), ("BC", b_zfa)):
            self.assertTrue(factor_reconstruction(views[v], observable).reconstructible)
        for v, observable in (("A", b_counts), ("C", b_counts),
                              ("AB", global_zfa), ("BC", global_zfa),
                              ("B_fold", b_zfa), ("B_net_fold", b_counts)):
            a = factor_reconstruction(views[v], observable)
            self.assertFalse(a.reconstructible, v)
            i, j = a.counterexample_indices
            self.assertEqual(views[v][i], views[v][j])
            self.assertNotEqual(observable[i], observable[j])
            print("FALSIFIER", v, repr(words[i]), repr(words[j]))
        # Preserve F4 as independent accounting control.
        faces = (set([0]), set([0, 1]), set([0, 1, 2]))
        increments = [faces[0]] + [b-a for a,b in zip(faces,faces[1:])]
        self.assertEqual(sum(map(len, faces)), 6)
        self.assertEqual(sum(map(len, increments)), len(faces[-1]))
        self.assertEqual(set.union(*increments), faces[-1])
        self.assertTrue(all(not a & b for i,a in enumerate(increments) for b in increments[i+1:]))
        print("PASS frozen eight-count F1-F4: 14425 histories; 28850 nested restrictions; net+fold cannot reconstruct eight counts")
