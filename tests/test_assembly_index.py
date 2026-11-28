"""Regression tests for the exact ZFA assembly-index census.

These tests are dependency-free.  They cross-check the branch-and-bound solvers
against independent breadth-first searches for short words, verify the
canonical-orbit weights against direct enumeration of balanced words, and pin
the small values quoted in Assembly_Index_QLF.md.
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import assembly_index as ai  # noqa: E402


class AssemblyIndexTests(unittest.TestCase):
    def test_known_values(self) -> None:
        cases = {
            "<>": (1, 1),
            "^v^v": (2, 2),
            "<><>": (2, 2),
            "^^^^": (2, 3),
            "^^^^vvvv": (5, 7),
        }
        for word, expected in cases.items():
            with self.subTest(word=word):
                self.assertEqual(
                    (ai.assembly_index(word), ai.assembly_index_closed(word)),
                    expected,
                )

    def test_brute_force_small(self) -> None:
        # Every canonical class through length 4, both metrics.
        for n in (2, 4):
            for word in ai.iter_canonical_words(n):
                with self.subTest(word=word, metric="ordinary"):
                    self.assertEqual(
                        ai.assembly_index(word),
                        ai.brute_force_assembly_index(word),
                    )
                with self.subTest(word=word, metric="closed"):
                    self.assertEqual(
                        ai.assembly_index_closed(word),
                        ai.brute_force_assembly_index_closed(word),
                    )
        # Ordinary metric through length 6 (70 classes).
        for word in ai.iter_canonical_words(6):
            with self.subTest(word=word, metric="ordinary"):
                self.assertEqual(
                    ai.assembly_index(word),
                    ai.brute_force_assembly_index(word),
                )

    def test_canonical_orbit_weights(self) -> None:
        for n in (2, 4, 6, 8, 10):
            words = list(ai.iter_canonical_words(n))
            with self.subTest(length=n):
                self.assertEqual(len(words), len(set(words)))
                self.assertEqual(
                    sum(ai.orbit_size(w) for w in words),
                    ai.balanced_word_count(n),
                )

    def test_fold_classes_partition(self) -> None:
        for n in (2, 4, 6, 8):
            with self.subTest(length=n):
                self.assertEqual(
                    sum(ai.fold_class_counts(n).values()),
                    ai.balanced_word_count(n),
                )

    def test_fold_class_counts_match_direct_enumeration(self) -> None:
        def balanced_words(n: int):
            def rec(prefix: str, counts: tuple[int, int, int, int]):
                if sum(abs(c) for c in counts) > n - len(prefix):
                    return
                if len(prefix) == n:
                    if all(c == 0 for c in counts):
                        yield prefix
                    return
                for twist in ai.TWISTS:
                    updated = list(counts)
                    updated[ai.AXIS[twist]] += ai.SIGN[twist]
                    yield from rec(prefix + twist, tuple(updated))

            yield from rec("", (0, 0, 0, 0))

        for n in (2, 4, 6):
            direct: dict[int, int] = {}
            for word in balanced_words(n):
                phase = ai.fold(word)
                assert phase is not None
                direct[phase] = direct.get(phase, 0) + 1
            with self.subTest(length=n):
                self.assertEqual(direct, ai.fold_class_counts(n))

    def test_fold_of_closed_words_is_real(self) -> None:
        # On the count-balanced census the fold is +I or -I; no +/-iI class occurs.
        for n in (2, 4, 6, 8):
            for word in ai.iter_canonical_words(n):
                with self.subTest(word=word):
                    self.assertIn(ai.fold(word), (0, 2))
        self.assertIsNone(ai.fold("^"))
        self.assertIsNone(ai.fold("^>"))
        # Pauli closure is strictly weaker than count balance: ^^^^ folds to +I
        # but is not count-balanced.
        self.assertEqual(ai.fold("^^^^"), 0)
        self.assertFalse(ai.is_closed("^^^^"))

    def test_index_sandwich(self) -> None:
        for n in (2, 4, 6):
            for word in ai.iter_canonical_words(n):
                a = ai.assembly_index(word)
                az = ai.assembly_index_closed(word)
                with self.subTest(word=word):
                    self.assertLessEqual(a, az)
                    self.assertLessEqual(az, len(word) - 1)

    def test_symmetry_invariance(self) -> None:
        # Axis permutation plus per-axis sign flips preserve both indices.
        def transform(word: str, perm: tuple[int, ...], flips: tuple[int, ...]) -> str:
            out = []
            for ch in word:
                axis = perm[ai.AXIS[ch]]
                sign = ai.SIGN[ch] * flips[axis]
                out.append(ai.PLUS_SYMBOL[axis] if sign == 1 else ai.MINUS_SYMBOL[axis])
            return "".join(out)

        words = ["< >".replace(" ", ""), "^v^v", "<><>", "^^^^vvvv", "^><><><v"]
        for word in words:
            with self.subTest(word=word):
                base = (ai.assembly_index(word), ai.assembly_index_closed(word))
                for perm in ((0, 1, 2, 3), (1, 0, 3, 2), (3, 2, 1, 0)):
                    for flips in ((1, 1, 1, 1), (-1, 1, -1, 1), (1, -1, -1, 1)):
                        moved = transform(word, perm, flips)
                        self.assertEqual(
                            (ai.assembly_index(moved), ai.assembly_index_closed(moved)),
                            base,
                        )

    def test_ordinary_index_depends_only_on_equality_pattern(self) -> None:
        # A bijection of the eight symbols preserves the ordinary index.
        word = "^v^v<>"
        moved = "".join({"^": "/", "v": "\\", "<": "+", ">": "-", "/": "^", "\\": "v", "+": "<", "-": ">"}[ch] for ch in word)
        self.assertEqual(ai.equality_pattern(word), ai.equality_pattern(moved))
        self.assertEqual(ai.assembly_index(word), ai.assembly_index(moved))

    def test_lz78_known_values(self) -> None:
        self.assertEqual(ai.lz78_phrases("<>"), 2)
        self.assertEqual(ai.lz78_phrases("^v^v"), 3)
        self.assertEqual(ai.lz78_phrases("^^^^"), 3)

    def test_closed_definition_matches_conjugate_counts(self) -> None:
        for word in ("", "<>", "^v^v", "^^^^", "^^^^vvvv", "^><><><v"):
            expected = all(
                word.count(t) == word.count(ai.CONJUGATE[t])
                for t in ("^", "<", "/", "+")
            )
            self.assertEqual(ai.is_closed(word), expected)


if __name__ == "__main__":
    unittest.main()
