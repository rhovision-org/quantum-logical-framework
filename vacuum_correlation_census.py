#!/usr/bin/env python3
"""Exact census behind lean/QLF_VacuumCorrelation.lean (gate H1 and its extension).

Part of the Quantum Logical Framework (QLF), see README.md and Vacuum_Correlation.md.

The fold is computed symbolically, as in the Lean module's `nfFold`: a phase in Z/4 (powers of i)
and an axis in the Klein four-group, with the cocycle of the sigma products. Every result is
exact; `twist_core.pauli_fold` is used only as a cross-check.

Reports:
  1. Every count-balanced history of length 4 over the eight twists, split by fold and by
     self-conjugacy (antiparticle = conjugate each twist and reverse).
  2. The 720 orderings of one pair from each spatial axis (length 6, three axes), the same split.
  3. Every count-balanced spatial history of length 6, the same split.

Run:  python3 vacuum_correlation_census.py
"""
import itertools

import twist_core

TWISTS = ['^', 'v', '<', '>', '/', '\\', '+', '-']
CONJ = {'^': 'v', 'v': '^', '<': '>', '>': '<', '/': '\\', '\\': '/', '+': '-', '-': '+'}
# twist -> (phase as a power of i, axis); matches twistNF in QLF_TwistAlphabet.lean
NF = {'^': (0, 'Y'), 'v': (2, 'Y'), '<': (2, 'X'), '>': (0, 'X'),
      '/': (0, 'Z'), '\\': (2, 'Z'), '+': (0, 'I'), '-': (2, 'I')}
# axis product with cocycle (power of i): sigma_x sigma_y = i sigma_z, etc.
KLEIN = {('X', 'Y'): ('Z', 1), ('Y', 'X'): ('Z', 3), ('Y', 'Z'): ('X', 1),
         ('Z', 'Y'): ('X', 3), ('Z', 'X'): ('Y', 1), ('X', 'Z'): ('Y', 3)}
PHASE_NAME = {0: '+I', 1: '+iI', 2: '-I', 3: '-iI'}


def axis_mul(a, b):
    if a == 'I':
        return b, 0
    if b == 'I':
        return a, 0
    if a == b:
        return 'I', 0
    return KLEIN[(a, b)]


def nf_fold(word):
    """Right fold, as in the Lean `nfFold`: returns (phase power of i, axis)."""
    phase, axis = 0, 'I'
    for t in reversed(word):
        p, a = NF[t]
        new_axis, c = axis_mul(a, axis)
        phase, axis = (p + phase + c) % 4, new_axis
    return phase, axis


def balanced(word):
    return all(word.count(t) == word.count(CONJ[t]) for t in '^</+')


def antiparticle(word):
    return ''.join(CONJ[t] for t in reversed(word))


def split(words):
    table = {}
    for w in words:
        ph, ax = nf_fold(w)
        assert ax == 'I', w  # count balance forces the trivial axis
        key = (PHASE_NAME[ph], 'self-conjugate' if antiparticle(w) == w else 'handed')
        table[key] = table.get(key, 0) + 1
    return dict(sorted(table.items()))


def cross_check(words):
    import numpy as np
    target = {0: np.eye(2), 1: 1j * np.eye(2), 2: -np.eye(2), 3: -1j * np.eye(2)}
    for w in words:
        assert np.allclose(np.array(twist_core.pauli_fold(w), dtype=complex).reshape(2, 2),
                           target[nf_fold(w)[0]]), w


def main():
    len4 = [''.join(p) for p in itertools.product(TWISTS, repeat=4) if balanced(''.join(p))]
    cross_check(len4)
    three_check = sorted(set("".join(p) for p in itertools.permutations("^v<>/\\")))
    cross_check(three_check)
    print('1. count-balanced length-4 histories, all eight twists:', len(len4))
    for k, v in split(len4).items():
        print('   ', k, v)
    neg_handed = sorted(w for w in len4 if nf_fold(w)[0] == 2 and antiparticle(w) != w)
    print('    -I and handed:', len(neg_handed), '(all spatial, two axes, pairs crossing:',
          all(set(w) <= set('^v<>/\\') and len(set(w)) == 4 for w in neg_handed), ')')

    three = sorted(set(''.join(p) for p in itertools.permutations('^v<>/\\')))
    print('2. orderings of one pair from each spatial axis:', len(three))
    for k, v in split(three).items():
        print('   ', k, v)

    sp6 = [''.join(p) for p in itertools.product('^v<>/\\', repeat=6) if balanced(''.join(p))]
    print('3. count-balanced spatial histories of length 6:', len(sp6))
    for k, v in split(sp6).items():
        print('   ', k, v)


if __name__ == '__main__':
    main()
