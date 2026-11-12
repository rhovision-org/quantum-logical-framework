#!/usr/bin/env python3
"""Finite MO2 reproduction, adapted from the Paper I v0.2 companion audit.

A separate finite implementation; not a Lean kernel run or physical experiment.
"""
from itertools import product
import json
from pathlib import Path
import sys

E = ('bot', 'ax', 'axp', 'az', 'azp', 'top')
COMP = {'bot':'top', 'top':'bot', 'ax':'axp', 'axp':'ax', 'az':'azp', 'azp':'az'}

def le(a, b):
    return a == 'bot' or b == 'top' or a == b

def sup(a, b):
    if a == 'bot': return b
    if b == 'bot': return a
    if a == 'top' or b == 'top': return 'top'
    return a if a == b else 'top'

def inf(a, b):
    if a == 'top': return b
    if b == 'top': return a
    if a == 'bot' or b == 'bot': return 'bot'
    return a if a == b else 'bot'

def cp(a): return COMP[a]

def run_audit():
    checks = {
        'reflexive': all(le(a,a) for a in E),
        'transitive': all(not(le(a,b) and le(b,c)) or le(a,c) for a,b,c in product(E,repeat=3)),
        'antisymmetric': all(not(le(a,b) and le(b,a)) or a==b for a,b in product(E,repeat=2)),
        'join_upper_left': all(le(a,sup(a,b)) for a,b in product(E,repeat=2)),
        'join_upper_right': all(le(b,sup(a,b)) for a,b in product(E,repeat=2)),
        'join_least_upper': all(not(le(a,c) and le(b,c)) or le(sup(a,b),c) for a,b,c in product(E,repeat=3)),
        'meet_lower_left': all(le(inf(a,b),a) for a,b in product(E,repeat=2)),
        'meet_lower_right': all(le(inf(a,b),b) for a,b in product(E,repeat=2)),
        'meet_greatest_lower': all(not(le(c,a) and le(c,b)) or le(c,inf(a,b)) for a,b,c in product(E,repeat=3)),
        'join_commutative': all(sup(a,b)==sup(b,a) for a,b in product(E,repeat=2)),
        'meet_commutative': all(inf(a,b)==inf(b,a) for a,b in product(E,repeat=2)),
        'join_associative': all(sup(sup(a,b),c)==sup(a,sup(b,c)) for a,b,c in product(E,repeat=3)),
        'meet_associative': all(inf(inf(a,b),c)==inf(a,inf(b,c)) for a,b,c in product(E,repeat=3)),
        'join_absorption': all(sup(a,inf(a,b))==a for a,b in product(E,repeat=2)),
        'meet_absorption': all(inf(a,sup(a,b))==a for a,b in product(E,repeat=2)),
        'complement_involution': all(cp(cp(a))==a for a in E),
        'complement_antitone': all(not le(a,b) or le(cp(b),cp(a)) for a,b in product(E,repeat=2)),
        'complement_bottom': all(inf(a,cp(a))=='bot' for a in E),
        'complement_top': all(sup(a,cp(a))=='top' for a in E),
    }
    assert all(checks.values()), [k for k,v in checks.items() if not v]
    comparable = sum(1 for a,b in product(E,repeat=2) if le(a,b))
    orthomodular_checked = sum(1 for a,b in product(E,repeat=2) if not le(a,b) or b==sup(a,inf(cp(a),b)))
    nonvacuous = sum(1 for a,b in product(E,repeat=2) if le(a,b) and b==sup(a,inf(cp(a),b)))
    failures_meet = [(a,b,c) for a,b,c in product(E,repeat=3) if inf(a,sup(b,c))!=sup(inf(a,b),inf(a,c))]
    failures_join = [(a,b,c) for a,b,c in product(E,repeat=3) if sup(a,inf(b,c))!=inf(sup(a,b),sup(a,c))]
    assert comparable==15 and orthomodular_checked==36 and nonvacuous==15
    assert len(failures_meet)==24 and len(failures_join)==24
    assert ('ax','az','azp') in failures_meet
    return dict(lattice_checks=checks, comparable_pairs=comparable, nonvacuous_orthomodular=nonvacuous,
        orthomodular_implications=orthomodular_checked, ordered_pairs=36,
        nondistributive_meet_over_join=len(failures_meet), nondistributive_join_over_meet=len(failures_join),
        ordered_triples=216, witness=['ax','az','azp'],
        scope='finite independent implementation; neither Lean proof nor physical experiment')

if __name__ == '__main__':
    print(json.dumps(run_audit(), indent=2, sort_keys=True))
