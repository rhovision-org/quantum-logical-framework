#!/usr/bin/env python3
"""Fast regression suite for the #207 amplitude and dispersion scripts.

Part of the Quantum Logical Framework (QLF). Runs each script on a small fixed
input (fixed seeds) and asserts its results, not only its exit code:

  * G3: eq. (13) equals the handedness polynomial on every tree graph, n = 3..5,
    and the 3-point leading singularity matches the paper's eq. (16);
  * G4b: planar one-loop n-gons give (-1)^n (D - 2) for n = 1..3; the non-planar
    annulus gives +-D on its closed curve;
  * G2c: unit-weighted closure sums vanish on every hidden-zero locus (n = 4..6)
    while multiplicity weights fail at n = 6; spinor momenta give exact zero/control
    counts; the derived propagator's zeros break with slope 2 in the spacing;
  * B-LIV: the walk trace identities and the linear coefficient 2/(3 sqrt 3).

The full 7/8-point sweeps stay optional (run the scripts directly).

Usage:
    python3 scripts/amplitude_regression.py
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FAILS: list[str] = []


def run(*args: str) -> str:
    out = subprocess.run([sys.executable, *args], cwd=ROOT, capture_output=True, text=True)
    if out.returncode != 0:
        FAILS.append(f'{" ".join(args)} exited {out.returncode}: {out.stderr.strip()[-400:]}')
    return out.stdout


def expect(name: str, ok: bool, detail: str = '') -> None:
    print(('PASS ' if ok else 'FAIL ') + name + (f'  [{detail}]' if detail and not ok else ''))
    if not ok:
        FAILS.append(name)


def all_matches(pattern: str, text: str) -> list[tuple[str, ...]]:
    return re.findall(pattern, text)


def main() -> int:
    # G3: trees
    out = run('curve_cover_census.py', '--check3', '--compare', '5')
    expect('G3 3-point LS matches paper eq. (16)', 'matches paper eq. (16): True' in out, out)
    rows = all_matches(r'n=(\d): eq\. \(13\) == Q3 on (\d+)/(\d+) graphs', out)
    expect('G3 eq. (13) == handedness polynomial on all trees n=3..5',
           [(int(n), int(a), int(b)) for n, a, b in rows] == [(3, 1, 1), (4, 2, 2), (5, 5, 5)], out)

    # G4b: planar one loop
    out = run('curve_cover_loop.py', '--tree-check', '5', '--ngon', '3')
    rows = all_matches(r'tree n=(\d): turn-word walker == eq\. \(13\) on (\d+)/(\d+)', out)
    expect('G4b walker reproduces eq. (13) on trees n=3..5',
           [(int(a), int(b)) for _, a, b in rows] == [(1, 1), (2, 2), (5, 5)], out)
    blocks = re.split(r'--- planar one-loop (\d)-gon', out)[1:]
    coef = {int(blocks[i]): re.findall(r'\(([-+0-9D]+)\)\*X2,p', blocks[i + 1]) for i in range(0, len(blocks), 2)}
    # (-1)^n (D - 2): n odd -> 2 - D, n even -> D - 2
    expect('G4b planar n-gon closed-curve coefficient (-1)^n (D-2), n=1..3',
           coef == {1: ['2-1D'], 2: ['-2+1D'], 3: ['2-1D']}, str(coef))

    # G4b: non-planar
    out = run('curve_cover_nonplanar.py', '--tree-check', '5', '--all', '3')
    rows = all_matches(r'tree n=(\d): momentum-named walker == eq\. \(13\) on (\d+)/(\d+)', out)
    expect('non-planar namer reproduces eq. (13) on trees n=3..5',
           [(int(a), int(b)) for _, a, b in rows] == [(1, 1), (2, 2), (5, 5)], out)
    cc = all_matches(r'\(0([+-])1D\) \*', out)
    expect('non-planar closed-curve coefficient is +-D (no constant term), 4 annuli',
           len(cc) == 4 and '1 carry the closed curve' in out, out)

    # G2c round 1: closure sums
    out = run('hidden_zero_closures.py', '--max-n', '6', '--points', '5')
    rows = {int(n): (int(t), [int(x) for x in f.split(', ')])
            for n, t, f in all_matches(r'n=(\d): \d+ decompositions; .*?; (\d+) points; '
                                       r'nonzero A for W0/W1/W2 = \[([0-9, ]+)\]', out)}
    expect('G2c unit weights vanish on every locus, n=4..6',
           set(rows) == {4, 5, 6} and all(f[0] == 0 for _, f in rows.values()), out)
    expect('G2c multiplicity weights W1, W2 fail at every n=6 point',
           rows.get(6, (0, [0, 0, 0]))[1][1:] == [rows[6][0]] * 2, out)

    # G2c round 4: spinor momenta, exact counts at a fixed seed
    out = run('hidden_zero_spinors.py', '--max-n', '6', '--points', '3')
    rows = all_matches(r'n=(\d): locus points built (\d+), singular (\d+), non-singular (\d+), '
                       r'A = 0 on (\d+)/(\d+); control: generic points (\d+), A = 0 on (\d+)', out)
    got = [tuple(int(x) for x in r) for r in rows]
    expect('G2c spinor zero/control counts (seed 207)',
           got == [(5, 15, 0, 15, 15, 15, 15, 0), (6, 27, 0, 27, 27, 27, 27, 0)], str(got))

    # G2c round 5: derived propagator, a^2 breaking
    out = run('hidden_zero_propagator.py', '--max-n', '6', '--points', '3')
    d1 = re.search(r'D1: max \|walk sum - geometric series\| over L <= 6 = ([0-9.e+-]+)', out)
    expect('propagator D1: walk sum equals geometric series to 1e-12', bool(d1) and float(d1.group(1)) < 1e-12, out)
    rows = all_matches(r'n=(\d): D2 max rel err ([0-9.e+-]+); locus points \d+, median slope ([0-9.]+).*?'
                       r'min R ([0-9.e+-]+); .*?median slope of R-R\(0\) ([0-9.]+)', out)
    expect('propagator: locus and control slopes in [1.9, 2.1], D2 < 1e-4, no exact zero',
           len(rows) == 2 and all(float(d2) < 1e-4 and 1.9 <= float(s1) <= 2.1 and float(mr) > 1e-10
                                  and 1.9 <= float(s2) <= 2.1 for _, d2, s1, mr, s2 in rows), out)

    # B-LIV
    out = run('liv_dispersion.py')
    m = re.search(r'palindromic cos E = prod cos k_i \(max err ([0-9.e+-]+)\); '
                  r'one-way cos E = prod cos - prod sin \(max err ([0-9.e+-]+)\)', out)
    expect('walk trace identities at 2000 random momenta to 1e-12',
           bool(m) and float(m.group(1)) < 1e-12 and float(m.group(2)) < 1e-12, out)
    expect('one-way linear coefficient 2/(3 sqrt 3) = 0.3849, E_QG1 = 2.60 E_P',
           'linear term |v - 1| <= 0.3849 (E/E_P), E_QG1 = 2.60 E_P' in out, out)
    expect('scalar walk axis xi = 1/6 (Euclidean), no quadratic term on axis (real time)',
           'formula +0.166667' in out and 'no quadratic term' in out, out)

    if FAILS:
        print(f'\n{len(FAILS)} check(s) failed')
        return 1
    print('\nall amplitude regression checks passed')
    return 0


if __name__ == '__main__':
    sys.exit(main())
