#!/usr/bin/env python3
"""
contextual_census.py — the contextual census, built as a falsification test.

QLF's phase question is closed: `phase_rule` (lean/QLF_PhaseRule.lean) proves that a
count-balanced history folds to

    phi(h) = (-1)^(#negative twists + inversions of its axis word) . I

and QLF_BasisIndependence proves the stored (X, Y, Z) alphabet is a coordinate chart, not a
preferred physical basis. What is left open is the *partition*: which histories count as the
joint closure of a preparation P, an apparatus M, and a result c. That set,

    J(P, M, c),

is the one remaining freedom, and a freely-chosen one would reproduce any amplitudes at all
(Philosophy.md 3a rule 4). So this script fixes it by the only substrate-native rule available
-- **a run is a way exactly when preparation, system strand and apparatus close together** --
and then measures, without fitting anything:

    A(c) = sum over s of phi(P ++ s ++ M_c),   over system strands s that make the run close
    P(c) = A(c)^2 / sum_k A(k)^2

Design commitments, so the result can falsify rather than accommodate:

  * the phase is the **proven formula**, never a matrix product -- a failure here cannot be
    blamed on an approximate phase model;
  * a **preparation is an unbalanced strand** (an open strand needing closure), not merely a
    string prefix -- a balanced prefix prepares nothing, and the script refuses one;
  * preparation and apparatus are specified **independently**, and the contribution map is
    relational, K = K(P, M): neither side alone decides which strands close;
  * every geometry is run at **increasing finite horizons** and reported as a scaling table,
    never at a single hand-picked horizon;
  * a battery of geometries is printed **together and blind** -- no per-case tuning.

It is also a checker. Two consequences of the Lean theorems are asserted against the numbers:
symmetric branch pairs must give exactly equal amplitudes (QLF_BasisIndependence), and the
DP must agree with brute-force enumeration wherever brute force is affordable.

What it found (reproduce with --depth-scan 3 --max-k 18)
--------------------------------------------------------
The transverse geometries are pinned to exactly 1/2 at every horizon, which is not evidence
about anything: QLF_BasisIndependence *forces* it, since the two branches are exchanged by a
relabeling that fixes the preparation. A number forced by a proven symmetry is bookkeeping
(Philosophy.md 3a rule 4), and the script prints it only as a regression check.

The aligned geometries are the informative ones, and they say something the framework has to
answer for: **for any fixed preparation, the contextual weight washes out toward 1/2 as the
horizon grows.** The branch ratio A(-)/A(+) climbs monotonically at every horizon computed --
at depth 1: 0, .125, .200, .267, .327, .381, .429, .472, .511, .546 through k = 18, reaching
.677 at k = 28 where P(+) has fallen to .686 -- and a deeper preparation only delays it (depth 2
is still .936 at k = 28, but its ratio is rising too). Conversely, letting the depth grow with
the horizon drives the weight to 1. Two independent code paths (recomputing the census per
horizon, and reusing one incrementally) agree exactly at every overlapping horizon.

So this partition does **not** define a horizon-independent contextual probability: the number
is set by the ratio of preparation depth to horizon, and both limits are degenerate (1/2 one
way, 1 the other). The limit itself is not proven -- monotone data through k = 18 is not a
theorem -- but it is enough to say a further principle is needed to fix the regime.

**Indexing does not rescue it, and that is now checked rather than assumed.** The obvious suspicion
is that the flat `P ++ s ++ M_c` is at fault: it puts system and apparatus in one Pauli algebra, where
distinct axes anticommute, whereas independent factors commute (QLF_IndexedFactors). Recomputing with
the system on factor 1 and the apparatus on factor 2 -- which deletes exactly the cross-inversion term
between `s` and `M_c` -- gives **identical probabilities at every horizon**, for aligned, transverse and
mixed geometries alike.

The reason is structural, not a coincidence: a strand's **axis parity is determined by its imbalance**
(`n_X = #> + #<` and `imbalance_X = #> - #<` agree mod 2, and likewise for Y and Z), so within the one
imbalance class that a branch selects, the cross term is a *constant sign*. A global sign per branch
cannot survive `|A|^2`. So the flat/indexed distinction is **invisible to Born weights here**, and the
wash-out is a property of the partition itself.

The listening horizon: run, and it does not rescue the partition (--listening 2,3,4)
--------------------------------------------------------------------------------------
Closure is **capacity-relative** (`closedAtHorizon_iff_maxExcursion_le`,
lean/QLF_ClosureDepthLaw.lean), so the candidate fix was to read the weight at the observer's
listening horizon rather than at k -> infinity: keep only runs whose free action
(twist_core.spatial_free_action + local_free_action, maximised over prefixes -- the multi-pair
form of Lean's `maxExcursion`) never exceeds a capacity R. That is now measured, and it fails,
for a reason sharper than the wash-out it was meant to cure:

  * **At every capacity the aligned weight still decays to exactly 1/2**, and the capacity only
    sets the rate: |P(+) - 1/2| falls by 0.666, 0.868, 0.906 per twist at R = 2, 3, 4, so a
    preparation stays readable for tau = 2.5, 7.1, 10.1 twists. **A larger listening horizon
    remembers longer, and forgets just as completely.**
  * **What a long run keeps of the preparation is not its direction.** Against an asymmetric
    branch pair (one no relabeling can exchange, so nothing is symmetry-forced) the limit does
    depend on the preparation -- three distinct values at R = 3, one per axis class -- but a
    preparation and its **reversal** land on the same limit, exactly: `/` with `\\`, `/>` with
    `/<`, `/^` with `/v`. The sense of the prepared strand, which is precisely what a Born weight
    must depend on, is erased; only its axis class survives.
  * **Mechanism, not coincidence.** At fixed capacity the walk is a finite signed transfer
    operator whose leading eigenvalue is a degenerate +-i.lambda(R) pair (lambda = 3.991, 4.383,
    4.638 at R = 2, 3, 4, each with a 16-fold top modulus). Every preparation collapses onto that
    same dominant subspace; the direction-carrying part lives in subdominant modes and decays no
    slower than the spectral gap lambda2/lambda1 = 0.752, 0.951, 0.979.
  * **A roundoff trap, recorded because it produced a wrong answer first.** In floating point the
    subdominant part sinks under the roundoff floor at k* ~ 16 ln 10 / ln(lambda1/lambda2) -- about
    730 twists at R = 3 -- and past that the arithmetic noise, which does overlap the dominant
    subspace, is what the ratio reports: every preparation appears to converge to one universal
    limit. It does not. The scan is exact-integer by default for this reason.

So capacity does not fix the regime, and the whole family of long-horizon readings is closed:
whatever carries a Born weight is in the **transient**, at horizons comparable to the preparation
itself, which is the regime the depth scan already showed to be depth-to-horizon-ratio dependent.
Physically the substrate is saying something reasonable -- free evolution inside a bounded capacity
thermalises, and a measurement is a prompt joint closure, not an infinite free run -- but it is not
yet a Born rule.

(Terminology: "listening" is this repo's established name for the capacity-relative count -- what
a horizon of capacity R can close, as against the absolute count of ways. It is a **physical closure
capacity**, a property of which histories can close at all, not an observer's act; measurement has
no potency here.)

First joint closure: the event ends the history (--first-closure 3)
-------------------------------------------------------------------
Every scan above asks what the weight is after a prescribed k further twists, which lets a run that
already closed at depth 4 keep contributing at 5, 6, ... 700 -- and that continuation is what mixes
the census until direction is gone. But a closure IS an event; continuing past it is a longer,
different history. So the absorbing census stops each run at its **first joint closure**, whichever
branch closes it: the run chooses its own stopping depth, and no k is chosen by us. Closure with
outcome c happens exactly when the running imbalance reaches -imbalance(M_c), so the branches
compete for one absorbing hit. Cross-checked against enumeration.

What it changes, and what it does not:

  * **Direction reaches the outcome again.** Reversing the preparation changes the weights --
    P(+) = 0.688 vs 0.312 on the ZX-mix at R = 3, and 1.000 vs 0.878 for a branch pair no
    relabeling can exchange. Under every long-horizon reading a preparation and its reversal shared
    one limit exactly; under first closure they do not. The aligned geometry closes at depth 0 with
    P(+) = 1 exactly, at every capacity, and nothing else ever closes.
  * **But the complementarity is symmetry-forced, so it is bookkeeping.** Where the two branches are
    exchanged by a relabeling that also reverses the preparation, P(+|psi) + P(+|reversed psi) = 1
    is forced by QLF_BasisIndependence, and the script says so. For a branch pair no relabeling can
    exchange the sums are 1.878 and 0.352 -- not complementary. The identity is a consistency check,
    never evidence.
  * **Unweighted over depth, the stopping scale is still a knob.** P(+|d) decays monotonically
    toward 1/2 as the closure depth grows (1.000, .962, .917, ... .690 at d = 15, R = 3), so both
    pre-registered aggregations -- coherent |sum_d A_c(d)|^2 and incoherent sum_d |A_c(d)|^2 --
    drift with the cutoff, and agree with each other to three digits, so the choice between them is
    not what is at stake.
  * **The depth measure is not a free choice after all: it is counted.** First closures are
    **prefix-free** (a run that has closed is not continued, so no first-closure word extends
    another), so the global cylinder measure on the Sigma_8 tree, mu(h) = 8^-|h|, is available and
    Kraft's inequality bounds the total at 1 with no probability theory -- just finite counting: at
    a common horizon K each first closure at depth d owns 8^(K-d) of the 8^K complete histories, and
    those sets are disjoint. The QLF reading is the multiplicity one: **an earlier closure weighs
    more because more complete histories contain it.** Capacity then causes **leakage**, never
    renormalisation -- the mass that never closes here is simply missing from the total, and one
    conditions once at the end. Measured, exactly: Kraft mass 1.000 (aligned), .321 (transverse),
    .180 (ZX mix) at R = 3, always at or below 1, always monotone. An earlier version of this
    weighting divided depth by depth by the *surviving capacity-limited* population instead and
    summed past 1 (1.02, 1.11); that was the error, not the measure.
  * **Under that measure the multiplicity reading converges and the amplitude reading does not --
    and that is the sharp obstruction.** Conditioned on closure, the counting probability
    P(c | closure) is knob-free, direction-sensitive, and settling in capacity: aligned 1.000,
    transverse .500, ZX-mix .9164/.9023/.9005 at R = 3/4/5 and .8600/.8237/.8151 for the deeper mix.
    But both phase-weighted forms **diverge**: a Born weight needs |A_c(d)| to grow no faster than
    sqrt(8)^d = 2.828^d, and the measured growth is 3.91^d, 4.35^d, 4.56^d at R = 3, 4, 5 -- the gap
    *widening* with capacity. **QLF's own phases cancel too weakly to define an amplitude under the
    one measure that makes its counts summable.** And since counts are provably not weights
    (interference is real -- QLF_Degeneracy), the convergent counting probability is not a Born rule
    either. That is where the route stands: a derived measure, a convergent multiplicity, and a
    quantitative threshold (2.828^d) that the signed census misses.

The normalized-event weight: multiplicity times squared mean phase
------------------------------------------------------------------
The divergence above is a normalisation, not a verdict. The raw signed sum treats each closing
word as its own outcome; if instead the W words that close as the same event at the same depth are
W *ways of one event*, the weight carries the many-to-one normalisation:

    B(c) = sum_d  A_c(d)^2 / (W_c(d) . 8^d)  =  sum_d (W_c(d)/8^d) . (A_c(d)/W_c(d))^2
                                                 multiplicity mass    coherence fraction

-- frequency from how many ways the event happens, interference from how coherently those ways add.
Nothing is fitted: the depth factor is the cylinder measure and the divisor is the size of the event
class. **Summability is then automatic**, since |A| <= W gives A^2/W <= W and Kraft bounds the rest
(lean/QLF_KraftMeasure.lean) -- convergence no longer depends on how strongly the phases cancel.

Measured, exactly, and it is the best-behaved construction in this file:

  * it **converges absolutely and fast** -- stable to 8 digits by depth 16, with no cutoff anywhere;
  * it is **nearly capacity-independent**: the ZX mix reads .99386152 at R = 3 against .99383011 at
    R = 4, a fifth-digit difference where every earlier reading moved in the first or second;
  * the limiting cases come out right: aligned 1.000000 (one closure, at depth 0), transverse
    .500000, and reversing the preparation gives the exact complement;
  * fully coherent ways keep their whole multiplicity mass, perfectly cancelling ways weigh zero.

**And it still does not render an angle, which is the test that matters.** Sweeping the apparatus
does not sweep the weight. Adding transverse letters one at a time gives 2.acos(sqrt(P)) = 0, 8.99,
13.04, 10.37, 12.89, 11.13 degrees for a = 0..5 -- wobbling, never accumulating, where a rotation
would step. A grid of apparatus with m Z-letters and n X-letters sits at .97-.99 almost everywhere
regardless of n/m, with one outlier at (m,n) = (2,1) that inverts to .075. And *order* dominates
composition: the same two letters give exactly .5 as X-then-Z and .994 as Z-then-X. Note also that
both values this construction gets right are symmetry-forced (aligned has a single closure;
transverse is QLF_BasisIndependence), so the free content is exactly the part that does not look
like quantum mechanics.

So the measure question is settled and the amplitude question is not: the honest statement is that
this weight is well-defined, convergent and parameter-free, and that its unforced values are not a
cos^2 family. The decisive next test is a geometry with a known QM answer that is *not* forced --
two-path interference, or the singlet -- which needs multi-history closure rather than a new
weighting.

Usage:  python3 contextual_census.py [--max-k 12] [--brute-check 4] [--depth-scan 3]
        python3 contextual_census.py --listening 2,3,4 [--listen-k 160]
        python3 contextual_census.py --first-closure 3 [--closure-depth 24]
        python3 contextual_census.py --spectrum 2,3,4          (needs numpy)
"""
from __future__ import annotations
import argparse
import itertools
import math
from fractions import Fraction
from collections import defaultdict

# --------------------------------------------------------------------------- #
# the alphabet, in the canonical chart (a chart, not a frame: QLF_BasisIndependence)
# --------------------------------------------------------------------------- #
ALPHABET = '^v<>/\\+-'
CONJ_PAIRS = [('^', 'v'), ('>', '<'), ('/', '\\'), ('+', '-')]
NEG_TWISTS = set('v<\\-')
# ordv: the gauge axis is outside the order entirely; X < Y < Z
ORDV = {'>': 1, '<': 1, '^': 2, 'v': 2, '/': 3, '\\': 3, '+': 0, '-': 0}
AXIS_INDEX = {1: 0, 2: 1, 3: 2}          # X, Y, Z -> parity slot


def imbalance(word: str) -> tuple[int, int, int, int]:
    """Net signed count per conjugate pair. A run closes iff this is all zeros."""
    return tuple(word.count(a) - word.count(b) for a, b in CONJ_PAIRS)


def is_balanced(word: str) -> bool:
    return all(v == 0 for v in imbalance(word))


def free_action(imb: tuple[int, int, int, int]) -> int:
    """The repo's own free-action functional on a running imbalance: |v|+|h|+|d| + |l|
    (twist_core.spatial_free_action + local_free_action). Its maximum over prefixes is the
    capacity a run demands -- the multi-pair form of Lean's `maxExcursion`, which is exactly
    this quantity for a single conjugate pair."""
    return sum(abs(x) for x in imb)


def neg_count(word: str) -> int:
    return sum(1 for c in word if c in NEG_TWISTS)


def inv_count(word: str) -> int:
    """Inversions of the axis word: later letters that ought to precede earlier ones."""
    a = [ORDV[c] for c in word]
    return sum(1 for i in range(len(a)) for j in range(i + 1, len(a))
               if a[j] > 0 and a[j] < a[i])


def phase(word: str) -> int:
    """The proven rule (QLF_PhaseRule.phase_rule). Defined for any word; physical when balanced."""
    return (-1) ** (neg_count(word) + inv_count(word))


def axis_parities(word: str) -> tuple[int, int, int]:
    """Parities of the X, Y, Z letter multiplicities -- all the phase rule needs of a segment."""
    p = [0, 0, 0]
    for c in word:
        o = ORDV[c]
        if o:
            p[AXIS_INDEX[o]] ^= 1
    return tuple(p)


def cross_parity(pu: tuple[int, int, int], pv: tuple[int, int, int]) -> int:
    """Parity of the inversions *between* segments u and v of u ++ v.

    An inversion crosses when the later letter is the smaller: nX_v(nY_u + nZ_u) + nY_v.nZ_u.
    Only parities matter, which is what makes the whole census a finite dynamic program.
    """
    uX, uY, uZ = pu
    vX, vY, vZ = pv
    return (vX * (uY + uZ) + vY * uZ) % 2


# --------------------------------------------------------------------------- #
# the system strands, as an exact dynamic program over (imbalance, axis parities)
# --------------------------------------------------------------------------- #
def strand_census(k: int) -> dict:
    """Signed census of all 8^k system strands of length k.

    Returns {(imbalance, axis_parities): sum of (-1)^(neg + inv) over strands in that class}.
    Exact, and polynomial in k where enumeration is 8^k -- the phase rule is what allows it,
    since appending a letter costs a sign determined by parities alone.
    """
    states = {((0, 0, 0, 0), (0, 0, 0)): 1}
    for _ in range(k):
        states = _step(states)
    return states


def _step(states: dict, capacity: int | None = None, letters: str = ALPHABET,
          signed: bool = True) -> dict:
    """Extend every strand by one letter. The sign it costs is fixed by axis-count parities
    alone -- which is exactly why the phase rule turns an 8^k enumeration into a polynomial
    dynamic program.

    With `capacity=R` the walk is confined to the closure capacity: any extension whose free
    action exceeds R is dropped (see `free_action`). With `letters` a single character, the
    step feeds one prescribed letter rather than branching over the alphabet. With
    `signed=False` it counts ways instead of summing phases -- the multiplicity, not the
    amplitude.
    """
    nxt = defaultdict(int)
    for (imb, par), amp in states.items():
        for c in letters:
            o = ORDV[c]
            # new inversions: earlier letters strictly greater than c (both non-gauge)
            if o == 1:      new_inv = (par[1] + par[2]) % 2
            elif o == 2:    new_inv = par[2] % 2
            else:           new_inv = 0
            sign = (-1 if (c in NEG_TWISTS) != (new_inv == 1) else 1) if signed else 1
            d = [0, 0, 0, 0]
            for idx, (a, b) in enumerate(CONJ_PAIRS):
                if c == a: d[idx] = 1
                elif c == b: d[idx] = -1
            nimb = tuple(imb[i] + d[i] for i in range(4))
            if capacity is not None and free_action(nimb) > capacity:
                continue                                    # unhearable at this capacity
            npar = list(par)
            if o: npar[AXIS_INDEX[o]] ^= 1
            nxt[(nimb, tuple(npar))] += sign * amp
    return dict(nxt)


def amplitude(prep: str, app: str, k: int, census: dict) -> int:
    """A(c) = sum over closing strands s of phi(prep ++ s ++ app), exactly."""
    need = tuple(-(imbalance(prep)[i] + imbalance(app)[i]) for i in range(4))
    p_par, a_par = axis_parities(prep), axis_parities(app)
    base = (neg_count(prep) + neg_count(app)
            + inv_count(prep) + inv_count(app)
            + cross_parity(p_par, a_par)) % 2          # the P-M cross term, K = K(P, M)
    total = 0
    for (imb, s_par), amp in census.items():
        if imb != need:
            continue
        # the strand's own phase is already in `amp`; add both crossings it introduces
        extra = (cross_parity(p_par, s_par) + cross_parity(s_par, a_par)) % 2
        total += amp * (-1) ** ((base + extra) % 2)
    return total


def amplitude_brute(prep: str, app: str, k: int) -> int:
    """Same quantity by direct enumeration -- the cross-check on the dynamic program."""
    tot = 0
    for s in itertools.product(ALPHABET, repeat=k):
        w = prep + ''.join(s) + app
        if is_balanced(w):
            tot += phase(w)
    return tot


# --------------------------------------------------------------------------- #
# the listening horizon: closure is capacity-relative, so read the weight at capacity R
# --------------------------------------------------------------------------- #
START = {((0, 0, 0, 0), (0, 0, 0)): 1}


def _feed(states: dict, word: str, capacity: int | None, signed: bool = True) -> dict:
    """Append a prescribed word, letter by letter, under the capacity bound."""
    for c in word:
        states = _step(states, capacity, letters=c, signed=signed)
        if not states:
            return {}
    return states


def listening_amplitude(prep: str, app: str, k: int, R: int) -> int:
    """A(c) at listening capacity R: the same signed sum, but over runs whose free action
    never exceeds R at any prefix -- exactly the runs a horizon of capacity R can close
    (closedAtHorizon_iff_maxExcursion_le). Exact integers."""
    st = _feed(START, prep, R)
    for _ in range(k):
        st = _step(st, R)
        if not st:
            return 0
    st = _feed(st, app, R)
    return sum(a for (imb, _), a in st.items() if imb == (0, 0, 0, 0))


def listening_amplitude_brute(prep: str, app: str, k: int, R: int) -> int:
    """Same quantity by enumeration -- the cross-check on the capacity-bounded program."""
    tot = 0
    for s in itertools.product(ALPHABET, repeat=k):
        w = prep + ''.join(s) + app
        imb = [0, 0, 0, 0]
        ok = True
        for c in w:
            for idx, (a, b) in enumerate(CONJ_PAIRS):
                if c == a: imb[idx] += 1
                elif c == b: imb[idx] -= 1
            if free_action(tuple(imb)) > R:
                ok = False
                break
        if ok and all(v == 0 for v in imb):
            tot += phase(w)
    return tot


def listening_scan(prep: str, branches: list[str], R: int, kmax: int,
                   exact: bool = True) -> list:
    """Branch amplitudes at capacity R over horizons 0..kmax, from a single walk.

    **Exact integers by default, and that is not fussiness.** At fixed capacity the walk is a
    finite signed transfer operator whose leading eigenvalues are a degenerate +-i.lambda(R)
    pair, so the amplitude carries a subdominant, preparation-dependent part suppressed only as
    (lambda2/lambda1)^k. In floating point that part sinks below the roundoff floor at

        k* ~ 16 ln 10 / ln(lambda1/lambda2)     (about 730 twists at R = 3),

    after which the arithmetic noise -- which has full overlap with the dominant subspace --
    is what the ratio reports. Run this in floats past k* and every preparation appears to
    converge to one universal limit; that limit is an artifact of the rounding, not of the
    substrate. Exact integers cost bigint arithmetic and are worth it.
    """
    st = _feed(START, prep, R)
    if not exact:
        st = {s: float(v) for s, v in st.items()}
    out = []
    for k in range(kmax + 1):
        out.append((k, [sum(v for (imb, _), v in _feed(st, a, R).items() if imb == (0, 0, 0, 0))
                        for a in branches]))
        if not st:
            break
        st = _step(st, R)
        if not st:
            break
        if not exact:
            m = max(abs(v) for v in st.values()) or 1.0
            st = {s: v / m for s, v in st.items()}
    return out


# --------------------------------------------------------------------------- #
# geometries: preparation vs apparatus, specified independently
# --------------------------------------------------------------------------- #
def geometries() -> list[tuple[str, str, str, str, str]]:
    """(label, preparation, branch '+', branch '-', what the relabeling theorem forces)."""
    return [
        # aligned: the branch pair is exchanged by flipZ, which does NOT fix a Z preparation
        ("Z-prep, Z-apparatus (aligned)",     "/",  "\\",    "/",     "free"),
        # transverse: exchanged by flipX / flipY, which DO fix a Z preparation
        ("Z-prep, X-apparatus (transverse)",  "/",  ">\\",   "<\\",   "forced equal"),
        ("Z-prep, Y-apparatus (transverse)",  "/",  "^\\",   "v\\",   "forced equal"),
        # intermediate: the branch pair mixes an absorbed Z with a transverse letter
        ("Z-prep, ZX mix a=1",                "/",  "\\>",   "/<",    "free"),
        ("Z-prep, ZX mix a=2",                "/",  "\\>>",  "/<<",   "free"),
        ("Z-prep, ZY mix a=1",                "/",  "\\^",   "/v",    "free"),
        # a deeper preparation: two units of Z imbalance
        ("ZZ-prep, Z-apparatus (aligned)",    "//", "\\\\",  "//",    "free"),
    ]


def depth_scan(dmax: int, kmax: int) -> None:
    """How the aligned contextual weight moves as the horizon grows, per preparation depth.

    Reuses one dynamic program across all horizons, so this reaches k ~ 20 in under a minute.
    """
    geos = [(f"depth d={d} (aligned)", "/" * d, "\\" * d, "/" * d) for d in range(1, dmax + 1)]
    states = {((0, 0, 0, 0), (0, 0, 0)): 1}
    rows: dict[str, list] = {label: [] for label, _, _, _ in geos}
    for k in range(0, kmax + 1):
        for label, prep, bp, bm in geos:
            Ap = amplitude(prep, bp, k, states)
            Am = amplitude(prep, bm, k, states)
            if Ap or Am:
                rows[label].append((k, Ap * Ap / (Ap * Ap + Am * Am), (Am / Ap) if Ap else None))
        if k == kmax:
            break
        states = _step(states)
    for label, rs in rows.items():
        print(f"\n== {label}")
        print(f"   {'k':>3}  {'P(+)':>10}  {'A(-)/A(+)':>10}")
        for k, p, r in rs:
            print(f"   {k:>3}  {p:>10.6f}  {r:>10.6f}" if r is not None
                  else f"   {k:>3}  {p:>10.6f}")


# --------------------------------------------------------------------------- #
# first joint closure: the event ends the history
# --------------------------------------------------------------------------- #
def first_closure_census(prep: str, branches: list[str], R: int, dmax: int,
                         signed: bool = True) -> tuple:
    """Absorbing census: a run contributes **once**, at the depth where it first closes.

    The scans above ask what the weight is after a prescribed k further twists, which lets a run
    that already closed at depth 4 go on contributing at 5, 6, ... 700 -- and that continuation is
    what mixes the census until the preparation's direction is gone. But a closure **is** an event
    (`achieves_ZFA`); continuing past it is a different, longer history, not the same one seen
    later. So here the history stops at its first joint closure, whichever outcome closes it, and
    the stopping depth is chosen by the run rather than by us.

    Closure with outcome `c` happens exactly when the running imbalance of `prep ++ s` reaches
    `-imbalance(M_c)`, so the absorbing set is one imbalance value per branch and the branches
    **compete** for the run: the first target hit ends it. Returns
    `(A, W, open_ways)` with `A[i][d]` the signed first-closure amplitude of branch `i` at depth
    `d`, `W[i][d]` its way-count (`signed=False` run), and `open_ways[d]` the states still open.
    """
    targets = [tuple(-v for v in imbalance(app)) for app in branches]
    if len(set(targets)) < len(targets):
        raise ValueError("two branches share an absorbing target: they close together, so this "
                         "geometry does not separate outcomes")
    st = _feed(START, prep, R, signed=signed)
    A = [[] for _ in branches]
    open_ways = []
    for _ in range(dmax + 1):
        for i, (app, t) in enumerate(zip(branches, targets)):
            hit = {s: v for s, v in st.items() if s[0] == t}
            closed = _feed(hit, app, R, signed=signed)
            A[i].append(sum(v for (imb, _), v in closed.items() if imb == (0, 0, 0, 0)))
        st = {s: v for s, v in st.items() if s[0] not in targets}   # the event ends the history
        open_ways.append(len(st))
        st = _step(st, R, signed=signed)
    return A, open_ways


def first_closure_brute(prep: str, branches: list[str], R: int, d: int) -> list[int]:
    """The same first-closure amplitudes at depth d by enumeration -- the cross-check."""
    targets = [tuple(-v for v in imbalance(app)) for app in branches]
    out = [0] * len(branches)
    for s in itertools.product(ALPHABET, repeat=d):
        word = prep + ''.join(s)
        imb, hit = [0, 0, 0, 0], None
        for j, c in enumerate(word):
            for idx, (a, b) in enumerate(CONJ_PAIRS):
                if c == a: imb[idx] += 1
                elif c == b: imb[idx] -= 1
            if free_action(tuple(imb)) > R:
                hit = "over"
                break
            if j >= len(prep) - 1 and tuple(imb) in targets:      # a closure, at strand depth
                hit = (j - len(prep) + 1, targets.index(tuple(imb)))
                break
        if hit == "over" or hit is None:
            continue
        # the preparation itself may already sit on a target: that is a closure at depth 0
        depth, which = hit
        if depth != d:
            continue
        full = word + branches[which]
        run, ok = [0, 0, 0, 0], True
        for c in full:
            for idx, (a, b) in enumerate(CONJ_PAIRS):
                if c == a: run[idx] += 1
                elif c == b: run[idx] -= 1
            if free_action(tuple(run)) > R:
                ok = False
                break
        if ok and all(v == 0 for v in run):
            out[which] += phase(full)
    return out


def capacity_spectrum(R: int) -> tuple:
    """The capacity-R transfer operator's spectrum: what sets the forgetting rate.

    Returns (dimension, |lambda1|, multiplicity of the top modulus, |lambda2|). The leading
    eigenvalue is a degenerate +-i.lambda pair, so amplitudes turn as well as grow, and the gap
    |lambda2|/|lambda1| is how fast everything but the dominant subspace -- the preparation's
    imprint included -- is forgotten.
    """
    import numpy as np                                   # only this mode needs it
    rng = range(-R, R + 1)
    states = [((a, b, c, d), (p & 1, (p >> 1) & 1, (p >> 2) & 1))
              for a in rng for b in rng for c in rng for d in rng
              if abs(a) + abs(b) + abs(c) + abs(d) <= R for p in range(8)]
    idx = {s: i for i, s in enumerate(states)}
    T = np.zeros((len(states), len(states)))
    for s, i in idx.items():
        for t, v in _step({s: 1}, R).items():
            T[idx[t], i] += v
    mags = np.abs(np.linalg.eigvals(T))
    l1 = mags.max()
    top = int((mags > l1 - 1e-7).sum())
    l2 = mags[mags < l1 - 1e-7].max()
    return len(states), l1, top, l2


def cylinder_readings(prep: str, branches: list[str], R: int, dmax: int) -> dict:
    """Aggregate the first-closure census under the **global cylinder measure** mu(h) = 8^-|h|.

    This is the one weighting over closure depths that is derived rather than chosen. A first
    closure at depth d is the prefix of 8^(K-d) equally generable futures out of 8^K, so relative
    to any common horizon its share is exactly 8^-d: an earlier closure weighs more because more
    complete histories contain it. And because first closures are **prefix-free** -- a run that
    closed at depth d is not continued, so no first-closure word extends another -- Kraft's
    inequality gives, with no probability theory at all,

        sum over first closures of 8^-|h|  <=  1,

    the leftover being the runs that never close here (they exceed the capacity, or wander
    forever). Capacity therefore causes **leakage**, never renormalisation: normalising depth by
    depth against the surviving capacity-limited population is what pushed an earlier version of
    this sum past 1 (measured 1.02, 1.11), and that was the error, not the measure.

    Returns the Kraft mass, its per-branch split (the multiplicity reading), and both
    phase-weighted forms with the growth diagnostic that decides whether they converge at all.
    """
    A, _ = first_closure_census(prep, branches, R, dmax)
    W, _ = first_closure_census(prep, branches, R, dmax, signed=False)
    mass = [sum(Fraction(W[i][d], 8 ** d) for d in range(dmax + 1)) for i in range(len(branches))]
    total = sum(mass)
    # the two phase-weighted forms: amplitude per measure-weighted way
    inc = [sum(Fraction(A[i][d] ** 2, 8 ** d) for d in range(dmax + 1)) for i in range(len(branches))]
    coh = [sum(A[i][d] / math.sqrt(8) ** d for d in range(dmax + 1)) for i in range(len(branches))]
    # do they converge? |A(d)| ~ a^d needs a < sqrt(8) for sum 8^-d |A|^2 to exist
    ds = [d for d in range(dmax + 1) if A[0][d]]
    growth = float('nan')
    if len(ds) >= 4:
        d0, d1 = ds[len(ds) // 2], ds[-1]
        growth = (abs(A[0][d1]) / abs(A[0][d0])) ** (1.0 / (d1 - d0))
    return {"kraft": total, "mass": mass, "incoherent": inc, "coherent": coh,
            "amplitude_growth": growth, "threshold": math.sqrt(8)}


# --------------------------------------------------------------------------- #
# event identity: which distinct words are ways of the *same* closure
# --------------------------------------------------------------------------- #
def event_classes(prep: str, branches: list[str], R: int, dmax: int,
                  signature) -> dict:
    """Enumerate first-closure runs one by one and group them by `signature`.

    `normalized_event_weights` takes the event to be `(branch, depth)`: every word closing the
    same branch at the same depth is one event. That is a *choice*, and by Cauchy-Schwarz in Engel
    form it is the extreme one -- `(ΣA)²/ΣW ≤ Σ A²/W` -- so **refining the quotient can only raise
    the weight**, with the finest quotient (each word its own event) giving exactly the multiplicity
    mass `W/8^d`. Every possible notion of "same event" therefore lies between those two, which is
    why this function exists to *test* derived candidates rather than to search for a fitting one.

    `signature(branch_index, depth, strand, run) -> hashable` names the event. Returns
    `{key: (W, A, depth, branch)}`.
    """
    targets = [tuple(-v for v in imbalance(app)) for app in branches]
    out: dict = {}
    prep_imb = imbalance(prep)
    if free_action(prep_imb) > R:
        return out

    def walk(strand: str, imb: tuple, depth: int) -> None:
        for i, (app, t) in enumerate(zip(branches, targets)):
            if imb == t:                                   # first joint closure: the event
                run = prep + strand + app
                ok, cur = True, [0, 0, 0, 0]
                for c in run:
                    for idx, (a, b) in enumerate(CONJ_PAIRS):
                        if c == a: cur[idx] += 1
                        elif c == b: cur[idx] -= 1
                    if free_action(tuple(cur)) > R:
                        ok = False
                        break
                if ok and all(v == 0 for v in cur):
                    key = signature(i, depth, strand, run)
                    W, A, _, _ = out.get(key, (0, 0, depth, i))
                    out[key] = (W + 1, A + phase(run), depth, i)
                return                                     # absorbed either way
        if depth >= dmax:
            return
        for c in ALPHABET:
            d = [0, 0, 0, 0]
            for idx, (a, b) in enumerate(CONJ_PAIRS):
                if c == a: d[idx] = 1
                elif c == b: d[idx] = -1
            nimb = tuple(imb[j] + d[j] for j in range(4))
            if free_action(nimb) > R:
                continue
            walk(strand + c, nimb, depth + 1)

    walk("", prep_imb, 0)
    return out


def prefixed_first_closure(prep: str, branches: list[str], R: int, dmax: int,
                           path: str, signed: bool = True) -> list:
    """First-closure census restricted to strands that begin with `path`.

    A **path** is a family of system histories sharing an opening segment -- the substrate's
    version of "which arm did it take". Depth counts strand twists including the opening segment,
    so two paths of equal opening length land in the same `(branch, depth)` event class and their
    amplitudes add there.
    """
    targets = [tuple(-v for v in imbalance(app)) for app in branches]
    st = _feed(START, prep, R, signed=signed)
    A = [[0] * (dmax + 1) for _ in branches]
    depth = 0
    for step in range(dmax + 1):
        for i, t in enumerate(targets):
            hit = {s: v for s, v in st.items() if s[0] == t}
            closed = _feed(hit, branches[i], R, signed=signed)
            A[i][step] = sum(v for (imb, _), v in closed.items() if imb == (0, 0, 0, 0))
        st = {s: v for s, v in st.items() if s[0] not in targets}
        if step == dmax:
            break
        st = (_step(st, R, letters=path[step], signed=signed) if step < len(path)
              else _step(st, R, signed=signed))
    return A


def quotient_probability(classes: dict, branch: int = 0) -> float:
    """P(branch | closure) under a given event quotient: Σ_E A_E²/(W_E·8^{d_E}), conditioned."""
    tot = [Fraction(0), Fraction(0)]
    for W, A, d, i in classes.values():
        if W:
            tot[i] += Fraction(A * A, W * 8 ** d)
    s = tot[0] + tot[1]
    return float(tot[branch] / s) if s else float('nan')


def axis_counts(word: str) -> tuple:
    """How many twists on each axis (order forgotten) -- a candidate physical invariant."""
    x = sum(1 for c in word if ORDV[c] == 1)
    y = sum(1 for c in word if ORDV[c] == 2)
    z = sum(1 for c in word if ORDV[c] == 3)
    return (x, y, z, len(word) - x - y - z)


def max_free_action(word: str) -> int:
    """The capacity the run demands: max prefix free action (the multi-pair `maxExcursion`)."""
    imb, m = [0, 0, 0, 0], 0
    for c in word:
        for idx, (a, b) in enumerate(CONJ_PAIRS):
            if c == a: imb[idx] += 1
            elif c == b: imb[idx] -= 1
        m = max(m, free_action(tuple(imb)))
    return m


def normalized_event_weights(prep: str, branches: list[str], R: int, dmax: int) -> list:
    """The **normalized-event** weight: multiplicity times squared mean phase.

    The raw signed sum treats each first-closure word as its own outcome. If instead the `W`
    words that close as the same event at the same depth are `W` *ways of one event*, the event's
    weight carries the many-to-one normalisation, and the aggregate becomes

        B(c) = sum_d  A_c(d)^2 / (W_c(d) . 8^d)
             = sum_d  (W_c(d)/8^d) . (A_c(d)/W_c(d))^2
               \\_____________/   \\________________/
                multiplicity mass   coherence fraction

    -- frequency from how many ways the event happens, interference from how coherently those
    ways add. Nothing is fitted: the depth factor is the cylinder measure (see `cylinder_readings`)
    and the normalisation is the size of the event class.

    **It is summable for free**, which the raw forms were not: |A| <= W gives A^2/W <= W, so
    B(c) <= sum_d W_c(d)/8^d <= 1 by Kraft (lean/QLF_KraftMeasure.lean, `twist_kraft`). Convergence
    no longer depends on how strongly the phases cancel. Exact rationals throughout.
    """
    A, _ = first_closure_census(prep, branches, R, dmax)
    W, _ = first_closure_census(prep, branches, R, dmax, signed=False)
    return [sum(Fraction(A[i][d] ** 2, W[i][d] * 8 ** d)
                for d in range(dmax + 1) if W[i][d])
            for i in range(len(branches))]


def coherent_limits(prep: str, branches: list[str], R: int, dmax: int) -> tuple:
    """The **unnormalized** coherent weight, exactly, where the census is summable.

    The event normalisation was introduced to make the weight converge, and it cost constructive
    interference (`merge_le_sum`). Drop it and the weight is the honest amplitude,

        T_c = sum_d A_c(d) . 8^(-d/2),      P(c) = |T_c|^2 / sum_j |T_j|^2,

    which converges exactly when the signed census grows slower than sqrt(8)^d -- and at **capacity
    2 it does** (2.59^d, 2.24^d measured) while at capacity 3 and above it does not (3.90^d, 4.34^d).
    So there is a low-capacity **window** in which the census is both summable and interference-
    capable, which the sub-additivity no-go does not reach.

    Closures of one geometry share a depth parity, so `8^(-d/2)` factors as a common irrational
    times a rational and the *ratio* -- hence `P(c)` -- is an exact rational. Returns
    `(T_limits, P_plus, summable, growth)` with the limits as `Fraction`s.
    """
    A, _ = first_closure_census(prep, branches, R, dmax)
    depths = [d for d in range(dmax + 1) if any(A[i][d] for i in range(len(branches)))]
    if not depths:
        return None, None, None, float('nan')
    par = depths[0] % 2
    if any(d % 2 != par for d in depths):
        return None, None, None, float('nan')          # mixed parity: needs Q(sqrt 2)
    # measure the growth from the TERMS of the series, in its tail -- a two-point fit taken too
    # early reads a transient: the same geometry gives 8.16 at depth 90 and 0.19 at depth 200
    terms = [(d, max(abs(A[i][d]) for i in range(len(branches)))) for d in depths]
    growth = float('nan')
    if len(terms) >= 6 and all(t > 0 for _, t in terms[-5:]):
        step = terms[-1][0] - terms[-2][0]
        ratio = (terms[-1][1] / terms[-5][1]) ** (1.0 / 4)      # per closure step
        growth = ratio ** (1.0 / step)                          # per depth
    T = []
    for i in range(len(branches)):
        num = sum(A[i][d] * 2 ** (3 * (dmax - d) // 2) for d in range(par, dmax + 1, 2))
        T.append(Fraction(num, 2 ** (3 * (dmax - par) // 2)))
    den = sum(t * t for t in T)
    P = (T[0] * T[0] / den) if den else None
    # a geometry that closes at one depth only is a finite sum: summable with nothing to check
    summable = True if growth != growth else (growth < math.sqrt(8))
    return T, P, summable, growth


def coherent_report(R: int, dmax: int) -> list[str]:
    """Read the geometries with the unnormalized weight, and say whether it exists at all."""
    failures: list[str] = []
    thr = math.sqrt(8)
    print(f"\n===== unnormalized coherent weight at capacity R = {R}"
          f"   (summable iff |A(d)| grows slower than {thr:.4f}^d)")
    for label, prep, bp, bm, forced in geometries():
        try:
            T, P, ok, growth = coherent_limits(prep, [bp, bm], R, dmax)
        except ValueError as exc:
            print(f"  {label}: {exc}")
            continue
        if T is None:
            print(f"  {label}: nothing closes here, or the closure depths are of mixed parity")
            continue
        state = ("one closure depth, finite sum" if growth != growth else
                 "summable" if ok else "DIVERGES")
        # a^2 is the informative number: measured values sit on integers at and below the
        # threshold of 8, and only above it do irrationals appear
        rate = "-" if growth != growth else f"{growth:.4f}^d  (a^2 = {growth * growth:.6f})"
        # the tail is geometric, so a truncation at dmax reconstructs the exact rational limit
        approx = T[0].limit_denominator(10 ** 5), T[1].limit_denominator(10 ** 5)
        print(f"  {label:<34} |A(d)| ~ {rate:<9} [{state}]")
        if ok:
            print(f"     T+ = {approx[0]}   T- = {approx[1]}   "
                  f"P(+) = {(P.limit_denominator(10 ** 5) if P is not None else '-')}"
                  f" = {float(P):.9f}")
            if forced == "forced equal" and T[0] != T[1]:
                failures.append(f"R={R} {label}: a preparation-fixing relabeling exchanges these "
                                f"branches, so QLF_BasisIndependence forces equality")
    print("  -- where this converges the weight is the plain amplitude, with no per-event "
          "normalisation,\n     so merging paths adds amplitudes and interference is available "
          "in both directions.")
    return failures


def two_path_report(R: int, dmax: int) -> list[str]:
    """The four-run interference test: A alone, B alone, both, and both with one path reversed.

    A **path** is a family of histories sharing an opening segment. Opening both merges them into
    one detector event, so their amplitudes add *before* the event normalisation. The weight is the
    fixed one -- nothing new is introduced for this test:

        B(E) = sum_d A_E(d)^2 / (W_E(d) . 8^d).

    The prediction being tested is quantum mechanics' interference identity: two coherent paths of
    equal amplitude should give |A+A|^2 = 4|A|^2 against |A|^2 + |A|^2, a factor of **two**.
    """
    failures: list[str] = []
    prep, branches = "/", ["\\>", "/<"]

    def census(path: str):
        return (prefixed_first_closure(prep, branches, R, dmax, path),
                prefixed_first_closure(prep, branches, R, dmax, path, signed=False))

    def mass(A, W, i=0):
        return sum(Fraction(A[i][d] ** 2, W[i][d] * 8 ** d)
                   for d in range(len(A[i])) if W[i][d])

    print(f"\n===== two-path interference at capacity R = {R}   prep={prep!r} "
          f"branches={branches}")
    for pa, pb, label in [("+", "-", "matched pair (equal amplitudes)"),
                          ("+", ">", "unequal pair")]:
        Aa, Wa = census(pa)
        Ab, Wb = census(pb)
        ba, bb = mass(Aa, Wa), mass(Ab, Wb)
        merged = [[Aa[i][d] + Ab[i][d] for d in range(dmax + 1)] for i in (0, 1)]
        opposed = [[Aa[i][d] - Ab[i][d] for d in range(dmax + 1)] for i in (0, 1)]
        Wm = [[Wa[i][d] + Wb[i][d] for d in range(dmax + 1)] for i in (0, 1)]
        bm, bn = mass(merged, Wm), mass(opposed, Wm)
        s = ba + bb
        print(f"  {label}: paths {pa!r} and {pb!r}")
        print(f"     B(A) = {float(ba):.6e}    B(B) = {float(bb):.6e}    sum = {float(s):.6e}")
        print(f"     B(A+B) = {float(bm):.6e}   ratio to sum = {float(bm / s):.6f}"
              f"   {'(quantum mechanics needs 2.0 here)' if pa == '+' and pb == '-' else ''}")
        print(f"     B(A-B) = {float(bn):.6e}   ratio to sum = {float(bn / s):.6f}"
              f"   destructive interference does work")
        if bm > s:
            failures.append(f"R={R} {label}: B(A+B) exceeded B(A)+B(B), contradicting "
                            f"QLF_KraftMeasure.merge_le_sum")
    print("  -- merging ways into one event can only lower the weight (merge_le_sum), so no path "
          "pair\n     can ever enhance a detection: constructive interference is unavailable to "
          "this weight.")
    return failures


def first_closure_report(capacities: list[int], dmax: int) -> list[str]:
    """The absorbing census, read at the depth the run itself chooses.

    Two aggregations over closure depth are fixed **before** any number is looked at, because a
    rule chosen after seeing the answer is a fitted parameter:

        coherent    P(c) proportional to |sum_d A_c(d)|^2      (one event, interfering depths)
        incoherent  P(c) proportional to sum_d |A_c(d)|^2      (distinct events, added frequencies)

    Both are reported at several cutoffs, since a value that moves with the cutoff has not earned
    the name probability.
    """
    failures: list[str] = []
    for R in capacities:
        print(f"\n===== first joint closure at capacity R = {R}")
        print("   (weights below use the global cylinder measure mu(h) = 8^-|h| on the Sigma_8 "
              "tree,\n    the one weighting over closure depths that is counted rather than chosen)")
        for label, prep, bp, bm, forced in geometries():
            try:
                A, _ = first_closure_census(prep, [bp, bm], R, dmax)
                W, _ = first_closure_census(prep, [bp, bm], R, dmax, signed=False)
            except ValueError as exc:
                print(f"  {label}: {exc}")
                continue
            depths = [d for d in range(dmax + 1) if A[0][d] or A[1][d]]
            if not depths:
                print(f"  {label}: nothing closes at this capacity")
                continue
            print(f"  {label}   [{forced}]   first closes at d = {depths[0]}")
            for d in depths[:3] + ([None] + depths[-2:] if len(depths) > 5 else []):
                if d is None:
                    print("     ...")
                    continue
                p = A[0][d] ** 2 / (A[0][d] ** 2 + A[1][d] ** 2)
                print(f"     d={d:>3}   A+ = {A[0][d]:>14}  A- = {A[1][d]:>14}   "
                      f"ways {W[0][d]:>12} / {W[1][d]:<12}   P(+|d) = {p:.6f}")
                if forced == "forced equal" and A[0][d] != A[1][d]:
                    failures.append(f"R={R} {label} d={d}: branches exchanged by a preparation-fixing "
                                    f"relabeling must have equal amplitudes (QLF_BasisIndependence)")
            for cut in sorted({depths[0], depths[len(depths) // 2], depths[-1]}):
                coh = [sum(A[i][:cut + 1]) for i in (0, 1)]
                inc = [sum(x * x for x in A[i][:cut + 1]) for i in (0, 1)]
                tc, ti = coh[0] ** 2 + coh[1] ** 2, inc[0] + inc[1]
                print(f"     unweighted, cutoff D={cut:>3}   coherent P(+) = {coh[0] ** 2 / tc:.6f}"
                      f"   incoherent P(+) = {inc[0] / ti:.6f}")

            # the derived weighting: the global cylinder measure 8^-d
            cyl = cylinder_readings(prep, [bp, bm], R, dmax)
            k = cyl["kraft"]
            if k > 1:
                failures.append(f"R={R} {label}: Kraft mass {float(k):.6f} exceeds 1 -- the "
                                f"first-closure set is not prefix-free, or a run was counted twice")
            ways = float(cyl["mass"][0] / k) if k else float('nan')
            print(f"     cylinder measure 8^-d:  Kraft mass = {float(k):.6f} "
                  f"(the rest never closes here)   multiplicity P(+|closure) = {ways:.6f}")
            B = normalized_event_weights(prep, [bp, bm], R, dmax)
            tb = B[0] + B[1]
            if tb:
                print(f"     normalized-event weight (multiplicity x squared mean phase): "
                      f"P(+) = {float(B[0] / tb):.8f}")
                if tb > 1:
                    failures.append(f"R={R} {label}: normalized-event mass {float(tb):.6f} exceeds "
                                    f"the Kraft bound of 1")
            g, thr = cyl["amplitude_growth"], cyl["threshold"]
            if g != g:                                   # a single closure depth: nothing to sum
                print("     phase-weighted forms: one closure depth only, so the weighting "
                      "question does not arise here")
            else:
                verdict = "converges" if g < thr else "DIVERGES, so no Born weight exists under it"
                print(f"     phase-weighted forms: |A(d)| ~ {g:.3f}^d against the {thr:.3f}^d the "
                      f"measure needs, so the amplitude sum {verdict}")

        # --- does the preparation's DIRECTION still reach the outcome? ---------------
        print("  -- direction test: the same apparatus against a preparation and its reversal")
        for label, prep, bp, bm in [("branches a relabeling exchanges", "/", "\\", "/"),
                                    ("branches a relabeling exchanges", "/", "\\>", "/<"),
                                    ("branches NO relabeling exchanges", "/", "\\", "/>>")]:
            vals = {}
            for p in (prep, "\\" if prep == "/" else "/"):
                A, _ = first_closure_census(p, [bp, bm], R, dmax)
                coh = [sum(A[i]) for i in (0, 1)]
                t = coh[0] ** 2 + coh[1] ** 2
                vals[p] = coh[0] ** 2 / t if t else float('nan')
            a, b = vals[prep], vals["\\" if prep == "/" else "/"]
            note = ("complementary -- but FORCED by QLF_BasisIndependence, so bookkeeping"
                    if abs(a + b - 1) < 1e-9 else "not complementary, as expected here")
            print(f"     {label:<34} ({bp!r},{bm!r}):  P(+) = {a:.6f} vs {b:.6f}   sum {a + b:.6f}"
                  f"   [{note}]")
            if a == b:
                failures.append(f"R={R} {bp!r}/{bm!r}: reversing the preparation changed nothing -- "
                                f"first closure is supposed to be direction-sensitive")
    return failures


def listening_report(capacities: list[int], kmax: int) -> list[str]:
    """Read the contextual weight at a finite listening horizon, and measure what survives it.

    Per capacity R: the scaling table of the standard geometries; what a long free run retains of
    the preparation; and how fast it stops retaining it.
    """
    failures: list[str] = []
    # an asymmetric branch pair -- no relabeling exchanges these, so any preparation dependence
    # is free to show itself rather than being forced away by QLF_BasisIndependence
    probe = ["\\", "/>>"]
    # each row is a preparation and its DIRECTION REVERSAL: same axis, opposite sense
    reversed_pairs = [("/", "\\"), ("/>", "/<"), ("/^", "/v")]

    for R in capacities:
        print(f"\n===== listening capacity R = {R}  "
              f"(runs whose free action never exceeds {R} at any prefix)")
        for label, prep, bp, bm, forced in geometries():
            rows = [(k, a[0], a[1]) for k, a in listening_scan(prep, [bp, bm], R, kmax)
                    if a[0] or a[1]]
            if not rows:
                print(f"  {label}: no run closes at this capacity")
                continue
            print(f"  {label}   [{forced}]")
            for row in rows[:3] + ([None] + rows[-2:] if len(rows) > 5 else []):
                if row is None:
                    print("     ...")
                    continue
                k, Ap, Am = row
                print(f"     k={k:>4}   P(+) = {Ap * Ap / (Ap * Ap + Am * Am):.9f}"
                      + (f"   A-/A+ = {Am / Ap:+.9f}" if Ap else ""))
                if forced == "forced equal" and Ap != Am:
                    failures.append(f"R={R} {label} k={k}: a preparation-fixing relabeling exchanges "
                                    f"these branches, so QLF_BasisIndependence forces equality")

        # --- what a long free run retains of the preparation ------------------------
        print(f"  -- what survives: limit of A(-)/A(+) for branches {probe}")
        for prep, rev in reversed_pairs:
            lim, drift = {}, {}
            for p in (prep, rev):
                seq = [a[1] / a[0] for _, a in listening_scan(p, probe, R, kmax) if a[0]]
                if seq:
                    lim[p] = seq[-1]
                    drift[p] = abs(seq[-1] - seq[-3]) if len(seq) >= 3 else float('inf')
            if len(lim) < 2:
                continue
            gap = abs(lim[prep] - lim[rev])
            # neither sequence has reached its own limit yet, so the pair can only be asked to agree
            # to within the drift each still has left -- a tighter test would just be reading noise
            tol = max(3 * max(drift[prep], drift[rev]), 1e-12)
            print(f"     {prep!r:>5} -> {lim[prep]:+.9f}      its reversal {rev!r:>5} -> "
                  f"{lim[rev]:+.9f}      |difference| = {gap:.1e}  (still drifting by {tol / 3:.1e})")
            if gap > tol:
                failures.append(f"R={R}: {prep!r} and {rev!r} differ by {gap:.1e}, more than the "
                                f"{tol:.1e} their own convergence allows -- they do NOT share a limit")

        # --- how fast the preparation stops being readable --------------------------
        rows = [(k, a[0], a[1]) for k, a in listening_scan("/", ["\\", "/"], R, kmax)
                if a[0] or a[1]]
        pts = [(k, abs(Ap * Ap / (Ap * Ap + Am * Am) - 0.5)) for k, Ap, Am in rows]
        pts = [(k, e) for k, e in pts if 1e-9 < e < 0.1]
        if len(pts) >= 4:
            (k0, e0), (k1, e1) = pts[0], pts[-1]
            decay = (e1 / e0) ** (1.0 / (k1 - k0))
            tau = -1.0 / math.log(decay)
            print(f"  -- coherence: on the aligned geometry |P(+) - 1/2| falls by {decay:.4f} per "
                  f"twist, so a preparation stays readable for tau = {tau:.1f} twists at R = {R}")
            if e1 >= e0:
                failures.append(f"R={R}: the aligned weight is not decaying toward 1/2")
    return failures


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--max-k", type=int, default=12, help="largest system-strand horizon")
    ap.add_argument("--brute-check", type=int, default=4,
                    help="verify the DP against enumeration up to this horizon (8^k words; 6 is slow)")
    ap.add_argument("--depth-scan", type=int, default=0, metavar="DMAX",
                    help="instead of the battery, scan preparation depths 1..DMAX over horizons")
    ap.add_argument("--listening", type=str, default="", metavar="R1,R2,...",
                    help="read the weight at finite listening capacities instead (closure is "
                         "capacity-relative: closedAtHorizon_iff_maxExcursion_le)")
    ap.add_argument("--first-closure", type=str, default="", metavar="R1,R2,...",
                    help="absorbing census: the history ends at its first joint closure, so the run "
                         "chooses its own stopping depth")
    ap.add_argument("--coherent", type=str, default="", metavar="R",
                    help="the UNNORMALIZED coherent weight at capacity R, with exact rational "
                         "limits where the census is summable")
    ap.add_argument("--two-path", type=str, default="", metavar="R",
                    help="four-run interference test at capacity R: A alone, B alone, both, and "
                         "both with one path reversed")
    ap.add_argument("--closure-depth", type=int, default=24,
                    help="deepest first-closure depth to enumerate")
    ap.add_argument("--spectrum", type=str, default="", metavar="R1,R2,...",
                    help="report the capacity-R transfer operator's spectrum: the forgetting rate "
                         "quoted by the listening scan is its spectral gap")
    ap.add_argument("--listen-k", type=int, default=600,
                    help="horizon to carry the listening scan to (the limit needs k >> tau(R))")
    args = ap.parse_args()

    if args.spectrum:
        print("== the capacity-R transfer operator (needs numpy)")
        print("   tau_gap is the SLOWEST forgetting time the operator allows (the global gap); a "
              "given\n   geometry may forget faster, as the aligned one does.")
        print(f"   {'R':>3}  {'states':>8}  {'|lambda1|':>10}  {'top mult':>9}  {'|lambda2|':>10}  "
              f"{'gap':>8}  {'tau_gap':>8}")
        for R in [int(x) for x in args.spectrum.split(",")]:
            n, l1, top, l2 = capacity_spectrum(R)
            gap = l2 / l1
            print(f"   {R:>3}  {n:>8}  {l1:>10.6f}  {top:>9}  {l2:>10.6f}  {gap:>8.6f}  "
                  f"{-1 / math.log(gap):>8.1f}")
        return

    if args.coherent:
        R = int(args.coherent)
        failures = coherent_report(R, args.closure_depth)
        print("\n== invariants")
        if failures:
            for f in failures:
                print(f"     - {f}")
            raise SystemExit(1)
        print("   all asserted invariants hold")
        return

    if args.two_path:
        failures = two_path_report(int(args.two_path), args.closure_depth)
        print("\n== invariants")
        if failures:
            for f in failures:
                print(f"     - {f}")
            raise SystemExit(1)
        print("   all asserted invariants hold (no path pair beat the sub-additivity bound)")
        return

    if args.first_closure:
        caps = [int(x) for x in args.first_closure.split(",")]
        print("== cross-check: absorbing program vs brute-force enumeration")
        bad = []
        for R in caps[:2]:
            for label, prep, bp, bm, _ in geometries():
                try:
                    A, _ = first_closure_census(prep, [bp, bm], R, min(args.brute_check, 4))
                except ValueError:
                    continue
                for d in range(min(args.brute_check, 4) + 1):
                    if [A[0][d], A[1][d]] != first_closure_brute(prep, [bp, bm], R, d):
                        bad.append(f"R={R} d={d} {prep!r}")
        print(f"   {'OK' if not bad else 'MISMATCH: ' + ', '.join(bad)}")
        failures = bad + first_closure_report(caps, args.closure_depth)
        print("\n== invariants")
        if failures:
            print("   FAILURES:")
            for f in failures:
                print(f"     - {f}")
            raise SystemExit(1)
        print("   all asserted invariants hold (absorbing program = enumeration; symmetric branch "
              "pairs exactly equal; reversing the preparation changes the outcome weights; the "
              "Kraft mass of\n   the prefix-free first-closure set stays at or below 1)")
        return

    if args.listening:
        caps = [int(x) for x in args.listening.split(",")]
        print("== cross-check: capacity-bounded program vs brute-force enumeration")
        bad = []
        for R in caps[:2]:
            for k in range(0, min(args.brute_check, 3) + 1):
                for label, prep, bp, bm, _ in geometries():
                    for app in (bp, bm):
                        if listening_amplitude(prep, app, k, R) != listening_amplitude_brute(prep, app, k, R):
                            bad.append(f"R={R} k={k} {prep!r}/{app!r}")
        print(f"   {'OK' if not bad else 'MISMATCH: ' + ', '.join(bad)}")
        failures = bad + listening_report(caps, args.listen_k)
        print("\n== invariants")
        if failures:
            print("   FAILURES:")
            for f in failures:
                print(f"     - {f}")
            raise SystemExit(1)
        print("   all asserted invariants hold (capacity program = enumeration; symmetric branch "
              "pairs exactly equal; a preparation and its reversal share one limit; the aligned "
              "weight decays toward 1/2)")
        return

    if args.depth_scan:
        depth_scan(args.depth_scan, args.max_k)
        return

    failures: list[str] = []

    # ---- the preparation must be an OPEN strand, or it prepares nothing -------------
    for label, prep, bp, bm, _ in geometries():
        if is_balanced(prep):
            failures.append(f"{label}: preparation {prep!r} is already closed, so it prepares nothing")

    # ---- the dynamic program must agree with enumeration ---------------------------
    print("== cross-check: dynamic program vs brute-force enumeration")
    for k in range(0, args.brute_check + 1):
        cen = strand_census(k)
        for label, prep, bp, bm, _ in geometries():
            for app in (bp, bm):
                a1 = amplitude(prep, app, k, cen)
                a2 = amplitude_brute(prep, app, k)
                if a1 != a2:
                    failures.append(f"DP != brute force at k={k}, {prep!r}/{app!r}: {a1} vs {a2}")
    print(f"   checked all geometries for k <= {args.brute_check}: "
          f"{'OK' if not failures else 'MISMATCH'}")

    # ---- the scaling tables --------------------------------------------------------
    censuses = {k: strand_census(k) for k in range(0, args.max_k + 1)}
    for label, prep, bp, bm, forced in geometries():
        print(f"\n== {label}    prep={prep!r}  branches=({bp!r}, {bm!r})   [{forced}]")
        print(f"   {'k':>3}  {'A(+)':>12} {'A(-)':>12}   {'P(+)':>8}")
        for k in range(0, args.max_k + 1):
            Ap = amplitude(prep, bp, k, censuses[k])
            Am = amplitude(prep, bm, k, censuses[k])
            if Ap == 0 and Am == 0:
                continue                                    # no run of this length closes
            tot = Ap * Ap + Am * Am
            print(f"   {k:>3}  {Ap:>12} {Am:>12}   {Ap * Ap / tot:>8.5f}")
            if forced == "forced equal" and Ap != Am:
                failures.append(f"{label} k={k}: branches exchanged by a preparation-fixing "
                                f"relabeling must have equal amplitudes (QLF_BasisIndependence), "
                                f"got {Ap} vs {Am}")

    print("\n== invariants")
    if failures:
        print("   FAILURES:")
        for f in failures:
            print(f"     - {f}")
        raise SystemExit(1)
    print("   all asserted invariants hold "
          "(DP = enumeration; symmetric branch pairs exactly equal; preparations open)")


if __name__ == "__main__":
    main()
