# Gluon Abelian control: does the non-Abelian vertex do work on singlet distance? (#286)

Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF. Issue #286 asks what
a gluon interaction does to the remaining distance `d_G` to colour-singlet closure. Its blocker,
GL2, is a colour move relation taken from the non-Abelian gluon algebra rather than from `d_G`.
PR #289 supplies one: two vertex channels on multisets of nonzero `F₃²` colour labels, both gated
by non-collinearity `symp(q, r) ≠ 0`, the condition for a nonzero three-gluon vertex
([`lean/QLF_GluonVertex.lean`](lean/QLF_GluonVertex.lean), `gluon_vertex_iff`):

* **create:** for non-collinear `q, r` in the state, add `p = −(q + r)`;
* **glue:** for non-collinear `q, r`, replace them by `p`.

PR #289 reports that every move producing a first singlet reduces `d_G`. This note asks two
questions the issue's guidance calls for, an independent algebraic test of that relation, before
any physical reading.

## §1 Pre-registration (committed before the companion script was run)

### Tests

The states, channels and search bound are #289's: multisets of size 1 to 4 over the eight nonzero
labels, singlet = total colour `0`, shortest path with intermediate sizes `≤ 5`. The **Abelian
control** is the same two channels with the gate removed: any pair `q, r` with `q + r ≠ 0` (so that
`p` is a label). It keeps colour addition and drops the only non-Abelian ingredient.

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| A1 | the first-singlet result can fail | some move relation on these states has a move into a singlet that does not reduce `d` | **fail**: for any relation, a move from a non-singlet (`d ≥ 1`) to a singlet (`d = 0`) reduces `d`. So #289's first-singlet result is bookkeeping by rule 4 |
| A2 | gated `d_G` is fixed by Abelian data | `d_G` is a function of the total colour and the multiset size | none stated |
| A3 | the gate changes distance | some state has a different `d_G` in the gated relation and in the Abelian control | none stated |
| A4 | the gate changes reachability | some state reaches a singlet in one relation and not the other | pass: `{(1,0), (1,0)}` has no non-collinear pair, so it is blocked when gated, and reaches `{(1,0)×3}` (total `0`) in one Abelian create |
| A5 | the gate changes the move classes | the counts of reducing, neutral and increasing moves differ between the two relations | none stated |

**Verdict rule.** A1 is recorded as a check on the existing claim, not a result. If A3 and A5 fail
and A4 passes only on states with no non-collinear pair, the non-Abelian vertex gates which states
can move at all but does no work on distance once a state can move, and `d_G` is an Abelian
quantity. If A3 or A5 passes, the non-Abelian algebra does work on `d_G`, and the A3 count measures
it. Either way the note says nothing about GL7 (logical to physical distance) or GL8 (string
tension).

## §2 Results

Run by [`gluon_abelian_control.py`](gluon_abelian_control.py); output in
[`data/gluon_abelian_control.json`](data/gluon_abelian_control.json). The gated relation reproduces
#289's census exactly (494 states, 454 with a singlet path, the same move classes). The algebra is
proved in [`lean/QLF_GluonAbelianControl.lean`](lean/QLF_GluonAbelianControl.lean), no QLF axioms.

| | Result | Verdict |
|---|---|---|
| A1 | 0 non-reducing first-singlet moves in either relation | **fails, as predicted**: `first_singlet_move_reduces` holds for every move relation |
| A2 | gated `d_G` takes several values on 24 of the 35 (total colour, size) classes | fails: `d_G` is not fixed by Abelian data |
| A3 | 24 states have `d_G = 2` gated and `d_G = 1` ungated; no state is shorter gated | **pass** (`gate_lengthens_witness`) |
| A4 | 32 states reach a singlet only ungated (`d_G = 1`), every one without a non-collinear pair | pass (`same_label_blocked_gated`, `same_label_closes_ungated`) |
| A5 | the move classes differ: ungated create 256 / 32 / 128 reducing / neutral / increasing, glue 592 / 272 / 544 | pass |

The 8 states the ungated relation cannot close are the single labels, which have no pair at all.

**Verdict.** The non-Abelian vertex does work on `d_G`. It does so in one direction only: the gate
removes moves, so it can only lengthen a path or block it, and the census finds 24 states lengthened
from one move to two and 32 blocked. The mechanism is visible in the closing conditions: one create
closes exactly when a pair sums to the total colour `T`, one glue exactly when it sums to `−T`
(`create_closes_iff`, `glue_closes_iff`), and on these 56 states the only such pair is collinear.

So in this relation the non-Abelian algebra makes singlet closure harder, not easier. Any
distance-reducing role for the gluon has to come from something other than its non-Abelian
structure, since removing that structure never lengthens a path. And #289's "every first-singlet
move reduces `d_G`" is bookkeeping (A1), so it carries no evidence for a distance-reduction reading.
The question #286 poses (whether first-singlet channels are preferentially distance-reducing) needs
a comparison over channels that could have been neutral or increasing, such as multi-step binding
paths. GL7 and GL8 are untouched.
