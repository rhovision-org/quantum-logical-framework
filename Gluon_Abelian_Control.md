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

To be filled from `gluon_abelian_control.py` after this section is committed.
