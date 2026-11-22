# Conscious dynamics: which update rule gives the receiver regime? (#278)

Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF. Issue #278 asks for a
finite dynamic competition: the next conscious expression is the eligible closure nearest to closing
(`argmin d`), and the listener context updates, `B_{t+1} = U(B_t, C_t*)`. The static skeleton in
[`lean/QLF_Consciousness.lean`](lean/QLF_Consciousness.lean) proves a regime change
([Consciousness.md](Consciousness.md) §4): with internal period `i < e` the internal closure is
conscious, and quieting it to `i ≥ e` moves the conscious content to the external joint closure
(`quieting_shifts_to_external`). The update rule `U` is the piece #278 leaves open. This note fixes
two candidate rules before running them and asks which one reproduces the skeleton's regime change.

## §1 Pre-registration (committed before the companion script was run)

### The race

The candidates are those of PR #279's table, eligible ones only: percept `T = 2`, thought `T = 5`,
feeling `T = 7`, external joint closure `T = 8`. Time is an integer. Each candidate carries a
remaining distance `d`, starting at its `T`. At each step the eligible candidate with least `d` is
promoted (ties broken by the order above), the elapsed time is that least `d`, and then:

* **Independent rule `U_ind`.** Every candidate's `d` falls by the elapsed time, and the promoted one
  is reset to its `T`. Each closure keeps its own clock; promotion does not disturb the others.
* **Reset rule `U_res`.** The promoted one is reset to its `T`, and every other candidate is also
  reset to its full `T`. Promotion is global: it re-starts every competing listening.

**Quieting** multiplies the internal periods (percept, thought, feeling) by `q ≥ 1` and leaves the
external one alone.

### Tests

Over a horizon of `H = 840` time units (a common multiple of the periods):

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| C1 | under `U_ind` the promotion count of each candidate is `H / T` | exact, unquieted | pass: each clock runs alone (bookkeeping under the rule) |
| C2 | under `U_res` one candidate takes every promotion | percept takes all, unquieted | pass |
| C3 | regime change under `U_res` | for `q ∈ {1, …, 6}`, the external closure takes every promotion iff `2q > 8`, and none otherwise | pass: the skeleton's threshold `e ≤ i`, made strict by the tie-break |
| C4 | no regime change under `U_ind` | the external share is the same for every `q`, `(H/8)` promotions | pass: its clock is never disturbed |

**Verdict rule.** If C1 to C4 pass, only the reset rule reproduces the skeleton's regime change: a
sharp threshold in `q` at which the conscious content switches wholesale to the external closure.
Under the independent rule there is no receiver regime at all; the external closure is expressed at
its own rate whatever the internal closures do, and quieting changes only the shares of the others.
So the receiver reading of [Consciousness.md](Consciousness.md) §4 commits #278 to a global update
(promotion re-starts the competing listenings), which is a claim about `U` and has to be stated as
one. Neither rule is derived here.

Note on C3's tie: at `2q = 8` the percept and the external closure tie and the declared order
breaks it toward the percept, so the switch is at `q ≥ 5`. The skeleton's `e ≤ i` puts the tie the
other way; that difference is a tie-break convention, not a result.

## §2 Results

To be filled from `conscious_update_rule.py` after this section is committed.
