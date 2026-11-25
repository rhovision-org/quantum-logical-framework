# The time-reversed universe exists by perspective

[Quantum Logical Framework (QLF)](README.md) · [Theory index](Theory_Of_Everything.md) · [Time-reversed clock domains](Time_Reversed_Clock_Domains.md) · [Reversibility](Reversibility.md) · [Time](Time.md)

Jim, 2026-11-25: *"Time and space are identical at light speed."* *"The interval is by perspective. This leads into our next topic. The time reverse universe. No singular reverse time perspective universe, except by perspective."* *"The relevance is that even reverse time exists by perspective."* *"Handedness is the distinction."* *"All possible time reverse universes exist"*, *"allowing our selection among them."*

Lean anchor: [`lean/QLF_TimeReversalPerspective.lean`](lean/QLF_TimeReversalPerspective.lean). No axiom is added. It builds on [`QLF_Minkowski`](lean/QLF_Minkowski.lean) (the state is Minkowski space), [`QLF_ClockPairing`](lean/QLF_ClockPairing.lean) (the paired-domain map `J`) and [`QLF_Motives`](lean/QLF_Motives.lean).

## 1. The statement, in five parts

The claim has five parts, and each has a different status.

1. **The interval's value is the same in every perspective; its split into time and space is not.** Proved.
2. **The order of two events is set by perspective when they are spacelike separated, and is not when they are causally connected.** Proved for an explicit boost family, plus a general statement for every Lorentz perspective.
3. **No reversed reading adds a separate collection of histories. Each is the same collection of closures, read from the other end or from the other domain.** Proved on finite twist histories and on paired clock-domain histories. That this reading *is* physical time reversal is an interpretation.

4. **Handedness is what distinguishes a reversed reading from ours.** Proved event by event (§4a).
5. **All possible reversed readings exist, sixteen of them, and the selection among them is ours.** Proved (§4b).

So every possible time-reversed universe exists, in the precise sense that every closure has all sixteen reversed readings and each of them is itself a closure. None of them is a separate collection of histories, because each reversed census is the census. ZFA does not choose among them; the choice is a perspective, and it is visible in the record.

## 2. The interval is invariant; the split is by perspective

A separation is a `Form` `(t, x, y, z)` with interval `t² − x² − y² − z²`, the determinant of the Hermitian state ([`QLF_Minkowski`](lean/QLF_Minkowski.lean), `det_toMatrix_eq_interval`).

| Theorem | Statement |
|---|---|
| `boost_interval` | every boost `(t, z) ↦ (ct + sz, st + cz)` with `c² − s² = 1` preserves the interval |
| `split_by_perspective` | the rest tick `(1, 0, 0, 0)` is pure time in its own perspective, and `(5/4, 0, 0, 3/4)` after the boost of velocity `3/5`; the interval is `1` in both |
| `timeReverse_interval` | `t ↦ −t` preserves the interval, so the interval cannot tell a separation from its reversed reading |
| `boost_null_iff`, `timeReverse_null_iff` | being on the light cone is the same in every perspective and under reversal |

The general Lorentz statement is `lorentz_preserves_interval` (every `A ∈ SL(2,ℂ)`). So "the interval is by perspective" is exact for the split and not for the value. That is what makes Jim's light-speed remark exact: on the light cone the time part and the space part are equal in every perspective, because the interval is `0` in every perspective (the time double slit's `light_cone_duality`, [PR #321](https://github.com/rhovision-org/quantum-logical-framework/pull/321)).

## 3. Which order is by perspective

| Theorem | Statement |
|---|---|
| `spacelike_order_by_perspective` | for the spacelike separation `(0, 0, 0, 1)`, one boost gives `Δt = 3/4` and the inverse boost `Δt = −3/4`: which event comes first is by perspective |
| `timelike_order_invariant` | for a future timelike separation, every boost in the family keeps `Δt > 0` |
| `null_order_invariant` | the same for a future null separation |
| `timeReverse_not_a_boost` | so the reversed reading of the rest tick is not reached by any boost in the family |
| `no_congruence_reverses_time` | for **every** `2×2` complex `A`, `A · I · A† ≠ −I`: no Lorentz perspective (indeed no congruence at all) sends the unit time direction to its reverse |

This is the standard relativity of simultaneity, stated on QLF's Hermitian state. It splits Jim's claim cleanly. For spacelike pairs, the time order really is a matter of perspective, and both orders are equally valid readings. For causal pairs, the forward direction is shared by every inertial perspective, so the reversed reading of a causal history is not one more inertial frame. It is a different kind of perspective: the reading from the other end of the record, or from the counterpart domain.

## 4. The reversed census is the census

On records the reversal is a word operation, and the census is closed under it.

| Theorem | Statement |
|---|---|
| `reverse_closure_iff` | a twist word closes iff its reversed reading closes |
| `dagger_closure_iff` | the same for the conjugate-reverse reading `dagger` |
| `J_admissible_iff` | on paired histories `(p, q)`, `J (p, q) = (dagger q, dagger p)` preserves and reflects admissibility |
| `reversed_census_is_census` | every admissible paired history is the reversed reading of an admissible paired history (its own `J`) |
| `self_reversed_exists` | `[up, down]` is its own dagger: its reversed reading is the same history |
| `reversed_reading_distinct` | the plaquette `[up, left, down, right]` closes, its reversed reading closes, and the two are different words |
| `each_reads_forward` | under `J` the counterpart's tick `i` is our tick `n − 1 − i`, conjugated: neither domain's own clock runs backward |

Together with `J_not_fixed_point_free` and the `8ⁿ` fixed-point count of [`QLF_ClockPairing`](lean/QLF_ClockPairing.lean), this gives the precise sense of "no singular reverse universe". There is no second collection of histories carrying the reversed time: the reversed collection *is* the census. Whether the reversed reading of one history names a different history depends on that history. For self-dagger histories it names the same one; for others it names a different closure that is already in the census.

## 4a. Handedness is the distinction

A twist is a handedness on an axis and nothing else ([`QLF_Handedness`](lean/QLF_Handedness.lean)). Reading a word in reverse order and reading it as the counterpart domain does (`dagger`, conjugate and reverse) differ in exactly one thing: handedness.

| Theorem | Statement |
|---|---|
| `handednessOn_reverse` | pure order reversal leaves the net handedness on every axis unchanged |
| `handednessOn_dagger` | the conjugate-reverse reading negates it on every axis |
| `reversed_tick_opposite_handedness` | tick `i` of the reversed reading is our tick `n − 1 − i` with opposite handedness, and handedness is never zero, so every event differs from its partner |
| `closure_totals_blind` | on a closure the net handedness is zero on every axis in both readings, so totals cannot tell them apart |
| `reversal_vs_dagger_differ` | for the plaquette `[up, left, down, right]` the pure reversal and the conjugate-reverse are different words |

So the reversed reading is not told apart by any total: a closure is handedness-balanced in both. It is told apart event by event, and the distinguishing datum is handedness. Order reversal alone (without the handedness flip) is a third reading, not the counterpart one. Charge is the gauge component of handedness (`chiralCharge_eq_handednessOn_gauge`), which is why the counterpart reading carries the opposite charge label (`charge3W_dagger` in [`QLF_ClockPairing`](lean/QLF_ClockPairing.lean)); calling that reading antimatter remains the interpretation step of issue #236.

## 4b. All possible reversed readings exist; the selection is ours

Reversing the order of a word can come with a reversal of handedness on any subset of the four axes. That gives `2⁴ = 16` reversed readings, `readingBy s` for `s : Axis → Bool`. Pure reversal is `s` false everywhere (`readingBy_false`); the counterpart reading `dagger` is `s` true everywhere (`readingBy_true`).

| Theorem | Statement |
|---|---|
| `readingBy_involutive` | every reading is an involution |
| `handednessOn_readingBy` | a reading reverses handedness exactly on the axes it selects |
| `readingBy_closure_iff` | every reading maps closures onto closures |
| `every_reading_is_the_census` | for every `s`, each closure is the `s`-reading of a closure: every reversed census is the census |
| `sixteen_reversed_readings` | for an eight-twist closure touching all four axes, the sixteen readings are sixteen different words, each a closure |
| `selection_identifiable` | two different selections never give the same reversed history of that closure |

This is the sense of "all possible time reverse universes exist, allowing our selection among them". All sixteen exist in the census, and closure admits every one, so ZFA does not choose. The choice is a perspective, four bits, one per handedness component. And it is visible: the reversed history records which selection made it. Which selection nature's counterpart domain (if there is one) corresponds to is not settled here.

## 5. What this is evidence for, and what it is not

Rule 4 of the working method ([`CLAUDE.md`](CLAUDE.md), *ZFA first, then every way*) asks what count a claim changes.

- §2 is bookkeeping on the interval, true of any Lorentzian quadratic form. It is the precise statement, not new evidence.
- §3 is the relativity of simultaneity. Its QLF content is that QLF's state space is Minkowski space, which [`QLF_Minkowski`](lean/QLF_Minkowski.lean) already proved.
- §4 and §4b hold for **any** alphabet closed under a count-preserving involution. It shows that the reversed reading adds no histories, which is the content of "no singular reverse universe". It does not show that nature contains a counterpart domain.

Not derived here: that `J` or word reversal *is* physical time reversal, an antimatter identification, any horizon or no-signalling law between domains, or any age relation. Those stay with the obligations of [`Time_Reversed_Clock_Domains.md`](Time_Reversed_Clock_Domains.md) (issue #236), where `J` was already shown not to double the census and not to supply an age factor.

The arrow of time is unaffected. Reversibility of the laws (the dagger involution) and irreversibility of the process (closure is many-to-one, `time_reverse_involutive_but_closure_degenerate` in [`QLF_Reversibility`](lean/QLF_Reversibility.lean)) both stand. What this module adds is that the reversed reading, which the involution guarantees exists, lives inside the same census: it is a perspective on the one collection of closures, not a rival history.
