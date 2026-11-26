# The time-reversed universe exists by perspective

[Quantum Logical Framework (QLF)](README.md) · [Theory index](Theory_Of_Everything.md) · [Time-reversed clock domains](Time_Reversed_Clock_Domains.md) · [Reversibility](Reversibility.md) · [Time](Time.md)

Jim, 2026-11-25: *"Time and space are identical at light speed."* *"The interval is by perspective. This leads into our next topic. The time reverse universe. No singular reverse time perspective universe, except by perspective."* *"The relevance is that even reverse time exists by perspective."* *"Handedness is the distinction."* *"All possible time reverse universes exist"*, *"allowing our selection among them."* Asked to relate this to free will and consciousness, he agreed to the write-up in §4c. Then: *"It makes sense that nothing can exist. That does not have a history."* (§4d)

Lean anchor: [`lean/QLF_TimeReversalPerspective.lean`](lean/QLF_TimeReversalPerspective.lean). No axiom is added. It builds on [`QLF_Minkowski`](lean/QLF_Minkowski.lean) (the state is Minkowski space), [`QLF_ClockPairing`](lean/QLF_ClockPairing.lean) (the paired-domain map `J`) and [`QLF_Motives`](lean/QLF_Motives.lean).

## 1. The statement, in five parts

The claim has five parts, and each has a different status.

1. **The interval's value is the same in every perspective; its split into time and space is not.** Proved.
2. **The order of two events is set by perspective when they are spacelike separated, and is not when they are causally connected.** Proved for an explicit family of proper orthochronous boosts along one axis, plus the statement that no congruence sends the unit time direction to its reverse. The general orthochronous case rests on the spinor cover (`lorentz_generated_by_boosts_rotations`) and is not re-proved here.
3. **No reversed reading adds a separate collection of histories. Each is the same collection of closures, read from the other end or from the other domain.** Proved on finite twist histories and on paired clock-domain histories. That this reading *is* physical time reversal is an interpretation.

4. **Handedness is what distinguishes a reversed reading from ours.** Proved event by event (§4a).
5. **There are sixteen reversed readings, one per selector, each mapping closures to closures; on a closure touching every axis they are sixteen different histories.** Proved (§4b). On other closures some readings coincide (§4b), and the existence of a selector is not by itself agency or a physically distinguishable choice (§4c).

So every possible time-reversed universe exists, in the precise sense that every selector gives a reversed reading of every closure and each of those readings is itself a closure. None of them is a separate collection of histories, because each reversed census is the census. ZFA does not choose among them. On a closure touching every axis the sixteen readings are distinct and identify their selector; in general they need not (§4b).

## 2. The interval is invariant; the split is by perspective

A separation is a `Form` `(t, x, y, z)` with interval `t² − x² − y² − z²`, the determinant of the Hermitian state ([`QLF_Minkowski`](lean/QLF_Minkowski.lean), `det_toMatrix_eq_interval`).

| Theorem | Statement |
|---|---|
| `boost_interval` | every boost `(t, z) ↦ (ct + sz, st + cz)` with `c² − s² = 1` preserves the interval |
| `split_by_perspective` | the rest tick `(1, 0, 0, 0)` is pure time in its own perspective, and `(5/4, 0, 0, 3/4)` after the boost of velocity `3/5`; the interval is `1` in both |
| `timeReverse_interval` | `t ↦ −t` preserves the interval, so the interval cannot tell a separation from its reversed reading |
| `boost_null_iff`, `timeReverse_null_iff` | being on the light cone is the same in every perspective and under reversal |

The general Lorentz statement is `lorentz_preserves_interval` (every `A ∈ SL(2,ℂ)`). So "the interval is by perspective" is exact for the split and not for the value. For a null separation, `|Δt|` equals the spatial length `|Δx|` in every perspective, because the interval is `0` in every perspective (`boost_null_iff`). That is the exact content here of Jim's light-speed remark. The time double slit's `light_cone_duality` ([PR #321](https://github.com/rhovision-org/quantum-logical-framework/pull/321)) is narrower: it assumes equal signed separations and a common frequency `ω = k`, and its `off_cone_distinguishable` is a single counterexample off the cone, not a general converse.

## 3. Which order is by perspective

| Theorem | Statement |
|---|---|
| `spacelike_order_by_perspective` | for the spacelike separation `(0, 0, 0, 1)`, one boost gives `Δt = 3/4` and the inverse boost `Δt = −3/4`: which event comes first is by perspective |
| `timelike_order_invariant` | for a future timelike separation, every boost in the family keeps `Δt > 0` |
| `null_order_invariant` | the same for a future null separation |
| `timeReverse_not_a_boost` | so the reversed reading of the rest tick is not reached by any boost in the family |
| `no_congruence_reverses_time` | for **every** `2×2` complex `A`, `A · I · A† ≠ −I`: no Lorentz perspective (indeed no congruence at all) sends the unit time direction to its reverse |

This is the standard relativity of simultaneity, stated on QLF's Hermitian state. It splits Jim's claim cleanly. For spacelike pairs, the time order really is a matter of perspective, and both orders are equally valid readings. For causal pairs, the forward direction is shared by every proper orthochronous perspective (shown here for the boost family; in general via the spinor cover), so the reversed reading of a causal history is not one more inertial frame. It is a different kind of perspective: the reading from the other end of the record, or from the counterpart domain.

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
| `selection_identifiable` | for that closure, two different selections never give the same reversed history |
| `readingBy_eq_of_agree` | selectors that agree on every axis a word touches give the same reading |
| `selectors_coincide_on_empty` | on the empty closure all sixteen readings coincide |
| `joint_recovery_fails` | `[up, down]` is both the pure-reversal reading of `[down, up]` and the `dagger` reading of itself, so a reading does not determine selector and history jointly |

This is the sense of "all possible time reverse universes exist, allowing our selection among them". Every selector's reading exists in the census, and closure admits every one, so ZFA does not choose. A selector is four bits, one per handedness component. Which of those bits make a difference depends on the closure: only the axes it touches, and on a closure touching all four the sixteen readings are distinct (`sixteen_reversed_readings`) and identify their selector (`selection_identifiable`). In general the reading does not record its selector (`readingBy_eq_of_agree`, `joint_recovery_fails`). Which selection nature's counterpart domain (if there is one) corresponds to is not settled here.

## 4c. Free will and consciousness: what is proved, what is a reading

[`Philosophy.md`](Philosophy.md) §3c already fixes the stance: to do is to close, an agent's closing *is* determination happening rather than the output of a determination made elsewhere, and there is no potency, no uncaused causer entering physics from outside ([`ScientificApproach.md`](ScientificApproach.md) §1b). This section only places the results above inside that stance.

**Proved (Lean names):**

- The filter is symmetric in time. Every reversed reading of a closure is a closure, for all sixteen readings (`every_reading_is_the_census`, `reversed_census_is_census`). So no count, and not ZFA itself, picks a time direction.
- Closure admits every selector, so the census does not choose among readings. On a closure touching every axis, different selectors give different reversed histories (`selection_identifiable`); on other closures some coincide (`readingBy_eq_of_agree`). This is a fact about word maps. That a selector exists does not show that any agent makes a selection, or that the selections are physically distinguishable.
- Closure is irrevocable: closed at a horizon means closed at every wider one (`closedAtHorizon_mono` in [`QLF_HorizonClosure`](lean/QLF_HorizonClosure.lean)). A perspective's record only grows.
- Some things are shared by every perspective and some are not. Records of one body share only constants with records of the other (`single_body_perspectives_share_only_constants` in [`QLF_PerspectiveHolography`](lean/QLF_PerspectiveHolography.lean)), and a record blind to phase cannot reconstruct the closure (`phase_blind_record_fails`). In the time double slit ([PR #321](https://github.com/rhovision-org/quantum-logical-framework/pull/321)) the fringe is the same in the reversed perspective (`time_reversed_perspective`). Its `reversed_amp_differs` compares one amplitude `i` with `−i`, which differ by a global phase only: a difference of representation, not an observable witness of handedness. A relative-phase or observable witness would be needed to call the private phase physically distinguishable.
- Handedness is the event-by-event difference between a reading and its reversal, invisible in a closure's totals (`reversed_tick_opposite_handedness`, `closure_totals_blind`).

**Readings (not derived):**

- *Free will is the selection among the readings, made by closing.* Since the filter does not choose a direction and the record is irrevocable, what fixes a perspective's forward direction is its own record. Each closure an agent makes is a selection among possibilities that all exist. It cannot be predicted from outside for the three non-ignorance reasons of [`Philosophy.md`](Philosophy.md) §3c (irreducibility, no outside vantage point, no final capacity). This is free will as authorship of one's own record, not as a force on physics. It is a compatibilist position; the classical statement is Dennett's (*Elbow Room: The Varieties of Free Will Worth Wanting*, MIT Press, 1984). QLF's addition is the substrate reason: the selection is among readings the census already contains, and the census is indifferent among them.
- *Experience sits where the two halves meet.* [`Consciousness.md`](Consciousness.md) and [`Conscious_Update_Rule.md`](Conscious_Update_Rule.md) read conscious content as the bound closure winning the race to close. In this document's terms, that is an open strand of the past meeting its opposite-handed half and becoming record: the present is where the forward and conjugate readings meet.
- *What can be shared is the count; what is one's own is the phase.* This is suggested by the shared/private split proved above and fits the qualia hypothesis of [`Consciousness.md`](Consciousness.md) §6, but the phase difference proved so far is a global phase, so it is not yet an observable private datum. The perspective framing is relational quantum mechanics (Rovelli, "Relational quantum mechanics", *Int. J. Theor. Phys.* 35, 1637 (1996), [arXiv:quant-ph/9609002](https://arxiv.org/abs/quant-ph/9609002)).

None of the three readings is a theorem. A count that each one would change is not yet identified, so by rule 4 of the working method they are framing, not evidence.

## 4d. Nothing exists without a history

Jim: *"It makes sense that nothing can exist. That does not have a history."* Read as: nothing exists that does not have a history.

**Proved.** In QLF the things that exist are closures, and a closure *is* a history (a twist word), so on this model the statement holds by construction. The nontrivial part concerns the reversed readings. A reversed universe might look like something that exists without a past of its own. It does not:

- `every_reading_is_the_census`: every closure that appears as a reversed reading is the reading of a closure, so it has a forward history in the census.
- `reading_has_unique_history`: for a **fixed** selector `s`, that history is unique and the reading recovers it. If `w` is the `s`-reading of `v`, then `v` is the `s`-reading of `w`. Selector and history are not recovered jointly: `joint_recovery_fails` gives one word that is the reading of two different histories under two different selectors.
- `closedAtHorizon_mono`: once closed, a history stays closed at every wider horizon, so the record is never lost.

**Reading.** Existence is having a closed record. A time-reversed universe exists in exactly that sense: as a reading of a history that exists, with that history recoverable from it once the reading's selector is given. That is the sense in which "reverse time exists by perspective": the perspective supplies the direction of reading, never a history that was not there. That nature satisfies "no existence without a history" is the possibilist premise ([`Philosophy.md`](Philosophy.md) §3), not something these theorems derive.

## 5. What this is evidence for, and what it is not

Rule 4 of the working method ([`CLAUDE.md`](CLAUDE.md), *ZFA first, then every way*) asks what count a claim changes.

- §2 is bookkeeping on the interval, true of any Lorentzian quadratic form. It is the precise statement, not new evidence.
- §3 is the relativity of simultaneity. Its QLF content is that QLF's state space is Minkowski space, which [`QLF_Minkowski`](lean/QLF_Minkowski.lean) already proved.
- §4 and §4b hold for **any** alphabet closed under a count-preserving involution. It shows that the reversed reading adds no histories, which is the content of "no singular reverse universe". It does not show that nature contains a counterpart domain.

Not derived here: that `J` or word reversal *is* physical time reversal, an antimatter identification, any horizon or no-signalling law between domains, or any age relation. Those stay with the obligations of [`Time_Reversed_Clock_Domains.md`](Time_Reversed_Clock_Domains.md) (issue #236), where `J` was already shown not to double the census and not to supply an age factor.

The arrow of time is unaffected. Reversibility of the laws (the dagger involution) and irreversibility of the process (closure is many-to-one, `time_reverse_involutive_but_closure_degenerate` in [`QLF_Reversibility`](lean/QLF_Reversibility.lean)) both stand. What this module adds is that the reversed reading, which the involution guarantees exists, lives inside the same census: it is a perspective on the one collection of closures, not a rival history.
