# Time-reversed clock domains: a proof program

[QLF](README.md) · [Theory index](Theory_Of_Everything.md) · [Gupta program](Gupta_CCC_TL.md) · [Clock conventions](Gupta_ClockConventions.md)

**Status: partial finite algebra, physical correspondence still B-OPEN.** Tracked in [issue #236](https://github.com/rhovision-org/quantum-logical-framework/issues/236). Jim proposes that our matter-world time perspective has a reversed antimatter counterpart: each side experiences events through its own local clock, while a joint closure relates the two. A horizon-like boundary would prevent reconstruction of the counterpart's internal history from our records. These physical identifications are research targets, not existing theorems.

This is separate from the external Gupta numerical benchmark. Proving or excluding the correspondence is needed before using it to explain the age difference; reproducing Gupta's equations does not depend on it. No numerical age is selected by this proposal. Pure order reversal preserves duration magnitude, so an age difference also requires a derived clock-rate or origin/count relation.

## Existing finite algebra

In [QLF_ClosureUnitarity](lean/QLF_ClosureUnitarity.lean), `dagger`, `fold_dagger`, `closure_by_dagger` and `countBalanced_append_dagger` give a conjugate-reverse completion of every finite twist history. [QLF_Majorana](lean/QLF_Majorana.lean) defines the same word operation as `antiparticle` and proves `antiparticle_involutive`.

These are concrete starting points. They do not identify the word operation with physical time reversal, establish two universe histories, or prove that dagger completion is the only possible completion. In particular, destructive interference of existing histories is different from absence of histories; the closure module explicitly distinguishes these cases.

## Obligations and falsifiers

| Target | Required result | What would defeat or limit it |
|---|---|---|
| Event-history objects | Finite labeled event orders, local clock records and a joint-closure relation, with nontrivial examples | An unconstrained interface satisfied by every history carries no physical selection |
| Reversal map J | Involution; order reversal across domains; monotone clock readings within each domain's own orientation | Word reversal alone does not establish these properties of physical event orders |
| Antimatter identification | Define the relevant charge/baryon labels; show how J transforms them while preserving the specified closure invariants | Charge conjugation and time reversal must not be identified by naming alone |
| Event pairing | Relate paired events to a joint ZFA closure; state whether pairing is sufficient or necessary, and whether it is unique | Other admissible completions defeat uniqueness; an unpaired closed event defeats an asserted necessity |
| Boundary observation | Define O from paired histories to finite records available on our side | An observation map chosen constant makes information hiding automatic and physically empty |
| Reconstruction obstruction | Exhibit distinct admissible counterpart histories with identical accessible records, hence no exact inverse on that class | Distinguishing records refute that equivalence; noninjectivity alone is not universal computational unconstructibility |
| Causal noninterference | Specify allowed counterpart interventions and prove the accessible-record invariance claimed under them | Inability to reconstruct is weaker than no influence or no signalling; test each claim separately |
| Boundary exchange | Define a candidate horizon-emission/absorption channel and show its compatibility with joint closure | Separate clocks do not imply causal isolation. An “only Hawking-type exchange” claim requires exclusion of every other allowed channel |
| Age bridge | Derive clock normalization, start surface and accumulated event/count relation without fitting either age | J by itself gives opposite orientation, not a factor of roughly two in elapsed age |

## First proof milestones

1. Reuse the finite dagger/involution results to construct a nontrivial paired-history model, keeping physical labels explicit.
2. Prove a finite observational nonidentifiability lemma: if distinct admissible histories have the same O-record, O has no exact left inverse on that class. Then construct a meaningful boundary model that actually satisfies its premise.
3. Separate this from causal noninterference and from the physical horizon interpretation. State assumptions and counterexamples before any physical promotion.
4. Only then connect to the clock-convention program and compare operational ages. Neither 13.8 nor 26.7 Gyr is an input for selecting J or the boundary map.

Formal identities, the physical correspondence and empirical evidence require separate verdicts. A successful toy model establishes one realization; it does not establish that our world realizes it. No new dynamics, framework rule adoption or physical conservative return is asserted by this plan.

## Frozen first implementation target: finite accessible records

The first Lean target is a concrete closure-only boundary model, before imposing a unique reversal partner. Let a history be a pair of finite twist lists `h = (p, q)`, admissible exactly when `countBalanced (p ++ q)`. Freeze the accessible record as `O(p, q) = (p, q.length)`: our full local word and the counterpart's aggregate length are accessible, but the counterpart's internal order is not. This is an explicitly chosen toy interface, not a derived physical horizon. It has no adjustable numerical parameters.

Use the following witnesses, in the alphabet of [QLF_TwistAlphabet](lean/QLF_TwistAlphabet.lean):

- `p = [up]`, `q₁ = [down, left, right]`, `q₂ = [down, right, left]`.
- Both concatenations are count-balanced, `q₁ ≠ q₂`, and both records are `([up], 3)`.
- `([up], [down])` is also admissible, with a different record `([up], 1)`. Thus O is nonconstant even with the local word fixed.

The first proposed statements are admissibility of these witnesses, equality of their records, inequality of their counterpart words, nonconstancy of O, and the absence of an exact reconstruction function `R` satisfying `R(O(p,q)) = q` for every admissible pair. The last result follows because R would have to return both q₁ and q₂ for the same input. These statements are implemented in [QLF_ClockDomains](lean/QLF_ClockDomains.lean) and passed kernel verification and the exact-axiom audit at `55a1be8`. The eleven new statements have empty axiom footprints; all 395 registered anchors passed the gate. The result is **partial algebra, still B-OPEN**. See the [verification record](verification/time-reversed-clock-domains/README.md).

This model establishes non-identifiability only for the stated record interface and admissible class. A stricter class could exclude a witness. In particular, imposing `q = dagger p` makes the counterpart reconstructible from p and defeats this example. No no-signalling conclusion follows: O deliberately exposes length, so a permitted length-changing intervention could affect the record. Allowed interventions and their invariances need a separate model.

## Alternative completions and fixed points

For `p = [up]`, the canonical dagger completion is `[down]`, but `[down, left, right]` and `[down, right, left]` also give count-balanced concatenations. Thus count-balance alone neither requires the canonical dagger completion nor selects a unique counterpart. These examples do not refute uniqueness under stronger, independently justified conditions such as a fixed length, fixed central phase or prescribed event pairing; those conditions must be stated and tested separately.

Involution also does not imply fixed-point freedom: [QLF_Majorana](lean/QLF_Majorana.lean) already proves that `[up, down]` is fixed by conjugate reversal. A general two-element-orbit counting theorem therefore needs an explicit fixed-point-free hypothesis or a correction for singleton orbits. Adding domain tags can enforce distinct partners in a toy construction, but does not derive a physical doubling of the event census.

## Two-way age-counting hypothesis

Jim suggests that Gupta may include both temporal directions in the quoted age. Locate an explicit source equation or author intermediate before attributing such a sum to the model: the inspected equation 50 is a single age integral. A signed reversal and a sum of positive elapsed durations are different operations. The rough ratio of the quoted ages alone does not establish either. Preserve this as an unverified source-audit hypothesis and do not alter the frozen benchmark to enforce it.

The candidate is `T_Gupta = T₊ + T₋`, with positive durations `T₊ = T₋`, and our operational age identified with T₊. Conditional on these premises, `T_ours = T_Gupta / 2`; the stored stage-1 present age would give approximately 13.3336059294 Gyr. This is retrospective arithmetic on a known baseline, not an independently selected QLF age. Equal durations for an exact reversal pair do not establish that Gupta's integral counts both members. The correspondence must also distinguish paired events from twice-counted descriptions of one event and justify a common tick normalization.

**Hard age-interpretation gate:** before this proposal may explain the Gupta age difference, derive a clock-rate, start-surface or accumulated-count relation on finite records, with operational units and a stated approximation error, and show how the source integral maps to it. The [stage-2 clock conventions](Gupta_ClockConventions.md) must be reviewed and frozen before applying that map. A free scale, an unsigned derivative or the existence of a reversed copy does not discharge this gate. Outcomes remain derived, permitted-but-underdetermined, or incompatible-within-the-frozen-class.

Gupta's benchmark uses fitted external inputs; its numerical reproduction does not make them QLF-derived. The comparison ΛCDM age is likewise model-dependent and uses a smooth FLRW description. These approximation limitations do not supply an error bound or establish the proposed factor of two. Jim has authorized exploring the hypothesis despite the unresolved Table 1 precision residual; that exploratory decision neither resolves the residual nor adopts the physical map. The frozen artifacts and tolerance remain unchanged.

## Second stage: paired local clocks and the map J (plan, now implemented)

Grok's second review, relayed by Jim on [PR #235](https://github.com/rhovision-org/quantum-logical-framework/pull/235) on 15 November 2026, proposes four Lean items and three documentation items. This section adopts them with the adjustments below and fixes what each statement may and may not be read as. The counts quoted were exact enumerations run before any Lean was written. The plan is kept as written; the [outcome](#second-stage-outcome) follows it.

**The candidate map.** On histories `h = (p, q)` put `J(p, q) = (dagger q, dagger p)`, with `dagger` from [QLF_ClosureUnitarity](lean/QLF_ClosureUnitarity.lean). It swaps the two domains and conjugate-reverses each word. This is one choice. Two others must be stated beside it so the choice is visible: the pure reversal `(q.reverse, p.reverse)` and the swap alone `(q, p)`.

| # | Planned statement | Why it is not empty, and what it may not be read as |
|---|---|---|
| J1 | `J (J h) = h`; `admissible h → admissible (J h)`; `J` sends lengths `(m, n)` to `(n, m)` | Involution follows from `antiparticle_involutive`; admissibility from `count_dagger`. Structural. |
| J2 | Local clocks: tick `k` of a word is its `k`-th event. Under `J` the event at tick `k` of a length-`n` word lands at tick `n − 1 − k` of the other domain, so cross-domain order is reversed while each domain's own reading still runs `0, 1, …, n − 1` | This is a property of list reversal. It models "each side reads its own clock forward"; it does not show that nature pairs domains this way. |
| J3 | **No-go:** `J` preserves each word's length, so total duration is unchanged and the two durations are exchanged. No map of this kind yields a factor of two | This is the useful direction: it proves order reversal alone cannot discharge the age gate. It is a `List.length_reverse` fact and must be labelled bookkeeping, not evidence for the hypothesis. |
| J4 | **Fixed points, counted.** `J h = h` exactly when `q = dagger p`. So every canonical dagger completion is its own counterpart, `([up], [down])` included. With both words of length `n` there are `8ⁿ` fixed points | Enumerated: length (1,1): 8 admissible, 8 fixed. Length (2,2): 168 admissible, 64 fixed, 116 orbits. Length (3,3): 5120 admissible, 512 fixed, 2816 orbits. So `J` does **not** double the census, and "every history has a distinct counterpart" is false for this map. With unequal lengths there are no fixed points because `J` exchanges the lengths. |
| L1 | Label kept separate from order: for `charge3W` of [QLF_QuarkSignature](lean/QLF_QuarkSignature.lean), `charge3W (dagger w) = − charge3W w` and `charge3W w.reverse = charge3W w` | Shows the sign flip comes from the conjugation in `dagger`, not from reversing order. Pure reversal leaves the label alone. This is what keeps the antimatter identification from being carried in by the word dagger. |
| L2 | For every admissible `(p, q)`, `charge3W p + charge3W q = 0` | Must be stated so nobody over-reads it: this follows from count balance for **any** completion, not from `J`. Opposite total label on the two sides is forced by closure, so it is no evidence for a reversed counterpart. |
| S1 | Stricter class `q = dagger p`: neither `extendedLeft` nor `extendedRight` belongs to it, and it has exactly one completion per local word | Turns the existing remark "a stricter class may remove the witnesses" into a theorem, next to `prescribed_counterpart_reconstructible`. |
| S2 | **The fiber, counted.** The record `([up], 3)` has exactly 21 admissible counterparts; `([up], 1)` has 1; `([up], 5)` has 640 | Replaces the two exhibited witnesses with the number of ways. Feasibility in the kernel without `native_decide` is to be tested on the 21 case first (512 candidates). If it is too slow it stays an enumeration with a script, and is labelled as such. |

**Order of work.** J1, J4 and S1 first (short, and J4 is the result with content), then L1 and L2, then J2 and J3, then S2. One PR, new statements added to [QLF_ClockDomains](lean/QLF_ClockDomains.lean) or a sibling module, each registered in the exact-axiom audit. No new axiom. Status stays partial algebra, B-OPEN.

**Kill conditions, stated first.** If J4's count comes out different in Lean from the enumeration, the enumeration or the map is wrong and the plan stops there. If a reviewer finds that J2 and J3 hold for every involution that reverses lists, they are recorded as structural and carry no weight for the physical reading (this is expected). The stage adds evidence for the time-reversed-domain hypothesis only if some statement would be false for a different admissible pairing; J4 and S2 are the candidates, because they are counts.

**Type of the missing age theorem (frozen as a target, not claimed).** To discharge the hard age gate, a later stage must supply: a function `N` from admissible paired histories to positive rationals (a tick count), a start-surface index on each history, a fixed unit `τ` and an error bound `ε`, with a proof that the operational age read from the finite record is within `ε` of `N · τ`, and a separate map from the source's equation-50 integral to that record. None of the five is defined yet. J3 shows that `J` supplies none of them.

**Not in this stage.** No mapping of Gupta's integral onto `T₊ + T₋`. No promotion of the toy record map or of `no_exact_reconstruction` to a horizon or no-signalling statement. No new dynamics. The half-total arithmetic above stays retrospective.

## Second-stage outcome

Implemented in [QLF_ClockPairing](lean/QLF_ClockPairing.lean), no axiom added. Every planned statement is proved, and the counts in Lean agree with the enumeration, so the first kill condition did not fire.

| Plan item | Theorems | Result |
|---|---|---|
| J1 | `J_involutive`, `J_admissible`, `J_lengths` | Proved. |
| J2 | `dagger_tick` | Proved: the event at tick `i` sits, conjugated, at tick `n − 1 − i` of the dagger. Structural, as expected. |
| J3 | `J_duration`, `J_equal_durations`, `reversal_duration`, `swap_duration` | Proved for all three maps. Order reversal gives no factor between the two durations. Bookkeeping; a no-go, not support. |
| J4 | `J_fixed_iff`, `fixedOfLength_length`, `fixedOfLength_nodup`, `J_not_fixed_point_free`, `J_fixed_lengths`, `census_one_one`, `census_two_two` | Proved for every length: the fixed points are exactly the histories with `q = dagger p`, and there are `8ⁿ` distinct ones at word length `n`. The (1,1) and (2,2) censuses (8 of 8; 64 of 168) are decided in the kernel. The (3,3) figures stay an enumeration. |
| L1 | `charge3W_dagger`, `charge3W_reverse`, `J_label`, `reversal_label` | Proved: the dagger negates the label, pure reversal leaves it unchanged. |
| L2 | `charge3W_balanced`, `admissible_label_opposite` | Proved: every admissible history has opposite total label on its two sides. |
| S1 | `strict_admissible`, `strict_unique`, `strict_no_collision`, `extendedLeft_not_strict`, `extendedRight_not_strict` | Proved. |
| S2 | `fiber_up_one`, `fiber_up_three` | Decided in the kernel without `native_decide`: 1 and 21. The length-5 figure (640) stays an enumeration. |

**One finding the plan did not state.** The stricter class of S1 and the fixed-point set of J4 are the same set (`J_fixed_iff`). So the class on which the counterpart *is* reconstructible is exactly the class on which `J` assigns a history to itself. Under this `J`, a history either has a distinct counterpart that the record does not determine, or has a determined counterpart that is not distinct. This is a property of this candidate map and this record interface, not of nature.

**What the stage does and does not support.** By the criterion set above, only J4 and S2 are counts. J4 counts against the simplest reading of the hypothesis: `J` does not double the event census. L2 removes one apparent support: opposite label on the two sides is forced by closure. J3 confirms that the age gate is untouched. Nothing here is evidence that our world has a time-reversed counterpart, and nothing excludes it; the stage narrows what a later physical map would have to supply.

## Third stage: interventions and the age-map interface

Implemented in [QLF_ClockIntervention](lean/QLF_ClockIntervention.lean), no axiom added. It tests two rows of the obligations table on the finite model: causal noninterference and the age bridge. Both come out as limits on the toy model, which is what the table's "what would defeat or limit it" column asked for.

**The record is not a no-signalling interface.** An intervention replaces the counterpart `q` by another admissible `q'`.

| Intervention | Theorems | Effect on the record `(p, q.length)` |
|---|---|---|
| Reorder the counterpart | `perm_admissible`, `perm_record` | Always admissible, never visible. |
| Any length-preserving change | `length_preserving_record` | Never visible. True by the definition of the record, so structural. |
| Insert a conjugate pair | `insert_pair_admissible`, `insert_pair_record` | Always admissible, always visible. |

So `record_signals`: there are admissible interventions that change what our side reads. The channel is unbounded (`channel_unbounded`): for every local word and every `k` there is an admissible counterpart of length `p.length + 2k`, so the counterpart could transmit any natural number through its length. Stage one proved the counterpart cannot be *reconstructed* from the record. That is a weaker property than the counterpart being unable to *influence* the record, and this record has the first without the second. A horizon reading needs the second.

**What cannot signal is only what the local word already fixes.** The parity of the counterpart's length equals the parity of ours (`admissible_parity`), so a record exposing only that parity is invariant under every admissible intervention (`parity_record_no_signal`). It is invariant because it carries no information about the counterpart. This is the table's warning made exact for this model: among records built from the counterpart's length, the one that hides everything is empty and the one that says anything signals.

**The hidden part, counted.** The 21 counterparts of `([up], 3)` form exactly 4 reorder classes (`fiber_up_three_classes`): which twist pair accompanies the `down`, with 3, 6, 6 and 6 orderings. The record hides both the class and the order.

**The age-map interface, measured (R6a).** The target frozen above asked for a positive tick count on admissible histories. Bundled as `AgeMap` and tested:

- `ageMap_nonempty`: a constant satisfies it. `ageMap_hits_any`: any positive number is the age of any history under some instance. So the bare interface excludes nothing and fixes no value; a later stage must add constraints before it can be wrong. This agrees with `free_clock_scale_hits_any_age` in [QLF_ClockRedshift](lean/QLF_ClockRedshift.lean).
- With the one tick count the model has, word length, "our age is half the total" is exactly equality of the two durations (`half_total_iff`). It holds on the strict class (`strict_half_total`).
- Closure does not force it (`half_total_not_forced`): `([up], [down, left, right])` is admissible with durations 1 and 3. And equal durations do not make a history a fixed point of `J` (`equal_durations_not_fixed`).

So the two-way age-counting hypothesis needs equal durations as a separate premise. Count balance does not supply it, and neither does `J`, which only exchanges the two durations. What would supply it is a pairing rule that ties each of our events to one counterpart event; on the strict class that rule is the dagger, and there the counterpart is not distinct. That tension is now the sharpest statement of what a physical map must resolve.

**Status after three stages.** Finite algebra only; physical correspondence B-OPEN. Open rows of the table: a boundary record that neither signals nor is empty (it cannot be a function of the counterpart's length alone), boundary exchange, and an age map with constraints that some instance could fail.

## Independent review record

[Grok's review and disposition](verification/time-reversed-clock-domains/grok_review.md), relayed by Jim on 14 November 2026, finds the issue appropriately scoped and requests the explicit age gate, alternative completions and a concrete non-identifiability target. Those requirements are specified above. The first finite record implementation is kernel-verified; the physical correspondence remains **B-OPEN**.

## Verified finite-record anchors

In namespace `QLF.ClockDomains`: `canonical_admissible`, `extendedLeft_admissible`, `extendedRight_admissible`, `alternative_completions`, `counterparts_distinct`, `records_equal`, `records_distinct`, `accessible_nonconstant`, `collision_blocks_reconstruction`, `no_exact_reconstruction`, and `prescribed_counterpart_reconstructible`. These discharge the concrete closure-only record target. The paired local-clock model and the fixed-point census are in [QLF_ClockPairing](lean/QLF_ClockPairing.lean), listed under the second-stage outcome above. The physical horizon and the age map remain open.
