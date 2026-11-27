# Principles — the canonical registry

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

This page lists QLF's principles: the one conjecture it rests on (and the known facts it takes as input), the structural laws it proves from them,
the candidate principles it is working toward, and the bridges that would connect them to physics.
Each principle has a stable ID, a statement, its scope and assumptions, its Lean anchors, what it
depends on, its known limits and counterexamples, the gate it still has to pass, and a status.

It is a registry, not a narrative and not evidence. The other two indexes do different jobs:
[`Theory_Of_Everything.md`](Theory_Of_Everything.md) is the map of the theory (what it says, rung by
rung), and [`Claim_Status.md`](Claim_Status.md) is the ledger of *physical* claims against comparators.
This page sits under both. A principle here is a general statement many results share; a claim there is
one comparison with the world. The Lean modules number in the hundreds; the full table is
[`lean/README.md`](lean/README.md).

**Every theorem name on this page was checked against `main` on 2026-11-27.** Names that live only on
an open PR are marked *(pending #N)* and link to the PR. When a PR merges, remove the marker.

---

## How to read the status

Status follows the two axes of [`ScientificApproach.md`](ScientificApproach.md) §3, with the
[`Claim_Status.md`](Claim_Status.md) code in brackets where one applies.

- **Mathematical:** *Proved* (machine-checked in Lean, axioms named) · *Exact computational*
  (exhaustive or exact-arithmetic over a stated finite domain) · *Paper proof* (a written proof not yet
  in Lean) · *Numerical evidence* · *Conjecture*.
- **Physical:** *Internal* (a substrate fact, no physical claim) · *Open bridge* (`B-OPEN`) ·
  *Consistency* · *Retrodiction* · *Pre-registered* · *Predicted absent* · *Derived bridge*.
- **Record:** *Restricted* (the general statement fails; a narrower one holds) · *Rejected route* ·
  *Superseded*.

Two rules from that section govern every row. **A formally verified structural law is not an empirical
physical law.** And **construction proves possibility, not uniqueness**: a witness shows a thing
happens in *some* way, never that it is the only way ([`Law_Of_Exceptions.md`](Law_Of_Exceptions.md)).

A proof can also be true and still carry no content. Method rule 4 of
[`Philosophy.md`](Philosophy.md) §3a asks what distribution over ways a statement would be false for;
where the answer is "none", the row says **bookkeeping**.

### Using the registry

A PR that touches a principle should say which ID it **establishes**, **strengthens**, **restricts**
or **refutes**, and update the row in the same PR. New principles get the next free ID in their
section. IDs are never reused: a refuted principle stays, marked *Rejected route*, so the next attempt
can see what failed.

---

## A. Foundations (what is assumed)

QLF rests on one well-supported conjecture: **A01**, equal and opposite logical action (ZFA).
Everything else in this section is one of three kinds, never a second conjecture: **derived** from A01 (a theorem), a **known
fact** taken as input and named with its source (A10–A14), or a **reading** or **bridge** that no
derivation may rest on. The framing, and what "QLF tests models" means formally, is
[`Framing.md`](Framing.md). A02–A09 keep their IDs (IDs are never reused); the *Kind* column records
what each now is.

**Postulates rest on what we know fundamentally, not on conjectures of emergence.** A known-fact input
(A10–A14) must be a fact at the substrate level: what a measurement returns, which observables are
incompatible, how much a region can hold. Anything that emerges from closures, such as a continuum
spacetime, a metric, fields, the Born rule or a classical limit, must be derived; until it is, it is a
bridge in section D, never an input ([`Framing.md`](Framing.md) §2).

| ID | Principle | Kind | Status and anchors |
|---|---|---|---|
| **A01** | **ZFA selection.** A history becomes an event exactly when its signed action is zero on every axis: equal and opposite logical action, zero free energy. "Equal and opposite" already contains the signed distinctions (P01), and "becomes an event" already contains the first-closure reading (A07). | **The one well-supported conjecture** | A definition in Lean, not an `axiom` (`achieves_ZFA`, `full_zeno_prune`, [`QLF_Axioms`](lean/QLF_Axioms.lean); `countBalanced`), with models, so it adds nothing to the logic. Empirically uncontradicted so far; kill condition in [`ScientificApproach.md`](ScientificApproach.md) §1a. |
| **A02** | **Possibilism.** Every generable history exists a priori as a way. Possibilism needs only one way: a single closure suffices for a thing to happen, and the first closure is the strongest way. | Absence of a second filter, plus a reading | Formal content: nothing but A01 restricts which histories count as ways. That unclosed ways are *real* is a reading ([`Philosophy.md`](Philosophy.md) §3). |
| **A03** | **Only logic is assumed.** Nature is assumed logical, not assumed to be QLF's construction; the construction is one model of the logical laws. | Method | A01 is that logical assumption: every distinction has its opposite. Worked case proved: `weakening_iff_persistence`, `no_time_loops_from_logic`, `histories_are_a_model`, and the counter-model `loopWorld_has_time_loop` ([`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean); [`Philosophy.md`](Philosophy.md) §3d). |
| **A04** | **Finite realizability.** A finite-information region cannot hold an actual continuum of distinguishable states; possibility is unbounded, but each manifestation is finite. | Derived from a known fact | `no_continuum_in_finite_region` ([`QLF_Realizability`](lean/QLF_Realizability.lean)) from the finite-information bound A12. |
| **A05** | **Information primacy.** Information relations precede matter, space and time. | Reading | ([`ScientificApproach.md`](ScientificApproach.md) §1b). |
| **A06** | **No observer potency.** An apparatus is a closure inventory and an observer is a perspective; measurement is joint closure and creates nothing. | Absence of an assumption | No observer appears in A01, so none may enter a derivation. Support: observers agree on closure and fold under frame relabelings (`observers_agree`, [`QLF_MultiObserver`](lean/QLF_MultiObserver.lean)). |
| **A07** | **A closure is an event.** Along a history, the first closure is the event (the absorbing reading). | Part of A01's statement | The mathematical side is proved: first closures are prefix-free and the cylinder mass is `≤ 1` (`twist_kraft`, [`QLF_KraftMeasure`](lean/QLF_KraftMeasure.lean)). Identifying the cylinder measure with probability is the bridge B09. |
| **A08** | **Finite perspective.** An observer receives only what closes within its capacity. | Derived, plus a bridge | The listening is proved (P17). "Capacity = apparatus resolution" is a bridge ([`ScientificApproach.md`](ScientificApproach.md) §1c). |
| **A09** | **Synthesized spacetime.** Space and time are outputs of closure, not a background. | Reading | Each physical form is a bridge in section D. |
| **A10** | **Measurements are counts.** Every measurement outcome is a finite count with a rational uncertainty; none has produced a real number. | Known fact | Metrology; the 2019 SI redefinition ([`Completeness_Evidence.md`](Completeness_Evidence.md) §2a). Used for: why the substrate is finite and the continuum a rendering. |
| **A11** | **Incompatible observables exist.** Spin along two axes cannot be jointly sharp. | Known fact | Stern–Gerlach (1922) and sequential spin measurements. With `noncommuting_iff_eight` ([`QLF_AlphabetNecessity`](lean/QLF_AlphabetNecessity.lean)) it fixes the alphabet at eight twists, given P01's frame posit. |
| **A12** | **Finite information in a bounded region.** | Known fact (established theory) | The Bekenstein bound (1981). A theoretical bound, not a direct measurement; results resting on it (A04) say so. |
| **A13** | **The measured constants fix the units.** | Known fact | CODATA `ℏ`, `c`, `G`; one calibration per dimensionful observable ([`ScientificApproach.md`](ScientificApproach.md) §5). |
| **A14** | **The minimal interface is two-dimensional, and only hydrogen has it whole** (Jim, 2026-11-27: *"Only hydrogen has a 2 dimensional interface"*). Hydrogen is the only atom with a single electron, so its entire interface is one spin-½: two states. Every other atom is a composite, a closed core with shells around it, and its interface has more dimensions. | Known fact | Phipps and Taylor (1927) split ground-state hydrogen into two beams; one electron is the atomic structure of hydrogen. Silver's two Stern–Gerlach beams (1922) are a doublet on a closed core, not a whole two-dimensional interface. Used for: the two-dimensional atom of [`QLF_PauliFrame`](lean/QLF_PauliFrame.lean), on which the Pauli frame is forced; larger interfaces compose from it. |

The named `axiom` declarations (the Millennium boundaries and continuum limits in the axiom inventory
of [`CLAUDE.md`](CLAUDE.md)) are not assumptions of QLF in this sense. Each is a bridge, and every
result that uses one shows it in its `#print axioms` footprint.

---

## B. Derived structural principles (proved within their stated domain)

Physical status for this section is *Internal* (`F`) unless the row says otherwise. None of these is a
physical law by association.

### P01 · Conjugate balance
- **Statement.** Each twist has one conjugate, and the four conjugate pairs are exactly the four axes,
  so balance is one integer condition per axis.
- **Anchors.** `toSignedAxis_conj` ([`QLF_AlphabetNecessity`](lean/QLF_AlphabetNecessity.lean));
  `countBalanced`. The alphabet size is constrained: `|Σ| ∈ {2,4,8}`, six is impossible, and two
  spatial axes force eight.
- **Limits.** That balance is *required* is the definition of A01, not a theorem. Signedness is part
  of A01 ("equal and opposite"); that the signed distinctions are the signed axes of the Pauli frame is
  derived on a two-dimensional atom: mutually anticommuting two-outcome axes number at most three
  and the third is `± i·AB` (`third_axis`, `no_fourth_axis`, [`QLF_PauliFrame`](lean/QLF_PauliFrame.lean)),
  so the fourth pair must commute with everything, as the gauge pair does (`gauge_commutes`). That the
  atom is two-dimensional is the known fact A14: hydrogen, the minimal interface, is one spin-½
  ([`ScientificApproach.md`](ScientificApproach.md) §1c). Given the frame, the known fact A11 fixes the
  size at eight.
- **Status.** Definition plus proved alphabet constraint.

### P02 · Pauli closure
- **Statement.** Every count-balanced twist history folds to a Pauli scalar, for every interleaving,
  and in fact to `±I`, never `±iI`.
- **Anchors.** `count_balanced_pauli_closed` ([`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean));
  `balanced_phase_is_real`, `unbalanced_can_be_imaginary`
  ([`QLF_BalancedPhaseReal`](lean/QLF_BalancedPhaseReal.lean)).
- **Depends on.** P01.
- **Limits.** The converse fails: unbalanced histories can also fold to Pauli scalars, including `±iI`
  (`unbalanced_can_be_imaginary`), which is why the runtime checks count balance as well. A
  self-adjoint fold does not imply balance either (`hermitian_not_implies_zfa`,
  [`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean)).
- **Status.** Proved.

### P03 · Quantum logic (MO2)
- **Statement.** The x-spin and z-spin closures generate the orthomodular, non-distributive lattice MO2.
- **Anchors.** `orthomodular`, `not_distributive`, `incompatibility_source`
  ([`QLF_QuantumLogic`](lean/QLF_QuantumLogic.lean)).
- **Limits.** Only MO2, the height-2 lattice of two incompatible propositions. The lattice is finite and
  checked by `decide`; its link to closures is the non-commuting Pauli pair. A general orthomodular
  representation theorem is open ([`Category_Theory_QLF.md`](Category_Theory_QLF.md)).
- **Status.** Proved (MO2 only).

### P04 · A priori orientation
- **Statement.** Every finite history has a completion. What the completion must supply is fixed by
  the history; how it is supplied is not.
- **Anchors.** `mirror_closes` ([`QLF_Discoveries2026`](lean/QLF_Discoveries2026.lean));
  `completion_net_determined`, `completion_not_unique` ([`QLF_Manifestation`](lean/QLF_Manifestation.lean)).
- **Depends on.** P01. **Status.** Proved.

### P05 · Isolation is closure
- **Statement.** A part is invisible to its environment's balance exactly when it is closed, even when
  its events are interleaved with the environment's; inserting a closed part changes the rest only by
  a global Pauli phase.
- **Anchors.** `isolated_iff_closed`, `isolation_interleaved`, `closed_insertion_is_phase`
  ([`QLF_Manifestation`](lean/QLF_Manifestation.lean); [`Manifestation.md`](Manifestation.md) §2).
- **Limits.** A statement about the closure algebra; not a derivation of laboratory isolation or
  decoherence.
- **Depends on.** P01, P02. **Status.** Proved.

### P06 · Forced sharing
- **Statement.** If a joint history closes and one part does not close on its own, neither does the
  other: the closure is shared, not a product of two closures.
- **Anchors.** `forced_sharing`, `vector_pair_shared`, `countBalanced_append_iff`
  ([`QLF_Discoveries2026`](lean/QLF_Discoveries2026.lean)).
- **Depends on.** P01. **Status.** Proved.

### P07 · Composability
- **Statement.** Closed histories compose into closed histories.
- **Anchors.** `countBalanced_append_iff` ([`QLF_Discoveries2026`](lean/QLF_Discoveries2026.lean));
  `closedLoop_append` ([`QLF_Folding`](lean/QLF_Folding.lean)) for lattice backbones;
  `isolation_interleaved` for interleaved composition.
- **Limits.** Composition does not make multiplicities factorize: the contact-order prediction built on
  that assumption failed ([`Protein_Folding.md`](Protein_Folding.md) §5e).
- **Status.** Proved.

### P08 · Conservation of the ledger
- **Statement.** Local events (joining, splitting, emitting a closure, reordering) conserve a region's
  net action ledger, so an imbalance persists under every sequence of local events. Gates that permute
  lines conserve the twist multiset.
- **Anchors.** `event_conserves_ledger`, `imbalance_persists`
  ([`QLF_Morphogenesis`](lean/QLF_Morphogenesis.lean)). The gate case is exhaustive over truth tables in
  [`fredkin_qlf.py`](fredkin_qlf.py) ([`Fredkin_QLF.md`](Fredkin_QLF.md)).
- **Restricts.** The inventory's wording ("closure-preserving transformations conserve the applicable
  invariants") is too vague to prove; the two statements above are what holds.
- **Status.** Proved (ledger); exact computational (gates).

### P09 · Reversible logic, irreversible process
- **Statement.** Time reversal is an involution (the Hermitian conjugate), but closure is many-to-one:
  distinct histories close to one outcome, so the past is not recoverable from the closure.
- **Anchors.** `eval_dagger` ([`RhoQuCalc`](lean/RhoQuCalc.lean));
  `time_reverse_involutive_but_closure_degenerate` ([`QLF_Reversibility`](lean/QLF_Reversibility.lean));
  [`Reversibility.md`](Reversibility.md).
- **Restricts.** "Histories admit conjugate reversals" is the first half only.
- **Status.** Proved.

### P10 · Computational universality
- **Statement.** Every terminating NAND-delay graph has an encoding that is a ZFA string and that the
  QuCalc generator produces.
- **Anchors.** `qlf_universality`, `encode_is_zfa` ([`QLF_Universality`](lean/QLF_Universality.lean);
  [`Universality.md`](Universality.md)).
- **Limits.** **Bookkeeping as it stands.** The encoding sends every edge to a cancelling pair
  (`[pos,neg]` or `[neg,pos]`), so it is ZFA for any edge list whatever. It records only edge types,
  not the graph or its output, and is not shown to be faithful.
- **Gate.** An encoding proved injective on computations (or output-preserving) whose image is ZFA.
- **Status.** Proved, but bookkeeping until the gate is passed.

### P11 · Unbounded complexity
- **Statement.** Closures are unbounded in number, prime (irreducible) closures exist at every even
  length, and closures grow exponentially.
- **Anchors.** `closures_unbounded`, `prime_closure_every_length`, `closures_at_least_eight_pow`
  ([`QLF_Manifestation`](lean/QLF_Manifestation.lean)); `closures_exponential`,
  `closure_search_lower_bound` ([`QLF_PossibilityGrowth`](lean/QLF_PossibilityGrowth.lean),
  [`Possibility_Growth.md`](Possibility_Growth.md)).
- **Limits.** Combinatorial; says nothing about life, minds or entropy.
- **Status.** Proved.

### P12 · Law of Exceptions
- **Statement.** Every finite closure capacity excludes a closure that a larger capacity admits;
  unbounded ZFA is the one exceptionless law.
- **Anchors.** `law_of_exceptions` ([`QLF_LawOfExceptions`](lean/QLF_LawOfExceptions.lean);
  [`Law_Of_Exceptions.md`](Law_Of_Exceptions.md)).
- **Restricts.** "Every law has an exception" is folklore and, as a set statement, a tautology. The
  proved form is about capacity.
- **Kill condition.** Exhibit another exceptionless law.
- **Status.** Proved.

### P13 · Closure is irrevocable
- **Statement.** A history closed at capacity `R` is closed at every larger capacity.
- **Anchors.** `closedAtHorizon_mono` ([`QLF_HorizonClosure`](lean/QLF_HorizonClosure.lean)).
- **Status.** Proved.

### P14 · Distance equals delay
- **Statement.** The shortest completion of a twist history has exactly the ℓ¹ norm of its signed
  action.
- **Anchors.** `delay_ge_distance`, `distance_eq_delay` ([`QLF_Manifestation`](lean/QLF_Manifestation.lean)).
- **Limits.** Defined on twist histories, not phase strings. Not a laboratory distance or a metric.
  Colour distance is bounded (at most one twist), so it cannot be this delay
  (`colour_distance_le_one`, [`QLF_ColourClosure`](lean/QLF_ColourClosure.lean)). Every shortest
  completion is a rearrangement of the canonical one (`shortest_completion_perm`), so the number of
  shortest completions is the multinomial of the per-axis imbalances. The delay includes the gauge
  component; restricting it to the three spatial axes is immediate, identifying it with physical
  separation is bridge B01.
- **Status.** Proved; the metric reading is bridge B01.

### P15 · Depth is latency
- **Statement.** For balanced, gauge-free phase strings, the number of pruning passes to closure is the
  maximum phase excursion.
- **Anchors.** `closedAtHorizon_iff_maxExcursion_le`, `closureDepth_eq_maxExcursion`
  ([`QLF_ClosureDepthLaw`](lean/QLF_ClosureDepthLaw.lean)); counted exactly by `W_eq_dp`
  ([`QLF_ClosureMultiplicity`](lean/QLF_ClosureMultiplicity.lean)).
- **Strengthened by** [`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean):
  `FirstPassageAt` is defined from `closedAtHorizon` alone and `firstPassageAt_iff_maxExcursion` derives
  the identity, where [`QLF_ZFAFirstPassageClock`](lean/QLF_ZFAFirstPassageClock.lean) defined ticks as
  the excursion.
- **Limits.** Both hypotheses are needed: `[+, gauge, −]` and `[+]` never close
  (`no_first_passage_gauge`, `no_first_passage_unbalanced`).
- **Status.** Proved.

### P16 · Time is not event count
- **Statement.** Histories with the same number of events can take arbitrarily different numbers of
  passes to close.
- **Anchors.** `event_count_cannot_determine_first_passage`, `nested_vs_adjacent_ratio`
  ([`QLF_ZFAFirstPassageClock`](lean/QLF_ZFAFirstPassageClock.lean)).
- **Strengthened by** C03 (inventory, not just count).
- **Status.** Proved. Pass count is not identified with proper time.

### P17 · Listening is capacity-relative
- **Statement.** A horizon of capacity `R` receives exactly the balanced, gauge-free histories whose
  excursion is at most `R`.
- **Anchors.** `closedAtHorizon_iff_maxExcursion_le` (the same theorem as P15, read as a listening;
  [`Philosophy.md`](Philosophy.md) §3a rule 2).
- **Status.** Proved.

### P18 · First-return decomposition
- **Statement.** Every closed history factors uniquely into an ordered sequence of prime (first-return)
  closures, so the closure generating function is `1/(1 − I)`.
- **Anchors.** `prime_prefix_exists`, `prime_prefix_unique`, `card_balanced_eq_sum_prime`
  ([`QLF_FirstReturn`](lean/QLF_FirstReturn.lean)); `census_irreducible_resummation`
  ([`QLF_AlphaBound`](lean/QLF_AlphaBound.lean)).
- **Status.** Proved.

### P19 · One closure decides
- **Statement.** On the two-body domain, observational equivalence is the greatest bisimulation of the
  append system, and one closing context (the first) decides it.
- **Anchors.** `obsEquiv_iff_exists_bisim`, `bisim_le_pairEquiv`, `one_closure_decides`,
  `first_closure_decides`, `phase_is_needed`
  ([`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean); [`Bridge_Tools.md`](Bridge_Tools.md)).
- **Limits.** That the joint-closure phase is the *only* observable is `B-OPEN`.
- **Status.** Proved (two-body domain).

### P20 · Selection without purpose
- **Statement.** In the net-balance niche model, two variants are admitted by the same niches exactly
  when they have the same net, and reordering within a net changes nothing.
- **Anchors.** `same_niches_iff_sameNet`, `rearrangement_neutral`
  ([`QLF_Manifestation`](lean/QLF_Manifestation.lean)).
- **Limits.** Not a biological or cognitive mechanism.
- **Status.** Proved.

### P21 · Perspective locality
- **Statement.** In the two-body tensor representation, local statistics are unchanged by remote local
  operations (no signalling), and the singlet violates every factorizable model's CHSH bound.
- **Anchors.** `perspective_locality`, `no_signalling`, `no_signalling_typed`,
  `marginal_setting_independent`, `chsh_factorizable_le`, `no_factorizable_model`
  ([`QLF_PerspectiveLocality`](lean/QLF_PerspectiveLocality.lean); [`Locality.md`](Locality.md)).
- **Counterexample to watch.** A naive census record does signal (`record_signals`,
  [`QLF_ClockIntervention`](lean/QLF_ClockIntervention.lean)); no-signalling for derived physical
  records is open.
- **Status.** Proved (two-body representation).

### P22 · Most possibility never closes
- **Statement.** The closure walk on `ℤ⁴` is transient: at least a quarter of possibility never closes
  (measured: about 80.7 %). Selection has teeth because there are more than two axes.
- **Anchors.** `polya_transience` ([`QLF_PolyaTransience`](lean/QLF_PolyaTransience.lean));
  `at_least_quarter_never_closes` ([`QLF_FirstReturn`](lean/QLF_FirstReturn.lean));
  `card_balanced_twist` ([`QLF_ProductWalk`](lean/QLF_ProductWalk.lean); [`Closure_Walk.md`](Closure_Walk.md)).
- **Consequence.** Closed histories cannot be normalized to probability one by fiat (issue
  [#207](https://github.com/rhovision-org/quantum-logical-framework/issues/207), kill condition 7).
- **Status.** Proved (bound); exact computational (the 80.7 %).

### P23 · Closures are colour singlets
- **Statement.** Every count-balanced history has total `F₃²` colour zero; the converse fails.
  Eight-twist balance, not the binary pos/neg projection, is what prunes colour.
- **Anchors.** `closure_is_colour_singlet`, `colour_singlet_not_closure`, `binary_projection_blind`,
  `spatial_vertex_iff_borromean` ([`QLF_ColourClosure`](lean/QLF_ColourClosure.lean)).
- **Limits.** The delay is colour-blind (`delay_colour_blind`), so a linear delay is not a string
  tension (GL8 open). Zero `F₃²` colour is not the same statement as a physical SU(3)-invariant
  singlet; the identification with SU(3) is conditional. Baryon winding, read on the junction,
  depends on where a loop is read from (`winding_not_rotation_invariant`) and is not additive under
  concatenation (`winding_not_additive`).
- **Status.** Proved; *Internal*.

### P24 · Organization carries phase
- **Statement.** Net action does not fix the fold. `^v><` (two closures in sequence) and `^>v<` (one
  interleaved closure) are rearrangements of one inventory, both closed, at delay `0` and colour
  neutral, and they fold to `+I` and `−I`; the interleaving flips the sign in every context. A closure
  inserted into both branches of a comparison leaves their relative phase unchanged; inserted into one
  branch it shifts it. On one pair from each of two spatial axes, the fold is `−I` exactly when the
  pairs cross, and those 8 orderings per plane (the electron loop and its mirror, with rotations) are
  the shortest closures that are both handed and carry the half-spin sign.
- **Anchors.** `same_inventory_opposite_phase`, `interleaving_flips_phase`, `interleaved_prime`,
  `common_mode_cancels`, `one_branch_closure_shifts_phase`, `neutrino_block_fold_blind`,
  `two_axis_classification`, `electron_class`
  ([`QLF_VacuumCorrelation`](lean/QLF_VacuumCorrelation.lean); [`Vacuum_Correlation.md`](Vacuum_Correlation.md)).
- **Limits.** "`−I` exactly when handed" holds at length 4 only: at length 6, 48 of the 720
  one-pair-per-axis orderings are self-conjugate with `−I` (exact computational,
  [`vacuum_correlation_census.py`](vacuum_correlation_census.py)). The H1 loops are uncharged, and
  nothing here relates phase to energy or mass.
- **Depends on.** P01, P05. **Status.** Proved; *Internal*.

### P25 · The closure clock is set by dependencies, not by serialization
- **Statement.** Identical per-perspective records can hide different closure depths: three
  perspectives each holding `+ −` close at depth 1 side by side and depth 3 nested (RC0). When
  actions of different perspectives commute, swaps never change a record and carry nested to side by
  side, so the depth-3 reading belongs to a serialization, not to the records. The
  serialization-free quantity is the least depth over the interleavings the dependencies allow; for
  independent perspectives it is a function of the records, and a dependency can only raise it.
- **Anchors.** `rc0_record_does_not_determine_clock`, `record_swap`, `nested_commutes_to_adjacent`,
  `reconcile_record`, `reconcile_not_always_minimal`, `relCapacity_example`,
  `dependency_increases_capacity`, `dependency_strict_increase`
  ([`QLF_RelationalClock`](lean/QLF_RelationalClock.lean);
  [`Planck_Dispersion_Prediction.md`](Planck_Dispersion_Prediction.md) §5).
- **Limits.** RC0 is proved for three perspectives and RC1 for two; the general partial-order
  version is not formalised. That nature realises the minimum over admissible interleavings is a
  proposed reading. No observable map (RC2–RC6).
- **Depends on.** P01. **Status.** Proved within the stated cases; *Internal*.

---

## C. Candidate principles

Each row says what is already proved, what is not, and the gate.

| ID | Candidate | What is proved | What is not / gate | Status |
|---|---|---|---|---|
| **C01** | **Time is unresolved logical depth.** | `FirstPassageAt` is unique and equals the excursion (`firstPassageAt_unique`, `firstPassageAt_iff_maxExcursion`, [`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean)). | Pass count is not identified with GR proper time or with the tick order of [`QLF_LocalityDefinitions`](lean/QLF_LocalityDefinitions.lean). | Proved as an operational clock; physical reading `B-OPEN`. |
| **C02** | **Capacity and latency are dual.** | `least_capacity_iff_firstPassageAt`, `closes_iff_latency_fits` ([`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean)). | The first is order-theoretic bookkeeping and the second restates the depth law (P15). | Proved, bookkeeping. |
| **C03** | **Latency depends on ordering, not inventory.** | Two rearrangements of the same events close after `d` and `1` passes (`same_census_different_latency`); no function of the event multiset fixes latency (`census_cannot_determine_first_passage`); the latencies at fixed inventory are exactly `{1,…,d}` (`latency_spectrum_exact`). All in [`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean). | | Proved. |
| **C04** | **Priority is first closure; frequency is multiplicity.** | Closure is irrevocable (P13); the shallowest closure is not the modal one (`depth_one_not_modal`, [`QLF_ClosureMultiplicity`](lean/QLF_ClosureMultiplicity.lean)). For competitors sharing no history, more ways at every horizon means at least as likely first. | That last theorem is a paper proof ([`MostWays_First.md`](MostWays_First.md) §2, checked by [`most_ways_first.py`](most_ways_first.py)), not Lean. It fails for overlapping competitors (Penney: HHH has more ways than TTHH, yet TTHH comes first 7 times in 12). "Frequency = multiplicity" holds under the uniform measure, which is a stated choice. | Priority: proved. Independent case: paper proof. Overlapping case: **Restricted**. |
| **C05** | **Listening takes time; events do not.** | Remaining latency counts down (`listening_countdown`), the record stays open until the last pass (`listening_open_before`) and closes at once (`listening_trigger`, `closure_event_atomic`). All in [`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean); [`Event_Timing_QLF.md`](Event_Timing_QLF.md) ET1. | The theorems count passes. Reading the closed state as "the event takes no time" is interpretation. | Proved; reading is interpretation. |
| **C06** | **Closure conserves the ledger and erases the route.** *(Restated; see note.)* | The ledger is conserved (P08). Closure is many-to-one (P09), and a class function of one closed history carries one bit (`fold_eq_classBit`, `class_function_factors`, [`QLF_ClassFactoring`](lean/QLF_ClassFactoring.lean)). Each half-spin closure resolves `log 2` (`binary_kl_delta_uniform`, [`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)). | The inventory's "closure preserves information" is false for the route: which history closed is not recoverable. | **Restricted**: proved in the restated form. |
| **C07** | **Diversity enables novel closures.** | Complementary composition creates a closure self-composition cannot (`complementary_composition_creates_novel_closure`, `self_composition_type_one`, [`QLF_DiversityNovelOutcome`](lean/QLF_DiversityNovelOutcome.lean)); no history missing a colour axis carries junction baryon number, while a closed three-axis one does (`three_colour_emergence`, [`QLF_DiversityEmergence`](lean/QLF_DiversityEmergence.lean)). | Witnesses show possibility, not frequency or advantage. **Strengthened:** of the 720 orderings of one conjugate pair per spatial axis, 576 are wound, and 384 of the 480 first closures (exact computational, [`borromean_census.py`](borromean_census.py) `--minimal`). **Restricted:** spreading an imbalance over more axes raises the number of shortest completions (multinomial, `shortest_completion_perm`), but the most diverse case cancels exactly once phases are counted: the 6 orderings of `^ < /` sum to `0`, while `^^^` (1 way) and `^^<` (3 ways) do not (`diverse_completions_cancel`, `cone_amplitude`). More unsigned ways is not an advantage by itself. | Proved (witnesses; the phase restriction); exact computational (the 720-ordering census). |
| **C08** | **Diversity increases collective capability.** | Registered D8c2 PASS, carried by one stratum and measure-limited ([`Diversity_Advantage_D8c2.md`](Diversity_Advantage_D8c2.md)). Library assembly PASS, coverage only ([`Library_Diversity_Assembly.md`](Library_Diversity_Assembly.md)). | Both tested rescues of D8c2 fail ([`Diversity_Revision_D8c2b.md`](Diversity_Revision_D8c2b.md)). The library advantage equals minus homogeneous synergy, and ordinary assembly gives the same Δ, so it is not closure-specific. | Conjecture; registered tests mixed. |
| **C09** | **Composability increases multiplicity.** | Unique prime factorization (P18) and exponential growth (P11). | The "factorial-class multiplicity" of composable structures ([`Philosophy.md`](Philosophy.md) §3a) is not proved. | Partial. |
| **C10** | **Self-similar structures dominate manifestation.** | Self-similar closure families exist and are counted; all sit at excursion 1, so every horizon hears them ([`self_similar_closures.py`](self_similar_closures.py)). | "Dominate" has no proved measure statement. | Exact computational (existence); dominance is a conjecture. |
| **C11** | **Interaction is first shared closure of independent histories.** | Shared closure is forced (P06); pair-built events read the same from either body, but whether an event was shared is not reconstructible from the bodies' words (`shared_event_not_from_bodies`, `pairing_not_reconstructible`, [`QLF_SharedEvent`](lean/QLF_SharedEvent.lean)); binding needs opposite orientation (`bind_iff_opposite`, [`QLF_Morphogenesis`](lean/QLF_Morphogenesis.lean)). | The *first* in the statement, and any dynamics of interaction, are not formalized. | Partial. |
| **C12** | **Every perspective is a finite information boundary.** | A04 and P17. | The identification of a perspective with a capacity is the A08 bridge. | Structural; `B-OPEN`. |
| **C13** | **Shared reality is the overlap of perspectives.** | `shared_iff_overlap`, `global_zfa_not_from_pair`, `relay_phase_transfer` ([`QLF_SharedReality`](lean/QLF_SharedReality.lean)); `joint_record_minimal`, `single_body_perspectives_share_only_constants` ([`QLF_PerspectiveHolography`](lean/QLF_PerspectiveHolography.lean)). | Accessibility from dynamics, shared-pair birth, and no-signalling for correlated histories ([`Holography_Audit.md`](Holography_Audit.md) §5). | Partial. |
| **C14** | **The boundary determines the accessible interior.** | Closure is a boundary property (`closure_iff_boundary_silent`, bookkeeping); every prefix closes (`every_prefix_closes`, so it constrains no path); the area law follows from locality (`cutEntropy_le_area`; `local_area_law`, [`QLF_LocalAreaLaw`](lean/QLF_LocalAreaLaw.lean)). Closure detects but cannot correct single errors (`single_error_not_correctable`). | The single-history projection is many-to-one ([`Holographic.md`](Holographic.md)). The perspective-consistent reconstruction theorem is open (issue [#296](https://github.com/rhovision-org/quantum-logical-framework/issues/296)). | Restricted formal results. |
| **C15** | **History carries memory that the instantaneous state loses.** | Two histories with the same events, hence the same inventory and net action, have different latencies (`census_cannot_determine_first_passage`, [`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean)). So inventory and net action are not a sufficient state for latency. | The pruning system on full histories is deterministic; the memory lives in the *projection*. Readings for memory, consciousness or QuantumOS are conjecture. | Proved for the projection. |
| **C16** | **Intelligence is the capacity to synthesize new closures.** | None specific. | Operational definition is `B-OPEN` ([`Claim_Status.md`](Claim_Status.md), strange-loop section; [`QLF_as_Intelligence.md`](QLF_as_Intelligence.md)). | Conjecture. |
| **C17** | **Agency is the capacity to change the multiplicity of accessible closures.** | None; the reading is [`Philosophy.md`](Philosophy.md) §3c, with laser cooling as the worked example ([`Mpemba.md`](Mpemba.md)). | A model where an agent's structure provably changes `W`. | Conjecture. |
| **C18** | **Active inference is the selection of jointly closing relations.** | For games: Nash equilibrium is closure (`nash_iff_closure`); a game has a free-action functional iff it is a potential game (`free_action_iff_four_cycle`); paying everyone the total makes welfare the potential (`welfare_game_potential`) ([`QLF_PotentialGames`](lean/QLF_PotentialGames.lean), [`Game_Theory_QLF.md`](Game_Theory_QLF.md)). | Matching pennies has no free-action functional. Active inference beyond potential games is open. | Partial. |
| **C19** | **Emergence proceeds by cancellation, preservation and lifting.** | Ingredients: inserting a closed part acts as a phase (P05); the ledger is conserved (P08). | The triple is a reading ([`Philosophy.md`](Philosophy.md) §9), not a theorem. | Reading with partial anchors. |
| **C20** | **Order arises without an external organizer.** | Imbalance persists under local events (P08). A registered lattice test found that the conserved ledger segregates a patternless population into domains (grade N, [`Morphogenesis.md`](Morphogenesis.md)). | A pattern-forming scale (Turing) is open. | Conjecture. |
| **C21** | **Closure networks resist perturbation.** | None. | A resilience measure and a theorem about it. | Conjecture. |
| **C22** | **Conservative self-reference enables self-knowledge.** | Toy forms: `conservative_return` ([`QLF_ConservativeReturn`](lean/QLF_ConservativeReturn.lean)), `no_event_cycle`. | Self-knowledge as a bisimulation is `NOT_STARTED` ([`Strange_Loops.md`](Strange_Loops.md), [`Claim_Status.md`](Claim_Status.md)). | Conjecture. |
| **C23** | **Recursive perspectival existence** (Jim, 2026-11-27). *Every manifest structure is a perspective with three spatial dimensions; the fourth logical axis expresses its relation to other perspectives; higher-order reality emerges through the shared closure of constituent perspectives.* | **Three plus one is forced.** Every axis frame contains the identity (gauge) axis (`frame_contains_I`), two spatial axes force the third (`two_spatial_axes_force_three`), and eight twists are the only size with non-commuting observables (`noncommuting_iff_eight`) ([`QLF_AlphabetNecessity`](lean/QLF_AlphabetNecessity.lean)), given the posit in P01. **The fourth axis is relation-free inside a perspective.** A gauge twist folds to `±I`, which commutes with every twist and changes no spatial relation, only a sign; in the `Form` it is the `t` (identity) coefficient, and a closure's charge is its gauge count (`chiralCharge_eq_gauge_counts`, [`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean)). **Higher-order reality by shared closure** is P06, C11 and C13; recursion is P05 and P18. | **Restricts the first clause:** the *frame* has three spatial axes, but a manifest structure need not occupy them; `+−` closes with no spatial twist and `^v` uses one axis. **The second clause is open, and its strong form is false:** shared closure does not need the fourth axis, since `vector_pair_shared` closes two perspectives with spatial twists only. **Participation is not tree-shaped** ([`QLF_PerspectiveNetwork`](lean/QLF_PerspectiveNetwork.lean)): three perspectives can each share a closure with each of the others (`shared_closure_cycle_exists`), so no tree on those perspectives carries the relations as edges (`tree_edges_insufficient`, graph-theoretic bookkeeping; mediator nodes not excluded), and the proton closure splits into three perspectives none of which, alone or in pairs, closes (`irreducible_three_way_closure`). Both witnesses use spatial twists only. A gauge twist keeps the winding and moves the `F₃²` colour (`gauge_keeps_winding_moves_colour`). Gate: show that what separates a joint closure from two separate ones is carried by the gauge axis (for example, the relay sign of `relay_phase_transfer`, [`QLF_SharedReality`](lean/QLF_SharedReality.lean)). | Clause 1: proved for the frame, restricted for structures. Clause 2: conjecture. Clause 3: partial (C11, C13); a hierarchy of perspectives and their participation network are distinct structures (proved witnesses). |
| **C24** | **Handedness mass gap** (AI review, 2026-11-27). *The electron is the least-energy persistent mode that sustains a confirmed electrical handedness; lighter structures take part in shared closures without a persistent electrical distinction.* | H1: the shortest closures that are handed and carry `−I` are the 24 electron-class loops at length 4; length-2 closures are all self-conjugate (`two_axis_classification`, `length_two_closures`, [`QLF_VacuumCorrelation`](lean/QLF_VacuumCorrelation.lean)). The electron's charge is an unmatched gauge twist (`electronCharged_not_countBalanced`). | Least complex is not least energetic. Gates H0 (confirmed handedness from shared closures), H2 (which loops carry a gauge distinction), H3 (persistence), then the bridge H4–H6 to an energy threshold and the electron mass, and H7 ([`Vacuum_Correlation.md`](Vacuum_Correlation.md) §6). | Conjecture; H1 proved. |
| **C25** | **A neutrino's significance is relational** (AI review, 2026-11-27). *What separates a neutrino from vacuum activity is the correlations it preserves and the closures it enables, not its energy.* | N0: the neutrino word `^v` reads the same as a vacuum pair, and in every context its fold equals that of any Hermitian pair on any axis (`neutrino_block_fold_blind`); provenance is not in the word (`no_word_observable_separates`, bookkeeping). Interleaving is a relation the fold sees (P24). | N1 (that a neutrino carries a relational invariant), N2 (persistence), N3 (a matched-conditions `ΔW_R ≠ 0`), N4–N5 (phase correlations, oscillation phenomenology). | Conjecture; N0 proved. |
| **C26** | **Native quantum universality on a common qubit** ([`Framing.md`](Framing.md) O1). *Hadamard, the count-weighted rotation and controlled-Z act natively on one encoded qubit space and compose coherently.* | The ingredients separately: `su2_dense`, `joint_closure_is_cz`, `cz_entangling`, `hadamard_sq` ([`QLF_QuantumComputer`](lean/QLF_QuantumComputer.lean)); Barenco as matrix algebra ([`QLF_Barenco`](lean/QLF_Barenco.lean)). | **Common encoding built** ([`QLF_NativeBell`](lean/QLF_NativeBell.lean)): on the presence qubit, native CZ (`nativeCZ_eq_cz`), native Hadamard by branching (`nativeHA_eq`) and a native non-Clifford phase `diag(1, z)` (`nativePA_eq`, `nativePhase_infinite_order`), with the joint sign read off folds (`jointSign_eq`). **Bell state by native operations** (`native_bell`), matching the standard circuit (`native_bell_matches_circuit`), entangled (`native_bell_not_product`), correlated in two bases (`native_bell_x_correlated`). **Assembled** ([`QLF_NativeUniversality`](lean/QLF_NativeUniversality.lean)): the mirror census gives `diag(1, z̄)` (`censusRatioMirror_eq_zbar`), native one-strand products are dense in `SU(2)` up to a scalar (`native_one_dense`), the `n`-strand native operations are the standard gates (`nativeBranch_eq`, `nativeJoint_eq`, `nativePhase_eq`, `nativeMirror_eq`), and every unitary on `n + 1` strands is a limit of scalar multiples of native circuits (`native_universal`). No approximation rate is claimed. | **Proved** (universality on rays). |
| **C27** | **Anthropic observational equivalence** ([`Framing.md`](Framing.md) §3a, O2). *Every correct, computable model agrees with QLF on everything observable.* | Observation is closure (A01 applied to observers); `ObsEquiv` is the tensor quotient for two bodies (`obsEquiv_iff_pairEquiv`, [`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean)); classical models run natively (`fredkin_complete`). | Universality does not give equivalence: a universal computer runs incorrect models too. Gate: `Correct(M) ⟹ ∃ E_M, O_QLF ∘ E_M = O_M`, preserving observables, dynamics and distributions; `ObsEquiv` extended to `N` bodies and the entangled sector. Premise: the model is computable (Deutsch 1985). Proved step: equivalent models receive the same verdict on every observable proposition (`equivalent_same_verdicts`, [`QLF_ModelTesting`](lean/QLF_ModelTesting.lean)). **The gate, proved at the level of records** ([`QLF_AnthropicEquivalence`](lean/QLF_AnthropicEquivalence.lean)): every model with a computable admissibility test and finite records has an encoding with `O_QLF ∘ E_M = O_M`, one decoder for all models (`anthropic_equivalence`), failing exactly where the model forbids (`encodeModel_canFail_iff`), with verdicts and ensemble counts transferred (`verdicts_transfer`, `frequencies_transfer`); for conservation-law models the encoding never consults admissibility (`conservation_equivalence`). Still open: `ObsEquiv` beyond two bodies. | **Proved** for records under the computability premise; `N`-body `ObsEquiv` open. |
| **C28** | **Model testing has five verdicts** ([`Framing.md`](Framing.md) §4, O3). *Any finitely expressible model, encoded as closures by an encoding that can fail, is necessary, possible, impossible, equivalent or undetermined relative to stated conditions.* | Worked verdicts: local hidden variables and non-contextual assignments impossible (`chsh_factorizable_le` with `singlet_chsh`; `no_choice_fixed_in_advance`), Boolean circuits possible (`fredkin_complete`). | **Interface built** ([`QLF_ModelTesting`](lean/QLF_ModelTesting.lean)): `Encoding`, the verdict predicates, `CanFail`; `vacuous_of_cannot_fail` proves a test through an encoding that cannot fail reduces to the model alone, and `pairEncoding_cannot_fail` shows the `qlf_universality` pattern is such an encoding. Open: instances for the worked verdicts (Bell, Kochen–Specker) stated through the interface. | Method; interface proved. |
| **C29** | **Computing by closure** ([`Framing.md`](Framing.md) §4a, O4). *A problem stated as its unresolved distinctions is solved by the substrate supplying an admissible closure.* | `closing_cost_exact` (minimal completion length = imbalance), `completion_perm_closes` ([`QLF_QuantumComputer`](lean/QLF_QuantumComputer.lean)). | Proved only for conjugate imbalance, not arbitrary constraints; encoding a hard problem can carry its hardness ([`P_vs_NP_QLF.md`](P_vs_NP_QLF.md)). **Closure selection** ([`QLF_ClosureSelection`](lean/QLF_ClosureSelection.lean)): choosing offered words so that an obligation closes is decided by a reachable-charge sweep (`selection_closes_iff`, `closable_iff`) with at most `(2L + 1)⁴` states (`reachable_card_le`); Subset Sum embeds in unary (`subset_sum_embeds`), so no NP-hardness transfers. The class is conservation of written counts. Open: optimization and collective inference beyond it. | **Proved** for closure selection. |

**The overarching candidate.** *The synthesis of reality resolves imbalance while keeping the
distinctions that can take part in higher closures, so organized complexity is unbounded.* This is a
conjecture that collects A01, P04, P05, P07, P11 and C07–C21. P11 makes the *unbounded* part a theorem
about counts. What is open is the part that would make it a principle: when the multiplicity,
persistence and resilience of organized structures increase.

---

## D. Physical bridges (open obligations)

None of these is promoted by the formal results it rests on. The `Claim_Status` code for each is
`B-OPEN` unless stated.

| ID | Bridge | First-order formal content | Outstanding obligation |
|---|---|---|---|
| **B01** | Space is synthesized by delay | P14 | Derive a metric from closure relations; the continuum-limit stages are in [`Continuum_Limit.md`](Continuum_Limit.md). |
| **B02** | Everything is a clock | Periodic return clock ([`QLF_LoopClosure`](lean/QLF_LoopClosure.lean)); C01 | Identify recurring closures with independent clocks. |
| **B03** | Gravity is balancing action | `order_metric_continuum_limit`, `benincasa_dowker_limit` are named axioms ([`CLAUDE.md`](CLAUDE.md) axiom inventory) | Derive gravitational dynamics. |
| **B04** | Binding contracts space; unbound like orientation expands it | `like_poles_expand`, `opposite_poles_destroy` ([`QLF_MagneticOrientation`](lean/QLF_MagneticOrientation.lean)) | The spatial response with a distance law, not an assumed contraction. |
| **B05** | Light is local in null geometry | `symbol_det` ([`QLF_LorentzSymbol`](lean/QLF_LorentzSymbol.lean)) | Reading the symbol's zeros as light's dispersion is an assumption (the kinetic reading). |
| **B06** | Charge is emergent | Closures are neutral (`zfa_closure_is_neutral`, [`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean)); [`QLF_Handedness`](lean/QLF_Handedness.lean) | Measurable charge from orientation and closure. |
| **B07** | Mass is persistent internal recurrence | `force_scales_with_shift` ([`QLF_Inertia`](lean/QLF_Inertia.lean), continuum algebra) | A counting version; the same `m` as the gauge-fold depth ([`Inertia.md`](Inertia.md)). |
| **B08** | Energy is informational activity | `log 2` per closure ([`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)) | The physical energy observable. |
| **B09** | Probabilities come from ways of closing | `born_from_ways`, `assignment_unique` ([`QLF_BornFromWays`](lean/QLF_BornFromWays.lean)); cylinder measure P22/A07 | Cylinder measure = event probability is open; physical refinement is a premise ([`Born_Rule.md`](Born_Rule.md)). |
| **B10** | Stationary action is the continuum rendering of ZFA | | The S-bridge ([`Lagrangian_Formulation.md`](Lagrangian_Formulation.md)). |
| **B11** | Holography follows from isolation | C14 | Reconstruction and its uniqueness domain (issue #296). |
| **B12** | Relativity follows from perspective | The step census has a preferred frame (`step_census_frame_dependent`); large-scale isotropy is Euclidean, not boost invariance (`boost_not_euclidean`) ([`QLF_RelativityScale`](lean/QLF_RelativityScale.lean)). Free Dirac-walk boost covariance has a claim record with bridge `OPEN` ([`claim_records/relativity_boost.json`](claim_records/relativity_boost.json)). | Boost covariance of the interacting theory without a preferred frame ([`Relativity_Principle.md`](Relativity_Principle.md)). |
| **B13** | Constants are closure invariants | α leading 137 and the formal band ([`Claim_Status.md`](Claim_Status.md)) | The coupling, scale and observable maps. |
| **B14** | Thermodynamic entropy comes from closure statistics | Cut entropy is the von Neumann entropy of cut singlets (`cutEntropy_eq_vonNeumann`, [`QLF_HolographicCompletion`](lean/QLF_HolographicCompletion.lean)) | Thermodynamic ensembles and entropy accounting. |
| **B15** | Recurring dominance is frequency in the world | C04 | That census multiplicity is the observed rate (needs B09). |
| **B16** | Vacuum correlations set both the α residual and neutrino phase evolution (AI review, 2026-11-27) | P24 (V0 for common mode, V1); [`QLF_NeutrinoOscillation`](lean/QLF_NeutrinoOscillation.lean) precession; the α bracket ([`Alpha_Residual.md`](Alpha_Residual.md)) | V2: a connected correlation `K_R(a,b)` from a phase-weighted closure measure fixed before the comparison (the post hoc weighting of [`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) §47 failed on the proton, §48); V3–V6: the α correction without fitting, neutrino phase differences, mixing angles and `Δm²`, one mechanism for both, within oscillation decoherence bounds. The 0.36 meV ↔ 87 GHz match with [`VacuumEnergy.md`](VacuumEnergy.md) §4 is a coincidence until a coupling is derived. |

---

## E. Corrected formulations

Overgeneralizations found while building the registry. Use the right-hand column.

| Do not say | Say | Where |
|---|---|---|
| What happens in the most ways happens first. | First closure decides priority; multiplicity decides frequency under a stated measure. "Most ways ⇒ first" holds for competitors that share no history. | C04; [`MostWays_First.md`](MostWays_First.md); [`Philosophy.md`](Philosophy.md) §3a |
| Every law has an exception. | Every finite closure capacity has an exception at a greater capacity. | P12 |
| Diversity is advantageous. | Diversity permits novel compositions; advantage has to be shown, and registered tests are mixed. | C07, C08 |
| Frequency is multiplicity. | Multiplicity, recurrence rate and coherent amplitude are three quantities; frequency = multiplicity holds under the uniform measure, and the bridge to rate is B15. | C04, B09 |
| Closure preserves information. | Closure conserves the ledger and erases the route. | C06 |
| Every terminating computation *is* a ZFA string. | Every terminating NAND-delay graph has a ZFA encoding; the encoding is not yet shown faithful. | P10 |
| One construction proves the mechanism. | One construction proves possibility, not physical identification or uniqueness. | Section A rules |
| All ZFA events are null. | Null propagation and ZFA closure are distinct structures; their relation is B05. | B05 |
| ZFA defeats entropy. | ZFA resolves imbalance. Whether it produces organization that resists entropy is C20/C21, both open. | C20, C21 |

---

## F. Where this came from, and what was checked

The registry was drafted from two AI reviews (2026-11-27) and checked against `main`. Changes from
those drafts, so the next revision does not reintroduce them:

- **Counts.** The reviews quoted "360 active modules" and a "375-anchor baseline". The footprint
  baseline in [`lean/axiom_footprints.expected.json`](lean/axiom_footprints.expected.json) now has 809
  anchors, and the module count lives only in [`lean/README.md`](lean/README.md).
- **Proved since the reviews.** C01–C03, C05 and the historical-memory candidate (C15) are proved in
  [`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean)
  ([#329](https://github.com/rhovision-org/quantum-logical-framework/pull/329)), which develops the
  first-passage work of #256 (closed into #259); the colour principle (P23) and the GL7 delay bound are
  proved in [#327](https://github.com/rhovision-org/quantum-logical-framework/pull/327).
- **Historical memory.** It is supported by the pruning clock
  ([`QLF_ClosureDepthTime`](lean/QLF_ClosureDepthTime.lean)), not by
  [`MostWays_First.md`](MostWays_First.md), which is about priority versus multiplicity.
- **Boost covariance.** The open interacting return is tracked in
  [`claim_records/relativity_boost.json`](claim_records/relativity_boost.json) and
  [`Relativity_Principle.md`](Relativity_Principle.md), not in issue #207 (the closure-amplitude
  programme).
- **Universality.** The anchor is real, but the encoding is ZFA by construction (P10).
- **Information preservation.** Restated (C06), since closure is many-to-one.
- **Reframed (2026-11-27).** Section A now rests on the one conjecture A01. A02–A09 are reclassified as derived
  results, readings, or the absence of an assumption, and the known-fact inputs A10–A13 are added
  ([`Framing.md`](Framing.md)).
- **Added.** P22 (transience) and P23 (colour), which neither draft listed, and the foundation A03
  (only logic is assumed), which is binding in this repository.

Related: [`Claim_Status.md`](Claim_Status.md) · [`Theory_Of_Everything.md`](Theory_Of_Everything.md) ·
[`ScientificApproach.md`](ScientificApproach.md) · [`Open_Problems.md`](Open_Problems.md) ·
[`Manifestation.md`](Manifestation.md) · [`FlowChart.md`](FlowChart.md)
