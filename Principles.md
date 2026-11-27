# Principles — the canonical registry

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

This page lists QLF's principles: the few things it assumes, the structural laws it proves from them,
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

These are the assumption budget, not nine physical axioms. Only **A01** is a selection premise; the
rest are ontology, event semantics or interpretation, as the ledger in
[`ScientificApproach.md`](ScientificApproach.md) §1c separates them.

| ID | Principle | Kind | Status and anchors |
|---|---|---|---|
| **A01** | **ZFA selection.** A history becomes an event exactly when its signed action is zero on every axis: equal and opposite logical action, zero free energy. | The premise | Standing, under test; kill condition in [`ScientificApproach.md`](ScientificApproach.md) §1a. Defined by `achieves_ZFA`, `full_zeno_prune` ([`QLF_Axioms`](lean/QLF_Axioms.lean)) and `countBalanced`. |
| **A02** | **Possibilism.** Every generable history exists a priori as a way. Possibilism needs only one way: a single closure suffices for a thing to happen, and the first closure is the strongest way. | Ontology | Interpretive commitment, not testable in isolation ([`ScientificApproach.md`](ScientificApproach.md) §1b, [`Philosophy.md`](Philosophy.md) §3). |
| **A03** | **Only logic is assumed.** Nature is assumed logical, not assumed to be QLF's construction; the construction is one model of the logical laws. | Method | Worked case proved: `weakening_iff_persistence`, `no_time_loops_from_logic`, `histories_are_a_model`, and the counter-model `loopWorld_has_time_loop` ([`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean); [`Philosophy.md`](Philosophy.md) §3d). |
| **A04** | **Finite realizability.** A finite-information region cannot hold an actual continuum of distinguishable states; possibility is unbounded, but each manifestation is finite. | Ontology + one theorem | `no_continuum_in_finite_region` proved ([`QLF_Realizability`](lean/QLF_Realizability.lean)) *given* a finite-information bound; the bound itself (Bekenstein) is physical input. |
| **A05** | **Information primacy.** Information relations precede matter, space and time. | Ontology | Interpretive ([`ScientificApproach.md`](ScientificApproach.md) §1b). |
| **A06** | **No observer potency.** An apparatus is a closure inventory and an observer is a perspective; measurement is joint closure and creates nothing. | Ontology | Interpretive floor ([`ScientificApproach.md`](ScientificApproach.md) §1b). Formal support: observers agree on closure and fold under frame relabelings (`observers_agree`, [`QLF_MultiObserver`](lean/QLF_MultiObserver.lean)). |
| **A07** | **A closure is an event.** Along a history, the first closure is the event (the absorbing reading). | Event semantics | Physical hypothesis, adopted after the alternatives were rejected ([`ScientificApproach.md`](ScientificApproach.md) §1c, §11). Its mathematical side is proved: first closures are prefix-free and the cylinder mass is `≤ 1` (`twist_kraft`, [`QLF_KraftMeasure`](lean/QLF_KraftMeasure.lean)). |
| **A08** | **Finite perspective.** An observer receives only what closes within its capacity. | Ontology + bridge | The listening is proved (P17). "Capacity = apparatus resolution" is a partially developed bridge ([`ScientificApproach.md`](ScientificApproach.md) §1c). |
| **A09** | **Synthesized spacetime.** Space and time are outputs of closure, not a background. | Ontology, then bridges | Interpretive; each physical reading is a bridge in section D. |

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
- **Limits.** That balance is *required* is the definition of A01, not a theorem. The residual posit
  ("an elementary distinction is a signed element of the observable frame") is open
  ([`ScientificApproach.md`](ScientificApproach.md) §1c).
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
  (`colour_distance_le_one`, *pending [#327](https://github.com/rhovision-org/quantum-logical-framework/pull/327)*).
- **Status.** Proved; the metric reading is bridge B01.

### P15 · Depth is latency
- **Statement.** For balanced, gauge-free phase strings, the number of pruning passes to closure is the
  maximum phase excursion.
- **Anchors.** `closedAtHorizon_iff_maxExcursion_le`, `closureDepth_eq_maxExcursion`
  ([`QLF_ClosureDepthLaw`](lean/QLF_ClosureDepthLaw.lean)); counted exactly by `W_eq_dp`
  ([`QLF_ClosureMultiplicity`](lean/QLF_ClosureMultiplicity.lean)).
- **Strengthened by** *pending [#329](https://github.com/rhovision-org/quantum-logical-framework/pull/329)*:
  `FirstPassageAt` is defined from `closedAtHorizon` alone and `firstPassageAt_iff_maxExcursion` derives
  the identity, where [`QLF_ZFAFirstPassageClock`](lean/QLF_ZFAFirstPassageClock.lean) defined ticks as
  the excursion.
- **Limits.** Both hypotheses are needed: `[+, gauge, −]` and `[+]` never close
  (`no_first_passage_gauge`, `no_first_passage_unbalanced`, pending #329).
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
  `spatial_vertex_iff_borromean` (*pending [#327](https://github.com/rhovision-org/quantum-logical-framework/pull/327)*).
- **Limits.** The delay is colour-blind (`delay_colour_blind`), so a linear delay is not a string
  tension (GL8 open).
- **Status.** Proved on the PR branch; *Internal*.

---

## C. Candidate principles

Each row says what is already proved, what is not, and the gate.

| ID | Candidate | What is proved | What is not / gate | Status |
|---|---|---|---|---|
| **C01** | **Time is unresolved logical depth.** | `FirstPassageAt` is unique and equals the excursion (`firstPassageAt_unique`, `firstPassageAt_iff_maxExcursion`, *pending [#329](https://github.com/rhovision-org/quantum-logical-framework/pull/329)*). | Pass count is not identified with GR proper time or with the tick order of [`QLF_LocalityDefinitions`](lean/QLF_LocalityDefinitions.lean). | Proved (pending #329) as an operational clock; physical reading `B-OPEN`. |
| **C02** | **Capacity and latency are dual.** | `least_capacity_iff_firstPassageAt`, `closes_iff_latency_fits` (pending #329). | The first is order-theoretic bookkeeping and the second restates the depth law (P15). | Proved, bookkeeping. |
| **C03** | **Latency depends on ordering, not inventory.** | Two rearrangements of the same events close after `d` and `1` passes (`same_census_different_latency`); no function of the event multiset fixes latency (`census_cannot_determine_first_passage`); the latencies at fixed inventory are exactly `{1,…,d}` (`latency_spectrum_exact`). All pending #329. | | Proved (pending #329). |
| **C04** | **Priority is first closure; frequency is multiplicity.** | Closure is irrevocable (P13); the shallowest closure is not the modal one (`depth_one_not_modal`, [`QLF_ClosureMultiplicity`](lean/QLF_ClosureMultiplicity.lean)). For competitors sharing no history, more ways at every horizon means at least as likely first. | That last theorem is a paper proof ([`MostWays_First.md`](MostWays_First.md) §2, checked by [`most_ways_first.py`](most_ways_first.py)), not Lean. It fails for overlapping competitors (Penney: HHH has more ways than TTHH, yet TTHH comes first 7 times in 12). "Frequency = multiplicity" holds under the uniform measure, which is a stated choice. | Priority: proved. Independent case: paper proof. Overlapping case: **Restricted**. |
| **C05** | **Listening takes time; events do not.** | Remaining latency counts down (`listening_countdown`), the record stays open until the last pass (`listening_open_before`) and closes at once (`listening_trigger`, `closure_event_atomic`). All pending #329; [`Event_Timing_QLF.md`](Event_Timing_QLF.md) ET1. | The theorems count passes. Reading the closed state as "the event takes no time" is interpretation. | Proved (pending #329); reading is interpretation. |
| **C06** | **Closure conserves the ledger and erases the route.** *(Restated; see note.)* | The ledger is conserved (P08). Closure is many-to-one (P09), and a class function of one closed history carries one bit (`fold_eq_classBit`, `class_function_factors`, [`QLF_ClassFactoring`](lean/QLF_ClassFactoring.lean)). Each half-spin closure resolves `log 2` (`binary_kl_delta_uniform`, [`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)). | The inventory's "closure preserves information" is false for the route: which history closed is not recoverable. | **Restricted**: proved in the restated form. |
| **C07** | **Diversity enables novel closures.** | Complementary composition creates a closure self-composition cannot (`complementary_composition_creates_novel_closure`, `self_composition_type_one`, [`QLF_DiversityNovelOutcome`](lean/QLF_DiversityNovelOutcome.lean)); no history missing a colour axis carries junction baryon number, while a closed three-axis one does (`three_colour_emergence`, [`QLF_DiversityEmergence`](lean/QLF_DiversityEmergence.lean)). | Witnesses show possibility, not frequency or advantage. | Proved (witnesses). |
| **C08** | **Diversity increases collective capability.** | Registered D8c2 PASS, carried by one stratum and measure-limited ([`Diversity_Advantage_D8c2.md`](Diversity_Advantage_D8c2.md)). Library assembly PASS, coverage only ([`Library_Diversity_Assembly.md`](Library_Diversity_Assembly.md)). | Both tested rescues of D8c2 fail ([`Diversity_Revision_D8c2b.md`](Diversity_Revision_D8c2b.md)). The library advantage equals minus homogeneous synergy, and ordinary assembly gives the same Δ, so it is not closure-specific. | Conjecture; registered tests mixed. |
| **C09** | **Composability increases multiplicity.** | Unique prime factorization (P18) and exponential growth (P11). | The "factorial-class multiplicity" of composable structures ([`Philosophy.md`](Philosophy.md) §3a) is not proved. | Partial. |
| **C10** | **Self-similar structures dominate manifestation.** | Self-similar closure families exist and are counted; all sit at excursion 1, so every horizon hears them ([`self_similar_closures.py`](self_similar_closures.py)). | "Dominate" has no proved measure statement. | Exact computational (existence); dominance is a conjecture. |
| **C11** | **Interaction is first shared closure of independent histories.** | Shared closure is forced (P06); pair-built events read the same from either body, but whether an event was shared is not reconstructible from the bodies' words (`shared_event_not_from_bodies`, `pairing_not_reconstructible`, [`QLF_SharedEvent`](lean/QLF_SharedEvent.lean)); binding needs opposite orientation (`bind_iff_opposite`, [`QLF_Morphogenesis`](lean/QLF_Morphogenesis.lean)). | The *first* in the statement, and any dynamics of interaction, are not formalized. | Partial. |
| **C12** | **Every perspective is a finite information boundary.** | A04 and P17. | The identification of a perspective with a capacity is the A08 bridge. | Structural; `B-OPEN`. |
| **C13** | **Shared reality is the overlap of perspectives.** | `shared_iff_overlap`, `global_zfa_not_from_pair`, `relay_phase_transfer` ([`QLF_SharedReality`](lean/QLF_SharedReality.lean)); `joint_record_minimal`, `single_body_perspectives_share_only_constants` ([`QLF_PerspectiveHolography`](lean/QLF_PerspectiveHolography.lean)). | Accessibility from dynamics, shared-pair birth, and no-signalling for correlated histories ([`Holography_Audit.md`](Holography_Audit.md) §5). | Partial. |
| **C14** | **The boundary determines the accessible interior.** | Closure is a boundary property (`closure_iff_boundary_silent`, bookkeeping); every prefix closes (`every_prefix_closes`, so it constrains no path); the area law follows from locality (`cutEntropy_le_area`; `local_area_law`, [`QLF_LocalAreaLaw`](lean/QLF_LocalAreaLaw.lean)). Closure detects but cannot correct single errors (`single_error_not_correctable`). | The single-history projection is many-to-one ([`Holographic.md`](Holographic.md)). The perspective-consistent reconstruction theorem is open (issue [#296](https://github.com/rhovision-org/quantum-logical-framework/issues/296)). | Restricted formal results. |
| **C15** | **History carries memory that the instantaneous state loses.** | Two histories with the same events, hence the same inventory and net action, have different latencies (`census_cannot_determine_first_passage`, pending #329). So inventory and net action are not a sufficient state for latency. | The pruning system on full histories is deterministic; the memory lives in the *projection*. Readings for memory, consciousness or QuantumOS are conjecture. | Proved (pending #329) for the projection. |
| **C16** | **Intelligence is the capacity to synthesize new closures.** | None specific. | Operational definition is `B-OPEN` ([`Claim_Status.md`](Claim_Status.md), strange-loop section; [`QLF_as_Intelligence.md`](QLF_as_Intelligence.md)). | Conjecture. |
| **C17** | **Agency is the capacity to change the multiplicity of accessible closures.** | None; the reading is [`Philosophy.md`](Philosophy.md) §3c, with laser cooling as the worked example ([`Mpemba.md`](Mpemba.md)). | A model where an agent's structure provably changes `W`. | Conjecture. |
| **C18** | **Active inference is the selection of jointly closing relations.** | For games: Nash equilibrium is closure (`nash_iff_closure`); a game has a free-action functional iff it is a potential game (`free_action_iff_four_cycle`); paying everyone the total makes welfare the potential (`welfare_game_potential`) ([`QLF_PotentialGames`](lean/QLF_PotentialGames.lean), [`Game_Theory_QLF.md`](Game_Theory_QLF.md)). | Matching pennies has no free-action functional. Active inference beyond potential games is open. | Partial. |
| **C19** | **Emergence proceeds by cancellation, preservation and lifting.** | Ingredients: inserting a closed part acts as a phase (P05); the ledger is conserved (P08). | The triple is a reading ([`Philosophy.md`](Philosophy.md) §9), not a theorem. | Reading with partial anchors. |
| **C20** | **Order arises without an external organizer.** | Imbalance persists under local events (P08). A registered lattice test found that the conserved ledger segregates a patternless population into domains (grade N, [`Morphogenesis.md`](Morphogenesis.md)). | A pattern-forming scale (Turing) is open. | Conjecture. |
| **C21** | **Closure networks resist perturbation.** | None. | A resilience measure and a theorem about it. | Conjecture. |
| **C22** | **Conservative self-reference enables self-knowledge.** | Toy forms: `conservative_return` ([`QLF_ConservativeReturn`](lean/QLF_ConservativeReturn.lean)), `no_event_cycle`. | Self-knowledge as a bisimulation is `NOT_STARTED` ([`Strange_Loops.md`](Strange_Loops.md), [`Claim_Status.md`](Claim_Status.md)). | Conjecture. |

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
  [#329](https://github.com/rhovision-org/quantum-logical-framework/pull/329), which develops the
  first-passage work of #256 (closed into #259); the colour principle (P23) and the GL7 delay bound are
  in [#327](https://github.com/rhovision-org/quantum-logical-framework/pull/327). Both are open.
- **Historical memory.** It is supported by the pruning clock (#329), not by
  [`MostWays_First.md`](MostWays_First.md), which is about priority versus multiplicity.
- **Boost covariance.** The open interacting return is tracked in
  [`claim_records/relativity_boost.json`](claim_records/relativity_boost.json) and
  [`Relativity_Principle.md`](Relativity_Principle.md), not in issue #207 (the closure-amplitude
  programme).
- **Universality.** The anchor is real, but the encoding is ZFA by construction (P10).
- **Information preservation.** Restated (C06), since closure is many-to-one.
- **Added.** P22 (transience) and P23 (colour), which neither draft listed, and the foundation A03
  (only logic is assumed), which is binding in this repository.

Related: [`Claim_Status.md`](Claim_Status.md) · [`Theory_Of_Everything.md`](Theory_Of_Everything.md) ·
[`ScientificApproach.md`](ScientificApproach.md) · [`Open_Problems.md`](Open_Problems.md) ·
[`Manifestation.md`](Manifestation.md) · [`FlowChart.md`](FlowChart.md)
