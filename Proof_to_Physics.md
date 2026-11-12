# Proof-to-physics evidence registry

This is a review ledger, not a declaration that the open physical bridges
have been solved. A formal proof is recorded separately from an
identification with a physical observable and from an experimental test.

| Area | Formal result or interface | What remains to establish | Acceptance evidence |
|---|---|---|---|
| Event probabilities | [QLF_KraftMeasure](lean/QLF_KraftMeasure.lean): prefix-free closure weights and Kraft bound | Identify cylinder measure with operational event probabilities, without selecting weights to fit the target result | A defined apparatus/outcome map, a normalized probability law, interference tests, cutoff control |
| Closure scattering | [QLF_ClosureKernel](lean/QLF_ClosureKernel.lean), [QLF_ClosureChannels](lean/QLF_ClosureChannels.lean): finite formal renewal and channel factorization | A physically interpreted channel-to-channel operator, nontrivial boundary transitions, optical identity and pole residues | Explicit channel basis, `S†S = I` or quantified leakage, and an independently checked benchmark ([#207](https://github.com/rhovision-org/quantum-logical-framework/issues/207)) |
| Fine-structure constant | [QLF_AlphaBound](lean/QLF_AlphaBound.lean): combinatorial bounds and defined counting models | Justify the bridge from count parameters to renormalized, experimentally measured electromagnetic coupling | Predeclared coupling/scale map and independent high-precision comparison |
| Yang–Mills mass gap | [QLF_MassGap](lean/QLF_MassGap.lean): positive substrate gap; explicit `yang_mills_gap` boundary | Reconstruction of continuum Yang–Mills and proof that its spectrum has the claimed gap | Continuum-QFT definitions and a proof not relying on the intended conclusion |
| Hodge | [QLF_Hodge](lean/QLF_Hodge.lean): closure encoding; explicit `hodge_algebraicity` bridge | Relate encoded classes faithfully to algebraic cycles of actual varieties | A concrete cycle/cohomology construction and proof of the geometric realization |
| P versus NP | [QLF_PvsNP](lean/QLF_PvsNP.lean): finite counting and an abstract `CostModel` | Link `PTime` and `search` to a standard uniform machine model | A stated complexity model and a separation proof without assuming the separation |
| Riemann hypothesis | [QLF_Riemann](lean/QLF_Riemann.lean), [QLF_RiemannMRE](lean/QLF_RiemannMRE.lean): formal implications from spectral or factorization axioms | Discharge the named conjecture-strength assumptions | An unconditional kernel-checked theorem about Mathlib's analytic zeta function |
| Causal continuum | [QLF_CausalContinuum](lean/QLF_CausalContinuum.lean), [QLF_OrderMetric](lean/QLF_OrderMetric.lean): discrete constructions and explicit continuum limit axioms | Establish convergence to Lorentzian geometric objects | Precise assumptions, convergence topology and quantitative error estimates |
| Gravity / metric | [QLF_MetricSinglet](lean/QLF_MetricSinglet.lean), [QLF_LatticeDivergence](lean/QLF_LatticeDivergence.lean): metric = singlet; null-cone step as singlet uniqueness; lattice divergence/Einstein equations with discrete Bianchi and conservation as hypotheses | Local Rindler/Raychaudhuri derivation; substrate curvature; physical identification of the lattice metric and `Λ`; an apparatus/observable map | Exact anchors in the 319-entry baseline; explicit premises; independent GR-limit check |
| Manifestation / selection | [QLF_Manifestation](lean/QLF_Manifestation.lean): orientation, isolation-is-closure, unbounded closures, `distance_eq_delay`, proton as the simplest isolated imbalance | Physical selection mechanism; apparatus/detector map; identification of the closure “proton” with the QCD proton; empirical test | [Manifestation.md](Manifestation.md); claim map only; no `E` |
| Dark matter / RAR | [QLF_DarkMatter](lean/QLF_DarkMatter.lean), [QLF_MondScale](lean/QLF_MondScale.lean), [QLF_RarBalance](lean/QLF_RarBalance.lean): algebraic RAR and `a0 = c H0/(2 pi)`; retrospective SPARC public-data benchmark | Independent replication of the SPARC result; demonstrate the interpolation form is not selected post hoc; formalize the `a0`/H0/M-L inputs | [claim_records/sparc_rar.json](claim_records/sparc_rar.json); third-party timestamp; held-out or Bayesian model comparison |
| Mercury perihelion | [QLF_MercuryPerihelion](lean/QLF_MercuryPerihelion.lean): perihelion form and per-century value | Show the holographic count → GR potential map is unique; compare at higher post-Newtonian order | [Claim_Status.md](Claim_Status.md); independent ephemeris comparison |
| α cannot drift | [QLF_Discoveries2026](lean/QLF_Discoveries2026.lean): `alpha_cannot_drift` | Specify the measured-coupling bridge and residual corrections; freeze the nuclear-clock observable, comparator and rejection rule before controlled target exposure | [claim_records/kill_conditions.json](claim_records/kill_conditions.json) |
| Born rule | [QLF_BornFromWays](lean/QLF_BornFromWays.lean): `born_from_ways`, `assignment_unique` | Prove the cylinder-measure → physical-probability step; define the apparatus/outcome map | [Claim_Status.md](Claim_Status.md); interference comparison |
| Strong CP / no axion | [QLF_StrongCP](lean/QLF_StrongCP.lean): `theta_zero_on_closure` | Identify the physical θ-term with the QLF CP-odd winding; distinguish an unnecessary axion from a separately posited absence hypothesis | [claim_records/kill_conditions.json](claim_records/kill_conditions.json) |
| CPT / antiparticle time mirror | [QLF_Discoveries2026](lean/QLF_Discoveries2026.lean): `antiparticle_length`, `charge3W_antiparticle`; [QLF_Majorana](lean/QLF_Majorana.lean): `neutrino_majorana` | Bridge length equality to mass equality; compare with BASE proton/antiproton data | [claim_records/kill_conditions.json](claim_records/kill_conditions.json) |

## Strange-loop / conservative-return criterion

A bridge can be read as a two-phase loop: a formal level, a physical level, and a return to a finite record. The loop is admissible only if the return is **conservative** — the finitary content claimed at the physical level is already available in the `RCA₀` core, or the bridge is marked `B-OPEN`. The full conceptual note is [`Strange_Loops.md`](Strange_Loops.md); the G3 checklist remains authoritative.

For each bridge, record:

1. the formal level and the physical level;
2. the map and its preservation obligations;
3. the finite record to which the loop returns;
4. why the return is conservative rather than target-derived;
5. a defeater that would break the loop.

A bridge with no such return is not a closed loop, however suggestive the numerical agreement. The four Paper I bridge records (`three_polarizer.json`, `alpha.json`, `sparc_rar.json`, `born_rule.json`) carry a `strange_loop` object plus a `proof_obligation` with domain, codomain, forward/return maps, composite identity, conservative-return status, imported axioms and falsifier. All four loops are `B-OPEN`; MO2 is `PARTIAL` with `QLF_ConservativeReturn` (and the generic `QLF_StrangeLoop` interface); Born is `PARTIAL` with `QLF_StrangeLoopBorn`; α and SPARC remain `NOT_STARTED`. A `TESTED` loop requires a `PROVED` return plus a real artifact; a `bridge: CLOSED` record requires a `TESTED` loop. The trigger predicate is `QLF.ConservativeReturn.StrangeLoopTrigger`; `toyTrigger_exists` checks only the toy instance, and `no_event_cycle` checks the toy no-time-loop analogue, not an operational map.

**Incomplete vs inconclusive.** `INCOMPLETE` describes a bridge whose first-order `F`/`N` result and comparator stand, but whose operational map or conservative return has not been constructed. `INCONCLUSIVE` is reserved for a comparator that exists but is ambiguous or fails to discriminate. Thus the four bridge records read “first-order `F+N` / `N` / `F` established; return incomplete,” not “nothing established.” The G3 gate is `INCOMPLETE`, not `INCONCLUSIVE`; the `B-OPEN` label is unchanged.

## Evidence categories

- **Kernel-proved:** the exact theorem and its axiom dependencies are recorded.
- **Conditional:** the result depends on an explicit mathematical or physical
  bridge assumption; that assumption is named.
- **Numerically checked:** input, seed, algorithm, precision and expected
  error are archived; this does not become a theorem.
- **Experimentally tested:** a measurable observable, independent dataset,
  calibration budget and predeclared failure condition are supplied.

## Review protocol

1. Identify the exact Lean declaration and print its axiom footprint.
2. List every definition or premise that contains the desired conclusion.
3. Identify the missing map from substrate quantities to the lab observable.
4. State the two-phase / strange-loop structure: the finite record to which it
   returns and why that return is conservative. If no return is exhibited, mark
   the bridge `B-OPEN` / `INCOMPLETE`; reserve `INCONCLUSIVE` for an ambiguous
   comparator.
5. Record at least one counterexample or failure condition and a baseline
   from conventional physics.
6. Reject promotion from conditional to derived unless the bridge itself
   has been proved and reviewed.

The current research programme is tracked in
[Open_Problems.md](Open_Problems.md) and issue
[#11](https://github.com/rhovision-org/quantum-logical-framework/issues/11).
