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
| Dark matter / RAR | [QLF_DarkMatter](lean/QLF_DarkMatter.lean), [QLF_MondScale](lean/QLF_MondScale.lean), [QLF_RarBalance](lean/QLF_RarBalance.lean): algebraic RAR and `a0 = c H0/(2 pi)`; retrospective blind SPARC analysis | Independent replication of the SPARC result; demonstrate the interpolation form is not selected post hoc; formalize the `a0`/H0/M-L inputs | [claim_records/sparc_rar.json](claim_records/sparc_rar.json); third-party timestamp; held-out or Bayesian model comparison |
| Mercury perihelion | [QLF_MercuryPerihelion](lean/QLF_MercuryPerihelion.lean): perihelion form and per-century value | Show the holographic count → GR potential map is unique; compare at higher post-Newtonian order | [Claim_Status.md](Claim_Status.md); independent ephemeris comparison |
| α cannot drift | [QLF_Discoveries2026](lean/QLF_Discoveries2026.lean): `alpha_cannot_drift` | Freeze the nuclear-clock comparator and the rejection criterion before unblinding | [claim_records/kill_conditions.json](claim_records/kill_conditions.json) |
| Born rule | [QLF_BornFromWays](lean/QLF_BornFromWays.lean): `born_from_ways`, `assignment_unique` | Prove the cylinder-measure → physical-probability step; define the apparatus/outcome map | [Claim_Status.md](Claim_Status.md); interference comparison |
| Strong CP / no axion | [QLF_StrongCP](lean/QLF_StrongCP.lean): `theta_zero_on_closure` | Identify the physical θ-term with the QLF CP-odd winding; state the axion-detection kill condition | [claim_records/kill_conditions.json](claim_records/kill_conditions.json) |
| CPT / antiparticle time mirror | [QLF_Discoveries2026](lean/QLF_Discoveries2026.lean): `antiparticle_length`, `charge3W_antiparticle`; [QLF_Majorana](lean/QLF_Majorana.lean): `neutrino_majorana` | Bridge length equality to mass equality; compare with BASE proton/antiproton data | [claim_records/kill_conditions.json](claim_records/kill_conditions.json) |

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
4. Record at least one counterexample or failure condition and a baseline
   from conventional physics.
5. Reject promotion from conditional to derived unless the bridge itself
   has been proved and reviewed.

The current research programme is tracked in
[Open_Problems.md](Open_Problems.md) and issue
[#11](https://github.com/rhovision-org/quantum-logical-framework/issues/11).
