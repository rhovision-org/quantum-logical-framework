# Theory of Everything: an index to QLF

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Status: draft index (2026-11-11).** This page is the map to read before writing a new QLF document. It
says where each part of the picture lives and how the parts connect. It proves nothing on its own; every
claim below points to the document or Lean module that carries it. The full visual map is the
[flow chart](FlowChart.md) ([clickable version](https://rhovision-org.github.io/quantum-logical-framework/FlowChart.html)).

**Merged formal backbone (12 November 2026).** PR #225 adds the metric-singlet /
lattice-Einstein representational result ([Einstein_Equations.md](Einstein_Equations.md) §6d–§6e);
PR #226 adds [Manifestation.md](Manifestation.md) (orientation, isolation-is-closure,
unbounded closures, `distance_eq_delay`, and the proton as the simplest isolated
imbalance). Both are formal `F` results in the reviewed **375-anchor** baseline.
Their physical readings remain `B-OPEN`; the map is still not evidence.

**The thesis** (Jim Whitescarver, 2026-11-11):

> The magic of possibilistic quantum logical manifestation is that it manifests unbounded in complexity,
> every possible world and our world, because there exist a priori solutions for orientation and
> isolation, and the promise of quantum computing.

Everything generable exists as possibility. ZFA closure selects what becomes an event. Two solutions
exist before any dynamics: **orientation**, from the top down, because every open history has a
completion fixed by its own imbalance; and **isolation**, from the bottom up, because a closed part is
invisible to everything else. From those two, complexity builds without bound, rung by rung, from the
first distinction to the proton, molecules, life and minds. We only ever see the closures of
interaction; the logical complexity inside them is far larger.

---

## 1. The foundation

| Topic | Read |
|---|---|
| Possibilist ontology; ZFA first, then every way | [Philosophy.md](Philosophy.md) §3a, [possibilist-ontology.md](possibilist-ontology.md) |
| Only logic is assumed; QLF's construction is one model | [Philosophy.md](Philosophy.md) §3d, [UniversalRelativity.md](UniversalRelativity.md) §4b |
| The method: status labels, kill conditions, counting ways | [ScientificApproach.md](ScientificApproach.md), [MostWays_First.md](MostWays_First.md) |
| The eight twists and why eight | [eight-twists-sufficiency.md](eight-twists-sufficiency.md), [HALF-SPIN-ZFA-EMBEDDING.md](HALF-SPIN-ZFA-EMBEDDING.md) |
| Closure is a walk back to the origin of `ℤ⁴`; most of possibility never closes | [Closure_Walk.md](Closure_Walk.md) |
| Every terminating computation is a ZFA string | [Universality.md](Universality.md) |
| No finite closure is final | [Law_Of_Exceptions.md](Law_Of_Exceptions.md) |
| Timing: listening takes time, closure does not; first shared closure; first-completion counts | [Event_Timing_QLF.md](Event_Timing_QLF.md), [Coincidence_QLF.md](Coincidence_QLF.md), [Closure_Uncertainty_QLF.md](Closure_Uncertainty_QLF.md) (draft programs with finite reference implementations) |
| How much construction a history needs: its assembly index | [Assembly_Index_QLF.md](Assembly_Index_QLF.md) (computed through length 10; Lean open) |
| Learning from one observation: the MrE update, specified and proved | [MrE_Update.md](MrE_Update.md), [MRE.md](MRE.md) |
| Mathematics from the substrate | [Mathematics_From_QLF.md](Mathematics_From_QLF.md), [Category_Theory_QLF.md](Category_Theory_QLF.md) |
| Two-phase / strange-loop bootstrapping; conservative return; primitive event, ρ/QKB and observer layers | [Mathematics_From_QLF.md](Mathematics_From_QLF.md) §2, [Philosophy.md](Philosophy.md) §3d, [Strange_Loops.md](Strange_Loops.md) §2A–§3B, [Quantum_Knowledge_Base.md](Quantum_Knowledge_Base.md) |

## 2. The two a priori solutions

| Solution | What is proved | Where |
|---|---|---|
| **Orientation (top down).** Every history completes to a closure using only itself | the dagger completes every history; a history joined to its mirror closes | [Reversibility.md](Reversibility.md), `QLF_ClosureUnitarity`, `QLF_Discoveries2026` (`mirror_closes`) |
| The shortest completion is the history's distance from closure | *distance equals delay* | [Manifestation.md](Manifestation.md) (`distance_eq_delay`), [`QLF_Manifestation`](lean/QLF_Manifestation.lean) |
| **Isolation (bottom up).** A part is isolated exactly when it is closed | *isolation is closure*; a closed part inserted anywhere costs only a global phase | [Manifestation.md](Manifestation.md) (`isolated_iff_closed`, `closed_insertion_is_phase`), [`QLF_Manifestation`](lean/QLF_Manifestation.lean); [`QLF_ClosureRenewal`](lean/QLF_ClosureRenewal.lean) |
| An open part cannot be hidden | forced sharing | [Discoveries_2026.md](Discoveries_2026.md) §3 |
| Isolation in practice: Markov blankets | blankets at every scale | [Emergent_Markov_Blankets.md](Emergent_Markov_Blankets.md), [Hadrons_Markov_Blankets.md](Hadrons_Markov_Blankets.md), [Primordial_Markov_Blankets.md](Primordial_Markov_Blankets.md) |
| Unbounded complexity | at least `8ⁿ` closures of length `2n`; a prime closure of every even length | [Manifestation.md](Manifestation.md) (`closures_unbounded`, `prime_closure_every_length`), [`QLF_Manifestation`](lean/QLF_Manifestation.lean) |

## 3. The hard problems possibility solves

| Problem | The possibilist answer | Read |
|---|---|---|
| Why this world (fine-tuning) | Every way happens; ours is what closes first and in the most ways | [Philosophy.md](Philosophy.md) §3a, [MostWays_First.md](MostWays_First.md) |
| Measurement | Closure is the event; no collapse postulate | [Measurement_Problem.md](Measurement_Problem.md), [Decoherence.md](Decoherence.md), [Born_Rule.md](Born_Rule.md), [Born_Readout_Criterion.md](Born_Readout_Criterion.md) |
| Isolation, the hard problem of quantum computing | A closed part is shielded up to a global phase | [Crystal_QuantumOS.md](Crystal_QuantumOS.md), [Error_Correction.md](Error_Correction.md), [QuantumOS.md](QuantumOS.md) |
| Orientation without a coordinator | The completion is fixed by the imbalance itself | §2 above, [Spin_QLF.md](Spin_QLF.md) |
| Infinities and singularities | No continuum in a finite region; vorticity is quantized | [TheContinuum.md](TheContinuum.md), [Navier_Stokes_Geometry.md](Navier_Stokes_Geometry.md) |
| Complexity from nothing | Closures and prime events are unbounded | §2 above, [Genesis.md](Genesis.md) |
| The arrow of time | Construction only adds; no time loops follow from logic | [Reversibility.md](Reversibility.md), [Time.md](Time.md) |
| Teleology in life | Selection is a filter on net action, not an aim | [Evolution.md](Evolution.md) |
| The stability of matter | The proton is the simplest isolated imbalance, and its ways are unbounded | §4 below |

## 4. The ladder: from the first distinction to everything that is

| Rung | Read | Flow chart |
|---|---|---|
| The first distinction and the logical bang | [Genesis.md](Genesis.md), `QLF_LogicalBang` | [Master map](FlowChart.md#master-map--the-substrate-and-its-twelve-domains) |
| Space and time synthesized, event by event | [SpaceTime.md](SpaceTime.md), [Spacetime_Constructor.md](Spacetime_Constructor.md), [spacetime-matter-emergence.md](spacetime-matter-emergence.md) | [1 Space and time](FlowChart.md#1-space-time-and-the-continuum) |
| The constants: the `6 spatial + 2 gauge` split of the eight twists fixes a family, with α the flagship | α⁻¹ ≈ 137: [Alpha.md](Alpha.md), [Alpha_Residual.md](Alpha_Residual.md); weak mixing `sin²θ_W = 3/8` and the Koide `2/3`: [Weak_Force.md](Weak_Force.md), [Lepton_Generations_Fourier.md](Lepton_Generations_Fourier.md) (the mass ratios are open, with a pre-registered attempt in [Lepton_Mass_Ratio_Protocol.md](Lepton_Mass_Ratio_Protocol.md) and its Stage B in [Lepton_Stage_B.md](Lepton_Stage_B.md)); `m_p/m_e = 6π⁵`: [Proton_Resonance_R_e.md](Proton_Resonance_R_e.md); `m_π/m_e ≈ 2/α`: [Pion_QLF.md](Pion_QLF.md); the coupling strengths: [Forces_From_Alpha.md](Forces_From_Alpha.md); the Planck scale and `c`, `ℏ`, `G`: [Planck_Scale.md](Planck_Scale.md), [Per_Qubit_Mass_Quantum.md](Per_Qubit_Mass_Quantum.md), [Gravity_From_Delay.md](Gravity_From_Delay.md); `Ω_Λ ≈ log 2`: [Cosmological_Constant.md](Cosmological_Constant.md); nuclear magic numbers: [Magic_numbers.md](Magic_numbers.md) | [2 Constants](FlowChart.md#2-the-fundamental-constants) |
| The electron: the simplest closure, a plane loop | [Spin_QLF.md](Spin_QLF.md) | [4 Atoms and QED](FlowChart.md#4-atoms-and-qed) |
| **The proton: the simplest isolated imbalance.** No closure shorter than six carries baryon number (the junction winding); the proton word closes at six with baryon number +1, and at least `2ⁿ` histories of length `6 + 2n` carry it | [Proton_Resonance_R_e.md](Proton_Resonance_R_e.md), [SEX.md](SEX.md), `QLF_BaryonWinding`, [Manifestation.md](Manifestation.md) (`proton_simplest_isolated_imbalance`, `proton_ways_unbounded`), [`QLF_Manifestation`](lean/QLF_Manifestation.lean) | [7 Particles](FlowChart.md#7-particles-and-the-standard-model) |
| Particles and the Standard Model | [Standard_Model.md](Standard_Model.md) | [7 Particles](FlowChart.md#7-particles-and-the-standard-model) |
| Three colours from three axes: necessity and existence | [Diversity_Quark_Emergence.md](Diversity_Quark_Emergence.md) | [7 Particles](FlowChart.md#7-particles-and-the-standard-model) |
| Atoms | [Atomic_Structure_QLF.md](Atomic_Structure_QLF.md) | [4 Atoms and QED](FlowChart.md#4-atoms-and-qed) |
| Molecules: a bond is a shared closure | [Chemistry.md](Chemistry.md) | [11 Chemistry](FlowChart.md#11-chemistry-molecules-and-folding) |
| Folding | [Protein_Folding.md](Protein_Folding.md) | [11 Chemistry](FlowChart.md#11-chemistry-molecules-and-folding) |
| Morphogenesis: closure erases the balanced part and the conserved residue differentiates | [Morphogenesis.md](Morphogenesis.md), [`QLF_Morphogenesis`](lean/QLF_Morphogenesis.lean) | [11 Chemistry](FlowChart.md#11-chemistry-molecules-and-folding) |
| Life: generate and select | [Evolution.md](Evolution.md), [Quantum_Biology.md](Quantum_Biology.md), [ZFA_DNA.md](ZFA_DNA.md) | [11 Chemistry](FlowChart.md#11-chemistry-molecules-and-folding) |
| Does diversity compose into advantage? (program #290: a cross-type witness passes; the advantage screens tested so far fail) | [Diversity_Composition_QLF.md](Diversity_Composition_QLF.md), [Diversity_Novel_Outcome_E1.md](Diversity_Novel_Outcome_E1.md), [Diversity_Interface_D3.md](Diversity_Interface_D3.md), [Diversity_Interface_Census_D3.md](Diversity_Interface_Census_D3.md), [Diversity_Continuation_D8c.md](Diversity_Continuation_D8c.md), [Diversity_Advantage_D8c2a.md](Diversity_Advantage_D8c2a.md), [Diversity_Revision_D8c2b.md](Diversity_Revision_D8c2b.md) | [11 Chemistry](FlowChart.md#11-chemistry-molecules-and-folding) |
| Minds and collectives | [Consciousness.md](Consciousness.md), [Conscious_Update_Rule.md](Conscious_Update_Rule.md), [QLF_as_Intelligence.md](QLF_as_Intelligence.md), [Game_Theory_QLF.md](Game_Theory_QLF.md) | [Master map](FlowChart.md#master-map--the-substrate-and-its-twelve-domains) |

## 5. Forces and the cosmos

| Reading | Read | Flow chart |
|---|---|---|
| Three gauge forces as one substrate interaction | [Forces_From_Three_Axes.md](Forces_From_Three_Axes.md), [Gluon_Abelian_Control.md](Gluon_Abelian_Control.md) (the non-Abelian vertex only lengthens singlet distance) | [3 Forces](FlowChart.md#3-forces) |
| The relativity principle: what the census proves and what it does not yet | [Relativity_Principle.md](Relativity_Principle.md) | [1 Space and time](FlowChart.md#1-space-time-and-the-continuum) |
| Locality: local statistics depend only on local information; closures are timelike; Bell's outcome independence fails, no-signalling holds | [Locality.md](Locality.md) | [1 Space and time](FlowChart.md#1-space-time-and-the-continuum) |
| Magnetism from orientation | [Magnetism_Spatial_Dynamics.md](Magnetism_Spatial_Dynamics.md), [Collective_Electrodynamics.md](Collective_Electrodynamics.md) (orientation proofs: [`QLF_MeadTransaction`](lean/QLF_MeadTransaction.lean), [`QLF_MagneticOrientation`](lean/QLF_MagneticOrientation.lean)) | [3 Forces](FlowChart.md#3-forces) |
| Gravity from balance; distance equals delay | [Gravity_From_Delay.md](Gravity_From_Delay.md), [Gravity.md](Gravity.md), [Quantum_Gravity.md](Quantum_Gravity.md) | [5 Gravity](FlowChart.md#5-gravity-and-gr) |
| Does binding contract space? Tested with both ledgers derived: the orientation ledger does not predict contraction | [Spatial_Response_Derived.md](Spatial_Response_Derived.md) | [5 Gravity](FlowChart.md#5-gravity-and-gr) |
| A toy continuum limit, fluxoids to Regge geometry: rejected as an identification | [Continuum_Limit.md](Continuum_Limit.md), [Stationary_Action.md](Stationary_Action.md) | [5 Gravity](FlowChart.md#5-gravity-and-gr) |
| **Metric = singlet; lattice divergence/Einstein equations** | [Einstein_Equations.md](Einstein_Equations.md) §6d–§6e, [Conformal_Comparison.md](Conformal_Comparison.md) (no local rescaling among letter substitutions; C1 in general open), `QLF_MetricSinglet`, `QLF_LatticeDivergence` — formal representational result under explicit premises; physical gravity bridge **open** | [5 Gravity](FlowChart.md#5-gravity-and-gr) |
| Cosmic age/redshift: external CCC+TL benchmark and open QLF clock bridge | [Gupta_CCC_TL.md](Gupta_CCC_TL.md), [Gupta_ClockConventions.md](Gupta_ClockConventions.md), [Gupta_ScaleFree.md](Gupta_ScaleFree.md), [AgeOfUniverse.md](AgeOfUniverse.md) — B-OPEN; substrate tick count N remains open | [6 Cosmology](FlowChart.md#6-cosmology-and-the-dark-sector) |
| Cosmic expansion by delay; dark energy and dark matter | [Cosmological_Constant.md](Cosmological_Constant.md), [DarkMatter.md](DarkMatter.md) | [6 Cosmology](FlowChart.md#6-cosmology-and-the-dark-sector) |
| Holography, stated precisely | [Holography_Audit.md](Holography_Audit.md), [Perspective_Holography_StageC.md](Perspective_Holography_StageC.md) | [8 Quantum gravity](FlowChart.md#8-quantum-gravity--toe-pillars) |

## 6. Boundaries: what is open

| Topic | Read | Flow chart |
|---|---|---|
| Time-reversed clock domains and observational boundary | [Time_Reversed_Clock_Domains.md](Time_Reversed_Clock_Domains.md) — proposed paired-history/antimatter correspondence; B-OPEN | [6 Cosmology](FlowChart.md#6-cosmology-and-the-dark-sector) |
| The gap registry | [Open_Problems.md](Open_Problems.md) | [Master map](FlowChart.md#master-map--the-substrate-and-its-twelve-domains) |
| Closing bridges: which can close now, and with which tools | [Bridge_Tools.md](Bridge_Tools.md) | [Master map](FlowChart.md#master-map--the-substrate-and-its-twelve-domains) |
| Strange-loop / conservative-return bridge discipline; ρ/QKB and active-inference/bisimulation targets; map ≡ territory | [Strange_Loops.md](Strange_Loops.md), [Map_Is_Territory.md](Map_Is_Territory.md), [rho_correspondence_target.md](verification/strange-loop/rho_correspondence_target.md), [self_knowledge_target.md](verification/strange-loop/self_knowledge_target.md), [Claim_Status.md](Claim_Status.md) | [Methods and evidence](FlowChart.md#methods-and-evidence-paper-i-v03) |
| The six Millennium reformulations, each one bridge axiom | [Millennium.md](Millennium.md) | [9 Millennium](FlowChart.md#9-the-millennium-prize-program) |
| Possibility growth: exact blind search costs every candidate; P vs NP and VP vs VNP; in what sense possibilities are real | [Possibility_Growth.md](Possibility_Growth.md) | [9 Millennium](FlowChart.md#9-the-millennium-prize-program) |
| Beyond the Standard Model | [Beyond_Standard_Model.md](Beyond_Standard_Model.md) | [10 Beyond the SM](FlowChart.md#10-beyond-the-sm) |
| QFT and renormalization | [Perturbation_Theory_QLF.md](Perturbation_Theory_QLF.md) | [12 QFT](FlowChart.md#12-quantum-field-theory-and-renormalization) |
| Quantum computation: one-qubit gates and CNOT generate every unitary (proved, Lean); the substrate performing them on superposed presence (open) | [Barenco_Universality.md](Barenco_Universality.md) | [Master map](FlowChart.md#master-map--the-substrate-and-its-twelve-domains) |

---

**For other threads writing documents:** place each new document on this index (a rung, a hard problem,
a force, or a boundary), link it from the matching row, and say which a priori solution it rests on. If
it fits no row, the index needs a new row, and that is worth saying in the document itself.

See also: [README.md](README.md), [Introducing_QLF.md](Introducing_QLF.md), [FlowChart.md](FlowChart.md).
