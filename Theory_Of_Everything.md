# Theory of Everything: an index to QLF

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Status: draft index (2026-11-11).** This page is the map to read before writing a new QLF document. It
says where each part of the picture lives and how the parts connect. It proves nothing on its own; every
claim below points to the document or Lean module that carries it. The full visual map is the
[flow chart](FlowChart.md) ([clickable version](https://rhovision-org.github.io/quantum-logical-framework/FlowChart.html)).

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

| Topic | Read | Flow chart |
|---|---|---|
| Possibilist ontology; ZFA first, then every way | [Philosophy.md](Philosophy.md) §3a, [possibilist-ontology.md](possibilist-ontology.md) | [Master map](FlowChart.md#master-map--the-substrate-and-its-twelve-domains) |
| Only logic is assumed; QLF's construction is one model | [Philosophy.md](Philosophy.md) §3d, [UniversalRelativity.md](UniversalRelativity.md) §4b | Master map |
| The method: status labels, kill conditions, counting ways | [ScientificApproach.md](ScientificApproach.md), [MostWays_First.md](MostWays_First.md) | Master map |
| The eight twists and why eight | [eight-twists-sufficiency.md](eight-twists-sufficiency.md), [HALF-SPIN-ZFA-EMBEDDING.md](HALF-SPIN-ZFA-EMBEDDING.md) | [1](FlowChart.md#1-space-time-and-the-continuum) |
| Closure is a walk back to the origin of `ℤ⁴`; most of possibility never closes | [Closure_Walk.md](Closure_Walk.md) | 1 |
| Every terminating computation is a ZFA string | [Universality.md](Universality.md) | Master map |
| No finite closure is final | [Law_Of_Exceptions.md](Law_Of_Exceptions.md) | Master map |
| Mathematics from the substrate | [Mathematics_From_QLF.md](Mathematics_From_QLF.md), [Category_Theory_QLF.md](Category_Theory_QLF.md) | Master map |

## 2. The two a priori solutions

| Solution | What is proved | Where |
|---|---|---|
| **Orientation (top down).** Every history completes to a closure using only itself | the dagger completes every history; a history joined to its mirror closes | [Reversibility.md](Reversibility.md), `QLF_ClosureUnitarity`, `QLF_Discoveries2026` (`mirror_closes`) |
| The shortest completion is the history's distance from closure | *distance equals delay* | `QLF_Manifestation` (`distance_eq_delay`), PR #226 |
| **Isolation (bottom up).** A part is isolated exactly when it is closed | *isolation is closure*; a closed part inserted anywhere costs only a global phase | `QLF_Manifestation` (`isolated_iff_closed`, `closed_insertion_is_phase`), PR #226; `QLF_ClosureRenewal` |
| An open part cannot be hidden | forced sharing | [Discoveries_2026.md](Discoveries_2026.md) §3 |
| Isolation in practice: Markov blankets | blankets at every scale | [Emergent_Markov_Blankets.md](Emergent_Markov_Blankets.md), [Hadrons_Markov_Blankets.md](Hadrons_Markov_Blankets.md), [Primordial_Markov_Blankets.md](Primordial_Markov_Blankets.md) |
| Unbounded complexity | at least `8ⁿ` closures of length `2n`; a prime closure of every even length | `QLF_Manifestation` (`closures_unbounded`, `prime_closure_every_length`), PR #226 |

## 3. The hard problems possibility solves

| Problem | The possibilist answer | Read |
|---|---|---|
| Why this world (fine-tuning) | Every way happens; ours is what closes first and in the most ways | [Philosophy.md](Philosophy.md) §3a, [MostWays_First.md](MostWays_First.md) |
| Measurement | Closure is the event; no collapse postulate | [Measurement_Problem.md](Measurement_Problem.md), [Decoherence.md](Decoherence.md), [Born_Rule.md](Born_Rule.md) |
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
| The first distinction and the logical bang | [Genesis.md](Genesis.md), `QLF_LogicalBang` | Master map |
| Space and time synthesized, event by event | [SpaceTime.md](SpaceTime.md), [Spacetime_Constructor.md](Spacetime_Constructor.md), [spacetime-matter-emergence.md](spacetime-matter-emergence.md) | [1](FlowChart.md#1-space-time-and-the-continuum) |
| The constants | [Alpha.md](Alpha.md), [Alpha_Residual.md](Alpha_Residual.md) | [2](FlowChart.md#2-the-fundamental-constants) |
| The electron: the simplest closure, a plane loop | [Spin_QLF.md](Spin_QLF.md) | [4](FlowChart.md#4-atoms-and-qed) |
| **The proton: the simplest isolated imbalance.** No closure shorter than six carries baryon winding; the proton word closes at six with winding +1, in unboundedly many ways | [Proton_Resonance_R_e.md](Proton_Resonance_R_e.md), [SEX.md](SEX.md), `QLF_BaryonWinding`, `QLF_Manifestation` (`proton_simplest_isolated_imbalance`, `proton_ways_unbounded`), PR #226 | [7](FlowChart.md#7-particles-and-the-standard-model) |
| Particles and the Standard Model | [Standard_Model.md](Standard_Model.md) | 7 |
| Atoms | [Atomic_Structure_QLF.md](Atomic_Structure_QLF.md) | 4 |
| Molecules: a bond is a shared closure | [Chemistry.md](Chemistry.md) | [11](FlowChart.md#11-chemistry-molecules-and-folding) |
| Folding | [Protein_Folding.md](Protein_Folding.md) | 11 |
| Life: generate and select | [Evolution.md](Evolution.md), [Quantum_Biology.md](Quantum_Biology.md), [ZFA_DNA.md](ZFA_DNA.md) | 11 |
| Minds and collectives | [Consciousness.md](Consciousness.md), [QLF_as_Intelligence.md](QLF_as_Intelligence.md), [Game_Theory_QLF.md](Game_Theory_QLF.md) | Master map |

## 5. Forces and the cosmos

| Reading | Read | Flow chart |
|---|---|---|
| Three gauge forces as one substrate interaction | [Forces_From_Three_Axes.md](Forces_From_Three_Axes.md) | [3](FlowChart.md#3-forces) |
| Magnetism from orientation | [Magnetism_Spatial_Dynamics.md](Magnetism_Spatial_Dynamics.md), [Collective_Electrodynamics.md](Collective_Electrodynamics.md) (orientation proofs in PR #223) | 3 |
| Gravity from balance; distance equals delay | [Gravity_From_Delay.md](Gravity_From_Delay.md), [Gravity.md](Gravity.md), [Quantum_Gravity.md](Quantum_Gravity.md) | [5](FlowChart.md#5-gravity-and-gr) |
| Cosmic expansion by delay; dark energy and dark matter | [Cosmological_Constant.md](Cosmological_Constant.md), [DarkMatter.md](DarkMatter.md) | [6](FlowChart.md#6-cosmology-and-the-dark-sector) |
| Holography, stated precisely | [Holography_Audit.md](Holography_Audit.md) | [8](FlowChart.md#8-quantum-gravity--toe-pillars) |

## 6. Boundaries: what is open

| Topic | Read | Flow chart |
|---|---|---|
| The gap registry | [Open_Problems.md](Open_Problems.md) | — |
| The six Millennium reformulations, each one bridge axiom | [Millennium.md](Millennium.md) | [9](FlowChart.md#9-the-millennium-prize-program) |
| Beyond the Standard Model | [Beyond_Standard_Model.md](Beyond_Standard_Model.md) | [10](FlowChart.md#10-beyond-the-sm) |
| QFT and renormalization | [Perturbation_Theory_QLF.md](Perturbation_Theory_QLF.md) | [12](FlowChart.md#12-quantum-field-theory-and-renormalization) |

---

**For other threads writing documents:** place each new document on this index (a rung, a hard problem,
a force, or a boundary), link it from the matching row, and say which a priori solution it rests on. If
it fits no row, the index needs a new row, and that is worth saying in the document itself.

See also: [README.md](README.md), [Introducing_QLF.md](Introducing_QLF.md), [FlowChart.md](FlowChart.md).
