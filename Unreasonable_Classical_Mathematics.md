# The Uncanny Unreasonableness of Classical Mathematics

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

Wigner (1960) called the effectiveness of mathematics in physics *unreasonable*, a miracle with no
rational explanation. [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §4 gives QLF's answer: the
mathematics that works is the mathematics that can be realized, because both are readings of one
closure process. This page is the other side of that answer. If effectiveness follows realizability,
then wherever classical mathematics asserts something no finite process can realize, it should stop
working, and in an odd, recognizable way. It produces paradoxes, objects that cannot be exhibited, and
answers that are wrong when applied to the world. That is the *uncanny unreasonableness*: the same
mathematics that is uncannily right inside the realizable is uncannily wrong just outside it, and the
boundary is the same in every case.

So QLF has to account for two things, and one account covers both. The account starts from ZFA, equal
and opposite logical action, which QLF takes as the sufficient basis of physics (§2). Mathematics is reasonable where it
describes finite closures and their large-count limits. It becomes unreasonable where it asserts
objects that no finite closure realizes. §1 sets this against Wigner's original paper point by point.
The rest of the page collects the failures, with a link for each to the document and Lean module where
it is worked out. The page adds no new theorem. What it adds is the observation that the scattered
results share one cause.

---

## 1. Wigner's paper, read both ways

Wigner's essay, *The Unreasonable Effectiveness of Mathematics in the Natural Sciences* (1960), makes
two claims. Mathematical concepts turn up in physics in places nobody expected, and the theories built
from them are more accurate than the data that suggested them. He offers no explanation for either and
ends: *"The miracle of the appropriateness of the language of mathematics for the formulation of the
laws of physics is a wonderful gift which we neither understand nor deserve."*

QLF disagrees with the conclusion, not with the observations. The table takes Wigner's main points in
order and gives QLF's account of why mathematics works there (the reasonableness) and where the same
reasoning says it must fail (the unreasonableness).

| Wigner's point | Why it works (reasonable) | Where it fails (unreasonable) |
|---|---|---|
| **π in the Gaussian.** His opening story: a statistician shows a friend a population curve containing `π`, and the friend suspects a joke, since population has nothing to do with circles. | Both are counts of the same thing. The Gaussian is the large-`n` limit of binomial counts, and `C(2n,n) ~ 4ⁿ/√(πn)` puts `π` into the count of ways a walk returns to its start. The circle's `π` and the statistician's `π` are one closure census read two ways ([`Physical_Pi.md`](Physical_Pi.md), [`closure_census`](lean/QLF_PhysicalPi.lean)). | `π` as a completed infinite decimal stored somewhere. What exists is the rational sequence of counts (§5c). |
| **Mathematics is invented for its own beauty**, as "the science of skillful operations with concepts and rules invented just for this purpose", so its fit to nature is a coincidence. | The concepts are not free inventions. Numbers, `+`, `×`, the unit group and su(2) arise from counting and composing closures ([`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §1). The mathematician explores the space of possible closures, which feels like invention, and finds the ones that close, which feels like discovery. | Concepts that no closure supports — the completed continuum, unrestricted Choice, ungrounded self-reference — are free inventions in exactly Wigner's sense. They are the ones that produce paradoxes (§4–§6). |
| **Complex numbers.** Nothing in experience suggests them, yet quantum mechanics is written in them. | `i` is in the substrate from the first step. Folding any twist history gives a Pauli scalar in `{±I, ±iI}`, the group `μ₄`, derived from the fold rather than assumed ([`QLF_Pauli`](lean/QLF_Pauli.lean); [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) rung 5). The `±i` belong to open histories: a completed, count-balanced closure always folds to `±I`, never `±iI` ([`balanced_phase_is_real`](lean/QLF_BalancedPhaseReal.lean), via [`count_balanced_pauli_closed`](lean/QLF_TwistAlphabet.lean)). So complex phases are suggested by experience at its finest grain, as the algebra of histories in progress. | The complex continuum `ℂ` as a set of points is the metric completion of `ℚ(i)`. It is a rendering, and it is right in the large-count limit (§7). |
| **Accuracy beyond the evidence.** Newton's law, fitted to rough data, holds to far better precision; matrix mechanics, built for hydrogen, works for helium. | A law that describes how closures count keeps working as more closures are counted. The accuracy is that of counting, which gives exact answers ([`Mercury_Perihelion.md`](Mercury_Perihelion.md); the census results in [`Closure_Walk.md`](Closure_Walk.md)). | Where a continuum theory is pushed past any cutoff, precision turns into infinity: the ultraviolet and vacuum catastrophes, singularities (§5d). Wigner's examples are all successes. The failures were known in 1960 and do not appear in the essay. |
| **The miracle of the existence of laws** at all, and of the mind's capacity to find them. | A world selected by one closure condition has regularities because it has one condition. The mind finding them is itself a set of closures in the same substrate, so the model and the thing modelled share a basis ([`Active_Inference_Mathematics.md`](Active_Inference_Mathematics.md)). Only logic is assumed for this, not that nature is QLF's construction (§2). | No finite-capacity closure is exceptionless: each has a genuine exception one level up ([`law_of_exceptions`](lean/QLF_LawOfExceptions.lean)). Taking a physical law to be such a closure is a modelling assumption; on it, laws hold as counts, not as decrees. |
| **His worry about false theories that work** (he names theories that agree with the data for a while and are later abandoned) and about two theories that cannot be reconciled. | A theory can be effective without being true when it renders the right counts in its domain. Effectiveness tracks realizability rather than truth of every axiom. | Relativity and quantum theory collide at points where both use the continuum: singularities and the vacuum energy. QLF locates the conflict at the continuum, not in either theory's realizable content (§5d). |

**The contrast in one sentence.** Wigner treats mathematics as one thing whose fit to nature is either
everywhere a miracle or nowhere explained. QLF splits it along one line, realizability. On one side the
fit is reasonable, because mathematics and physics are two readings of the same closures. On the other
side the fit fails, in ways that can be predicted and checked. Wigner's "neither understand nor deserve"
becomes "understand, within limits that can be stated".

---

## 2. The claim, stated once and precisely

**Contrast, once.** Nothing here says classical mathematics is *inconsistent*. ZFC does not prove
`0 = 1`, and `ℝ` is a consistent structure. Saying otherwise would be a category error. The claim is
**consistency ≠ realizability**: a consistent theory can describe objects that no finite-information
world can contain, and when such a theory is applied to the world it can certify results that are
false there ([`TheContinuum.md`](TheContinuum.md) "Consistency is not realizability";
[`Banach_Tarski_QLF.md`](Banach_Tarski_QLF.md) §2).

**What is assumed.** QLF assumes that nature is *logical*, and nothing about nature being QLF's
construction ([`Philosophy.md`](Philosophy.md) §3d). The construction is one model of that assumption.
One further premise enters this page, and it is named rather than hidden: **a bounded region holds
finitely many distinguishable states.** That is Bekenstein's bound. QLF did not invent it, and it is the
`[Finite R]` hypothesis of
[`no_continuum_in_finite_region`](lean/QLF_Realizability.lean). The physical-realizability argument of
§5 is that premise plus logic. §6 does not depend on it: its critique of Choice is set-theoretic and
constructive.

**ZFA is the sufficient basis.** QLF's thesis is that one principle is enough to build physics on:
**ZFA, equal and opposite logical action**. Every distinction is paired with its opposite, and the pair
closes with zero free energy. Nothing else is posited. Numbers, the unit group `{±1, ±i}`, spin, the
non-distributive logic of measurement and the census constants are derived from that one closure
condition. Least action is approached the same way. The realized history is the one realized in the
most ways, and because every twist has a conjugate of equal weight, the discrete multiplicity is
stationary, and maximal, at balance. That is proved
([`QLF_StationaryAction`](lean/QLF_StationaryAction.lean), and
[`QLF_StationaryPhase`](lean/QLF_StationaryPhase.lean) for the signed phase on all four axes, no
axioms). Reading that multiplicity as Hamilton's action, `S ↔ −ħ log W`, is an identification, not yet
derived, so the step from ZFA to `δS = 0` is an open bridge
([`Stationary_Action.md`](Stationary_Action.md)) ([`Philosophy.md`](Philosophy.md) §3a, [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md)
§1, [`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md)). Where a derivation still needs
something more, the gap is named as an explicit bridge, not added as a second principle (the axiom
inventory in [`Open_Problems.md`](Open_Problems.md)). This is what turns the rest of the page into
predictions. If equal and opposite logical action is sufficient, classical mathematics can only be
reasonable where it describes such closures and their large-count limits. Its completed infinities and
unconstructed choices are additions the basis does not need, and they are where the paradoxes and
wrong answers turn up.

**Natural laws derived from ZFA.** The table lists the laws QLF obtains from equal and opposite
logical action, with the honest status of each. It is a summary: the status ledger of record is
[`Mysteries_Of_Physics.md`](Mysteries_Of_Physics.md) with [`Open_Problems.md`](Open_Problems.md), and
where they differ, they win. "Proved" means a Lean theorem with no QLF axiom.
"Derived" means a derivation whose steps are named in the linked document, with the step that is not
yet Lean-checked or that is cited from standard physics stated there. "Leading value" means the number
is reached but a residual remains open.

| Law | What QLF shows | Status | Where |
|---|---|---|---|
| **Newton's third law** (action = reaction) | ZFA *is* equal and opposite action at every elementary event; *actio = reactio* is how it looks when the pairings blur together | The principle itself | [`Philosophy.md`](Philosophy.md), [`Introducing_QLF.md`](Introducing_QLF.md) |
| **Least action** (`δS = 0`) | The most-ways history sits at balance, where the first variation of multiplicity vanishes | **Proved:** discrete multiplicity is stationary at balance. **Open bridge:** multiplicity → physical action functional | [`QLF_StationaryAction`](lean/QLF_StationaryAction.lean), [`QLF_StationaryPhase`](lean/QLF_StationaryPhase.lean), [`Stationary_Action.md`](Stationary_Action.md) |
| **Newton's gravitation** (`F = GMm/r²`) | Holographic event count `4πR²` × `log 2` per event gives the area law; the entropy gradient gives the force; only 3-D space gives `1/r²` | **Derived**; area law and the `1/r²` exponent proved, the Bekenstein-gradient step structural | [`QLF_GravityFromDelay`](lean/QLF_GravityFromDelay.lean) (`holographic_entropy_eq`, `newton_exponent_only_3d_matches`), [`Gravity_From_Delay.md`](Gravity_From_Delay.md) |
| **Newton's second law** (`F = ma`) | A rest mass is a closed light-speed circulation; acceleration shifts it, and the force is exactly proportional to the shift | **Proved** for the two-leg light clock (Route A); the counting version is open | [`QLF_Inertia`](lean/QLF_Inertia.lean), [`Inertia.md`](Inertia.md) |
| **Special relativity** | The state is a 2×2 Hermitian matrix whose determinant is the Minkowski interval; `SL(2,ℂ)` acts as the Lorentz group | **Proved**; surjectivity onto `SO⁺(1,3)` rests on one named bridge | [`QLF_Minkowski`](lean/QLF_Minkowski.lean) (`det_toMatrix_eq_interval`), [`QLF_LorentzCover`](lean/QLF_LorentzCover.lean) |
| **`E = mc²`** | Mass is closure depth; `c` is one event length per event time | **Derived** | [`E_mc2_derivation.md`](E_mc2_derivation.md) |
| **Einstein's field equations** | Jacobson's route: the equations are the equation of state of horizon thermodynamics, and QLF supplies both inputs (area law, Unruh temperature) from the substrate | **Derived** via a cited route | [`QLF_EinsteinEquations`](lean/QLF_EinsteinEquations.lean), [`Einstein_Equations.md`](Einstein_Equations.md) |
| **Mercury's perihelion** (43″/century) | Newton's law composed with the weak-field Schwarzschild metric | **Derived**; the Schwarzschild components are not yet Lean-anchored individually | [`QLF_MercuryPerihelion`](lean/QLF_MercuryPerihelion.lean), [`Mercury_Perihelion.md`](Mercury_Perihelion.md) |
| **Fine-structure constant** | `α⁻¹ = 128 + 3² = 137` from the 8-twist alphabet and 3-D space, with no observed input (0.026 % from measured) | **Leading value proved**; residual bracketed two-sided, `+0.036` open | [`QLF_FineStructureSubstrate`](lean/QLF_FineStructureSubstrate.lean) (`alpha_QLF_eq`), [`Alpha.md`](Alpha.md) |
| **Maxwell** | No magnetic monopoles; Faraday's law as flux conservation over the event sequence | **Proved** (`∇·B = 0`, Faraday integral form) | [`ZFAEventDynamics`](lean/ZFAEventDynamics.lean) (`no_magnetic_monopoles`), [`QLF_MaxwellCurl`](lean/QLF_MaxwellCurl.lean), [`Maxwell.md`](Maxwell.md) |
| **Spin-½** | The twists are spin; a genuine `SU(2) → SO(3)` double cover | **Proved** | [`QLF_Spin`](lean/QLF_Spin.lean), [`Spin_QLF.md`](Spin_QLF.md) |
| **Pauli exclusion** | The antisymmetric combination of two identical processes is zero | **Proved** | [`PauliExclusion`](lean/PauliExclusion.lean) (`pauli_exclusion`) |
| **Heisenberg uncertainty** | The `ħ/2` quantum is the half-width of one count bin; the product form uses the proved non-commuting axes | **Proved** for the quantum; product form cites the entropic relation | [`QLF_Uncertainty`](lean/QLF_Uncertainty.lean), [`UncertaintyPrinciple.md`](UncertaintyPrinciple.md) |
| **Quantum logic** | Measurement propositions form the orthomodular, non-distributive `MO2` | **Proved** | [`QLF_QuantumLogic`](lean/QLF_QuantumLogic.lean) |
| **Landauer's bound** | Each half-spin closure releases `log 2` nats of variational free energy | **Proved** as a dimensionless information identity (binary KL); the physical energy `k_B T log 2` is an identification, not derived | [`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean) (`zfa_closure_minimizes_free_energy`) |
| **Born rule** | Why the *square*: an event is a ket–bra pair, so its count is `a · a*` | **Half proved**; that the norm is the count of ways is open | [`QLF_BornCounting`](lean/QLF_BornCounting.lean), [`Born_Rule.md`](Born_Rule.md) |
| **The arrow of time** | No time loops, from the law of weakening alone | **Proved** | [`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean) |
| **Horizon thermodynamics** (Unruh, Hawking, de Sitter) | All three are one Unruh relation `T = ℏa/2πck_B` at the right acceleration; the `2π` is the loop phase | **Derived** | [`QLF_HorizonTemperature`](lean/QLF_HorizonTemperature.lean) |
| **Entanglement** (ER = EPR) | Entanglement is a shared closure of two histories, a shared past rather than a signal | **Proved** that a shared closure does not factorize; ER = EPR is a reading | [`QLF_IndexedFactors`](lean/QLF_IndexedFactors.lean) (`shared_closure_not_factorizable`), [`ER_EPR_QLF`](lean/ER_EPR_QLF.lean), [`Entanglement.md`](Entanglement.md) |
| **Three spatial dimensions** | 3 is the least dimension in which every finite relational graph renders without crossings | **Proved** | [`QLF_Generations`](lean/QLF_Generations.lean), [`SpaceTime.md`](SpaceTime.md) §3a |
| **Galactic dynamics** (the radial acceleration relation) | Derived with `a₀ = cH₀/2π`, no particle and no free parameter; blind-tested on 147 SPARC galaxies | **Derived and benchmarked** | [`QLF_DarkMatter`](lean/QLF_DarkMatter.lean), [`DarkMatter.md`](DarkMatter.md), [`SPARC.md`](SPARC.md) |
| **Primordial helium** | Every surviving neutron ends in ⁴He, so `Y_p = 1/4` at freeze-out `n/p = 1/7` (measured 0.247) | **Derived** | [`QLF_Nucleosynthesis`](lean/QLF_Nucleosynthesis.lean) |
| **Strong CP** (`θ̄ = 0`) | Every CP-odd winding vanishes on every closure, so no axion is needed | **Mechanism proved**; field-theoretic reading open | [`QLF_StrongCP`](lean/QLF_StrongCP.lean) |
| **Proton stability** | Baryon number is a winding that no gauge twist changes | **Proved** | [`QLF_BaryonWinding`](lean/QLF_BaryonWinding.lean) |
| **Weak mixing angle** | `sin²θ_W = 3/8` at unification, from the same 6+2 split as α | **Unification value**; running to 0.231 open | [`QLF_WeinbergAngle`](lean/QLF_WeinbergAngle.lean), [`Weak_Force.md`](Weak_Force.md) |
| **Proton–electron mass ratio** | `m_p/m_e = 6π⁵` | **Leading value**; residual open | [`QLF_LenzMassRatio`](lean/QLF_LenzMassRatio.lean), [`Proton_Resonance_R_e.md`](Proton_Resonance_R_e.md) |
| **The hierarchy of scales** | `ln(M_P/m_p) = 2π·b₀ = 14π`, 0.07 % from measured | **Derived** from one posit (`α_s` at the Planck scale) | [`QLF_AlphaS`](lean/QLF_AlphaS.lean) |

The full survey, mystery by mystery and including the particles QLF predicts are absent (supersymmetric partners, the axion, a dark-matter particle, monopoles, proton decay), is [`Mysteries_Of_Physics.md`](Mysteries_Of_Physics.md). The open entries are listed with their owning documents in [`Open_Problems.md`](Open_Problems.md).

**Why determinism sharpens the point.** In QLF every outcome is fixed by counting closures: what
happens first is what closes first, and what happens most often is what closes in the most ways
([`Philosophy.md`](Philosophy.md) §3a, [`UniversalRelativity.md`](UniversalRelativity.md) §6a). QLF is
often read as superdeterministic for this reason. It shares superdeterminism's absence of free
variables but not its mechanism of hidden values correlated with settings, so the precise relation is
in [`Interpretations.md`](Interpretations.md) §5. For this page the relevant fact is simpler. A world in
which every outcome is decided by a finite count has no room for an object that no count can decide.
Classical mathematics has many such objects: a sentence whose truth value cannot settle, a real number
with no finite description, a choice that no procedure makes. In a determinate world those objects
refer to nothing, and statements that depend on them come out empty or wrong.

---

## 3. The pattern: three ways to ask for something no closure delivers

Every failure collected below asks the world for one of three things:

1. **A closure that contains itself.** Self-reference with no grounding: the liar, Russell's set, a
   time loop. A closure's history strictly precedes what it closes, and no history strictly precedes
   itself ([`no_time_loops`](lean/QLF_NoTimeLoops.lean),
   [`generation_has_no_loops`](lean/QLF_ConstructionAdds.lean)).
2. **Infinitely many distinguishable states in a finite place.** The completed continuum, Hilbert's
   hotel, a stored real-valued angle. Pigeonhole forbids it
   ([`no_continuum_in_finite_region`](lean/QLF_Realizability.lean)).
3. **A selection that no construction makes.** The Axiom of Choice applied where no rule picks the
   element: Vitali's set, Banach–Tarski, the infinite hat puzzle. A selection in QLF is a closure, and
   a closure is a finite construction ([`TheContinuum.md`](TheContinuum.md) §6).

The three are not independent. (1) gives an infinite regress, which (2) forbids in a finite region
([`time_loop_forgets`](lean/QLF_HandedLoops.lean)). (3) produces the non-measurable sets that only (2)
makes possible. Sections 4 to 6 take them in turn.

---

## 4. Paradoxes resolved

Status labels follow [`ScientificApproach.md`](ScientificApproach.md): **proved** (Lean, no axiom),
**reading** (an interpretation that rests on proved pieces but is not itself a theorem), and **prior
art** where the resolution is classical and QLF supplies only the substrate reason.

### 4a. The liar: "this sentence is false"

Classically the liar has no consistent truth value. Tarski (1936) responded by banning a language from
defining its own truth predicate. Kripke (1975) showed that a truth predicate can be built in stages,
and the liar is simply never assigned a value at any stage, because it is *ungrounded*: its value
depends only on itself.

QLF reads truth as a receipt. A proposition is true as an event when its closure has happened, and a
receipt, once issued, stays issued ([`closure_receipt_stable`](lean/QLF_ConstructionAdds.lean),
[`weakening_iff_persistence`](lean/QLF_LogicalPersistence.lean)). The liar fails on both counts:

* **It cannot be grounded.** Its receipt would have to be issued by a closure that already includes
  that receipt, which is a history strictly preceding itself. The construction has no such loop
  ([`generation_has_no_loops`](lean/QLF_ConstructionAdds.lean)), and an evaluation that keeps
  deferring to itself is an infinite regress, which a depth-raising process cannot contain
  ([`finite_depth_no_infinite_regress`](lean/QLF_HandedLoops.lean)).
* **It cannot be revised.** The revision reading ("if true then false, so false, so true, …", Gupta &
  Belnap 1993) needs each step to revoke the previous receipt. Closure is many-to-one, so no function
  un-closes ([`no_unclosing`](lean/QLF_ConstructionAdds.lean)), and receipts are never revoked. The
  oscillation is not a sequence of events.

So the liar never receives a receipt. It lives in possibility, where every distinction is generated,
and never becomes an event. That is Kripke's answer, and QLF should not claim the resolution as new
(review note 1 in [`CLAUDE.md`](CLAUDE.md)). What QLF adds is a reason why the physical world contains
no liar event: an ungrounded sentence is a non-terminating evaluation, and non-terminating histories are
exactly the ones `full_zeno_prune` never closes
([`qlf_universality`](lean/QLF_Universality.lean) for the terminating side;
[`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md) §3). **Status: reading**, built on
proved pieces; prior art Kripke.

A related dissolution *is* a theorem. Bar-Hillel and Carnap (1952) noticed that, measured by the models
it excludes, a contradiction carries maximal information. In QLF a contradiction (an unbalanced
ledger) admits no closure and so carries zero realized information
([`contradiction_no_receipt`](lean/QLF_ContradictionReceipt.lean);
[`Information_Physics.md`](Information_Physics.md)). **Status: proved**, given that definition of a
contradiction.

### 4b. Russell's set, Berry's number, and the "exception to every rule"

* **Russell (1902).** The set of all sets that do not contain themselves contains itself if and only
  if it does not. ZF already blocks it by building sets in stages (separation, foundation). QLF's
  version of the stages is the depth grading: every history in generation `n + 1` extends one in
  generation `n` ([`expand_generation_has_parent`](lean/QLF_ConstructionAdds.lean)), so nothing contains
  itself, and the totality of all histories is never itself a history because there is no last
  generation ([`no_final_closure`](lean/QLF_LawOfExceptions.lean)). **Status: reading**; prior art the
  cumulative hierarchy.
* **Berry (via Russell 1906).** "The least number not definable in fewer than sixty letters" defines
  that number in fewer than sixty letters. The paradox is about the function *shortest description*,
  which is not computable (Chaitin 1974). QLF reads that function as belonging to the non-terminating
  tail that never closes, beside Chaitin's Ω; that identification is a stance, not a theorem
  ([`Information_Physics.md`](Information_Physics.md) §4,
  [`Active_Inference_Mathematics.md`](Active_Inference_Mathematics.md) §6). **Status: reading.**
* **"There is an exception to every rule, except this one."** Self-reference proves nothing here, and
  [`Law_Of_Exceptions.md`](Law_Of_Exceptions.md) §1 shows why. What does prove it is capacity: every
  finite-capacity closure has an exception that genuinely closes one level up
  ([`law_of_exceptions`](lean/QLF_LawOfExceptions.lean)). The witnesses are decidable, terminating
  closures, which is why this is not Gödel (§6 there). **Status: proved** for finite-capacity
  closures; reading every restrictive law as such a closure is a modelling assumption, stated in the
  module's header.

### 4c. Paradoxes of time and motion

* **Zeno.** Achilles needs infinitely many completed steps in a finite stretch. In QLF an intermediate
  point is an event only if a closure exists there, and the infinite-step sequence is a non-terminating
  history, which never closes ([`TheContinuum.md`](TheContinuum.md) §5). **Status: reading.**
* **The grandfather paradox and time loops.** Logic alone forbids loops: if weakening holds at every
  state, established facts persist, and no chain of events returns to its start
  ([`no_time_loops_from_logic`](lean/QLF_LogicalPersistence.lean)). Logics without weakening do have
  loops ([`loopWorld_has_time_loop`](lean/QLF_LogicalPersistence.lean)). So loops live in possibility,
  and time is the record ([`Philosophy.md`](Philosophy.md) §3d). Gödel's rotating universe is a
  consistent solution of the field equations that no finite-information region can realize, because a
  loop that never forgets would need infinitely many distinct records
  ([`time_loop_forgets`](lean/QLF_HandedLoops.lean);
  [`UniversalRelativity.md`](UniversalRelativity.md) §4b). **Status: proved.**

### 4d. Paradoxes of quantum measurement

These are paradoxes of classical (Boolean) logic applied to quantum events.

* **The three-polarizer paradox.** Adding a filter lets more light through. The sieve picture assumes
  stored properties and a distributive logic. The closure propositions form the orthomodular,
  non-distributive lattice `MO2` ([`not_distributive`](lean/QLF_QuantumLogic.lean)), the photon has room
  for one bit, and each closure forgets what preceded it (`no_unclosing`)
  ([`Three_Polarizer_Paradox.md`](Three_Polarizer_Paradox.md)). **Status: proved** for the lattice and
  the forgetting; Malus's `cos²θ` at arbitrary angles is still imported.
* **The delayed-choice eraser.** The apparent retrocausality is a joint closure across two causal
  diamonds, and nothing reaches back ([`Delayed_Choice_Eraser.md`](Delayed_Choice_Eraser.md)).
  **Status: reading.**
* **EPR.** The correlation is a shared past, not a signal, and there are no pre-assigned values on
  non-commuting axes ([`Entanglement.md`](Entanglement.md) §5–6, [`ER_EPR_QLF.md`](ER_EPR_QLF.md)).
  **Status: reading**, with the non-commutativity proved.
* **Schrödinger's cat (1935).** On the textbook account, the cat in the sealed box is in a
  superposition of alive and dead until someone looks. In QLF, measurement is closure, and an
  apparatus is a closure inventory, not a mind ([`ScientificApproach.md`](ScientificApproach.md) §1b).
  The atom's decay closes with the Geiger counter, and the counter's state closes with the cat, long
  before the box is opened. Opening the box closes the observer's record with an outcome that has
  already been closed; it adds a receipt and changes nothing that happened. There is no stage at
  which a large, warm object waits for an observer, because observers have no special power to
  close anything ([`Measurement_Problem.md`](Measurement_Problem.md),
  [`Decoherence.md`](Decoherence.md)). **Status: reading**; prior art decoherence (Zurek 2003) and
  relational quantum mechanics (Rovelli 1996).
* **Wigner's friend (1961).** It is the same Wigner. A friend measures a system inside a sealed lab
  and sees a definite result. Wigner, outside, describes the whole lab, friend included, as a
  superposition. Who is right? In QLF the friend's measurement is a closure, and a closure stays
  closed for every observer at every wider horizon
  ([`closure_receipt_stable`](lean/QLF_ConstructionAdds.lean)). Wigner lacks the friend's receipt,
  which is a limit of his perspective and does not put the friend into a superposition. "Many worlds"
  are many observers, each holding a consistent record of what it has received
  ([`Interpretations.md`](Interpretations.md) §2). The extended versions, such as Frauchiger and Renner
  (2018), derive a contradiction from three assumptions together: quantum theory applies to agents
  who have measured, agents' reasoning is consistent, and each measurement has one outcome. QLF denies
  the first in one specific respect: an outside agent cannot treat a closed measurement as reversible,
  because closure is many-to-one and no operation un-closes it
  ([`no_unclosing`](lean/QLF_ConstructionAdds.lean)). **Status: reading**, resting on the two proved
  facts named.

### 4e. Paradoxes of collective choice, and how conflict resolves

Collective choice has its own liar. Condorcet (1785) noticed that majority preference can go round in
a circle: a majority prefers A to B, another prefers B to C, and a third prefers C to A. Arrow (1951)
showed this is no accident. With three or more options, no rule for turning individual rankings into
a group ranking satisfies all of the following at once: it accepts any rankings, respects unanimity,
lets the choice between two options depend only on how people rank those two, and is not a
dictatorship. Both results are finite and correct. In the terms of §3 they are failures of the first
kind: a cycle is a group decision that would have to precede itself, so it never closes.

QLF has the corresponding results for games, proved with no axioms:

* **A game has a free-action functional exactly when it has no improvement cycle**
  ([`free_action_iff_four_cycle`](lean/QLF_PotentialGames.lean), and for any number of players
  [`QLF_NPlayerPotential`](lean/QLF_NPlayerPotential.lean)). Matching pennies is the liar of game
  theory: each player's best reply undoes the other's, and the play cycles with no closure.
* **Where a functional exists, a Nash equilibrium is a ZFA closure** (zero regret is zero free
  action, [`nash_iff_closure`](lean/QLF_PotentialGames.lean)), so relaxation reaches one and cannot
  cycle.
* **Conflict resolves by making the closure joint.** Pay every player the shared total and the game
  becomes one whose functional *is* welfare ([`welfare_game_potential`](lean/QLF_PotentialGames.lean)).
  In the runs this took the welfare-best convention from 0 % to 100 %, and turned a Prisoner's
  Dilemma into full cooperation ([`Game_Theory_QLF.md`](Game_Theory_QLF.md)).

The same reading is built into the group tools. A cycle is handled the way §4a handles the liar: it
receives no receipt. Every peer computes the result and gets the same answer.

* **quantum-os.** In liquid democracy a vote follows its delegation chain to the first person who
  voted directly, and a chain that loops or reaches no direct voter **abstains**
  ([Governance.md](https://github.com/rhovision-org/quantum-os/blob/main/Governance.md)). That is
  Kripke's treatment of the liar applied to votes: an ungrounded vote is assigned nothing. In
  collective optimization a cycling loop "is the substrate reporting that the problem was posed as
  conflict", and the cure is to score candidates on the shared objective
  ([Collective_Optimization.md](https://github.com/rhovision-org/quantum-os/blob/main/Collective_Optimization.md)).
  `/solve` on a room's joint position is deterministic, so every peer reaches the same closure
  without negotiating ([`QLF_as_Intelligence.md`](QLF_as_Intelligence.md) §8,
  [`QucalcSearch.md`](QucalcSearch.md)).
* **rhogov.** The on-chain governance app applies the same rules
  ([README](https://github.com/rhovision-org/rhogov/blob/main/README.md)). Delegation loops abstain.
  Trust is well-founded: a rating can confer at most one level below the rater's own, so two strangers
  cannot vouch each other up, which is the governance form of "no closure contains itself". Every
  figure about standing or outcome comes from one read-only query that anyone can re-run and must get
  the same answer. A council's stakeholder weights are the median of participants' estimates, so a
  few extreme estimates cannot swing them.

One caution, which Arrow's theorem forces. rhogov's ranked-choice votes use instant runoff, which
always produces a winner, so by Arrow it must give up one of his conditions; instant runoff gives up
the independence condition and can miss an option that beats every other head to head. QLF does not
remove Arrow's theorem. It explains where the cycle comes from and offers a way out that changes the
question: score the shared outcome, and the cycle has nothing to run on. **Status:** Condorcet and
Arrow classical; the game theorems proved; the governance rules are design choices consistent with
this reading, and the group testing in quantum-os is where they meet human data.

---

## 5. Failures of the continuum

The single proved fact behind this section is pigeonhole: an infinite set has no injection into a
finite one, so no bounded region faithfully holds a continuum
([`no_continuum_in_finite_region`](lean/QLF_Realizability.lean),
[`real_continuum_not_realizable`](lean/QLF_Realizability.lean)). The proof uses only the continuum's
infinitude and never claims `ℝ` is inconsistent. Everything else in this section follows from it or
illustrates it.

### 5a. The infinite set paradoxes are pigeonhole failures

* **Galileo (1638) and Hilbert's hotel.** An infinite set matches itself one-for-one with a proper
  part: the squares with the integers, a full hotel with room for one more. That property, Dedekind
  infinity, is exactly what a finite region lacks. In a finite region a full hotel is full. **Status:
  proved** (it is the same pigeonhole).
* **Banach–Tarski** (§6) is the same failure in geometric form.

### 5b. Cantor's diagonal argument and the continuum hypothesis

The diagonal argument (Cantor 1891) is sound, and QLF does not dispute it. Given any list of infinite
digit sequences, it builds a sequence that is not on the list. What it proves is a statement about
*lists*: no sequence of reals exhausts the reals. Constructive analysis keeps the theorem in exactly
that form (Bishop 1967), and it never needs the reals as a completed totality. The step classical set
theory adds is the reading of that result as "there exist more reals than integers, as a definite
completed size". That reading then meets three classical results:

1. **The size is not determined.** The continuum hypothesis is independent of ZFC (Gödel 1940, Cohen
   1963). ZFC does not determine the value of `2^ℵ₀`: it is consistent with ZFC for it to be `ℵ₁`,
   `ℵ₂`, and many other values. The axioms leave "how many reals" open.
2. **The uncountable has a countable model** (Löwenheim–Skolem; Skolem's paradox). A countable model
   can satisfy "the reals are uncountable" internally, because the enumeration that counts them from
   outside is not a function inside the model. This is not a contradiction; it shows the sentence does
   not pin down a size from outside.
3. **It adds no finitary theorem.** `WKL₀`, strong enough for much of classical analysis, proves
   no `Π⁰₂` statement that the computable base `RCA₀` does not already prove (Friedman, Harrington;
   Simpson, *SOSOA*).

With QLF's two further results (unrealizable, §5 above; unneeded, §5c below) these are the "five
converging strikes" of [`TheContinuum.md`](TheContinuum.md). The diagonal argument stands. The
completed uncountable totality it is usually taken to describe is undetermined, inessential for
finitary content, and unrealizable.

### 5c. Irrational numbers exist as rational processes

An irrational number is not a thing found in a finite region. It is the limit of a rational process,
and what physics compares is the process. Three examples:

* **`√2`.** "`√2` is irrational" is a theorem about integers: there are no `p, q` with `p² = 2q²`. The
  rational process is the Pell sequence, with `p² − 2q² = ±1` exactly at every step. Both statements
  are finite and exact, and neither needs an infinite decimal.
* **`π`** comes from the closure census. The count of ways a walk returns, `C(2n,n)`, gives
  `returnDensity`, a rational at every `n` ([`closure_census`](lean/QLF_PhysicalPi.lean),
  [`Physical_Pi.md`](Physical_Pi.md)). Its convergence to `1/(πn)` behaviour is a cited classical
  theorem; the count is proved.
* **`ζ(3)`** comes from `aperySum`, a finite rational partial sum ([`QLF_AperyPeriod`](lean/QLF_AperyPeriod.lean)).

The warning that comes with this view is classical too. Specker (1949) built a computable, bounded,
increasing sequence of rationals whose limit is not computable. A rational process can converge to
something no process computes, so "the limit exists" is a stronger claim than "the process runs", and
QLF keeps the weaker one. The practical rule, used in recent work, is to compare the generating rational
sequences rather than their limits.

### 5d. The continuum gives wrong answers where it is forced onto the world

This is the empirical side, collected in [`TheContinuum.md`](TheContinuum.md) and
[`Continuum_Choice_Fallacy.md`](Continuum_Choice_Fallacy.md):

* the **ultraviolet catastrophe** (equipartition over a continuum of modes);
* the **vacuum catastrophe**, a mismatch of about 10¹²² ([`VacuumEnergy.md`](VacuumEnergy.md),
  [`Cosmological_Constant.md`](Cosmological_Constant.md));
* **singularities**, where a continuum field reaches infinite density;
* **Navier–Stokes blow-up**, which needs unbounded vorticity, while discrete vorticity is quantized per
  cell ([`Navier_Stokes_Geometry.md`](Navier_Stokes_Geometry.md) §2–3).

In each case a continuum theory produces a divergence or is pushed beyond its domain of
applicability. These failures are not all alike. For the ultraviolet catastrophe the accepted fix
(quantization) is a discreteness; the vacuum energy and singularities have no accepted fix at all;
and Navier–Stokes regularity is an open mathematical question, not a known failure. So together they
**motivate** a discrete substrate; they do not prove one. QLF's thesis is that the continuum's
successes are the cases where a cutoff was present without being named
([`TheContinuum.md`](TheContinuum.md), "every continuum *success* is smuggled-in discreteness"). That
gives the thesis a falsifiable edge that Wigner's miracle lacks: effectiveness should fail where
realizability does, and the places it has failed so far are consistent with that.

---

## 6. Failures of the Axiom of Choice

The Axiom of Choice says that for any collection of non-empty sets there is a function picking one
element from each, even when no rule does the picking. It is independent of ZF, and it is very useful.
Its strangest consequences all come from that one feature: selections that cannot be exhibited.

* **Vitali's set (1905).** Choose one real from each class of reals that differ by a rational. The
  result has no Lebesgue measure: no length can be assigned to it at all.
* **Banach–Tarski (1924).** A ball is cut into finitely many pieces that reassemble, by rotations
  alone, into two balls of the same size. The pieces are non-measurable, and the group of rotations
  used is non-amenable. In QLF every closure folds to a finite Pauli group, finite groups are amenable,
  and the pieces would need a continuum of points to cut. Duplication in QLF is never free: copying
  needs distinguishability and pays `log 2` per copied bit
  ([`duplication_pays_log_two`](lean/QLF_NoFreeDuplication.lean)). Mitosis is the realizable twin, and
  it pays for what Banach–Tarski takes for nothing ([`Banach_Tarski_QLF.md`](Banach_Tarski_QLF.md)
  §1–4).
* **A Hamel basis of `ℝ` over `ℚ`.** With choice there are additive functions `f(x + y) = f(x) + f(y)`
  that are not linear and whose graphs are dense in the plane. No such function can be written down.
* **A well-ordering of `ℝ`.** Choice guarantees one exists but supplies no canonical, constructive
  one. Whether one can be defined depends on further set-theoretic assumptions: under `V = L` a
  definable well-ordering exists, and in ZFC alone none is provably definable.
* **The infinite hat puzzle.** Countably many people each see the hats in front of them and guess
  their own. With choice there is a strategy under which all but finitely many guess correctly
  (Hardin & Taylor 2013). Nobody can carry the strategy out: it requires a choice from each of
  continuum-many equivalence classes, and an infinite record of the hats seen.

The diagnosis is classical. Solovay (1970), assuming an inaccessible cardinal, built a model of ZF
with dependent choice (DC) in which every set of reals is Lebesgue measurable. In that model Vitali's
set and Banach–Tarski's pieces do not exist, while the analysis physics uses, which needs only
countable or dependent choice, is untouched. So the pathologies need nonconstructive choice principles
that the Solovay model lacks. These need not be full Choice: some non-measurability results follow from
weaker principles, such as a choice of representatives for `ℝ/ℚ` or a non-principal ultrafilter on
`ℕ`.

Two limits leave a physical selection nothing for full Choice to do. **The Planck limit** bounds the
options. No region is divided below the Planck length
([`planck_length_floor`](lean/QLF_PlanckScale.lean)), and a bounded region holds finitely many
distinguishable states (§2). So every choice a physical process makes is among finitely many options,
and choice from finitely many non-empty finite sets is a theorem of ZF, proved by induction with no
Axiom of Choice. The continuum-many classes that Vitali's set and the hat strategy need are never on
offer. **Impossibility** bounds them further. Only what closes can be selected: a contradiction
receives no receipt ([`contradiction_no_receipt`](lean/QLF_ContradictionReceipt.lean)), so an
inconsistent option is never among the choices. Together the two leave only finite selections among
consistent options, and those are exactly the ones an algorithm can make. **Status: reading**, resting
on the named theorems and the finite-information premise.

QLF's replacement is a selection that is a construction. Of all the ways a position can close, the
substrate takes the first-reached one by a deterministic rule that any caller can recompute
([`QucalcSearch.md`](QucalcSearch.md), `/solve`). That is a choice function, and it can be exhibited
because it is an algorithm. QLF's physical core uses no Axiom of Choice
([`TheContinuum.md`](TheContinuum.md) §6). One caution from the review history applies: Choice plays no
role in the finitary Millennium statements, such as the lattice mass-gap claims, where ZF and ZFC agree.
"Choice's defect" should be reserved for the places where Choice actually does work
([`Continuum_Choice_Fallacy.md`](Continuum_Choice_Fallacy.md) §4; framing rule 4 in
[`CLAUDE.md`](CLAUDE.md)).

---

## 7. What classical mathematics keeps

None of this removes classical mathematics. Calculus, Hilbert space, and Lie theory are the
*rendering*: the statistical completion of finite closure counts, and they are right wherever the
counts are large and the cutoff is invisible ([`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) rungs
7–8). Lean proofs in this repository use Mathlib's real numbers freely, and that is not circular,
because the substrate results they render are finitary and `WKL₀` is conservative over them for that
content ([`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §2).

So the boundary runs through classical mathematics, not around it:

| Side | What lives there | How it behaves |
|---|---|---|
| Realizable | counting, finite groups, computable analysis, the rendered continuum as a limit | uncannily effective (Wigner) |
| Unrealizable | the completed continuum as an object, unrestricted Choice, ungrounded self-reference | consistent, and wrong or paradoxical when applied to the world |

One filter decides both sides. ZFA closure selects what is physical and also what mathematics can
realize, so the two cannot drift apart.

---

## 8. In the end: consciousness and the manifestation of spirit

> **Scope note.** This section is of a different kind from §§1–7. It extends the closure reading to
> mind, social reality and spirit. Apart from the theorems it names, its content is **reading** or
> **stance**, labelled as such, and nothing in §§1–7 depends on it.

Wigner's two famous puzzles came a year apart. In 1960 he called the fit of mathematics to nature a
miracle. In 1961, in *Remarks on the mind-body question*, he argued that consciousness completes a
quantum measurement, so that his friend's result became definite only when a mind took it in. He later
moved away from that view. Classical foundations leave both puzzles where he left them, because they
separate the mathematics, the world and the mind as three kinds of thing, and offer nothing to say why
any of them should fit the others.

QLF answers both puzzles with one move, and the move works in two directions.

**Consciousness does not cause closure.** Nothing in QLF has the power to make an outcome happen by
attending to it. An observer is a perspective, an apparatus is a closure inventory, and Schrödinger's
cat and Wigner's friend (§4d) close without anyone looking. That rules out the 1961 proposal.

This does not make the mind inert. A mind's frequencies are physical, and like every biological
rhythm, from the heartbeat to circadian clocks, they have physical effects. Brain oscillations produce
electric and magnetic fields measured outside the skull (EEG and MEG), those fields feed back on the
neurons that produce them (ephaptic coupling, Anastassiou et al. 2011), and through the body a mind
acts on everything it touches. In QLF terms the mind's closures are closures among others, with their
own frequencies ([`Consciousness.md`](Consciousness.md) §2), and they couple to the world the way any
closures do. What QLF rules out is narrower: a mind deciding an outcome by observing it, with no
physical coupling in between.

**Consciousness is a closure.** It is not outside the substrate either. A self-aware system is a
Markov blanket that models itself and terminates, and conscious thought is the highest-frequency
closure the system binds ([`Consciousness.md`](Consciousness.md) §1–§3). The frequency ordering of
that architecture is formalized in Lean ([`QLF_Consciousness`](lean/QLF_Consciousness.lean)): binding
raises frequency, and quieting the internal closures shifts awareness to an external one. These are
simple lemmas about periods, not a proof about minds. The mind that finds mathematics
effective is made of the same closures as the world it describes. That is the deepest reason the fit is
reasonable where it is: the model and the modelled share one basis, and the mathematician's sense of
discovery is a closure recognizing closures ([`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §4).

**Spirit, read through closure.** QLF's ontology gives a precise sense to *manifestation*. Every
logically admissible history exists as possibility, in no place and at no time
([`Philosophy.md`](Philosophy.md) §3; [`Open_Eternal_Mind.md`](Open_Eternal_Mind.md) §2). A possibility
becomes manifest, an event with a record, when it closes: when an action meets its equal and opposite
and the ledger balances at zero free energy. Read this way, spirit is the possibility that has not yet
closed, and manifestation is its closure. Three things then follow from results already in the repo:

* **Only what balances manifests.** A contradiction never receives a receipt
  ([`contradiction_no_receipt`](lean/QLF_ContradictionReceipt.lean)). It exists as possibility, like
  every generable history, but it never closes as a persistent event, however vividly it is imagined.
* **What manifests in common is a joint closure.** The meeting of minds in a room, the shared closure
  of entanglement, and the welfare-best outcome of a group (§4e) are all one kind of event: a closure
  no single party could complete alone. Collective intelligence is spirit manifesting jointly.
* **Experience may be the inside of that.** [`Consciousness.md`](Consciousness.md) §6 proposes that a
  quality felt from within is a self-model coupled to a shared closure larger than itself, the
  receiver regime of §4 there. That is a stance, a dual-aspect hypothesis, and the document states the
  observations that would count against it (§7 there).

**Social reality: closure in minds, effects in the world.** A brain can reach a closure that the
universe does not. A consistent story balances inside a self-model even when the event it describes
never closes physically: no sleigh is ever recorded crossing the sky. When many minds share that
story, it becomes a joint closure among them, a social reality, and a joint closure has real effects.
Santa Claus exists in spirit, and presents are bought, children wait, and families gather because of
him. The effects are physical closures (the gift is really given); the cause is a closure held in
minds. Searle (1995) described the same layer as institutional facts, such as money, marriage and
property, which exist because they are collectively held and are no less effective for that. The
memetic side of the same idea is in [`Memetics_QLF.md`](Memetics_QLF.md): a closure is a meme to the
degree its record is held redundantly by others. The no-receipt theorem limits even this layer. A
story can close in minds only if it is consistent. A self-contradictory belief can be repeated widely,
but what spreads is the wording; it never closes as a shared record. Spirit, in this sense, is not opposed to the
physical. It is possibility that closes in minds first and then acts in the world through them.

**Truth gives a belief its power.** A belief held only socially acts through the people who hold it. A
belief that also matches a closure in the world acts twice: through the minds that share it, and
through the world that confirms it each time it is tested. The connectedness of all things is an
example of the second kind. In QLF it is literal, in three senses, the first two proved. Every history descends,
step by step, from the same first distinction
([`expand_generation_has_parent`](lean/QLF_ConstructionAdds.lean)), so everything shares an origin.
Entanglement is a shared closure that does not split into separate parts
([`shared_closure_not_factorizable`](lean/QLF_IndexedFactors.lean)), so connected systems are one
event, not two linked ones. And, as standard cosmology rather than a QLF theorem, the cosmic horizon is a boundary that every smaller system sits
inside ([`Consciousness.md`](Consciousness.md) §4). The connectedness is a shared past and a shared
closure. It is not a channel: nothing is signalled through it, which is why it never contradicts
relativity ([`Entanglement.md`](Entanglement.md) §5–6). A belief in that connectedness is powerful in
the way true beliefs are, because the world keeps answering it.

**Spirit frequencies have long periods.** In QLF a closure's frequency is the inverse of its depth,
`f = 1/R`, so a deeper closure is a slower one ([`QLF_Consciousness`](lean/QLF_Consciousness.lean),
`freq_lt_of_lt`). A thought is a fast closure inside one brain. A closure held jointly across many
minds, or across a community and its world, is far larger, and so far slower. Its rhythm is the
year, the generation, or the age of a tradition: Santa returns each December, and a culture's shared
stories last for centuries. This is the same ordering [`Consciousness.md`](Consciousness.md) §4 uses
for the receiver regime, where quieting the fast internal closures lets a mind tune to a slow,
shared one. Mind frequencies and spirit frequencies are then one spectrum. The spirit end is low,
long-period and shared, and it acts on the world as slowly and as surely as the seasons do. **Status:
reading**, resting on the formalized `f = 1/R` ordering.

**What possibilism proves, and what it doesn't.** Given possibilism, the reading of spirit is not an
extra assumption. QLF's floor is that every generable history is a real way, and that ZFA decides which
ways persist as events, not which exist ([`ScientificApproach.md`](ScientificApproach.md) §1b). From that
premise it follows directly that all admissible possibilities are real, that manifestation is closure,
and, with the proved no-receipt theorem, that only what balances manifests. So the first two points
above are consequences of the premise, not a separate reading. Two things stay outside the proof.
Possibilism itself is QLF's founding commitment: it is not tested in isolation, and its warrant is the
derivations it supports (§2). And possibilism says what exists and what manifests; it does not say that
a closure is felt from the inside. That third point, experience, remains the qualia hypothesis, a stance
with stated tests.

**Does possibilism bring the infinity back?** It seems to. If every admissible history exists a priori,
the totality of possibility is infinite, and nobody can survey it. Three distinctions show what returns
and what does not.

* **Countable, finite parts.** The possibility space is the free monoid on eight twists: countably
  many histories, each finite and finitely described. Nothing in it is a completed continuum, and no
  finite region holds more than finitely many of them, so it does not conflict with
  [`no_continuum_in_finite_region`](lean/QLF_Realizability.lean). Every proof in the Lean core uses it
  in the potential form, one finite generation at a time
  ([`expand_generation_length`](lean/QLF_ConstructionAdds.lean)).
* **The totality is never an event.** There is no last generation and no final closure
  ([`no_final_closure`](lean/QLF_LawOfExceptions.lean)), so the whole of possibility is never itself
  received by anyone. It is unknowable as a whole for the same reason a full hotel is full in a finite
  region (§5a): no finite capacity holds it.
* **One part is genuinely unknowable.** Which computations never terminate is the halting question,
  and its information content is Chaitin's Ω. Possibilism does reintroduce this. `full_zeno_prune`
  itself is a terminating recursion on finite strings and decides no halting question; identifying the
  boundary of what never closes with Ω is an ontological stance, not a theorem
  ([`Information_Physics.md`](Information_Physics.md) §4,
  [`Active_Inference_Mathematics.md`](Active_Inference_Mathematics.md) §6). On that stance it sits
  entirely on the side of what never manifests, so no physical record depends on it.

* **The Planck limit ends it in the world.** Below the Planck scale a closure would sit inside its own
  horizon and cannot close ([`planck_length_floor`](lean/QLF_PlanckScale.lean),
  [`Planck_Scale.md`](Planck_Scale.md)), so no region is divided without end. And the world so far is a
  finite count of Planck events, about 10⁶⁰ in the cosmic age ([`AgeOfUniverse.lean`](lean/AgeOfUniverse.lean)).
  Nothing infinite exists in this world: not a region, not a duration, not a record.

So the infinity returns as possibility and never as event. There is one honest tension. Saying the
totality "exists" a priori is a completed-totality claim of the kind Brouwer rejected, and QLF could
take the weaker potential reading (every history *can* be generated) without losing any theorem. That
choice is metaphysical, and it is the founding commitment named above.

**Is this reverse causality?** It looks like it. Whether an open strand becomes an event depends on
steps that come after it: a step closes only when its conjugate arrives. The same appearance runs
through physics. Least action selects a path by a condition on the whole path, which is why it seemed
teleological from Maupertuis on ([`Stationary_Action.md`](Stationary_Action.md) proves the discrete
multiplicity is stationary at balance; the bridge to the physical action is open).
Wheeler and Feynman's absorber theory, Cramer's transactional interpretation and Mead's handshake photon
([`Collective_Electrodynamics.md`](Collective_Electrodynamics.md)) all have the future end take part.
QLF's reading is that none of this is causation running backward. Before closure nothing has happened;
an open strand is possibility, not an event later rewritten. The closure is a single event with two
ends, and neither end causes the other. Once it closes, nothing can reach back to change it
([`no_unclosing`](lean/QLF_ConstructionAdds.lean)), and no chain of events returns to its start
([`no_time_loops_from_logic`](lean/QLF_LogicalPersistence.lean)). The selection is atemporal, a
condition on whole histories, and time is the record of what has closed. The delayed-choice eraser is
the laboratory case ([`Delayed_Choice_Eraser.md`](Delayed_Choice_Eraser.md)). **Status: reading**,
resting on the named theorems.

This is where the page's argument ends up. Classical mathematics can describe the
world only from outside, and it becomes unreasonable exactly where it asserts what cannot close. A
logic of closure describes the world, the mind, and their meeting in the same terms. In that logic,
Wigner's "gift we neither understand nor deserve" can be understood as the logic itself, manifesting.

---

## 9. Status at a glance

| Claim | Status | Where |
|---|---|---|
| No infinite state space injects into a finite region | **Proved** | [`QLF_Realizability`](lean/QLF_Realizability.lean) |
| No closure precedes itself; generation has no loops | **Proved** | [`QLF_NoTimeLoops`](lean/QLF_NoTimeLoops.lean), [`QLF_ConstructionAdds`](lean/QLF_ConstructionAdds.lean) |
| No un-closing; receipts persist | **Proved** | `no_unclosing`, `closure_receipt_stable` |
| No time loops, from the law of weakening alone | **Proved** | [`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean) |
| A contradiction carries no realized information | **Proved** (given the definition) | [`QLF_ContradictionReceipt`](lean/QLF_ContradictionReceipt.lean) |
| Every finite-capacity closure has an exception that closes one level up | **Proved** (extending it to every restrictive law is a modelling assumption) | [`QLF_LawOfExceptions`](lean/QLF_LawOfExceptions.lean) |
| Measurement propositions are non-distributive `MO2` | **Proved** | [`QLF_QuantumLogic`](lean/QLF_QuantumLogic.lean) |
| `π`, `ζ(3)` as limits of finite rational counts | **Proved** counts; convergence cited | [`QLF_PhysicalPi`](lean/QLF_PhysicalPi.lean), [`QLF_AperyPeriod`](lean/QLF_AperyPeriod.lean) |
| Discrete multiplicity is stationary at balance | **Proved**, no axiom; the bridge to the physical action `δS = 0` is open | [`QLF_StationaryAction`](lean/QLF_StationaryAction.lean), [`QLF_StationaryPhase`](lean/QLF_StationaryPhase.lean) |
| Manifestation = closure; only what balances manifests | **Follows** from possibilism (the founding commitment) + `contradiction_no_receipt` | §8 |
| Consciousness as a frequency hierarchy of closures | **Formalized** (simple lemmas on periods); qualia remain a stance | [`QLF_Consciousness`](lean/QLF_Consciousness.lean), §8 |
| The liar receives no receipt | **Reading** (prior art: Kripke 1975) | §4a |
| Russell, Berry, Zeno, eraser, EPR, Schrödinger's cat, Wigner's friend | **Reading** | §4b–4d |
| Improvement cycles ⟺ no free-action functional; Nash = closure; joint closure = welfare | **Proved** | [`QLF_PotentialGames`](lean/QLF_PotentialGames.lean), §4e |
| The completed continuum is gratuitous | Three classical results + two proved | [`TheContinuum.md`](TheContinuum.md) |
| Choice's pathologies need nonconstructive choice beyond ZF + DC | **Classical** (Solovay 1970, relative to an inaccessible) | §6 |
| Effectiveness tracks realizability | **Thesis**; its failures are the evidence | §5d, [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §4 |

The finite-information premise (Bekenstein) is the one physical input. If it failed, so that a bounded
region could hold infinitely many distinguishable states, §5 would lose its force, and §4 and §6 would
be unaffected.

---

## 10. What not to say

* **Not "ZFC is inconsistent" or "the reals are false."** They are consistent. The claim is that they
  are unrealizable and that they mislead when they are applied to the world.
* **Not "QLF solved the liar."** Kripke did. QLF says why no liar is an event.
* **Not "Cantor was wrong."** The diagonal argument is correct. What fails is reading it as the
  measurement of a completed totality.
* **Not "Choice is behind every hard problem."** Only where Choice does work.
* **Not "nature is QLF's construction."** Nature is logical, and QLF is one model of that.

---

## See also

* [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §4: Wigner dissolved, the positive side of this
  page.
* [`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md): quantum logic as the correct
  foundation, and why it is not incomplete.
* [`Continuum_Choice_Fallacy.md`](Continuum_Choice_Fallacy.md) and [`TheContinuum.md`](TheContinuum.md):
  the full case against the continuum and Choice.
* [`Banach_Tarski_QLF.md`](Banach_Tarski_QLF.md): Banach–Tarski and mitosis.
* [`Three_Polarizer_Paradox.md`](Three_Polarizer_Paradox.md): a paradox of Boolean logic, resolved.
* [`Law_Of_Exceptions.md`](Law_Of_Exceptions.md): self-reference, capacity, and why it is not Gödel.
* [`ReverseMathematics.md`](ReverseMathematics.md): where QLF sits in the subsystem hierarchy.
* [`Interpretations.md`](Interpretations.md) §5: QLF and superdeterminism.
* [`Mysteries_Of_Physics.md`](Mysteries_Of_Physics.md): the open questions of physics and what QLF says about each.
* [`Open_Problems.md`](Open_Problems.md): the gap registry.

## References

* Bar-Hillel, Y. & Carnap, R. (1952). *An Outline of a Theory of Semantic Information.* MIT RLE Tech.
  Rep. 247.
* Anastassiou, C. A., Perin, R., Markram, H. & Koch, C. (2011). Ephaptic coupling of cortical neurons. *Nat. Neurosci.* 14, 217–223.
* Arrow, K. J. (1951). *Social Choice and Individual Values.* Wiley.
* Banach, S. & Tarski, A. (1924). Sur la décomposition des ensembles de points en parties respectivement
  congruentes. *Fund. Math.* 6, 244–277.
* Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio for bounded systems.
  *Phys. Rev. D* 23, 287.
* Bishop, E. (1967). *Foundations of Constructive Analysis.* McGraw-Hill.
* Cantor, G. (1891). Über eine elementare Frage der Mannigfaltigkeitslehre. *Jahresber. DMV* 1, 75–78.
* Chaitin, G. J. (1974). Information-theoretic limitations of formal systems. *J. ACM* 21, 403–424.
* Cohen, P. J. (1963). The independence of the continuum hypothesis. *PNAS* 50, 1143–1148.
* Condorcet, Marquis de (1785). *Essai sur l'application de l'analyse à la probabilité des décisions rendues à la pluralité des voix.* Paris.
* Frauchiger, D. & Renner, R. (2018). Quantum theory cannot consistently describe the use of itself. *Nat. Commun.* 9, 3711.
* Galilei, G. (1638). *Discorsi e dimostrazioni matematiche intorno a due nuove scienze.*
* Gödel, K. (1940). *The Consistency of the Continuum Hypothesis.* Princeton.
* Gupta, A. & Belnap, N. (1993). *The Revision Theory of Truth.* MIT Press.
* Hamming, R. W. (1980). The unreasonable effectiveness of mathematics. *Amer. Math. Monthly* 87, 81–90.
* Hardin, C. S. & Taylor, A. D. (2013). *The Mathematics of Coordinated Inference.* Springer.
* Kripke, S. (1975). Outline of a theory of truth. *J. Philosophy* 72, 690–716.
* Rovelli, C. (1996). Relational quantum mechanics. *Int. J. Theor. Phys.* 35, 1637–1678.
* Russell, B. (1906). Les paradoxes de la logique. *Revue de Métaphysique et de Morale* 14, 627–650.
* Schrödinger, E. (1935). Die gegenwärtige Situation in der Quantenmechanik. *Naturwissenschaften* 23, 807–812.
* Searle, J. R. (1995). *The Construction of Social Reality.* Free Press.
* Simpson, S. G. (2009). *Subsystems of Second Order Arithmetic*, 2nd ed. Cambridge.
* Solovay, R. M. (1970). A model of set-theory in which every set of reals is Lebesgue measurable.
  *Ann. of Math.* 92, 1–56.
* Specker, E. (1949). Nicht konstruktiv beweisbare Sätze der Analysis. *J. Symbolic Logic* 14, 145–158.
* Tarski, A. (1936). Der Wahrheitsbegriff in den formalisierten Sprachen. *Studia Philosophica* 1,
  261–405.
* Vitali, G. (1905). *Sul problema della misura dei gruppi di punti di una retta.* Bologna.
* Wigner, E. P. (1960). The unreasonable effectiveness of mathematics in the natural sciences. *Comm.
  Pure Appl. Math.* 13, 1–14.
* Wigner, E. P. (1961). Remarks on the mind-body question. In I. J. Good (ed.), *The Scientist Speculates.* Heinemann.
* Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Rev. Mod. Phys.* 75, 715–775.
