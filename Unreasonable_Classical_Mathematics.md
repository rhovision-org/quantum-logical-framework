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

So QLF has to account for two things, and one account covers both. Mathematics is reasonable where it
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
| **Complex numbers.** Nothing in experience suggests them, yet quantum mechanics is written in them. | `i` is in the substrate from the first step. Every balanced closure folds to one of `{+1, −1, +i, −i}`, a group derived from the fold, not assumed ([`count_balanced_pauli_closed`](lean/QLF_TwistAlphabet.lean), [`QLF_Pauli`](lean/QLF_Pauli.lean); [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) rung 5). Complex numbers are suggested by experience at its finest grain. | The complex continuum `ℂ` as a set of points is the completion of `ℤ[i]`. It is a rendering, and it is right in the large-count limit (§7). |
| **Accuracy beyond the evidence.** Newton's law, fitted to rough data, holds to far better precision; matrix mechanics, built for hydrogen, works for helium. | A law that describes how closures count keeps working as more closures are counted. The accuracy is that of counting, which gives exact answers ([`Mercury_Perihelion.md`](Mercury_Perihelion.md); the census results in [`Closure_Walk.md`](Closure_Walk.md)). | Where a continuum theory is pushed past any cutoff, precision turns into infinity: the ultraviolet and vacuum catastrophes, singularities (§5d). Wigner's examples are all successes. The failures were known in 1960 and do not appear in the essay. |
| **The miracle of the existence of laws** at all, and of the mind's capacity to find them. | A world selected by one closure condition has regularities because it has one condition. The mind finding them is itself a set of closures in the same substrate, so the model and the thing modelled share a basis ([`Active_Inference_Mathematics.md`](Active_Inference_Mathematics.md)). Only logic is assumed for this, not that nature is QLF's construction (§2). | No finite law is exceptionless: every finite closure law has a genuine exception one level up ([`law_of_exceptions`](lean/QLF_LawOfExceptions.lean)). Laws hold as counts, not as decrees. |
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
[`no_continuum_in_finite_region`](lean/QLF_Realizability.lean). Everything in §5 and §6 below is that
premise plus logic.

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
  which is not computable (Chaitin 1974). In QLF that function sits in the non-terminating tail that is
  pruned, beside Chaitin's Ω ([`Active_Inference_Mathematics.md`](Active_Inference_Mathematics.md) §6).
  **Status: reading.**
* **"There is an exception to every rule, except this one."** Self-reference proves nothing here, and
  [`Law_Of_Exceptions.md`](Law_Of_Exceptions.md) §1 shows why. What does prove it is capacity: every
  finite closure law has an exception that genuinely closes one level up
  ([`law_of_exceptions`](lean/QLF_LawOfExceptions.lean)). The witnesses are decidable, terminating
  closures, which is why this is not Gödel (§6 there). **Status: proved.**

### 4c. Paradoxes of time and motion

* **Zeno.** Achilles needs infinitely many completed steps in a finite stretch. In QLF an intermediate
  point is real only if a closure exists there, and the infinite-step sequence is a non-terminating
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
   1963). `2^ℵ₀` can be made almost anything the axioms allow, so "how many reals" has no answer.
2. **The uncountable has a countable model** (Löwenheim–Skolem; Skolem's paradox). A countable model
   satisfies "the reals are uncountable", so the sentence does not pin down a size from outside.
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

In each case the continuum answer is wrong, and the working fix restores a cutoff, which is to say a
discreteness. The continuum's successes are the cases where that cutoff was already present without
being named ([`TheContinuum.md`](TheContinuum.md), "every continuum *success* is smuggled-in
discreteness"). This is the falsifiable edge that Wigner's miracle lacks: effectiveness should fail
exactly where realizability does, and it does.

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
* **A well-ordering of `ℝ`.** Choice guarantees one exists, and none can be defined.
* **The infinite hat puzzle.** Countably many people each see the hats in front of them and guess
  their own. With choice there is a strategy under which all but finitely many guess correctly
  (Hardin & Taylor 2013). Nobody can carry the strategy out: it requires a choice from each of
  continuum-many equivalence classes, and an infinite record of the hats seen.

The diagnosis is classical and sharp. Solovay (1970) built a model of ZF with dependent choice in which
every set of reals is Lebesgue measurable. In that model Vitali's set and Banach–Tarski's pieces do not
exist, while the analysis physics uses is untouched. The pathologies come from full Choice and nothing
else.

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

## 8. Status at a glance

| Claim | Status | Where |
|---|---|---|
| No infinite state space injects into a finite region | **Proved** | [`QLF_Realizability`](lean/QLF_Realizability.lean) |
| No closure precedes itself; generation has no loops | **Proved** | [`QLF_NoTimeLoops`](lean/QLF_NoTimeLoops.lean), [`QLF_ConstructionAdds`](lean/QLF_ConstructionAdds.lean) |
| No un-closing; receipts persist | **Proved** | `no_unclosing`, `closure_receipt_stable` |
| No time loops, from the law of weakening alone | **Proved** | [`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean) |
| A contradiction carries no realized information | **Proved** (given the definition) | [`QLF_ContradictionReceipt`](lean/QLF_ContradictionReceipt.lean) |
| Every finite law has a real exception | **Proved** | [`QLF_LawOfExceptions`](lean/QLF_LawOfExceptions.lean) |
| Measurement propositions are non-distributive `MO2` | **Proved** | [`QLF_QuantumLogic`](lean/QLF_QuantumLogic.lean) |
| `π`, `ζ(3)` as limits of finite rational counts | **Proved** counts; convergence cited | [`QLF_PhysicalPi`](lean/QLF_PhysicalPi.lean), [`QLF_AperyPeriod`](lean/QLF_AperyPeriod.lean) |
| The liar receives no receipt | **Reading** (prior art: Kripke 1975) | §4a |
| Russell, Berry, Zeno, eraser, EPR | **Reading** | §4b–4d |
| The completed continuum is gratuitous | Three classical results + two proved | [`TheContinuum.md`](TheContinuum.md) |
| Choice's pathologies are Choice's alone | **Classical** (Solovay 1970) | §6 |
| Effectiveness tracks realizability | **Thesis**; its failures are the evidence | §5d, [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §4 |

The finite-information premise (Bekenstein) is the one physical input. If it failed, so that a bounded
region could hold infinitely many distinguishable states, §5 would lose its force, and §4 and §6 would
be unaffected.

---

## 9. What not to say

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
* [`Open_Problems.md`](Open_Problems.md): the gap registry.

## References

* Bar-Hillel, Y. & Carnap, R. (1952). *An Outline of a Theory of Semantic Information.* MIT RLE Tech.
  Rep. 247.
* Banach, S. & Tarski, A. (1924). Sur la décomposition des ensembles de points en parties respectivement
  congruentes. *Fund. Math.* 6, 244–277.
* Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio for bounded systems.
  *Phys. Rev. D* 23, 287.
* Bishop, E. (1967). *Foundations of Constructive Analysis.* McGraw-Hill.
* Cantor, G. (1891). Über eine elementare Frage der Mannigfaltigkeitslehre. *Jahresber. DMV* 1, 75–78.
* Chaitin, G. J. (1974). Information-theoretic limitations of formal systems. *J. ACM* 21, 403–424.
* Cohen, P. J. (1963). The independence of the continuum hypothesis. *PNAS* 50, 1143–1148.
* Galilei, G. (1638). *Discorsi e dimostrazioni matematiche intorno a due nuove scienze.*
* Gödel, K. (1940). *The Consistency of the Continuum Hypothesis.* Princeton.
* Gupta, A. & Belnap, N. (1993). *The Revision Theory of Truth.* MIT Press.
* Hamming, R. W. (1980). The unreasonable effectiveness of mathematics. *Amer. Math. Monthly* 87, 81–90.
* Hardin, C. S. & Taylor, A. D. (2013). *The Mathematics of Coordinated Inference.* Springer.
* Kripke, S. (1975). Outline of a theory of truth. *J. Philosophy* 72, 690–716.
* Russell, B. (1906). Les paradoxes de la logique. *Revue de Métaphysique et de Morale* 14, 627–650.
* Simpson, S. G. (2009). *Subsystems of Second Order Arithmetic*, 2nd ed. Cambridge.
* Solovay, R. M. (1970). A model of set-theory in which every set of reals is Lebesgue measurable.
  *Ann. of Math.* 92, 1–56.
* Specker, E. (1949). Nicht konstruktiv beweisbare Sätze der Analysis. *J. Symbolic Logic* 14, 145–158.
* Tarski, A. (1936). Der Wahrheitsbegriff in den formalisierten Sprachen. *Studia Philosophica* 1,
  261–405.
* Vitali, G. (1905). *Sul problema della misura dei gruppi di punti di una retta.* Bologna.
* Wigner, E. P. (1960). The unreasonable effectiveness of mathematics in the natural sciences. *Comm.
  Pure Appl. Math.* 13, 1–14.
