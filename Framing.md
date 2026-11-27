# One conjecture: QLF as the quantum computer that tests models

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

Jim Whitescarver (2026-11-27): *"QLF IS the quantum computer that proves other models or not. ... We
assume equal and opposite logical action only. It stands without contradiction. Postulates based on
what we know rather than conjecture."* And: *"Equal and opposite logical action is the only well
supported conjecture. The anthropic principle proves QLF is equivalent to any solution."*

This page states that framing once, in the form the rest of the repository should follow. It has
four parts: the one conjecture (§1), the four kinds every other statement falls into (§2), what it
means for QLF to be a quantum computer (§3) equivalent to any solution (§3a), and how it tests other
models (§4). The registry form, with
stable IDs, is [Principles.md](Principles.md) §A.

---

## 1. The one conjecture

QLF rests on one well-supported conjecture, and on nothing else that is conjectural.

**ZFA.** A history becomes an event exactly when every action in it has been matched by its equal and
opposite action, so that its free action, and its free energy, is zero.

Everything QLF claims either follows from this, comes from a known fact named with its source, or is
marked as a bridge or a reading (§2). Two things are already inside the statement:

- **Signed distinctions.** "Equal and opposite" means each elementary action has an opposite. That is
  the conjugate pairing of the twist alphabet (P01 in [Principles.md](Principles.md)), so it is not a
  second conjecture.
- **Closure is the event.** The statement says when a history *becomes an event*: at its first
  closure. The absorbing reading recorded as A07 is this half of the statement, not an extra posit.

**It stands without contradiction**, in two senses that should be kept apart.

1. **Logically.** In Lean, ZFA is a *definition* (`achieves_ZFA`, `full_zeno_prune` in
   [`QLF_Axioms`](lean/QLF_Axioms.lean); `countBalanced`), not an `axiom`, so it adds nothing to the
   logic it is stated in, and it has models: the empty history and `^v` close, and every count-balanced
   history folds to `±I` (`count_balanced_pauli_closed`,
   [`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean)). A theorem that rests on ZFA alone has a
   `#print axioms` footprint with no QLF name in it, which
   [`QLF_AxiomAudit`](lean/QLF_AxiomAudit.lean) checks on every push. This is consistency relative to
   Lean's logic, which is the strongest kind available.
2. **Empirically.** The premise has a kill condition: a persistent physical event that requires a
   history with non-zero free action ([ScientificApproach.md](ScientificApproach.md) §1a). None has been
   observed, and the predicted-absent list ([Mysteries_Of_Physics.md](Mysteries_Of_Physics.md) §6) is
   where it is most exposed. That is a record of tests passed, not a proof, and the tests continue.

The named `axiom` declarations in the repository (the Millennium boundaries and the continuum limits,
listed in the axiom inventory of [CLAUDE.md](CLAUDE.md)) are **not** further conjectures of QLF. Each is
a bridge (§2): a result that uses one says so in its footprint, and is conditional on it.

---

## 2. Everything else is one of four kinds

| Kind | What it is | How it may be used |
|---|---|---|
| **Derived** | A theorem from ZFA, machine-checked, or an exact computation over a stated finite domain | Freely |
| **Known fact** | An input from observation or established physics, named with its source | As an input, cited, one per role; never a conjecture in disguise |
| **Bridge** | An open identification between a substrate object and a laboratory quantity | Only in conditional results that name it |
| **Reading** | An interpretation of a proved result | Never as a premise of a derivation |

A well-supported conjecture is allowed, labelled as a conjecture ("no proof, no bs"). What is not
allowed is to use one as a postulate.

**Postulates rest on what we know fundamentally, not on conjectures of emergence.** A known fact
that QLF may take as input is a fact at the level of the substrate: what a measurement returns (a
count), that two observables are incompatible, that a bounded region holds finite information. What
emerges from closures may not be postulated: a continuum spacetime, a metric, fields, particles as
given objects, the Born rule, or a classical limit. Each of those is a claim about what many closures
add up to, so it has to be derived, and until it is, it is a bridge (Principles §D), never an input.
The test for a candidate postulate: if it describes something QLF says is *synthesized*, it is a
conjecture of emergence and it is out. Standard physics runs the other way, postulating the emergent
layer (a manifold, a Hilbert space with a fixed tensor structure, a Lagrangian) and leaving the
fundamental one unexplained; that is the inversion QLF is built to undo.

### The known facts QLF takes as inputs

| ID | Known fact | Source | What it is used for |
|---|---|---|---|
| A10 | Every measurement outcome is a finite count with a rational uncertainty; none has produced a real number | Metrology; the 2019 SI redefinition ([Completeness_Evidence.md](Completeness_Evidence.md) §2a) | Why the substrate is finite and the continuum a rendering |
| A11 | Incompatible observables exist: spin along two axes cannot be jointly sharp | Stern–Gerlach (1922) and sequential spin measurements | With `noncommuting_iff_eight` ([`QLF_AlphabetNecessity`](lean/QLF_AlphabetNecessity.lean)), the alphabet has eight twists |
| A12 | A bounded region holds finitely many distinguishable states | The Bekenstein bound (1981): established theory, not a direct measurement | `no_continuum_in_finite_region` ([`QLF_Realizability`](lean/QLF_Realizability.lean)) |
| A13 | The measured constants fix the units | CODATA values of `ℏ`, `c`, `G` | One calibration per dimensionful observable ([ScientificApproach.md](ScientificApproach.md) §5) |

A12 is labelled as what it is: the best-supported bound in physics, but a theoretical one. If it were
withdrawn, results resting on it would become conditional, and they say so.

### The former foundations, reclassified

[Principles.md](Principles.md) §A listed nine foundations. Under this framing A01 is the only conjecture:

| ID | Was | Now |
|---|---|---|
| A01 | ZFA selection | **The one well-supported conjecture** |
| A02 | Possibilism | Its formal content is the absence of any second filter: nothing but ZFA restricts which histories count as ways. That the unclosed ways are *real* is a reading |
| A03 | Only logic is assumed | The method; ZFA is that logical assumption (every distinction has its opposite) |
| A04 | Finite realizability | Derived (`no_continuum_in_finite_region`) from the known fact A12 |
| A05 | Information primacy | Reading |
| A06 | No observer potency | The absence of an assumption: no observer appears in ZFA, so none may enter a derivation. Supported by `observers_agree` ([`QLF_MultiObserver`](lean/QLF_MultiObserver.lean)) |
| A07 | A closure is an event | Part of the statement of A01 (§1) |
| A08 | Finite perspective | Derived (the listening, P17); "capacity = apparatus resolution" is a bridge |
| A09 | Synthesized spacetime | Reading, with each physical form a bridge in [Principles.md](Principles.md) §D |

### Structural choices that stay auditable

Reclassifying an assumption does not eliminate it. "Equal and opposite" alone does not fix the Pauli
algebra, since many structures satisfy cancellation. So QLF has **one proposed fundamental principle**,
and every structural choice, empirical input and open bridge is accounted for separately. These are
the structural choices still carried, each to be audited on its own and, where possible, replaced by
a necessity proof:

| Choice | Where it enters | Status |
|---|---|---|
| The signed distinctions are the signed axes of the Pauli frame | The alphabet ([ScientificApproach.md](ScientificApproach.md) §1c) | Open structural posit; given it, A11 fixes eight twists |
| Generation is uniform over the alphabet | The cylinder measure `8^{−\|h\|}` (`twist_kraft`) | A stated choice; biased alphabets break stationarity ([Stationary_Action.md](Stationary_Action.md)) |
| The first closure is the event | A01's event semantics (A07) | Part of the conjecture, but auditable: the alternatives were tested and rejected ([ScientificApproach.md](ScientificApproach.md) §11) |
| Cylinder measure = physical probability | Every frequency claim | Bridge B09 |
| Logical free action = physical free energy | The `log 2` per closure, thermodynamic readings | Bridge (B08, B14) |

---

---

## 3. QLF is the quantum computer

Four claims about computation are easy to run together, and they need to be kept apart:

| Level | What it is | Status |
|---|---|---|
| **Natural quantum computation** | The universe synthesizes its events through quantum logical closure; its evolution *is* the computation | The foundational thesis: what A01 says, read as computation (Lloyd 2006). Not a second conjecture |
| **Classical programmable computation** | Substrate networks evaluate any finite Boolean function | Proved in the substrate model |
| **Universal programmable quantum computation** | Substrate operations compose into any quantum circuit on one encoded qubit space | The algebra is proved; native composition on a common qubit is **open** |
| **Classical simulation of quantum computation** | QuCalc, RhoQuCalc, [`qucalc_search.py`](qucalc_search.py) and QuantumOS run closures on ordinary hardware | Implemented; cost depends on the size of the history space, and no efficiency claim is made |

The first level does not wait on the third: investigating reality as a quantum logical system does not
need the substrate to be programmable for arbitrary circuits. The third is a capability to establish,
and the fourth must not be overstated as the first. What is proved toward the programmable levels
([Universe_Quantum_Computer.md](Universe_Quantum_Computer.md)):

| Part | Status | Anchor |
|---|---|---|
| The substrate computes every Boolean function with ZFA-preserving gates | Proved | `fredkin_complete`, `substrate_computes` ([`QLF_QuantumComputer`](lean/QLF_QuantumComputer.lean)) |
| A single twist history reaches only a finite group of 16 gates | Proved | `twist_folds_finite` |
| Count-weighted alternatives give a rotation of infinite order | Proved | `rotation_powers_injective`, `quantum_power_needs_weighted_ways` |
| Those rotations and their Hadamard conjugates are dense in SU(2) | Proved | `su2_dense` |
| Dense single-qubit gates plus CNOT are universal | Proved, as matrix algebra | [`QLF_Barenco`](lean/QLF_Barenco.lean) ([Barenco_Universality.md](Barenco_Universality.md)) |
| A joint closure carries the controlled-Z sign table | Proved | `joint_closure_is_cz`, `cz_entangling` |
| That sign table acts as a gate on superposed presence states | **Open** | [Universe_Quantum_Computer.md](Universe_Quantum_Computer.md) §7 |

**The obstacle is a common qubit.** The Hadamard acts on the spinor space that folds live in; the
controlled-Z signs act on the presence or absence of a closed pair. They do not yet act on the same
encoded qubit. The target (obligation O1, §6) is one substrate encoding `E` and native operations
`T_U` with

  `T_U(E(ψ)) ~ E(Uψ)`,

where `~` is observational equivalence (`ObsEquiv`, below), for `U` the Hadamard, the count-weighted
rotation and controlled-Z, preserving coherence and composing, without defining the gate action into
the encoding. The decisive test is the Bell state: take `|00⟩` to `(|00⟩ + |11⟩)/√2` by native
operations only, and check its relative phase and correlations without assuming the circuit semantics
under test.

So QLF is a **classical universal computer in the substrate, proved**, and a **universal programmable
quantum computer up to O1**. O1 is a proof obligation inside the consequences of ZFA, not a second
conjecture. Being a quantum computer gives no NP oracle
([Universe_Quantum_Computer.md](Universe_Quantum_Computer.md) §4).

---

## 3a. Equivalence to any solution: the anthropic argument

Jim's claim is that **QLF is equivalent to any solution**: any theory that correctly describes our
universe agrees with QLF on everything that can be observed. The argument has three steps.

1. **Observation is closure.** We exist, and every observation we make is an event. Under A01 an
   event is a closure, so every observation is a closure, and so is every observer's record of it
   (A06: an apparatus is a closure inventory). This is the anthropic step: a solution only has to
   account for what can be observed from inside, and what can be observed is what closes.
2. **Any solution can be run as closures.** A solution that is computable is a process the
   substrate can evaluate with its own gates: for its classical part this is proved
   (`fredkin_complete`, `substrate_computes`, [`QLF_QuantumComputer`](lean/QLF_QuantumComputer.lean));
   for its quantum part it waits on the gate of §3.
3. **What no closure can tell apart is the same.** Two histories are observationally equivalent when
   every closing context closes them with the same phase (`ObsEquiv`,
   [`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean)); that relation is proved
   to be the tensor quotient (`obsEquiv_iff_pairEquiv`), so nothing finer is observable within its
   domain.

**Status.** Step 1 is A01 applied to observers. Step 3 is proved for its domain (two bodies, under the
independence premises of [`QLF_TensorFromClosure`](lean/QLF_TensorFromClosure.lean)). Step 2 is proved
for classical computation and open for quantum computation. And the three steps do not yet meet:
**universality alone does not give equivalence**, because a universal computer runs incorrect models
as readily as correct ones. What is needed is the theorem (obligation O2, §6)

  `Correct(M) ⟹ ∃ E_M, O_QLF ∘ E_M = O_M`,

an encoding of a correct model `M` that preserves its observable distinctions, its dynamics and its
probability distributions, with `O` the observable map. `ObsEquiv` supplies `O_QLF`; extending its
domain to `N` bodies and the entangled sector, and building `E_M` non-circularly, is the work. Until
then the equivalence is the conjecture's predicted consequence, not a theorem. It also carries two
named premises:

- **The solution is computable.** This is Deutsch's physical Church–Turing principle (1985). With
  A10 (no measurement yields a real number) it is well supported, but it is a premise, and a solution
  that used an uncomputable resource would fall outside the argument.
- **Equivalence is observational, not internal.** Two solutions that agree on every closure can still
  differ in what they say happens between closures. That is why Bohm, Everett and ZFA are not
  separated by any experiment ([Completeness_Evidence.md](Completeness_Evidence.md) §5): QLF does not
  claim to be the only internal story, only that every correct story is equivalent to it where
  anything can be checked.

So the anthropic principle does not add a conjecture. It is A01 read from inside: whatever explains
our observations explains closures, and QLF computes closures. What it would buy, once O2 is proved,
is equivalence of observable consequences without equivalence of the competing theories' internal
representations. It connects to the holographic reconstruction problem (issue
[#296](https://github.com/rhovision-org/quantum-logical-framework/issues/296)), conservative return
([ScientificApproach.md](ScientificApproach.md) §5e) and the capacity limits of
[Law_Of_Exceptions.md](Law_Of_Exceptions.md).

---

## 4. Testing a model

A *model* is any theory that says which processes happen: a hidden-variable theory, a gate set, a
logic, a folding rule, one of QLF's own candidate readings. QLF tests it in four steps.

1. **Encode.** Map the model's states and processes to histories, and its predicted events to
   closures.
2. **Check the encoding can fail.** The encoding must keep apart what the model distinguishes. An
   encoding that makes every input ZFA tests nothing: `qlf_universality` sends every edge to a
   cancelling pair, so it is ZFA for any edge list whatever, and it is bookkeeping (P10 in
   [Principles.md](Principles.md)). This is the review rule that an oracle must be one the
   construction could fail.
3. **Run.** Either the closures the model predicts exist (the model is **realizable**), or the model
   forbids a closure the substrate exhibits, or requires an event that cannot close (the model is
   **refuted in the substrate**).
4. **Carry the verdict to the world.** A substrate verdict becomes a verdict about nature only through
   a known fact (§2) or a bridge, and it names which.

A test returns one of five verdicts, each relative to stated conditions (an alphabet, a capacity, an
observational domain):

| Verdict | Meaning | How it is established |
|---|---|---|
| **Necessary** | Every admissible realization satisfies the proposition | A theorem over all histories in the domain |
| **Possible** (realizable) | At least one admissible realization exists | A witness: possibility, never uniqueness ([Law_Of_Exceptions.md](Law_Of_Exceptions.md)) |
| **Impossible** (refuted) | No admissible realization exists under the conditions | A theorem, or exhaustion of a finite domain |
| **Equivalent** | Two models are indistinguishable in a stated observational domain | `ObsEquiv` or a proved bijection of observables |
| **Undetermined** | The computation or proof available does not decide it | The default; stated with what was tried |

Two errors this table blocks. **Failing to find a closure is not impossibility**: a search to depth `d`
that finds nothing returns *undetermined* unless the domain is finite and exhausted. And **finding a
closure is not necessity**: it shows the model happens in some way, not that nature does it that way.
Finite-capacity verdicts are bounded by the Law of Exceptions: every finite closure capacity has an
exception at a greater one (P12), so an *impossible* proved at capacity `R` says nothing beyond `R`
unless the theorem is capacity-free.

### Verdicts so far

In the table below, *refuted* means **impossible** and *realizable* means **possible**.

| Model | Verdict | Anchors |
|---|---|---|
| Local hidden variables (factorizable response functions) | **Refuted.** Their CHSH value is at most 2; a QLF joint closure reaches `2√2`, as observed in loophole-free tests (Hensen et al., *Nature* 526, 682, 2015) | `chsh_factorizable_le` ([`QLF_PerspectiveLocality`](lean/QLF_PerspectiveLocality.lean)); `singlet_chsh` ([`QLF_JointClosure`](lean/QLF_JointClosure.lean)); `twistChsh_tsirelson` ([`QLF_Tsirelson`](lean/QLF_Tsirelson.lean)) |
| Non-contextual value assignments | **Refuted** (Kochen–Specker, in the 18-vector form of Cabello, Estebaranz and García-Alcaine 1996) | `no_choice_fixed_in_advance` ([`QLF_QuantumComputer`](lean/QLF_QuantumComputer.lean)) |
| A continuum of distinguishable states in a bounded region | **Refuted**, given A12 | `no_continuum_in_finite_region` ([`QLF_Realizability`](lean/QLF_Realizability.lean)) |
| Free duplication of a closure | **Refuted in the substrate**: identical copies are Pauli-blocked, and a realizable copy pays `log 2` | `identical_copy_pauli_blocked`, `duplication_pays_log_two` ([`QLF_NoFreeDuplication`](lean/QLF_NoFreeDuplication.lean)) |
| A computable predictor of every program's halting | **Refuted** (Turing's halting theorem) | `no_computable_superdeterministic_theory` ([`QLF_QuantumComputer`](lean/QLF_QuantumComputer.lean)) |
| Boolean circuits | **Realizable**, with the substrate's own gates | `fredkin_complete` |
| Logics without weakening | **Realizable and separated**: their models contain time loops; QLF's histories satisfy weakening and have none | `loopWorld_has_time_loop`, `histories_are_a_model` ([`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean)) |
| Universal quantum computation in the substrate | **Undetermined** (O1, §3) | |

The tester also refutes QLF's own candidates, and those results stay on the record: the contact-order
prediction of folding rates ([Protein_Folding.md](Protein_Folding.md) §5e), an every-epoch
`Ω_Λ = log 2` ([Cosmological_Constant.md](Cosmological_Constant.md)), and three gluon carrier states
([Carbon_Superconductivity.md](Carbon_Superconductivity.md) §37). A tester that only passes its own
models would not be one.

Several of these verdicts are classical theorems (Bell, Kochen–Specker, Turing) proved here in Lean.
What QLF adds is not the theorem but the other side of the comparison: the closure that the refuted
model forbids, built from the one conjecture. Rival classes that others have already excluded are
collected in [Completeness_Evidence.md](Completeness_Evidence.md) §4a.

---

## 4a. Computing by closure

Two proved results suggest a way of computing that does not prescribe an algorithm. The shortest
continuation that closes a history has length exactly its imbalance, `min_{c : F(hc)=0} |c| = F(h)`
(`closing_cost_exact`), and every ordering of that minimal completion closes (`completion_perm_closes`,
both in [`QLF_QuantumComputer`](lean/QLF_QuantumComputer.lean)). So a problem can be stated as its
**unresolved distinctions**, and the substrate supplies an admissible closure:

  problem → algorithm → solution  becomes  problem → logical obligations → admissible closure.

This is what `/solve` does ([QucalcSearch.md](QucalcSearch.md)). The limit has to stay attached: the
theorem solves *conjugate imbalance*, not arbitrary constraint satisfaction, and encoding a hard
problem as a closure can carry all of its hardness into the encoding
([P_vs_NP_QLF.md](P_vs_NP_QLF.md)). Which useful problems (composition, optimization, constraint
satisfaction, collective inference) can be stated directly as closure obligations is a research
programme (O4, §6), not a result.

---

## 5. What would change this framing

- A persistent event that needs non-zero free action refutes the conjecture itself (§1).
- If a known fact in §2 turns out to rest on a conjecture, every result that uses it becomes
  conditional, and its row moves to **Bridge**.
- If a result is found to need an assumption not listed here, it is either derived, added as a named
  known fact or bridge, or withdrawn. It is never kept with the assumption unstated.

---

## 6. Registered obligations

The framing creates proof obligations as well as wording. Each is registered here and in
[Principles.md](Principles.md) §C; none is claimed proved.

| ID | Obligation | Principles |
|---|---|---|
| O1 | **Native gates on a common qubit.** One encoding `E` and native `T_U` with `T_U(E ψ) ~ E(Uψ)` for Hadamard, the weighted rotation and controlled-Z; decisive test: the Bell state by native operations (§3) | C26 |
| O2 | **The anthropic equivalence theorem.** `Correct(M) ⟹ ∃ E_M, O_QLF ∘ E_M = O_M`, with `ObsEquiv` extended to `N` bodies and the entangled sector (§3a) | C27 |
| O3 | **A generic, non-circular model-encoding interface.** A typed interface for "encode a model as closures" whose instances must be able to fail, returning one of the five verdicts (§4) | C28 |
| O4 | **Closure-oriented programming.** Which problems can be posed as closure obligations, and at what cost (§4a) | C29 |
| O5 | **Necessity proofs for the structural choices** of §2, or their retention as named choices | P01, B08, B09 |
| O6 | **Machine-checkable consistency** between this page, [Principles.md](Principles.md), [Claim_Status.md](Claim_Status.md) and the axiom footprints, extending [`scripts/axiom_audit.sh`](scripts/axiom_audit.sh) beyond axiom names to semantic dependencies | — |

Related: [Principles.md](Principles.md) · [ScientificApproach.md](ScientificApproach.md) ·
[Universe_Quantum_Computer.md](Universe_Quantum_Computer.md) ·
[Theory_Of_Everything.md](Theory_Of_Everything.md) · [Claim_Status.md](Claim_Status.md)
