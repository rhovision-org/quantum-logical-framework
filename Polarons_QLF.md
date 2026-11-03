# Polarons in the Quantum Logical Framework

> Part of the [**Quantum Logical Framework (QLF)**](README.md). QLF treats physical reality as finite histories that persist by **Zero Free Action (ZFA)** closure; this page applies that substrate to polarons. New readers can start with [`README.md`](README.md) or [`Introducing_QLF.md`](Introducing_QLF.md).

> **Status:** **substrate mechanism machine-verified; physical polaron identification still open.** [`QLF_Polarons`](lean/QLF_Polarons.lean) proves that an open impurity plus a bath can form one irreducible shared ZFA closure, that bath openness is forced by shared closure, that the bath exactly compensates the impurity's signed action on all four axes, that Pauli closure follows from balance, and that a prime non-factorizable witness exists. What remains open is the bridge from these closure classes to the measured Fröhlich/Landau–Pekar and Bose-polaron spectra.

A **polaron** is normally described as an impurity or charge carrier dressed by excitations of its surrounding medium. In a polar crystal the medium response is phononic; in an ultracold Bose gas it is the collective response of the condensate. QLF asks whether the same phenomenon can be described without making either the impurity or the dressing field fundamental.

The proposed answer is:

\[
\boxed{\text{open impurity history} + \text{bath response} \longrightarrow \text{one composite ZFA closure}.}
\]

The impurity alone carries unresolved free action. The bath contributes complementary directional history. When the joint history closes, the impurity and its dressing are no longer two independent objects: they are one irreducible shared closure. In this reading, **the polaron is the closure, not a bare particle plus an added cloud**.

See [`README.md`](README.md) for the QLF premise, [`QuCalc.md`](QuCalc.md) for composite histories, [`BOSE-EINSTEIN-CONDENSATE.md`](BOSE-EINSTEIN-CONDENSATE.md) for the repo's condensate shared-prefix model, [`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) for lattice closure counting, and [`Particles.md`](Particles.md) for the particle-as-closure ontology.

---

## Why this document now — Laurent Simons and the “new state of matter” announcement

A widely circulated 2026 announcement asks whether **Laurent Simons** had found a “new state of
matter.” The scientifically precise story is even more relevant to QLF: Simons' doctoral work at the
University of Antwerp studied **Bose polarons in superfluids and supersolids** — an impurity that
becomes inseparable from the collective excitations of an ultracold quantum medium.

The age in the viral retelling varies with when the work is being described. The University of
Antwerp records Simons' public PhD defense, *Bose polarons in superfluids and supersolids*, on
17 November 2025; popular coverage describes him as **15** at the defense. His first supersolid-polaron
paper had already been submitted in July 2024, while the research program was underway.

The peer-reviewed result is not that a new elementary substance was discovered. The underlying
**supersolid** is already an exotic state of matter, combining crystalline order with superfluidity.
Simons, Wouters and Tempere asked what happens when an impurity is placed inside that state. Their
2025 *Physical Review B* paper found that the impurity is dressed by the supersolid excitations; at
strong impurity–atom coupling the calculated polaron radius can localize to a single droplet, so the
object behaves like a small solid-state polaron. A companion *Physical Review Research* paper showed
that its optical response carries signatures of the supersolid excitation spectrum, including the
two Goldstone-mode Van Hove singularities.

That is exactly why the result is interesting from the QLF side. The experimental/theoretical object
is neither a bare impurity nor the medium alone. It is a **composite dressed state whose identity
belongs to the impurity-plus-environment system**. QLF already has a native discrete object with that
form:

\[
\boxed{
\text{open impurity}
+
\text{open bath response}
\longrightarrow
\text{one irreducible shared ZFA closure}.
}
\]

The new Lean module [`QLF_Polarons.lean`](lean/QLF_Polarons.lean) proves that this composite-closure
structure exists in the QLF substrate and that it has the required irreducibility properties. What it
does **not** yet prove is that Simons' supersolid polaron is quantitatively the same closure class.
That is now the concrete bridge to test: reproduce the supersolid-polaron localization, branch
structure and optical spectrum from the QLF closure census without inserting them by hand.

**Announcement and external anchors:** the popular hook is Nap Theory's [*Did This 15-Year-Old Just Find a New State of Matter?*](https://www.youtube.com/watch?v=IeNBid9X5dw). The scientific anchors are the University of Antwerp's [*Bose polarons in superfluids and supersolids* PhD defense](https://www.uantwerpen.be/en/about-uantwerp/faculties/faculty-of-science/news-and-calendar/phd-defences/public-defences-2025/) (17 Nov 2025); Laurent H. A. Simons, Michiel Wouters & Jacques Tempere, [*Polarons in supersolids: Path-integral treatment of an impurity in a one-dimensional dipolar supersolid*](https://doi.org/10.1103/PhysRevB.111.054524), **Physical Review B 111, 054524 (2025)**; and Laurent H. A. Simons et al., [*Optical response of the supersolid polaron*](https://doi.org/10.1103/kl1y-pj63), **Physical Review Research 7, L032033 (2025)**.

---

## What is now proved specifically for polarons

The new module [`QLF_Polarons.lean`](lean/QLF_Polarons.lean) packages the existing closure machinery
into a polaron-specific theorem set. Its key result is not merely that a composite closure is possible,
but that the **dressing structure follows from the minimal definition**.

Let

```lean
IsPolaron impurity bath :=
  ¬ countBalanced impurity ∧ countBalanced (impurity ++ bath)
```

Then Lean proves:

- `polaron_bath_open` — if the impurity is open and the joint history closes, the bath is necessarily open too;
- `isPolaron_iff_coupled` — the minimal definition is equivalent to the full coupled-sector statement: neither factor closes alone, but the pair does;
- `polaron_actions_compensate` — the bath carries the exact negative signed action of the impurity on all four twist axes;
- `polaron_pauli_closed` — joint ZFA balance automatically puts the fold in the Pauli-scalar sector;
- `polaron_has_prime_prefix` — every closing impurity+bath history has a prime first closure;
- `prime_polaron_no_early_closure` — a prime polaron has no earlier nonempty ZFA prefix;
- `prime_polaron_first_closure_unique` — that first closure is unique;
- `polaronClass_eq_of_equiv` — equal ledger+fold closure tokens define one reportable polaron class;
- `demo_prime_polaron` / `demo_nonfactorizable` — the concrete `^ | v` pair is a prime, genuinely coupled witness;
- `prime_polaron_exists` — at least one irreducible, non-factorizable composite closure of the required form exists;
- `polaron_substrate_summary` — bundles openness of both factors, joint balance, Pauli closure and irreducibility.

These are **machine-verified substrate theorems**, not a derivation of a laboratory polaron. The
physical bridge is now sharply localized: show that the closure classes and their coherent census
reproduce the observed polaron branches, scaling and strong-coupling effective mass.

---

## Existing QLF substrate already proved

The polaron proposal does **not** need to invent its closure mechanics. Several pieces are already
machine-verified elsewhere in the repository:

| Existing result | What it buys the polaron model | Status |
|---|---|---|
| **Joint closure = exact compensation** — `countBalanced_append_iff` | if impurity `I` and bath response `B` close together, the signed action vector of `B` is exactly the negative of `I` on every axis | **Proved**, [`QLF_Discoveries2026`](lean/QLF_Discoveries2026.lean) |
| **Balance implies Pauli closure** — `count_balanced_pauli_closed` | the joint history does not need a second independent “Pauli closed” assumption; count balance already forces the fold into the Pauli-scalar sector | **Proved**, [`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean) |
| **Coupled closures really exist** — `shared_closure_not_factorizable` | two open factors can form one joint closure even though neither factor closes independently; this is the exact structural pattern required for dressing | **Proved**, [`QLF_IndexedFactors`](lean/QLF_IndexedFactors.lean) |
| **First closure is unique** — `prime_prefix_exists`, `prime_prefix_unique` | an “irreducible polaron” can be defined as a **prime** joint closure, eliminating histories that already closed earlier | **Proved**, [`QLF_FirstReturn`](lean/QLF_FirstReturn.lean) |
| **Prime closures can be counted exactly** — `card_fiber_prime`, `walkCount_eq_sum_prime` | branch weights can be based on first-return closures rather than arbitrary raw continuations | **Proved**, [`QLF_FirstReturn`](lean/QLF_FirstReturn.lean), [`QLF_ProductWalk`](lean/QLF_ProductWalk.lean) |
| **Closed-state quotient** — `closureToken`, `ClosureEquiv` | different microscopic bath histories can be grouped only when they have the same ledger **and** fold, giving a principled definition of a polaron branch/class | **Proved**, [`QLF_ClosureEquivalence`](lean/QLF_ClosureEquivalence.lean) |
| **Closure renewal** — `closure_renewal` | after the composite closes, its closing futures are the vacuum's up to one retained sign, giving a precise sense in which the composite can behave as one reusable quasiparticle event | **Proved**, [`QLF_ClosureRenewal`](lean/QLF_ClosureRenewal.lean) |
| **Depth = maximum excursion** — `closureDepth_eq_maxExcursion` | supplies an exact discrete depth variable for self-trapping tests **in the gauge-free phase submodel** | **Proved with scope restriction**, [`QLF_ClosureDepthLaw`](lean/QLF_ClosureDepthLaw.lean) |
| **Coherent signed census** — `signed_mode_at_balance` | spectroscopy should ultimately use coherent/signed closure weight, not unsigned multiplicity alone | **Proved**, [`QLF_StationaryPhase`](lean/QLF_StationaryPhase.lean) |

A particularly useful existing demonstration is `joint_closure_allows_unequal_components` in
[`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean): two open histories of **different lengths**
neither close alone, yet their concatenation closes. It is not a polaron model, but it proves that the
substrate already admits the exact kind of unequal-component composite closure a dressed impurity needs.

---

## 1. What has to be reproduced

Any QLF account of polarons has to recover at least these established features.

| Target | Established physics | QLF target | Status here |
|---|---|---|---|
| **Dressing** | An impurity couples to collective modes of a medium and becomes a quasiparticle | impurity prefix and bath response form one joint closure | **Proposed mapping** |
| **Fröhlich weak/intermediate coupling** | continuum electron–phonon model with a coupling parameter | number/phase of admissible bath completions supplies the effective coupling census | **Open derivation** |
| **Landau–Pekar strong coupling** | strong-coupling energy and effective mass are governed by Pekar/Landau–Pekar asymptotics | deep shared closures should produce a large effective inertia/fold depth | **Phenomenological target** |
| **Attractive and repulsive Bose polarons** | both branches are observed in ultracold Bose gases | opposite bath-response sectors of the same impurity closure problem | **Proposed mapping** |
| **Universal Bose-polaron scaling** | recent homogeneous-BEC measurements collapse onto bath density plus a dimensionless interaction variable | normalized closure census should collapse onto the same reduced variables | **Open quantitative test** |
| **Self-localization / trapping** | sharp self-trapping is *not* generic in generalized Fröhlich models; pinning or other non-Fröhlich structure can create sharp behavior | a discrete fold-depth jump is a distinct QLF prediction, and therefore a falsifier unless its domain is stated | **Prediction / open** |

The last row is deliberately restrictive. QLF should not claim that a discontinuous self-trapping transition is already a known Fröhlich result. The proposed fold-depth jump must either be derived in a more specific lattice/pinning model or fail.

---

## 2. The QLF construction

Let `I` be an impurity history prefix and `B` a bath response. In QuCalc language both are finite strings over the eight twists

```text
^ v < > / \ + -
```

with the conjugate pairs

```text
^ ↔ v,  < ↔ >,  / ↔ \,  + ↔ -.
```

The impurity is *open* when it still carries free action:

\[
F(I) > 0.
\]

A bath completion `B` dresses the impurity when the **joint** history reaches ZFA:

\[
F(I \circ B)=0.
\]

For twist histories that is already enough to obtain structural Pauli closure:
`count_balanced_pauli_closed` proves that every count-balanced joint history folds to a Pauli scalar.
The fold condition is therefore a **theorem downstream of balance**, not a second polaron postulate.

The minimal proposed predicate is consequently

\[
\operatorname{Polaron}(I,B)
\iff
F(I)>0 \;\land\; F(I\circ B)=0.
\]

For the stronger claim made by this page — that the dressed object is an **irreducible shared history** —
use the first-return condition as well:

\[
\operatorname{PrimePolaron}(I,B)
\iff
\neg ZFA(I) \;\land\; \neg ZFA(B)
\;\land\;
\operatorname{IsPrime}(I\circ B).
\]

`IsPrime` is already defined in [`QLF_FirstReturn`](lean/QLF_FirstReturn.lean), where first closure is
proved to exist and be unique. This makes “irreducible” operational: neither factor is a physical
closure by itself, and the combined history closes for the first time as one event.

The exact compensation law is also already proved:
[`countBalanced_append_iff`](lean/QLF_Discoveries2026.lean) says the bath's signed action vector must
be the negative of the impurity's on **every axis**. There is no independently real deformation field
that later attaches to a particle; the environment supplies the complementary distinctions required
for one physical closure.

### 2.1 Crystal polaron

For a crystal, `B` is the directional history supplied by a lattice distortion. Different phonon configurations correspond to different closure completions of the same open impurity prefix. The standard Fröhlich coupling is then to be recovered as the continuum rendering of how strongly the impurity census is connected to those lattice completions.

### 2.2 Bose polaron

For an impurity in a Bose-Einstein condensate, the bath already has the shared-prefix organization described in [`BOSE-EINSTEIN-CONDENSATE.md`](BOSE-EINSTEIN-CONDENSATE.md). The impurity does not acquire an independent cloud in this reading; it joins and deforms the condensate's shared closure history. An attractive or repulsive branch should correspond to distinct closure sectors of that same joint impurity–bath problem.

---

## 3. Confluence is the binding mechanism

QLF needs no separate polaron force. The proposed binding mechanism is **shared closure plus confluence**: the bath exactly compensates the impurity ledger, while many microscopic completions may land in the same physical closure class. The class itself should be defined by [`ClosureEquiv`](lean/QLF_ClosureEquivalence.lean), which preserves both the ledger and the ordered Pauli fold rather than quotienting histories by count alone.

If

\[
\mathcal C(I)=\{B : \operatorname{Polaron}(I,B)\},
\]

then the native QLF observable is the closure inventory

\[
W_I = |\mathcal C(I)|
\]

or, when phases matter, the corresponding signed/coherent sum rather than the unsigned count.

This gives a concrete computational program:

1. fix an impurity prefix `I`;
2. enumerate bath continuations at bounded depth/capacity;
3. retain only joint ZFA + Pauli closures;
4. quotient completions by the joint closure invariant;
5. record closure depth, multiplicity, phase and branch label;
6. compare the resulting spectra with the Fröhlich and Bose-polaron observables.

**Important:** multiplicity is a frequency statistic, not the event-priority rule. First closure remains the QLF priority rule; this page uses the census to characterize how often each composite polaron closure occurs.

---

## 4. Strong coupling and the Landau–Pekar limit

In the strong-coupling Fröhlich problem the polaron becomes heavy. Modern mathematical results establish the Pekar strong-coupling energy structure and the Landau–Pekar effective-mass asymptotics; in particular the effective mass grows as the fourth power of the coupling in the strong-coupling limit.

QLF's candidate reading is geometric rather than field-theoretic: stronger impurity–bath coupling forces closure through a deeper, more distributed joint history. If the effective inertial delay of a closure is controlled by its fold depth/capacity, then a strong-coupling polaron should be heavier because more bath history is inseparable from one impurity translation.

That is a **bridge hypothesis**, not yet a derivation. A successful QuCalc model must recover the known strong-coupling asymptotics rather than merely reproduce the qualitative statement "more dressing means more mass."

Pre-registered target:

\[
m_{\mathrm{eff}}(\alpha) \propto \alpha^4
\qquad (\alpha\to\infty)
\]

up to the known Landau–Pekar coefficient after the substrate-to-continuum calibration is specified.

---

## 5. Bose polarons: the cleanest experimental test

Ultracold gases provide a particularly direct target because the impurity–bath interaction can be tuned and the spectrum measured.

Experiments have observed attractive and repulsive Bose polarons. More recent measurements in a homogeneous condensate found a single attractive branch on the attractive side, strong broadening near resonance, and on the repulsive side both a repulsive-polaron branch and an attractive many-body branch. The dynamics show universal scaling controlled by bath density and a dimensionless interaction parameter.

For QLF this suggests an unusually sharp test:

### B1 — branch count

The bounded joint-closure census should produce one dominant closure family in the weak attractive regime and two distinguishable families on the repulsive side when the experimental branch split occurs.

### B2 — universal reduction

After converting substrate depth/energy to the experimental units, spectra computed at different bath densities should collapse under the same reduced variables used experimentally. If extra substrate parameters are required, the claimed universality has failed.

### B3 — quasiparticle breakdown

Near resonance the experiment shows strong broadening. In QLF language the prediction is not that closure disappears, but that no single closure class dominates the listening: weight spreads across many joint completions. The quasiparticle can fail while the closure census remains well defined.

---

## 6. Self-trapping: a QLF prediction, not a borrowed result

A tempting discrete picture is that increasing coupling eventually forces the impurity into a deeper closure shell:

\[
R_* \longrightarrow R_*+1.
\]

Because closure depth is integer-valued, that change would be discontinuous even when the continuum coupling is varied smoothly. QLF would then render self-trapping as a **fold-depth jump** rather than as a singular continuum field.

But this cannot be advertised as a generic recovery of the Fröhlich model. Gerlach and Löwen proved analyticity results excluding a genuine self-trapping phase transition for a broad class of generalized Fröhlich models. Therefore the QLF claim has to be one of the following:

- the depth jump occurs only when additional lattice/pinning structure is present;
- the apparent jump becomes a continuum crossover after the rendering map is applied; or
- the QLF model is wrong.

This is a useful kill condition. The QuCalc census should decide which of the three occurs before the wording is strengthened.

---

## 6a. Proof and demonstration ladder

The fastest way to strengthen this document is to close the polaron-specific gap in this order.

### P1 — exact shared-closure theorem

Define a twist-level `CoupledPolaron I B` as

```lean
¬ countBalanced I ∧
¬ countBalanced B ∧
countBalanced (I ++ B)
```

and prove immediately that the bath exactly compensates the impurity using
`QLF_Discoveries2026.countBalanced_append_iff`. This is mostly a packaging theorem over an existing
result, but it anchors the ontology in the actual twist algebra.

### P2 — Pauli closure comes for free

From the joint balance proof, derive

```lean
∃ p : PauliScalar,
  twistMatrixFold (I ++ B) = pauliScalarToMatrix p
```

directly with `count_balanced_pauli_closed`. This removes an unnecessary assumption from the current
sketch.

### P3 — irreducibility / first return

Define a **prime polaron** by requiring `FirstReturn.IsPrime (I ++ B)`. Then the existing
`prime_prefix_unique` theorem gives a unique first closure. This is the clean proof of the phrase
“irreducible shared history.”

### P4 — branch classes from the closure quotient

Use `closureToken = (ledger, fold)` and `ClosureEquiv` to group microscopic bath completions.
Only after that quotient should the resulting classes be compared with the experimental
**attractive** and **repulsive** branches. This prevents a branch label from being put in by hand.

### P5 — exact finite census

A new `polaron_census.py` should enumerate a fixed impurity prefix against bounded bath words and
report, for every coupling rule:

- first-return length;
- closure token / equivalence class;
- unsigned multiplicity;
- signed/coherent amplitude;
- factorized versus genuinely coupled sector;
- capacity/depth where applicable.

Cross-check the raw balanced-history totals against
[`QLF_ProductWalk`](lean/QLF_ProductWalk.lean) and the first-return totals against
[`QLF_FirstReturn`](lean/QLF_FirstReturn.lean). That turns the simulation from a bespoke script into a
regression against proved combinatorics.

### P6 — self-trapping only after the gauge-free restriction is explicit

The existing theorem `closureDepth_eq_maxExcursion` applies to **gauge-free** phase histories. A
fold-depth self-trapping claim should therefore first be tested in a crystal/phonon submodel satisfying
that hypothesis. Extending the depth law to general eight-twist histories would be a separate theorem;
without it, a general polaron depth jump is not yet licensed.

### P7 — strong-coupling mass requires the mass bridge

Before testing `m_eff ∝ α^4`, specify the QLF observable that is being called effective mass.
[`Higgs.md`](Higgs.md) and [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) tie mass to
constructing delay/fold depth, but that identification is not yet a polaron effective-mass theorem.
The decisive quantitative result would be a derived map

\[
\text{joint closure statistic} \longrightarrow m_{\rm eff}
\]

that approaches the Landau–Pekar `α^4` asymptotic without fitting a new exponent.

---

## 7. Minimal QuCalc experiment

A first simulation does not need a full material model. It only needs to test whether the proposed composite-closure mechanism produces the right qualitative branch structure.

```python
# sketch, not yet committed as an implementation
for g in couplings:
    closures = []
    for bath in enumerate_bath_histories(max_depth=R, coupling=g):
        h = impurity_prefix + bath
        if achieves_zfa(h) and is_pauli_closed(h):
            closures.append({
                "history": h,
                "depth": closure_depth(h),
                "phase": fold_phase(h),
            })

    spectrum[g] = quotient_and_count(closures)
```

The first report should contain **inventory before interpretation**:

- number of joint closures at each coupling;
- first closure depth;
- modal depth;
- signed/coherent weight by closure class;
- whether one or two persistent branch families are present;
- whether any depth discontinuity survives increasing the capacity cutoff.

Only after that census should labels such as "attractive," "repulsive," or "self-trapped" be attached.

---

## 8. Lean target

The formal target can be kept small because most of the substrate mechanics is already proved. No continuum polaron Hamiltonian is needed for the first theorem.

```lean
def CoupledPolaron (impurity bath : List Twist) : Prop :=
  ¬ countBalanced impurity ∧
  ¬ countBalanced bath ∧
  countBalanced (impurity ++ bath)

def PrimePolaron (impurity bath : List Twist) : Prop :=
  CoupledPolaron impurity bath ∧
  QLF.FirstReturn.IsPrime (impurity ++ bath)
```

The first useful theorems should reuse the existing core rather than re-prove it:

```lean
theorem polaron_pauli_closed
    (h : CoupledPolaron impurity bath) :
    ∃ p : PauliScalar,
      twistMatrixFold (impurity ++ bath) = pauliScalarToMatrix p :=
  count_balanced_pauli_closed h.2.2

theorem polaron_actions_compensate
    (h : CoupledPolaron impurity bath) :
    -- bath net action = negative impurity net action on all four axes
    _ :=
  (QLF.Discoveries2026.countBalanced_append_iff impurity bath).mp h.2.2
```

Then add the polaron-specific layer:

- classify `PrimePolaron` histories by [`ClosureEquiv`](lean/QLF_ClosureEquivalence.lean);
- count first-return fibers using [`QLF_FirstReturn`](lean/QLF_FirstReturn.lean);
- compare unsigned and signed weights using [`QLF_StationaryPhase`](lean/QLF_StationaryPhase.lean);
- prove or refute a depth-jump theorem under a precisely stated **gauge-free** coupling rule;
- connect the counted spectrum to a continuum observable only through a named bridge.

---

## 9. What would count as evidence

| Result | Interpretation |
|---|---|
| QuCalc produces the experimental branch topology with no branch-specific patch | evidence for the composite-closure mapping |
| Reduced spectra collapse with bath density + one interaction variable | evidence for the proposed universal census |
| Strong-coupling effective inertia approaches the Landau–Pekar scaling | quantitative bridge evidence |
| A claimed fold-depth jump disappears as capacity increases | **QLF self-trapping conjecture rejected/superseded** |
| A robust jump remains only with a pinning/lattice term | supports a restricted, non-generic self-trapping claim |
| No joint-closure census reproduces attractive/repulsive branch structure | composite-closure model falsified |

The standard is the same as elsewhere in the repository: construction proves possibility, exact census establishes the discrete result, and only a separately tested bridge licenses a physical identification.

---

## Internal QLF crosslinks

This page sits at the intersection of several existing QLF threads:

- [`README.md`](README.md) — QLF overview and proof-status conventions.
- [`QuCalc.md`](QuCalc.md) — the eight-twist history language and composite closures.
- [`QLF_Polarons`](lean/QLF_Polarons.lean) — polaron-specific shared-closure, compensation, Pauli and prime-first-closure theorems.
- [`QLF_Discoveries2026`](lean/QLF_Discoveries2026.lean) — exact opposite-action condition for joint closure.
- [`QLF_IndexedFactors`](lean/QLF_IndexedFactors.lean) — product versus coupled sectors and non-factorizable shared closure.
- [`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean) — count balance implies Pauli closure.
- [`QLF_FirstReturn`](lean/QLF_FirstReturn.lean) — prime/irreducible first closures and their exact census.
- [`QLF_ClosureEquivalence`](lean/QLF_ClosureEquivalence.lean) — principled quotient into physical closure classes.
- [`QLF_ClosureRenewal`](lean/QLF_ClosureRenewal.lean) — how a completed closure acts on future continuations.
- [`QLF_ClosureDepthLaw`](lean/QLF_ClosureDepthLaw.lean) — exact depth/excursion law in its gauge-free domain.
- [`QLF_StationaryPhase`](lean/QLF_StationaryPhase.lean) — coherent signed closure weights.
- [`BOSE-EINSTEIN-CONDENSATE.md`](BOSE-EINSTEIN-CONDENSATE.md) — condensate shared-prefix model used by the Bose-polaron case.
- [`Chemistry.md`](Chemistry.md) — shared closure as the emergent-matter binding motif.
- [`Protein_Folding.md`](Protein_Folding.md) — exact closure census plus explicit failed bridges and kill conditions.
- [`Higgs.md`](Higgs.md) / [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) — current QLF mass/delay interpretation needed before claiming an effective-mass derivation.
- [`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) — lattice/condensed-matter closure tests and status discipline.
- [`FlowChart.md`](FlowChart.md) — domain 11 placement in Emergent Matter.

---

## 10. References

- Nap Theory, “Did This 15-Year-Old Just Find a New State of Matter?” (2026). https://www.youtube.com/watch?v=IeNBid9X5dw
- University of Antwerp, “Bose polarons in superfluids and supersolids — Laurent Simons,” public PhD defense, 17 November 2025. https://www.uantwerpen.be/en/about-uantwerp/faculties/faculty-of-science/news-and-calendar/phd-defences/public-defences-2025/
- H. Fröhlich, “Electrons in lattice fields,” *Advances in Physics* **3**, 325–361 (1954). DOI: https://doi.org/10.1080/00018735400101213
- R. P. Feynman, “Slow Electrons in a Polar Crystal,” *Physical Review* **97**, 660–665 (1955). DOI: https://doi.org/10.1103/PhysRev.97.660
- B. Gerlach and H. Löwen, “Analytical properties of polaron systems or: Do polaronic phase transitions exist or not?”, *Reviews of Modern Physics* **63**, 63 (1991). DOI: https://doi.org/10.1103/RevModPhys.63.63
- M. Brooks and R. Seiringer, “The Fröhlich polaron at strong coupling: Part I — The quantum correction to the classical energy,” *Communications in Mathematical Physics* **404**, 287–337 (2023). DOI: https://doi.org/10.1007/s00220-023-04841-3
- M. Brooks and R. Seiringer, “The Fröhlich polaron at strong coupling: Part II — Energy-momentum relation and effective mass,” *Publications Mathématiques de l’IHÉS* **140**, 271–309 (2024). DOI: https://doi.org/10.1007/s10240-024-00150-0
- N. B. Jørgensen *et al.*, “Observation of Attractive and Repulsive Polarons in a Bose-Einstein Condensate,” *Physical Review Letters* **117**, 055302 (2016). DOI: https://doi.org/10.1103/PhysRevLett.117.055302
- M.-G. Hu *et al.*, “Bose Polarons in the Strongly Interacting Regime,” *Physical Review Letters* **117**, 055301 (2016). DOI: https://doi.org/10.1103/PhysRevLett.117.055301
- J. Etrych *et al.*, “Universal Quantum Dynamics of Bose Polarons,” *Physical Review X* **15**, 021070 (2025). DOI: https://doi.org/10.1103/PhysRevX.15.021070

---

## Status

**Established externally:** Fröhlich polarons, strong-coupling Pekar/Landau–Pekar behavior, attractive and repulsive Bose-polaron branches, and universal Bose-polaron scaling.

**Machine-verified in QLF:** the polaron substrate pattern itself — open impurity + open bath + irreducible joint ZFA closure; exact four-axis compensation; Pauli closure from balance; unique prime first closure; closure-class quotienting; and an explicit non-factorizable witness (`QLF_Polarons`).

**Physical identification:** still a **proposed bridge**. The theorem proves that QLF contains the exact composite-closure structure required for dressing; it does not yet prove that experimental polarons instantiate that structure.

**Open:** derive the continuum Fröhlich/Pekar limits from the closure census; derive the Bose-polaron attractive/repulsive branch structure quantitatively; derive the strong-coupling effective mass; determine whether a genuine discrete fold-depth transition exists and in what domain.

**Falsifier:** failure of the joint-closure census to reproduce the observed branch/scaling structure without ad hoc branch-specific rules.