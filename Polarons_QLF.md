# Polarons in the Quantum Logical Framework

> **Status:** proposed QLF composite-closure model with established experimental targets. The external polaron physics cited here is standard or experimentally observed; the QLF identification of a polaron with a particular class of shared ZFA histories is a model to be tested, not yet a Lean theorem.

A **polaron** is normally described as an impurity or charge carrier dressed by excitations of its surrounding medium. In a polar crystal the medium response is phononic; in an ultracold Bose gas it is the collective response of the condensate. QLF asks whether the same phenomenon can be described without making either the impurity or the dressing field fundamental.

The proposed answer is:

\[
\boxed{\text{open impurity history} + \text{bath response} \longrightarrow \text{one composite ZFA closure}.}
\]

The impurity alone carries unresolved free action. The bath contributes complementary directional history. When the joint history closes, the impurity and its dressing are no longer two independent objects: they are one irreducible shared closure. In this reading, **the polaron is the closure, not a bare particle plus an added cloud**.

See [`README.md`](README.md) for the QLF premise, [`QuCalc.md`](QuCalc.md) for composite histories, [`BOSE-EINSTEIN-CONDENSATE.md`](BOSE-EINSTEIN-CONDENSATE.md) for the repo's condensate shared-prefix model, [`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) for lattice closure counting, and [`Particles.md`](Particles.md) for the particle-as-closure ontology.

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

A bath completion `B` dresses the impurity when the joint history closes:

\[
F(I \circ B)=0
\]

together with the structural Pauli/fold closure required by QLF. The proposed polaron predicate is therefore

\[
\operatorname{Polaron}(I,B)
\iff
F(I)>0 \;\land\; F(I\circ B)=0 \;\land\; \operatorname{PauliClosed}(I\circ B).
\]

This is intentionally a **joint** predicate. There is no independently real deformation field that later attaches to a particle. The environment supplies the complementary distinctions required for one physical closure.

### 2.1 Crystal polaron

For a crystal, `B` is the directional history supplied by a lattice distortion. Different phonon configurations correspond to different closure completions of the same open impurity prefix. The standard Fröhlich coupling is then to be recovered as the continuum rendering of how strongly the impurity census is connected to those lattice completions.

### 2.2 Bose polaron

For an impurity in a Bose-Einstein condensate, the bath already has the shared-prefix organization described in [`BOSE-EINSTEIN-CONDENSATE.md`](BOSE-EINSTEIN-CONDENSATE.md). The impurity does not acquire an independent cloud in this reading; it joins and deforms the condensate's shared closure history. An attractive or repulsive branch should correspond to distinct closure sectors of that same joint impurity–bath problem.

---

## 3. Confluence is the binding mechanism

QLF needs no separate polaron force. The proposed binding mechanism is **confluence**: many open continuations of `I` enter the same composite closure class once the bath is included.

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

The formal target can be kept small. No continuum polaron Hamiltonian is needed for the first theorem.

```lean
structure PolaronWitness where
  impurity : List Twist
  bath     : List Twist
  impurity_open : ¬ countBalanced impurity
  joint_balanced : countBalanced (impurity ++ bath)
  joint_closed : PauliClosed (impurity ++ bath)

def IsPolaron (impurity bath : List Twist) : Prop :=
  (¬ countBalanced impurity) ∧
  countBalanced (impurity ++ bath) ∧
  PauliClosed (impurity ++ bath)
```

Suggested first theorem:

```lean
theorem polaron_is_composite_closure
    (h : IsPolaron impurity bath) :
    countBalanced (impurity ++ bath) ∧
    PauliClosed (impurity ++ bath) :=
  ⟨h.2.1, h.2.2⟩
```

That theorem is intentionally modest. The scientifically interesting Lean work would come next:

- define a bath-response equivalence class;
- prove conjugation maps attractive/repulsive candidate sectors appropriately, if it does;
- define closure depth for the joint history;
- prove or refute a discrete depth-jump theorem under a precisely stated coupling rule;
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

## 10. References

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

**Already available in QLF:** finite twist histories, open prefixes, ZFA closure, Pauli closure, composite histories, closure depth/capacity and multiplicity machinery.

**Proposed here:** identify a polaron with an impurity–bath composite ZFA closure.

**Open:** derive the continuum Fröhlich/Pekar limits from the closure census; derive the Bose-polaron branch structure quantitatively; determine whether a genuine discrete fold-depth transition exists and in what domain.

**Falsifier:** failure of the joint-closure census to reproduce the observed branch/scaling structure without ad hoc branch-specific rules.