# Strange loops and the two-phase bridge discipline

**Status:** conceptual and methodological note (Paper I v0.3 companion), not a new theorem, not a physical bridge closure, and not empirical evidence.

**Short version.** A strange loop is a level-crossing self-reference that returns to its starting level after an apparent ascent. QLF already contains a controlled example: its proofs are checked in Lean + Mathlib, while ordinary mathematics is then exhibited as what the substrate does. That loop is not vicious because the finitary content is conservative over the `RCA₀` core. The same shape is a useful **constraint** on the still-open formal-to-physical bridges: a bridge that presents itself as self-referential must exhibit a conservative return to a finite record, or it remains **`B-OPEN` / `INCOMPLETE`**. The strange-loop reading does not replace the G3 checklist and does not promote any physical claim.

---

## 1. What a strange loop is here

Hofstadter's strange loop is a hierarchy in which a move upward through levels unexpectedly returns to the level it started from. The return is not a syntactic contradiction; it is a **level-crossing self-reference**. The useful question is not "is self-reference allowed?" but "what makes the return conservative rather than vicious?"

QLF's answer has two parts:

1. **The loop must be typed.** Name the formal level, the physical or semantic level, the map between them, and the level to which the loop returns.
2. **The return must be conservative.** The finitary content claimed at the top must already be available at the bottom. If the return imports the conclusion, the loop is circular; if it proves a genuinely new finitary fact, the loop is not a loop but a one-way bridge.

A strange loop is therefore a **shape constraint**, not a fifth evidence gate. G3 remains the gate. The constraint sharpens G3 by asking what a non-circular return would look like.

---

## 2. The two-phase loop QLF already has

The closest controlled example is the relation between QLF's metatheory and its generated mathematics. It has two phases.

### Phase 1 — the metalanguage

The substrate rules are written and kernel-checked in Lean 4 + Mathlib. Lean is the **metalanguage** in which QLF's claims are verified. This is ordinary object-theory/metatheory separation, not yet a circularity: every formal system is checked in some metatheory.

### Phase 2 — the substrate re-derives the ink

Ordinary mathematics then reappears as what the substrate does:

- counting closures gives `ℕ`;
- the two folds give `+` and `×`;
- the fold target gives `μ₄ = (ℤ[i])ˣ`;
- commutators give `su(2)`/`su(3)`;
- the continuum is the completion/rendering of the discrete.

The full ladder is in [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §1, and the bootstrapping resolution is §2 of that document.

### Why the loop is not vicious

The safeguard is **conservativity**. The finitary content provable with the continuum apparatus is already provable in the `RCA₀` base; `WKL₀` is conservative for `Π⁰₂` statements (Friedman/Harrington). Using Mathlib's rendered algebra to certify a finitary substrate fact therefore proves nothing the computable base did not already prove. The slogan is: **borrow the pen, re-derive the ink.**

Two further qualifications keep this honest:

- **The concrete tell is that nothing is imported.** No substrate type imports its group or ring laws. `PauliScalar`'s group laws are proved from the fold; the additive `count_*_append` laws are proved from concatenation; the substrate's fold target is exhibited as the standard cyclic group of order four in [`QLF_AlgebraEmergence`](lean/QLF_AlgebraEmergence.lean).
- **The residue is the universal one.** QLF does not prove the consistency of its own metatheory. By Gödel's second incompleteness theorem, no consistent system strong enough for arithmetic does. The regress is relocated to the smallest defensible floor — finite computation — not eliminated. The full scope statement is [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §2.

The loop is therefore a **self-consistent fixed point**: the verifier is an instance of what it verifies, and the trust that remains is "finite computation is sound," not "ZFC + the continuum + choice is sound."

---

## 3. Observer loops are not time loops

The observer/consciousness layer has the same shape. An observer is a finite, terminating, self-referential **Markov blanket**: it models itself, its environment, and their interaction, and its ZFA closures synthesize its local time and world. The relevant documents are [`Philosophy.md`](Philosophy.md) §3d, [`Time.md`](Time.md) §7a, [`Hadrons_Markov_Blankets.md`](Hadrons_Markov_Blankets.md), and [`Consciousness.md`](Consciousness.md).

The crucial distinction is between **possibility** and **record**:

- **Loops live in possibility.** The reversible closure algebra admits loops. In a logic without weakening, a two-state world can have an eventful time loop (`loopWorld_has_time_loop`, `weakening_fails_in_loopWorld`).
- **Realized histories do not loop.** An event is a step at which some new fact holds; no chain of events returns to its start (`no_time_loops_from_logic`). States that each follow the other hold exactly the same facts (`loop_same_facts`). Add finite construction, and every causal interval is finite (`logical_world_globally_hyperbolic`). QLF's histories satisfy both (`histories_are_a_model`, `histories_finite_pasts`), all in [`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean).

So an observer's self-model can be a strange loop in the **possibility algebra** without being a closed timelike curve in the **realized history**. The loop is pruned where facts become records. That is the precise sense in which QLF has self-reference without time travel.

---

## 4. The strange-loop reading of the open bridges

A physical bridge is a map from substrate structure to an observable, with domain, codomain, preservation conditions, a probability/outcome rule, and a defeater. The G3 checklist in [`Proof_to_Physics.md`](Proof_to_Physics.md) and Paper I v0.3 §11.2 states the minimum. The strange-loop reading adds one question:

> **What returns?** If the bridge claims a loop, name the finite record to which it returns and show that the return is conservative. If no such record can be exhibited, mark the bridge `B-OPEN` / `INCOMPLETE`.

The four Paper I bridge cases then read as follows.

| Bridge | Levels | What would return | Current status | Defeater |
|---|---|---|---|---|
| **MO2 → optical apparatus / Malus `1/8`** | formal MO2 lattice → toy `ℂ²` projector embedding → ideal polarizer → detector outcome | the finite lattice/closure count realized by the same substrate that produces the polarizers | **`B-OPEN` / `INCOMPLETE`: first-order `F+N` established; return incomplete.** The finite MO2 laws are `F`; the `1/8` is imported ideal Malus/Born optics. The toy embedding is not an operational map. | A circular angle/detector map; a non-preserving embedding; a calibrated mismatch under a frozen apparatus map. |
| **α count → renormalized coupling** | 8-twist census → residual weight/multiplicity → renormalized coupling at a stated scale → CODATA comparison | the formal comparator-residual band and the leading count, with the scale map fixed before comparison | **`B-OPEN` / `INCOMPLETE`: first-order `F+N` established; return incomplete.** Leading `137` and the formal band are `F`; `137.032` is reported/structural, not re-derived; the multiplicity/resummation is open. | A post-hoc `w`, an undeclared scale/scheme, or a confirmed α variation. |
| **SPARC RAR** | public SPARC data → closure-balance RAR → `a₀ = cH₀/(2π)` → residual summary | a predeclared, information-isolated prediction scored once | **`B-OPEN` / `INCOMPLETE`: first-order `N` established; return incomplete.** The benchmark is retrospective and target-informed; the self-seal is not an independent chronology. | A failed independent replication, a reproduced mismatch, or an `H₀`/M-L dependence that removes the result. |
| **Born uniqueness (Gaussian-integer register)** | Gaussian-integer amplitude register → unit-way refinement → ZFA closure/event → operational probability | the finite unit-way count that the uniqueness theorem quantifies over, realized as a physical refinement | **`B-OPEN` / `INCOMPLETE`: first-order `F` established; return incomplete.** `born_from_ways` and `assignment_unique` prove the finite characterization; `refine` is a premise, and no theorem shows QLF dynamics performs an amplitude-preserving physical refinement. | A refinement rule that assumes the target Born weights; a detector comparison that fails under a frozen map. |

The same test applies to the merged metric-singlet/lattice-Einstein result and to Manifestation: their exact statements are `F`, but neither supplies the physical `g` map. They strengthen the ToE claim map; they do not close G3.

**Incomplete vs inconclusive.** The four rows above are `INCOMPLETE`: their first-order `F`/`N` results and comparators stand, but the operational map or conservative return is missing. `INCONCLUSIVE` is reserved for a comparator that exists but is ambiguous or fails to discriminate. “Incomplete” is not a denial of the first-order success; it names the missing higher-order closure.

### What the loop does not do

- It does **not** make `1/8` a QLF prediction. The ideal-optics comparator remains imported.
- It does **not** identify the 8-twist count with the measured coupling at a scale.
- It does **not** turn the retrospective SPARC benchmark into a prospective test.
- It does **not** derive the Born rule from detector physics; it names the missing refinement step more sharply.

The only non-circular bridge is one whose formal level is already a realized subsystem of the physical level it describes. That is a **working criterion**, not a theorem. It is the criterion the G3 checklist operationalizes.

---

## 5. A concrete ledger entry: Born refinement as a loop candidate

The cleanest place to encode the loop in the claim-record ledger is the Born rule. The finite theorem is:

- `QLF.BornFromWays.born_from_ways` — every admissible assignment is `‖ψᵢ‖² / Σⱼ‖ψⱼ‖²`;
- `QLF.BornFromWays.assignment_unique` — the assignment is unique under the declared interface;
- `QLF.BornFromWays.exists_refinement` — the unit-way partition exists mathematically.

The open step is not the algebra. It is the **physical return**: is the refinement process itself a ZFA closure that the uniqueness theorem talks about? If yes, the loop is:

```
Gaussian-integer register
    -> unit-way refinement
    -> ZFA closure / event
    -> detector record
    -> finite unit-way count
```

and the return is conservative only if the detector record is a count of the same unit ways, not a probability law inserted to match the target. The current claim record marks this `B-OPEN`; see [`claim_records/born_rule.json`](claim_records/born_rule.json) and [`Born_Rule.md`](Born_Rule.md) §9.

The same schema — including a `proof_obligation` naming the domain, codomain, forward/return maps, composite identity, imported axioms and falsifier — is attached to `alpha.json`, `sparc_rar.json`, and `three_polarizer.json`. The validator enforces the shape: a `strange_loop` entry must name at least two levels, a return level, a conservative-return statement, a noncircularity witness, a status (`B-OPEN`, `SPECIFIED`, or `TESTED`), and a defeater. A record cannot mark `bridge: CLOSED` unless its loop is `TESTED`.

---

## 6. What must be proved

The strange-loop reading becomes checkable only when it states a proof obligation. The following is the minimal interface; it is a **specification**, not a theorem and not evidence.

### 6.1 The conservative strange-loop bridge interface

Once the relevant categories are specified, a candidate bridge is a pair of structure-preserving maps (functors, in the categorical reading)

```
F : Formal -> Physical
R : Physical -> Formal
```

with:

1. **Conservative return:** `R ∘ F = id` on the finitary `RCA₀` core.
2. **No smuggled continuum:** every finitary theorem used by `F` is already proved in the substrate without the continuum apparatus.
3. **Explicit return witness:** the image under `F` of each MO2 proposition (or Gaussian-integer amplitude) is a ZFA-closed history whose count and phase invariants recover the original formal object.
4. **Visible imports:** every physical/statistical axiom used by `F` or `R` is named.
5. **Falsifier:** a predeclared observation or formal result that would break the return.

Each claim record also carries a `strange_loop.first_order_evidence` field (`F`, `N`, `F+N` or `NONE`) and a `first_order_note`, plus a `proof_obligation` object with `domain`, `codomain`, `forward_map`, `return_map`, `composite_identity_on`, `conservative_return_status` (`NOT_STARTED` / `PARTIAL` / `PROVED`), `proof_artifact`, `imported_axioms` and `falsifier`. MO2 and Born are `PARTIAL` with toy Lean artifacts; α and SPARC remain `NOT_STARTED`. A `TESTED` loop requires `PROVED` plus a real artifact.

The trigger shape itself is now a Lean structure, `QLF.ConservativeReturn.StrangeLoopTrigger`, packaged in `lean/QLF_ConservativeReturn.lean`: its fields are the formal core, closed-history type, closure predicate, `F`, `R`, count/phase maps, composite identity, image closure, and count/phase recovery. `toyTrigger_exists` proves the structure is inhabited on the two-element toy, and `no_event_cycle` proves the toy analogue of `no_time_loops_from_logic`: toy events strictly increase history length, so no event chain returns to its start. This is a machine-checked *predicate*, not an instantiation for any Paper I bridge; every actual bridge still has to supply its own maps and remains `B-OPEN`.

### 6.2 The four concrete obligations

| Bridge | What must be proved | Current status |
|---|---|---|
| **MO2 → Malus `1/8`** | An operational map from the 15 comparable pairs and 24 distributivity failures to the three-polarizer geometry, plus a proof that the induced probability on the image is exactly `1/8` after the map is applied, and that the map conservatively returns the original lattice inequalities. | Toy embedding exists; `QLF_StrangeLoop` proves the interface shape and `QLF_ConservativeReturn` proves the toy count/phase return on a closed twist history; first-order `F+N` established; operational map still open; G3 `INCOMPLETE`. |
| **Born uniqueness** | That refinement additivity in `QLF_BornFromWays` is itself realized by a ZFA closure on the same Gaussian-integer register the theorem quantifies over — the self-referential return. | Finite uniqueness proved; first-order `F` established; `QLF_StrangeLoopBorn` proves the finite unit-way return; physical refinement still a premise. |
| **α residual** | A predeclared, scale-independent multiplicity rule whose leading term is forced by the capacity-horizon bifibration self-similarity, with the residual weight `w = 1/2` derived rather than fitted. | First-order `F+N` established; leading `137` structural; multiplicity/return open. |
| **SPARC RAR** | A blinded, pre-registered prediction of the RAR curve from closure balance alone, on data held out from the original analysis. | First-order `N` established retrospectively; return/prospective test incomplete. |

Any one of these, if proved under the §6.1 interface, would constitute support. Partial results — for example, a return map for the Boolean sublattice only — are valuable if labelled as partial and kept `B-OPEN`.

### 6.3 Minimal next proofs

1. **Lean statement and proof of the interface** — **done as a toy** in `QLF_StrangeLoop.lean` (generic two-element interface) and strengthened in `QLF_ConservativeReturn.lean`, which maps a formal count/phase object to a net-zero twist history and proves `R ∘ F = id`, closure, and count/phase recovery. Both are no-Mathlib/no-axiom and now anchored in the 343-anchor baseline; the claim record remains `PARTIAL` because this is a toy, not the actual operational bridge.
2. **An instantiation for the Born uniqueness theorem** — **partial**: `QLF_StrangeLoopBorn.lean` proves the finite unit-way return on the existing `QLF_BornFromWays` register; the physical refinement remains open.
3. **One blinded numerical check** whose protocol is committed before the numbers are looked up — three-polarizer or α residual. The three-polarizer protocol draft is [`verification/strange-loop/blinded_protocol.md`](verification/strange-loop/blinded_protocol.md); it is `AWAITING_DATA`, not executed.

### 6.4 What is not required

- A general theory of consciousness or Hofstadter-style self-models.
- Collapse of the map/territory distinction; Paper I correctly keeps it open.
- Continuum Gleason or measure-theoretic uniqueness; the finite characterizations already in the repository are the right strength.

Until these proofs exist, the strange-loop reading is a useful organising hypothesis that correctly highlights why the bridges are still incomplete: the first-order `F`/`N` results stand, but the return is missing. It is not yet evidence that they can be closed.

---

### 6.5 Tensor products: the best current near-return

`QLF_TensorFromClosure` is the strongest existing candidate for a nearly complete
conservative bridge. It does not assume the tensor product for the independent
sector. From three premises — each body has its own fold, the joint fold is
multiplicative, and events of distinct independent bodies have no relative order
— it derives commutation, the universal property `composite_is_tensor`, the
two-body realization `tensorEquiv`, and the `N`-body versions
`n_composite_is_tensor` / `nTensorEquiv`.

The proposed reading is:

> **Closure composition is primitive; the tensor product is a conservative
> representation of independent composition.**

The forward direction is largely present:

```
F : ([h_A], [h_B]) ↦ U(h_A) ⊗ U(h_B).
```

The return cannot demand the raw pair of factors. `pair_scalar_ambiguity` exposes
the obstruction:

```
(-I) ⊗ I = I ⊗ (-I).
```

The tensor object does not remember where a common scalar phase was assigned.
The correct target is therefore

```
R ∘ F = id   on closure classes, not syntax.
```

The bottom level should contain only physically meaningful finitary information:
ledger, fold, factor assignment where meaningful, closure status, and
first-closure structure. Word order that the theory declares irrelevant must not
be demanded back.

`QLF_ConservativeReturn.QuotientStrangeLoopTrigger` now formalizes exactly this
shape: a finite class side, a tensor side, a physical equivalence, a forward map
that respects it, and a return that is the identity on classes. The toy instance
`toyQuotientTrigger_exists` checks the shape; it is not the tensor theorem.

**Quotient theorem, now proved.** `QLF_TensorConservativeReturn` instantiates
`QuotientStrangeLoopTrigger` with

- `Core` = `ClosureClass`, two-body histories quotiented by equality of the tensor image,
- `Tensor` = the subtype of `M ⊗[ℂ] M` in the image of `F`,
- `forward` = `forwardImage`,
- `ret` = `R`, choosing a class from an image,
- `coreEquiv` = equality of classes,

and proves `tensor_conservative_return` / `tensorTrigger_exists`. `class_of_step`
shows that interleaving moves land in the same class. This proves the **coherence
of the quotient return**, not that the quotient is the physically selected
closure equivalence, and not the entangled-sector return. It is in the
343-anchor baseline.

For the entangled sector the hierarchy is:

```
primitive shared/independent closure relations
        ↓
H_A ⊗ H_B
        ↓
product or entangled state
        ↓
closure-class invariants
```

The loop closes only if the last step returns the correct substrate distinction.
An entangled state such as the singlet is acceptable as a QLF rendering only when
its return identifies an irreducible shared closure rather than two independently
closed factors. That is a criterion, not a theorem about the singlet yet.

This is a level-crossing in possibility space, not a physical time loop. Toy
events still strictly advance (`no_event_cycle` in `QLF_ConservativeReturn`); the
return is a map between descriptions, not a cycle in the event record.

The general rule suggested by this case is:

> **Every conventional quantum construction should be required to have a
> conservative return to closure.**

Tensor products are the first strong example. The same criterion can later be
applied to Hilbert spaces, unitarity, the S-matrix, poles, zeros and Born
probabilities. It is a test of whether QLF has derived the conventional object
rather than merely translated it.

## 7. The toy observer model

[`tools/strange_loop_observer.py`](tools/strange_loop_observer.py) is a finite toy model, not evidence. It represents a Markov-blanket observer as a subset of MO2 elements and a lattice state, runs a three-stage polarizer sequence, and compares:

- an operational Malus map;
- a pure closure-count model with uniform branch weights;
- the same closure model with different branch weights;
- a blanket that integrates only the first two stages.

The result is deliberately negative: a pure MO2 meet walk gives `0` (it blocks at the second polarizer), while a re-preparation walk reproduces `1/8` only when the branch weights are assumed uniform; other weights with the same lattice pass/block pattern give different transmissions. The lattice alone does not select the Malus weights. The model does not show that a self-referential observer "produces" the optical law; it shows where the operational map would have to enter. Output and scope are in [`verification/strange-loop/`](verification/strange-loop/README.md).

---

## 8. Current status and what would strengthen it

**Already in place:**

- 343-anchor Lean baseline (post-#224/#225/#226/#230), including 17 MO2 and 18 QuantumLogic anchors, 5 metric/lattice anchors, 12 Manifestation anchors, and 24 conservative-return/tensor-return anchors.
- Complete finite MO2 enumeration: 15 comparable pairs, 36/36 orthomodular implications (15 non-vacuous), 24 distributivity failures in each direction; all 19 lattice checks pass.
- α leading value `137`, formal comparator-residual band `(1/64, 0.04814)`, reported structural `137.032`, 0.026% leading agreement.
- `m_p/m_e = 6π⁵`, one-loop `g−2` form, and the other reported entries in Paper I Table 1.
- Born finite uniqueness on Gaussian integers; no continuum or Gleason continuity step.
- `QLF_StrangeLoop.lean` — toy two-element conservative-return interface, no Mathlib/no axioms; in the 343 baseline.
- `QLF_ConservativeReturn.lean` — toy formal → net-zero twist history return with count/phase recovery, trigger/quotient structures and no-event-cycle; no Mathlib/no axioms; in the 343 baseline.
- `QLF_StrangeLoopBorn.lean` — finite unit-way Born return on the existing Gaussian-integer register; in the 343 baseline; physical refinement still `B-OPEN`.
- `no_time_loops_from_logic` and `loop_same_facts` for realized histories; loops in the reversible possibility algebra.

**What would materially strengthen the claim:**

1. **A conservative-return witness for a bridge.** Exhibit a finitary fact at the physical level that is already proved in the `RCA₀` core, with no target-derived input. Until then, the bridge remains `B-OPEN` / `INCOMPLETE`; its first-order `F`/`N` result is not in doubt.
2. **A concrete ledger entry tested, not just specified.** The Born refinement loop is the best candidate. It needs a physical refinement process defined independently of the Born weights, plus a detector comparison that could fail.
3. **A predeclared optical test.** For the three-polarizer case, specify the angle/detector map and the comparator before data; the current `1/8` is an imported ideal-optics illustration.
4. **A prospective SPARC test.** Freeze the selection, `H₀`, M/L and interpolation form, control target access, and score once. The current benchmark is `N`, not `E`.
5. **A scale/scheme map for α.** Predeclare the count-to-coupling map and the residual multiplicity; do not select `w` after seeing CODATA.

These are research tasks, not results. The strange-loop reading makes them sharper; it does not shorten them.

---

## 9. Relation to Paper I v0.3

Paper I v0.3's method contribution is the typed separation:

- **`F`** — audited formal statement;
- **`N`** — reproduced numerical result;
- **`B-OPEN`** — interpretation bridge not yet supplied;
- **`E`** — empirical evidence, not established here.

The strange-loop reading is the conceptual shape of the `B-OPEN` row. It is not a new evidence type and not a promotion rule. The paper's G3 checklist remains authoritative; the loop clause is an additional review question:

> **G3 loop clause.** A bridge candidate must name its levels and its conservative return, or be marked `B-OPEN`. A `bridge: CLOSED` claim requires a `TESTED` loop entry.

The Paper I v0.3 Gist is linked from the [flow chart](FlowChart.md) and the repository's evidence index. The audited snapshot remains [`verification/paper-i-v0.3/`](verification/paper-i-v0.3/README.md).

### 9.1 Map is the territory (issue #213)

[Issue #213](https://github.com/rhovision-org/quantum-logical-framework/issues/213), “Map is the Territory,” is the
interpretive claim that under ZFA the relational rewrite network is not a map of a separate territory; its
self-consistent closed execution *is* the territory. Standard QM and classical physics are then incomplete maps
of that single territory.

The issue already grades the claim correctly:

- **`F` / verified:** the discrete substrate, ZFA closure, MO2, continuum unrealizability, pair structure and
  ER=EPR formal components.
- **`B-OPEN` / conjecture:** the identification “map ≡ territory / entanglements are the only effects.” No
  noncircular map from the formal expression to the physical event has been specified.
- **`E-candidate`:** exclusivity of ZFA, with kill conditions.

That is exactly the gap the conservative-return interface addresses. `TensorConservativeReturn` is a worked
example of the required bridge form:

```
finite closure composition  →  tensor/Hilbert representation
                            →  same finite closure information
                               (on the physical quotient).
```

The checked `R ∘ F = id` on tensor-image classes is a noncircular preservation result for one conventional
construction. It does **not** close “map is the territory”: the physically selected closure equivalence, the
entangled-sector return, and the formal-to-event map remain open. It supplies the form such a bridge must take,
under the same non-circularity and no-time-loop constraints as the rest of this note.


---

## 10. References and internal links

- [`Mathematics_From_QLF.md`](Mathematics_From_QLF.md) §1–§2 — the emergence ladder and the bootstrapping/conservativity resolution.
- [`Philosophy.md`](Philosophy.md) §3d — only logic is assumed; time loops live in possibility.
- [`Time.md`](Time.md) §7a — no time loops in realized histories.
- [`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md) §2 — MO2 and the quantum-logical foundation.
- [`Born_Rule.md`](Born_Rule.md) §8–§9 — the finite uniqueness theorem and the open physical refinement.
- [`Three_Polarizer_Paradox.md`](Three_Polarizer_Paradox.md) — the optical case and the imported Malus law.
- [`Alpha.md`](Alpha.md) — the α derivation programme and its honest scope.
- [`SPARC.md`](SPARC.md) — the retrospective benchmark and its limits.
- [`Claim_Status.md`](Claim_Status.md) — the human-readable claim ledger.
- [`lean/QLF_TensorFromClosure.lean`](lean/QLF_TensorFromClosure.lean) — independent composition derives the tensor universal property; the quotient return `TensorConservativeReturn` is proved in `QLF_TensorConservativeReturn` (in the 343 baseline).
- [`verification/strange-loop/tensor_return_target.md`](verification/strange-loop/tensor_return_target.md) — the explicit `TensorConservativeReturn` target, now `PROVED` as a quotient construction; physical selection remains open.
- [`lean/QLF_ConservativeReturn.lean`](lean/QLF_ConservativeReturn.lean) — `StrangeLoopTrigger` / `QuotientStrangeLoopTrigger`, the toy return and `no_event_cycle`.
- [`Proof_to_Physics.md`](Proof_to_Physics.md) — G3 and the bridge registry.
- [Issue #213](https://github.com/rhovision-org/quantum-logical-framework/issues/213) — “Map is the Territory”: the interpretive claim, graded `B-OPEN`/conjecture; the tensor quotient is a worked bridge form, not a closure.
- [`ScientificApproach.md`](ScientificApproach.md) §5 — the bridge protocol.
- [`claim_records/`](claim_records/README.md) — typed records and the `strange_loop` field.
- [`flowchart_source.md`](tools/flowchart_source.md) / [live FlowChart](https://rhovision-org.github.io/quantum-logical-framework/FlowChart.html) — the navigation map.
- Paper I v0.3 Gist: <https://gist.github.com/jimscarver/71a87155e7e65099c9bfd8ba710462f1>.

**External lineage:** D. Hofstadter, *Gödel, Escher, Bach* (1979) and *I Am a Strange Loop* (2007); K. Gödel (1931); S. G. Simpson, *Subsystems of Second Order Arithmetic* (2009) for `RCA₀`/`WKL₀`; H. Friedman and L. Harrington on conservativity; Friston on Markov blankets.
