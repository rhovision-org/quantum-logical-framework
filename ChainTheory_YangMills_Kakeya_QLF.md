# Chain Theory, the strong force and Kakeya: what QLF proves about the autumn-2026 results

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

Three results reached a general audience in October 2026 (Turing Post, *Attention Span*):

1. **Chain Theory** (Alex Wissner-Gross) obtains the fine-structure constant from quantum entanglement.
2. **OpenAI** says its models proved that four-dimensional quantum Yang–Mills theory and QCD exist.
3. **OpenAI** also says its models proved Sogge's local smoothing conjecture in every dimension, which
   would settle the Kakeya and restriction conjectures, and refuted the Exponential Time Hypothesis (ETH).

This note asks what QLF has **machine-verified** that bears on each one. It sorts every statement into
the status labels of [ScientificApproach.md](ScientificApproach.md): *proved* (Lean, no `sorry`),
*conjecture*, *open bridge*, or *no connection*. The external results are reported as their authors state
them. None of the three has finished independent review, and OpenAI has withheld the physics proofs.

**Summary.**

| Result | What QLF has proved that bears on it | Status of the connection |
|---|---|---|
| Chain Theory's α | Its value lies inside QLF's proven census band and respects QLF's screening bound. It is distinguishable from QLF's own `w = ½` prediction by more than `0.0038`. New module [`QLF_ChainTheory`](lean/QLF_ChainTheory.lean) | **Proved compatibility, not support.** The two derivations differ, and no rational weighting of QLF's census reaches Chain Theory's number (§1.4) |
| Yang–Mills existence | Discrete colour structure: confinement as the singlet-closure obstruction, the `SL(2,3)` colour flux, su(3) closure. The gap side is one axiom, measured as definitional | **No overlap yet.** An existence proof would discharge part of what QLF's `yang_mills_gap` assumes, not the gap (§2) |
| Kakeya / local smoothing | Nothing | **No connection.** The finite-field Kakeya theorem is a natural new target (§4.3) |
| ETH refuted | `QLF_PvsNP` makes no ETH claim | **Unaffected.** A false ETH is compatible with P ≠ NP (§3) |

---

## 1. Chain Theory and α

### 1.1 What Chain Theory claims

Chain Theory starts from one axiom: nothing exists except finitely many maximally entangled pairs of
finite-dimensional systems, and some are known only by distilling them
([announcement](https://theinnermostloop.substack.com/p/chain-theory),
[compendium](https://alexwg.org/publications/ChainTheoryCompendium.pdf),
[talk](https://alexwg.org/publications/ChainTheoryTalk.pdf)). The electromagnetic link is a **qutrit
maximally entangled with a qubit**. A weighted count over its 172 measurement records gives

```
α(0) = (79 + 48√2 + 42√3 + 3√6) / 31104,      α⁻¹ = 137.035999189566…
```

CODATA 2022 gives `137.035999177(21)`, so the value is 0.6σ away and matches ten significant figures.
The author says the formula is a theorem of the axiom plus "a few stated readings", and that it is checked
in Lean. **The identification of this number with α(0) is stated as a conjecture.** An independent audit
([chain-theory-audit](https://github.com/SproutSeeds/chain-theory-audit)) reproduces the count. It finds
the value 1.4σ from unexpanded CODATA inputs. Of 1,492,992 combinations of the alternatives the paper lists,
only the published one lies within 1σ. It also flags a tension between the photon identification and the
program's own charge assignment and weak angle.

### 1.2 What QLF already had (proved, before this note)

From [Alpha.md](Alpha.md) and [Alpha_Residual.md](Alpha_Residual.md):

- **The leading value `α⁻¹ = 128 + 9 = 137`.** `2⁷` comes from the 8-twist alphabet and `d² = 9` from the
  three spatial axes. It is the only `d` that gives 137
  ([`QLF_FineStructureSubstrate`](lean/QLF_FineStructureSubstrate.lean) `only_3d_substrate_gives_137`;
  [`QLF_AlphaRigidity`](lean/QLF_AlphaRigidity.lean) `alpha_unique`).
- **The screening bound `α⁻¹ > 137`**, because EM is abelian and every correction screens
  ([`QLF_AlphaBound`](lean/QLF_AlphaBound.lean) `alpha_inv_gt_137`).
- **A two-sided census band** `137.0159 < α⁻¹ < 137.0481`, in exact closed forms `263 − 16√62` and
  `(217 + 512√62)/31` (`irreducibleCap_eq`, `alphaInvCap_eq`, `censusTail_eq`, all with no axiom).
- **The structural prediction `α⁻¹ = 137.032`** at equal weight `w = ½`. This is about 5 significant
  figures. The last `~0.004` is the continuum vacuum-polarisation running, which QLF does not derive
  ([Alpha_Residual.md](Alpha_Residual.md) §2a, §9c).

### 1.3 What is now proved ([`QLF_ChainTheory`](lean/QLF_ChainTheory.lean), no axioms)

| Theorem | Statement |
|---|---|
| `ctAlphaInv_bounds` | `137.03599 < α⁻¹_CT < 137.03601` |
| `ct_above_leading` | `α⁻¹_CT > 137`: Chain Theory's value respects QLF's screening bound |
| `ct_in_census_band` | `137 + 1/64 < α⁻¹_CT < (217 + 512√62)/31`: it lies inside QLF's census band |
| `equalWeight_closed_form` | QLF's `w = ½` prediction is exactly `135 + 8√62/31` (≈ 137.032002) |
| `ct_separated_from_equalWeight` | `α⁻¹_CT − (135 + 8√62/31) > 0.0038` |
| `ct_denominator_factor`, `qlf_leading_factor` | `31104 = 2⁷·3⁵` and `137 = 2⁷ + 3²` |

What this proves: the two programs **do not contradict each other**. Chain Theory's number is inside every
bound QLF has proved. What it does not prove: that QLF supports Chain Theory's derivation. A band
`0.032` wide contains many numbers, and passing it is weak evidence (rule 4 of the working method in
[CLAUDE.md](CLAUDE.md): the claim changes no count of ways). The `2⁷`/`3` factorisations are arithmetic.
Both programs build α from the primes 2 and 3, but nothing here shows the same mechanism.

### 1.4 Where they differ (stated precisely)

- **Number fields.** Every exact closed form QLF's census produces for α lies in `ℚ(√62)`. Chain Theory's
  value is an irrational element of `ℚ(√2, √3)`. These fields meet only in `ℚ`, because `62 = 2·31` is
  not a square times 1, 2, 3 or 6. So **no rational weighting of QLF's two census tails gives Chain
  Theory's number exactly.** If QLF were to reach it, the route would need a census sector carrying
  `√3`, a qutrit, which the present α census does not have. (This is standard field theory, checked by
  hand. It is not yet in Lean.)
- **Precision.** QLF claims about 5 significant figures as a structural prediction. Chain Theory claims 10
  as a theorem of its axiom plus readings. The audit's census of alternatives (one hit in ~1.5 million) is
  the right test of how much those readings carry. QLF applies the same test to itself
  ([Alpha_Residual.md](Alpha_Residual.md) §0a, the discovery/confirmation firewall).
- **Foundation.** Chain Theory postulates entangled pairs. QLF assumes only that nature is logical and
  treats ZFA closures as one model ([Philosophy.md](Philosophy.md) §3d). Both are finite and discrete.
  Both reject a continuum at the base ([TheContinuum.md](TheContinuum.md)).

### 1.5 Structural parallels that are already proved

These are QLF theorems that touch Chain Theory's ingredients. They are parallels, not derivations of its
formula.

- **The 8-twist alphabet carries both a qubit and a qutrit.** The twists' unit-determinant folds form the
  quaternion group `Q₈ ⊂ SU(2)`, the qubit side ([`QLF_Pauli`](lean/QLF_Pauli.lean),
  [`BraKetRhoQuCalc`](lean/BraKetRhoQuCalc.lean) `weak_isospin_su2`). The same eight twists are exactly
  the eight nonzero vectors of `F₃²`, the Weyl qutrit (`colVec_injective`, `colVec_surjective` in
  [`QLF_ColourFlux`](lean/QLF_ColourFlux.lean)). Together they generate `SL(2,3)`, checked exactly in
  [colour_flux.py](colour_flux.py). Chain Theory's elementary link is a qutrit⊗qubit pair.
- **Entanglement as shared closure.** Two histories close together iff their action vectors are opposite
  on every axis (`countBalanced_append_iff`), and an open child forces an open partner (`forced_sharing`),
  both in [`QLF_Discoveries2026`](lean/QLF_Discoveries2026.lean). Chain Theory's monogamy constraint
  plays the corresponding role.
- **The ℤ₆ quotient.** Chain Theory gets the Standard Model group with its ℤ₆ quotient from changes of
  basis on its links. QLF tried a "spin × colour = ℤ₆" reading and **retired** it, because the plaquette
  `−1` is fermion parity, not the doublet bit ([Carbon_Superconductivity.md](Carbon_Superconductivity.md)
  §29). This is a real difference between the programs, not a match.

---

## 2. The strong force and Yang–Mills

### 2.1 What OpenAI claims

On 26 October 2026 OpenAI said its models produced a rigorous proof that certain four-dimensional quantum
field theories exist, including pure Yang–Mills and QCD
([The Next Web](https://thenextweb.com/news/openai-exponential-time-hypothesis-false-kakeya-yang-mills),
[Unite.AI](https://www.unite.ai/openai-says-its-models-produced-three-proofs-in-math-cs-and-physics/),
[Xenospectrum](https://xenospectrum.com/en/openai-yang-mills-kakeya-eth-release/)). David Gross leads a
group with Douglas, Jaffe, Klebanov and Nekrasov that will write it up. **The physics proofs are withheld**
for now, and the reports do not say whether the mass gap is addressed. The Clay problem
([Clay Mathematics Institute](https://www.claymath.org/millennium/yang-mills-the-maths-gap/)) asks for two
things: existence of the theory on ℝ⁴ satisfying the Wightman/Osterwalder–Schrader axioms, **and** a
positive mass gap. The claim, as reported, is the first.

### 2.2 What QLF has proved about the strong force

All with no QLF axiom unless noted:

- **Confinement as an obstruction.** Any annihilation-odd signed charge, colour included, is zero on every
  ZFA closure. So a net-coloured state is not a closure (`charged_not_closed`, `singlet_closure`,
  [`QLF_Confinement`](lean/QLF_Confinement.lean)). This is *qualitative* confinement. The string tension
  and the linear potential are open.
- **The colour ℤ₃ and its flux.** Cyclic relabelling of the axes preserves baryon number
  (`baryon_cyc_invariant`, [`QLF_BaryonWinding`](lean/QLF_BaryonWinding.lean)). With the axis cycle as a
  transport primitive, twists on distinct axes have uniform symplectic product 1 (`flux_uniform`), and a
  colour line around a plaquette picks up a `2π/3` phase (`colour_plaquette`,
  [`QLF_ColourFlux`](lean/QLF_ColourFlux.lean)).
- **Quark signature.** The W is one gauge twist and is colour-blind (`colour_blind_W`). Every word obeys
  `charge3W + nW = 3·kW`, the charge lock (`lock_word`). Carriers are curvature: a bracket is nonzero iff the axes differ
  (`bracket_iff_distinct_axes`), all in [`QLF_QuarkSignature`](lean/QLF_QuarkSignature.lean).
- **su(3) algebra** facts: traceless commutators, non-abelian generators
  ([`QLF_StrongAlgebra`](lean/QLF_StrongAlgebra.lean)).
- **Asymptotic freedom** `b₀ = 7 > 0` for `N_c = 3`, `n_f = 6`
  ([`QLF_BetaFunction`](lean/QLF_BetaFunction.lean)). The `11` in `b₀` is **imported** standard group
  theory, not derived.
- **The hierarchy** `ln(M_P/m_p) = 14π` follows from `α_s(M_P) = 1/49`, which is a **posit**
  ([`QLF_AlphaS`](lean/QLF_AlphaS.lean)).

### 2.3 What QLF has about the mass gap

- **Proved:** `gaugeMassGap = log 2 > 0`, and the lightest closure carries exactly that free-energy quantum
  (`mass_gap_quantum_pos`, `lightest_closure_is_gap_quantum`, [`QLF_MassGap`](lean/QLF_MassGap.lean)).
  The dispersion side: a massless lattice field is gapless at zero momentum and a massive one has rest gap
  `m²` ([`QLF_MassGapDispersion`](lean/QLF_MassGapDispersion.lean)).
- **One axiom, `yang_mills_gap`.** It bundles the continuum theory's gap together with its identification
  as `log 2`. The repo has already **measured** it as definitional: `continuumGap_nonempty` builds a model
  by `rfl`. So in Lean it excludes nothing, and its content is the interpretation
  ([CLAUDE.md](CLAUDE.md) axiom inventory).
- **The census does not show a spectral gap.** The unsigned closure walk returns like `8^L/L²` (massless).
  The signed π-flux census has a continuous band edge. `log 2` is an *information* quantum per closure,
  not an energy gap ([YangMills_MassGap_QLF.md](YangMills_MassGap_QLF.md) §7). This is a negative result
  and it stands.

### 2.4 How the two fit

If OpenAI's existence proof holds up, it supplies the continuum object that `yang_mills_gap` presupposes.
That would discharge part of what the axiom assumes. It would not supply the gap or its identification
with `log 2`. QLF's discrete results (confinement as singlet closure, the `SL(2,3)` colour structure) are
lattice-side and do not touch a continuum existence proof. **No QLF theorem supports or is supported by
OpenAI's claim today.** Whether the construction passes through a lattice and a reflection-positive transfer
matrix decides whether QLF's discrete side can connect. We will know when the proof is released.

---

## 3. ETH, Kakeya and local smoothing

- **ETH.** OpenAI says a model refuted the Exponential Time Hypothesis, with a released Lean proof. Russell
  Impagliazzo, Ramamohan Paturi and Ryan Williams are reviewing it. QLF makes **no ETH claim**.
  [`QLF_PvsNP`](lean/QLF_PvsNP.lean) proves the count of balanced histories (`C(2n,n)`) and the
  verify-filter identity. Its one axiom, `qlf_cost_model`, is P ≠ NP-shaped and already measured as
  constraining nothing about polynomial time ([P_vs_NP_QLF.md](P_vs_NP_QLF.md)). A false ETH is
  compatible with P ≠ NP, so nothing in QLF is contradicted. The "exponential tree" language in
  [P_vs_NP_QLF.md](P_vs_NP_QLF.md) is about counts of histories, not running time.
- **Kakeya.** Wang and Zahl proved the Kakeya set conjecture in three dimensions in 2025
  ([arXiv:2502.17655](https://arxiv.org/abs/2502.17655v1)). OpenAI says its models proved local smoothing in
  every dimension, which would imply Kakeya and restriction in every dimension; a write-up and Lean proof
  are released. **QLF has no theorem that bears on this.** It is harmonic analysis on ℝⁿ, which QLF treats
  as a rendering. QLF does not claim a connection.

---

## 4. New ways to get results in QLF

The developments suggest four concrete routes. Each is stated with what would count as success and as
failure, per [ScientificApproach.md](ScientificApproach.md).

### 4.1 A qubit⊗qutrit closure census for α

Chain Theory's α comes from one qutrit–qubit link. QLF's alphabet already *is* a qubit (`Q₈`) and a qutrit
(`F₃² \ {0}`) at once (§1.5). QLF's α census so far counts closures of the qubit side only, which is why
its closed forms live in `ℚ(√62)` (§1.4). The route: count closures with the `SL(2,3)` transport, where
qutrit phases enter, and see whether `√3` appears in the exact tail. **Pre-register** the weighting rule
before evaluating. Chain Theory's audit shows how sharply the readings matter: one hit in ~1.5 million
combinations. **Success:** a census-derived closed form in `ℚ(√2,√3)` with no weight chosen after seeing
the value. **Failure:** `√3` never appears, or appears only with a chosen weight.

### 4.2 Reflection positivity, the missing Yang–Mills step

Chain Theory's Lean work proves that maximally entangled links across a mirror are Osterwalder–Schrader
reflection positive (after Lieb 1989). QLF has the mirror already: a history joined to its mirror always
closes (`mirror_closes`, [`QLF_Discoveries2026`](lean/QLF_Discoveries2026.lean);
`equal_and_opposite_balances`, [`QLF_HandedLoops`](lean/QLF_HandedLoops.lean)), and time reversal is the
Hermitian adjoint ([Reversibility.md](Reversibility.md)). What QLF lacks is a reflection-positivity theorem
for its transfer matrix. That is the step that turns a lattice theory into a Hilbert space with a
Hamiltonian, and so the step that would let a discrete gap say anything about a continuum one. It is a
finite, decidable Lean target. **Success:** RP for the closure transfer matrix on a finite slab.
**Failure:** a counterexample, which would itself be informative about the π-flux sign structure.

### 4.3 Finite-field Kakeya

Dvir (2008) proved that a set in `F_qⁿ` containing a line in every direction has at least `C_n·qⁿ` points,
by the polynomial method. A finite substrate is where Kakeya is native, and the statement is a lower bound
on a count, which is the form rule 1 of the working method asks for. **QLF has no Kakeya result today.**
This is a candidate for a self-contained Lean module, of interest in its own right. It would not claim to
bear on the real-variable problem.

### 4.4 Lean as the shared language

All three external programs released or announced Lean proofs. QLF's results can be compared with them
theorem by theorem rather than in prose, as `QLF_ChainTheory` does. When OpenAI's physics proofs are
released, the first check is whether their construction has a lattice stage, and if so whether it is
reflection positive (§4.2).

### 4.5 Rational processes, not irrational limits

Irrational numbers are not in reality; they name the limits of rational processes. The test case is
Hofstadter's butterfly, defined only at rational flux and built from phase-weighted closure counts. QLF's
proved π and 2π/3 fluxes are its `q = 2` and `q = 3` points. It is pre-registered and run in
[Hofstadter_Butterfly_QLF.md](Hofstadter_Butterfly_QLF.md).

---

## 5. Honest scope

- **Proved here:** the numerical placement of Chain Theory's α against QLF's bounds
  ([`QLF_ChainTheory`](lean/QLF_ChainTheory.lean), no axioms).
- **Proved before, reused:** QLF's α band, the colour structure, confinement as singlet closure, and the
  `log 2` closure quantum.
- **Checked by hand, not in Lean:** the number-field separation of §1.4.
- **Not claimed:** that QLF derives Chain Theory's formula or supports its mechanism. That QLF proves or
  supports Yang–Mills existence or a mass gap. Any link to Kakeya, local smoothing or ETH.
- **External claims** are as reported on 26–28 October 2026 and are under review. OpenAI's physics proofs
  are not public.

## References

- A. Wissner-Gross, *Chain Theory* (2026): [announcement](https://theinnermostloop.substack.com/p/chain-theory),
  [compendium](https://alexwg.org/publications/ChainTheoryCompendium.pdf),
  [talk](https://alexwg.org/publications/ChainTheoryTalk.pdf).
- SproutSeeds, *chain-theory-audit* (2026): [GitHub](https://github.com/SproutSeeds/chain-theory-audit).
- OpenAI announcement of Yang–Mills/QCD existence, local smoothing and ETH (26 Oct 2026), as reported by
  [The Next Web](https://thenextweb.com/news/openai-exponential-time-hypothesis-false-kakeya-yang-mills) and
  [Unite.AI](https://www.unite.ai/openai-says-its-models-produced-three-proofs-in-math-cs-and-physics/).
- H. Wang & J. Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three
  dimensions* (2025): [arXiv:2502.17655](https://arxiv.org/abs/2502.17655v1).
- Z. Dvir, *On the size of Kakeya sets in finite fields*, J. Amer. Math. Soc. **22** (2009) 1093–1097.
- E. H. Lieb, *Two theorems on the Hubbard model*, Phys. Rev. Lett. **62** (1989) 1201.
- K. Osterwalder & R. Schrader, *Axioms for Euclidean Green's functions*, Comm. Math. Phys. **31** (1973) 83–112.
- CODATA 2022: `α⁻¹ = 137.035999177(21)`.
