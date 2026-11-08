# Radical Simplification of Quantum Mechanics in QLF: the postulate ledger

Part of the [Quantum Logical Framework (QLF)](README.md). Tracking issue:
[#207](https://github.com/rhovision-org/quantum-logical-framework/issues/207).

ZFA is equal and opposite quantum logical action with zero free energy, the principle of QLF.

**The claim, and how to check it.** QLF says the postulates of quantum mechanics are not primitive. Each
is either derived from finite twist histories and ZFA closure, replaced by something simpler, or still
open. "Radical" means *at the root*: the simplification changes the primitives, not the bookkeeping. A
claim like that is only worth something if it can be checked row by row, so this document is a ledger,
not an argument. Every row gives:

- the Lean theorem, if there is one, and the premises it actually uses;
- what the theorem establishes physically, which is often less than its name;
- what would count against the reading.

The ledger audits **both sides**. Standard quantum mechanics is empirically successful, and none of its
postulates is falsified in its domain; what is in question is whether they are fundamental. QLF has
primitives of its own, listed in §3, and the test of the whole programme is §4: does QLF remove an
assumption, or does the assumption come back in through a definition, a premise, a normalization or a
rendering map?

The three layers are kept apart on purpose, because mixing them makes an argument look stronger than it
is:

- **Layer A** (§1): the postulates of quantum mechanics itself.
- **Layer B** (§2): what quantum field theory and its spacetime models add.
- **Layer C** (§3): the primitives QLF needs.

Status labels follow [`ScientificApproach.md`](ScientificApproach.md) §3: **proved** (a Lean theorem,
premises as stated), **exact computation**, **numerical**, **conditional** (proved from a premise that is
not itself derived), **reading** (an interpretation resting on named theorems), **open**, **assumed**.

---

## 1. Layer A: the postulates of quantum mechanics

The formulation compared against is Nielsen and Chuang's four postulates (*Quantum Computation and
Quantum Information*, 2000, §2.2), with measurement split into its three parts and observables and
superposition listed separately, since textbooks differ on whether those are postulates.

| # | Standard postulate | QLF replacement | Lean anchor and premises | Status | What would count against it |
|---|---|---|---|---|---|
| A1 | **State space.** A system is a ray in a complex Hilbert space. | A state is a 2×2 Hermitian `Form`, built from the eight twists. The eight-element alphabet is forced once two spatial axes are distinguishable. | `alphabet_eight_of_two_spatial_axes`, `noncommuting_iff_eight`, `no_six_twist_alphabet` ([`QLF_AlphabetNecessity`](lean/QLF_AlphabetNecessity.lean)). **Premise:** the candidate axes are the Klein four-group `{I, X, Y, Z}` of the Pauli matrices. | **Conditional.** The size is derived; the complex numbers are not (they arrive with `σ_y`). | A system whose states need more than finite tensor products of the spin-½ space. |
| A2 | **Observables** are Hermitian operators; outcomes are eigenvalues. | Every twist is a Hermitian involution, so its outcomes are `±1`. | `twist_unitary` (Hermitian and squares to `I`), [`QLF_ClosureUnitarity`](lean/QLF_ClosureUnitarity.lean). | **Proved for twists**; general observables are assumed Hermitian wherever they appear (e.g. `tsirelson_bound`). | An observable outcome that is not a sum of twist outcomes. |
| A3 | **Dynamics is unitary** (Schrödinger, or Dirac). | Every finite history is unitary. The realizable walk is unitary at every momentum, and its generators are the Weyl and Dirac operators. | `history_unitary`; `realStep_unitary`, `realWalk_unitary`, `rawStep_not_unitary` ([`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean)); `realWalk_generator`, `diracWalk_generator` ([`QLF_DiracWalk`](lean/QLF_DiracWalk.lean)). **Premises:** each twist is unitary; the step keeps only the projector `(1 + M(t))/2`. | **Proved**, with the caveat in §4a. The walk-to-Dirac route is Bialynicki-Birula (1994) and Meyer (1996). | A finite history, or a realizable step, that is not unitary. |
| A4 | **Superposition.** Amplitudes of alternatives add linearly. | Amplitudes are signed sums over histories. Interference zeros are then theorems: structural, or exact cancellations. | `zero_taxonomy`, `antiHermitian_seed_forbidden`; `mixed_channel_zero` ([`QLF_ChannelZeros`](lean/QLF_ChannelZeros.lean)); `cone_amplitude`, `cone_zero_iff` ([`QLF_LightCone`](lean/QLF_LightCone.lean)). **Premise:** the sum over histories is the definition of an amplitude. | **Proved** consequences of a **defined** linearity. | An interference pattern not expressible as a signed sum over finite histories. |
| A5 | **Born rule.** Probability is `\|amplitude\|²`. | Probability counts equal ways: an outcome of norm `m` is `m` unit ways. Separately, a measure with no third-order interference is a squared vector amplitude. | `born_from_ways` ([`QLF_BornFromWays`](lean/QLF_BornFromWays.lean)): **premise** `refine`, that an outcome of norm `m` splits into `m` equal ways. `quadratic_of_third_order_free`, `vector_amplitude_iff` ([`QLF_InterferenceNoGo`](lean/QLF_InterferenceNoGo.lean)): **premise** Sorkin's `I₃ = 0` (Sorkin 1994). | **Conditional.** Both routes are uniqueness theorems; neither premise is yet derived from dynamics. Close in spirit to Zurek's envariance (2005). | A ways-refinement rule other than `\|ψ\|²` that matches experiment, or a measured `I₃ ≠ 0`. |
| A6 | **Measurement** yields one outcome (collapse, or a projection postulate). | A measurement is a closure: a count-balanced history folds to the central point `±I` of its unitary path. No extra collapse dynamics. | `closure_on_unitary_path`, `unitary_history_not_closure` ([`QLF_ClosureUnitarity`](lean/QLF_ClosureUnitarity.lean)). | **Proved** structure; that a closure *is* the measurement event is a **reading** (compare Zurek's decoherence, 2003). | A recorded measurement outcome with no corresponding closure. |
| A7 | **State update** after measurement (Lüders rule). | Not yet stated. | None. | **Open.** | n/a until stated. |
| A8 | **Composition** is the tensor product. | Two histories close jointly; the closed two-spin state is exactly the singlet, and it saturates Tsirelson's bound. | `closed_iff_singlet`, `singlet_saturates` ([`QLF_JointClosure`](lean/QLF_JointClosure.lean)); `chsh_tsirelson`, `tsirelson_bound` ([`QLF_Tsirelson`](lean/QLF_Tsirelson.lean), [`QLF_TsirelsonBound`](lean/QLF_TsirelsonBound.lean)). Tensor product itself: `same_composite_iff`, `interleaving_invariant_iff`, `composite_is_tensor`, `tensorEquiv` ([`QLF_TensorFromClosure`](lean/QLF_TensorFromClosure.lean)). **Premises:** each body acts through its own fold, the joint fold is multiplicative, and swapping adjacent events of different bodies leaves it unchanged. | **Derived for two bodies (operator algebra).** Interleaving invariance forces the bodies to commute, every independent composite factors uniquely through `M ⊗ M`, and the twist realization is `M ⊗ M ≅ Mat₄(ℂ)`. Still classical, not formalized: faithfulness in an arbitrary joint algebra (simplicity of `Mat₄`), `ℂ⁴` as the state space, and `N > 2` bodies. What is proved inside it (the singlet as the closure, `2√2`) is standard quantum mechanics. | Correlations beyond `2√2`, a composite whose joint fold depends on how separate bodies' events interleave, or a composite whose joint closures do not match its tensor-product states. |

**Layer A tally.** One row is derived outright (A3, unitary dynamics, given unitary twists). Three are
proved consequences of a definition or a structure (A2, A4, A6). Two are conditional on a premise not yet
derived (A1's complex numbers, A5's refinement). One is assumed (A8) and one is open (A7).

---

## 2. Layer B: what quantum field theory and its spacetime models add

These are not postulates of quantum mechanics. Several are where QLF's challenge is sharpest, and the
challenge is not new in any of them; the classical source is credited first.

| # | Assumption | Who questioned it first | QLF replacement | Lean anchor and premises | Status | What would count against it |
|---|---|---|---|---|---|---|
| B1 | **A fixed background spacetime.** | General relativity (Einstein 1915): spacetime is dynamical, so a fixed background is in tension with gravity. This is a QFT assumption, not a QM one. | Spacetime is synthesized from closures. The interval is the determinant of the state. | `det_toMatrix_eq_interval`, `lorentz_preserves_interval` ([`QLF_Minkowski`](lean/QLF_Minkowski.lean)); curvature through the bridge axiom `benincasa_dowker_limit` ([`QLF_CausalContinuum`](lean/QLF_CausalContinuum.lean)) and the metric through `order_metric_continuum_limit` ([`QLF_OrderMetric`](lean/QLF_OrderMetric.lean)). | **Proved** for the interval; Einstein's equations **open** (one bridge each). | A gravitational observation that requires a background. |
| B2 | **A continuum of points.** | Planck-scale arguments; Bekenstein (1972) for finite information. | Finite histories. A finite-information region cannot hold a continuum faithfully. | `no_continuum_in_finite_region` ([`QLF_Realizability`](lean/QLF_Realizability.lean)). **Premise:** the region holds finitely many distinguishable states (Bekenstein, assumed). | **Proved** given that premise. No experiment has resolved a continuum, but absence of evidence is not evidence of falsity; the case is the five strikes in [`TheContinuum.md`](TheContinuum.md) §2. | A measurement that resolves more distinguishable states than the bound allows. |
| B3 | **Exact Lorentz invariance.** | None: it is extremely well tested. | Lorentz symmetry from the spinor double cover; on the lattice it is broken at order `a²` and restored in the continuum. | `spinor_hom` ([`QLF_LorentzCover`](lean/QLF_LorentzCover.lean)); surjectivity through the bridge axiom `lorentz_generated_by_boosts_rotations`. The `a²` breaking: [`Hidden_Zeros_Closure.md`](Hidden_Zeros_Closure.md) §12. | **Proved** homomorphism, one bridge for surjectivity; the breaking is an **exact computation**. | See benchmark §5 (B-LIV). |
| B4 | **The propagator `1/p²`** is put into perturbation theory. | Symanzik (1969): it is the sum over random walks. | The resolvent of the eight-twist walk under the Kraft measure, `1/(1 − φ(k))`, which is `8/k²` at long wavelength. | `twist_kraft` ([`QLF_KraftMeasure`](lean/QLF_KraftMeasure.lean)); the propagator itself is an **exact computation** ([`Hidden_Zeros_Closure.md`](Hidden_Zeros_Closure.md) §11–§12). | **Exact computation** of a scalar walk; **open bridge** from closures: the sum runs over all unconstrained histories by net displacement, with no ZFA selection and no Pauli fold, so the projection from closure histories to this scalar walk is **assumed** ([`Hidden_Zeros_Closure.md`](Hidden_Zeros_Closure.md) §12). The Wick rotation is also **assumed**. | A Lorentzian walk whose resolvent is not `1/p²` at long wavelength, or a closure-selected, fold-weighted sum that does not reduce to it. |
| B5 | **Renormalization** subtracts infinities. | Wilson (1971): renormalization is a flow over scales. | Every counterterm is finite, one per octave of capacity; no infinity is ever subtracted. | `counterterm_finite`, `dyson_unique`, `landau_capacity` ([`QLF_VacuumResolvent`](lean/QLF_VacuumResolvent.lean)); finite flow in [`QLF_ExactRG`](lean/QLF_ExactRG.lean). | **Proved** finite core; the prime electromagnetic kernel **open**. | A physical divergence that no finite capacity absorbs. |
| B6 | **The gauge group** `SU(3)×SU(2)×U(1)` is postulated. | Unexplained in the Standard Model. | The groups come from the axis algebra: the τ subalgebra is weak isospin; colour is the ℤ₃ relabeling. | `weak_isospin_su2` ([`BraKetRhoQuCalc`](lean/BraKetRhoQuCalc.lean)); `baryon_cyc_invariant` ([`QLF_BaryonWinding`](lean/QLF_BaryonWinding.lean)); `yang_mills_iff` ([`QLF_NonAbelianField`](lean/QLF_NonAbelianField.lean)). | **Proved** algebras and lattice field equations; couplings **open**. | A gauge structure the axis algebra cannot generate. |
| B7 | **Locality and microcausality.** | Built into QFT. | Histories compose only along shared closures; the shell kernel composes over intermediate shells. | `shellKernel_compose` ([`QLF_LightCone`](lean/QLF_LightCone.lean)); `kernel_compose`, `kernel_dagger` ([`QLF_ChannelGroupoid`](lean/QLF_ChannelGroupoid.lean)). | **Proved** composition; microcausality of operators **open**. | A spacelike correlation that is not a joint closure. |
| B8 | **The S-matrix is unitary**, and the optical theorem holds. | Standard. | The optical theorem as a sum over intermediate channels, for every history and the realizable walk; the raw census violates it by exactly `2/3`. | `optical_forward`, `raw_optical_defect` ([`QLF_OpticalTheorem`](lean/QLF_OpticalTheorem.lean)). | **Proved** for the realizable walk; a normalized `S` on boundary states with `S†S = I` **open**. | An unnormalizable channel operator. |

---

## 3. Layer C: QLF's own primitives

QLF is not postulate-free. These are its primitives, stated as plainly as the standard ones, each marked
**forced** (derived from something weaker), **chosen**, or **bridge** (an explicit axiom).

| # | Primitive | Forced, chosen, or bridge | Where |
|---|---|---|---|
| C1 | **Logic only.** Records persist (weakening). | Chosen as the floor: "we can only assume nature is logical." Persistence and no time loops follow from weakening. | `weakening_iff_persistence` ([`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean)); [`Philosophy.md`](Philosophy.md) §3d |
| C2 | **Possibilism.** Every generable history exists as possibility. | Chosen: the founding commitment, not a theorem. | [`Philosophy.md`](Philosophy.md) |
| C3 | **The alphabet.** Distinctions are signed axes, represented by the Pauli matrices. | The **size** is forced (eight, given two spatial axes); the **Pauli representation**, and with it the complex numbers, is **chosen**. | [`QLF_AlphabetNecessity`](lean/QLF_AlphabetNecessity.lean) |
| C4 | **Histories** are finite words; composition is concatenation. | Chosen. | [`QLF_Axioms`](lean/QLF_Axioms.lean) |
| C5 | **ZFA selection.** A history is an event when it is count-balanced on every axis. | Chosen as the selection rule. Pauli closure then follows. | `count_balanced_pauli_closed` ([`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean)) |
| C6 | **The measure.** A history of length `L` carries weight `8^{−L}`. | Forced by prefix-freeness once closures are events, but the choice of a cylinder measure itself is a premise. | `twist_kraft` ([`QLF_KraftMeasure`](lean/QLF_KraftMeasure.lean)) |
| C7 | **Finite information** in a bounded region. | Assumed (Bekenstein). | Premise of `no_continuum_in_finite_region` |
| C8 | **Rendering bridges** to the continuum. | **Bridge**: each is an explicit axiom, listed with its strength in [`CLAUDE.md`](CLAUDE.md)'s axiom inventory and [`Open_Problems.md`](Open_Problems.md). | e.g. `lorentz_generated_by_boosts_rotations`, `benincasa_dowker_limit`, `order_metric_continuum_limit` |

**The count.** Standard quantum mechanics with QFT needs eight postulates in Layer A and eight more
assumptions in Layer B. QLF needs seven primitives (C1–C7) plus the bridges (C8). That is not yet a
smaller number of assumptions, so the simplification claim has to rest on their *kind*: C1–C7 are
combinatorial and logical, where Layer A's are analytic (Hilbert space, a probability rule, a measurement
postulate). Whether that counts as simpler is a judgement the ledger makes visible but cannot make for the
reader.

---

## 4. The reintroduction audit

The question that decides the programme: where does a removed assumption come back? Each entry names the
place it re-enters.

**a. Unitarity re-enters through the alphabet.** `history_unitary` is closure of the unitary group under
multiplication, given that each twist is a Pauli matrix. So A3 removes the postulate that *evolution* is
unitary, by moving it into C3, the choice of unitary primitives. That is a genuine reduction (one
postulate about primitives in place of one about dynamics), not a derivation from nothing. The
realizable step adds a second choice, the projector `(1 + M(t))/2`, justified by the raw step's failure
(`rawStep_not_unitary`).

**b. The Born weight re-enters through the refinement premise.** `born_from_ways` assumes that an outcome
of Gaussian norm `m` is `m` equal ways. The norm *is* `|ψ|²`, so the theorem shows that `|ψ|²` is the
**only** consistent assignment once ways are counted that way. It does not show that dynamics produces
that count. A5 stays conditional until the refinement is derived from the closure census.

**c. Universality is true by encoding.** `qlf_universality` encodes each edge (gate) of a finite computation as
a balanced pair (`[+, −]` or `[−, +]`), so the encoded string is ZFA whatever the computation does; the
theorem never uses termination. The statement "every terminating computation is a ZFA string" is
therefore a property of the encoding, not evidence that ZFA tracks termination. The framing that
non-terminating computations are what ZFA prunes needs a separate theorem.

**d. The complex numbers re-enter through `σ_y`.** The alphabet's size is forced, but the step from the
Klein four-group to complex 2×2 matrices is a choice (C3). A1 is conditional on it.

**e. Lorentz symmetry and Lorentzian signature re-enter through a bridge and a rotation.** The double
cover's surjectivity is the axiom `lorentz_generated_by_boosts_rotations`, and the derived propagator
(B4) is Euclidean, reaching Lorentzian momenta by an assumed Wick rotation.

**f. One anchor is empty.** `qlf_state_is_minkowski` in [`QLF_Minkowski`](lean/QLF_Minkowski.lean) is
`True := trivial`. It anchors nothing; the real content is `det_toMatrix_eq_interval` and
`lorentz_preserves_interval`, which this ledger cites instead.

**g. The tensor product was assumed** (A8). It is now derived for two bodies at the level of the operator algebra ([`QLF_TensorFromClosure`](lean/QLF_TensorFromClosure.lean)): "distinct bodies have no relative order" forces commutation, and commutation forces `M ⊗ M`. The premise that carries the weight is interleaving invariance, and the flat one-word model fails it (`flat_not_independent`). Remaining: faithfulness for an arbitrary joint algebra, the state space as `ℂ⁴`, and `N > 2`. Terminology: tensor products **do** represent entanglement (the singlet is a vector of the tensor space). The claim QLF can defend is that a product of independently closed factors cannot produce a shared closure (`kron_scalar_iff`, `product_never_joint_closure`).

**What survives the audit.** Unitary dynamics (moved to the primitives, not removed), measurement as
closure with no collapse dynamics, interference zeros as theorems, the Minkowski interval as a
determinant, finite renormalization, the propagator as a sum over (unselected, fold-free) histories, and the gauge algebras. What
does not survive as a derivation: the Born rule, the complex numbers, universality as
a statement about termination, and Lorentzian signature.

---

## 5. The distinguishing benchmark

Everything in §1–§2 reproduces standard physics. A defensible "radical simplification" also needs at
least one quantitative prediction, fixed in advance, that standard physics does not make. None of the
candidates below has passed yet; each is stated with its kill condition.

| Candidate | QLF prediction | Standard expectation | Kill condition | State |
|---|---|---|---|---|
| **B-LIV: axis-aligned dispersion** | At Planck spacing the photon dispersion is `E² = k²[1 − ξ(n)(ℓ_P k)²]`, with `ξ` set by the direction `n` relative to the twist axes, so `E_QG,2 ≈ 2.4–5 E_P` (§5a). | Exact Lorentz invariance. | A bound on quadratic Lorentz violation above `E_QG,2 ≈ 2.4 E_P` (or, for the real-time walk, a sign opposite to the one it predicts). | **A number, but untestable now.** It is allowed by the best time-of-flight bound (`E_QG,2 > 6 × 10⁻⁸ E_P`, LHAASO 2024) by a factor of `4–8 × 10⁷`. Its sign depends on how the time axis is discretized, which is not yet fixed (§5a). |
| **No α drift** | `α` cannot vary in time (`alpha_cannot_drift`). | The Standard Model allows no drift either; many extensions do. | A confirmed drift, for instance in thorium-229 nuclear clocks. | Distinguishes QLF from drift models, **not** from the Standard Model. |
| **Predicted absences** | No supersymmetric partners, axion, WIMP, magnetic monopole, proton decay or light sterile `ν_R` ([`Mysteries_Of_Physics.md`](Mysteries_Of_Physics.md) §6). | The Standard Model has none of these either. | Discovery of any one. | Distinguishes QLF from extensions, **not** from the Standard Model. |
| **`α⁻¹` from the census** | `137.032` structural ([`Alpha_Residual.md`](Alpha_Residual.md)). | Measured `137.035999…`. | Already a miss by `0.004`, attributed to continuum running. | **Not a pass.** Listed so it is not hidden. |

So the honest position is: QLF reorganizes quantum mechanics onto combinatorial primitives and removes
the collapse and fixed-background assumptions, but it does not yet have a benchmark that separates it
from the Standard Model. B-LIV is now a number (§5a), but one that present experiments cannot reach.

### 5a. B-LIV at Planck spacing

Setting the lattice spacing to the Planck length `ℓ_P` fixes the scale with no free parameter. A massless
mode is a zero of the walk's inverse propagator `Σ_a (1 − cos a K_a)` ([`Hidden_Zeros_Closure.md`](Hidden_Zeros_Closure.md)
§11). The script [`liv_dispersion.py`](liv_dispersion.py) solves it exactly and reads off
`E² = k²[1 − ξ(n)(ℓ_P k)²]`, checking each `ξ` against its series formula.

How the time axis is continued decides the result, and QLF has not fixed it:

| Time axis | Exact dispersion | `ξ(n)`, with `s₄ = Σ_i n_i⁴` | Along an axis | Body diagonal | Character |
|---|---|---|---|---|---|
| Wick-rotated Euclidean walk (round 8) | `cosh(ℓ_P E) = 1 + Σ_i 2 sin²(ℓ_P k_i/2)` | `(1 + s₄)/12` | `1/6`, `E_QG,2 = 2.45 E_P` | `1/9`, `E_QG,2 = 3.00 E_P` | subluminal, anisotropic |
| Time on the lattice directly | `cos(ℓ_P E) = 1 − Σ_i 2 sin²(ℓ_P k_i/2)` | `(s₄ − 1)/12` | `0` (no quadratic term) | `−1/18`, `E_QG,2 = 4.24 E_P` | superluminal off-axis, anisotropic |

`E_QG,2` is quoted in the convention `E² = p²[1 − s(p/E_QG,2)²]`, so `E_QG,2 = E_P/√|ξ|`; the bound's own
convention may differ by a factor of order one, which does not affect the conclusion. The group velocity
differs from `c` by `(3/2)ξ(E/E_P)²`, about `10⁻³¹` at 10 TeV.

**What this settles.** Planck's constant is enough to turn B-LIV into a parameter-free prediction:
quadratic, direction-dependent Lorentz violation at `E_QG,2 ≈ 2.4–5 E_P`. It is consistent with the
strongest time-of-flight bound, `E_QG,2 > 6 × 10⁻⁸ E_P` from LHAASO's observation of GRB 221009A
(*Phys. Rev. Lett.* 133, 071501, 2024), by more than seven orders of magnitude.

**What it does not.** (1) It is not testable now: a seven-order gap is far beyond any planned
time-of-flight improvement. (2) The sign is not a prediction until the Lorentzian walk is fixed; the
realizable Dirac walk ([`QLF_DiracWalk`](lean/QLF_DiracWalk.lean)) is the candidate, and its dispersion
should be computed next. (3) A lattice picks a rest frame and an orientation of its axes in the sky; QLF
says neither, so a directional search has no predicted axes yet. (4) Only time-of-flight bounds are
checked here, not threshold effects such as photon decay.

### 5b. The realizable walk itself: a linear term, and how time symmetry removes it

The rows above use the scalar walk. QLF's own spin-½ walk is the realizable Weyl walk of
[`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean), `realWalk = step_y · step_x · step_z` with each
step `exp(i k σ)`: every spin component moves at `c` along one axis per sub-step. Solving it exactly
([`liv_dispersion.py`](liv_dispersion.py)):

| Ordering | Along an axis | Body diagonal | Leading term |
|---|---|---|---|
| The one-way order `y, x, z` (the Lean order before this change) | exact, `E = k` | `E = k ± k²/(3√3)`, sign set by the octant | **linear**: `cos E = Π cos k_i − Π sin k_i`, so `E ≈ k + k_x k_y k_z / k` |
| Palindromic (a half step in each order, `y x z` then `z x y`) | exact, `E = k` | `E = k − k³/18` | quadratic: `cos E = Π cos k_i` exactly, so no odd term in any direction; `ξ = 1/9` on the body diagonal, `E_QG,2 = 3.0 E_P`, subluminal |

Both trace identities hold at **arbitrary** momenta, not only along the sampled directions:
`Re tr(realWalk)/2 = cos k_y cos k_x cos k_z` for the palindrome, and `Π cos k_i − Π sin k_i` for the
one-way order. Since `cos E` is then even in every `k_i`, the palindrome's dispersion has no odd
(linear-in-energy) term in any direction. They are checked numerically at 2,000 random momenta to
`10⁻¹⁵` ([`liv_dispersion.py`](liv_dispersion.py), run in CI by
[`scripts/amplitude_regression.py`](scripts/amplitude_regression.py)). The palindrome's identity is now
**proved** in Lean ([`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean), no axioms): `realStep_eq_cos_sin`
writes each realizable step as `cos k · 1 + i sin k · M(t)`, `realWalk_trace` proves the full complex
trace is `2 cos k_y cos k_x cos k_z` (so its imaginary part vanishes too), and `realWalk_trace_even`
proves it is even in each `k_i`. The one-way identity stays numerical, since that order is no longer the
Lean walk.

The fixed order breaks time reversal and parity, and that leaves a term **linear** in energy. Its sign
flips between octants and between the two chiralities (the Dirac walk runs the other chirality at
`−k`), and its size is `|v − 1| ≤ (2/(3√3)) E/E_P`, so `E_QG,1 = 2.6 E_P`. **If photons propagated with
this dispersion, it would be excluded**: LHAASO's linear bound is `E_QG,1 > 10 E_P`. Two qualifications
stop that being a refutation of QLF. The walk is a spin-½ walk, and nothing yet shows a photon inherits
its dispersion. And the term comes from the order of the sub-steps, not from the walk: the palindromic
ordering, which is time-symmetric, cancels it exactly and leaves only the quadratic term, allowed by
about `5 × 10⁷`.

**The electron bound, and the assumption it needs.** In QLF the interaction is between electrons, which
are spin-½, and the photon has no properties apart from the electrons it connects
([`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) §40). If the spin-½ walk describes the
electron's propagation, the first qualification does not help, because electrons have their own bound.
That identification is an **additional physical assumption**, not a consequence of the Lean results:
the bound concerns the measured, interacting electron, and no theorem shows that it propagates by this
walk or that the walk's time ordering is physical time reversal. Granting it: In the convention
`E² = p² + m² + η p³/E_P`, the one-way order gives `η = 2 n_x n_y n_z` per chirality, up to `±0.385` with
both signs occurring. The Crab nebula's synchrotron emission requires `η > −7 × 10⁻⁸` for electrons, and
vacuum Čerenkov radiation `η < 0.01` (Jacobson, Liberati and Mattingly, *Nature* 424, 1019, 2003). So
**the one-way walk at Planck spacing, read as the electron, is excluded by about `5 × 10⁶`**, whatever
the photon is. The palindromic order has no linear term and survives.

So, under that identification, the data **select** something: at Planck spacing, a realizable walk must
be time-symmetric within each tick. The Lean `realWalk` ([`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean)) now uses the
palindromic order. Its unitarity and its generator (`realWalk_unitary`, `realWalk_generator`) carry over
unchanged in statement, so everything built on them (the Dirac walk, the optical theorem, the poles) is
unaffected.

**The massive walk, proved.** The electron is massive, so the identification needs the Dirac walk
`D = massStep m · handed k` of [`QLF_DiracWalk`](lean/QLF_DiracWalk.lean), not the massless Weyl walk. Its
exact dispersion is now proved in Lean, with no axioms:

* `realWalk_neg`: the palindromic walk at `−k` is the adjoint of the walk at `k`, and `realWalk_add_star`
  gives `W + W† = 2 Π cos k_i · 1`.
* `beta_handed_beta`: the mass generator `β` swaps the two handednesses, so `β H β = H†`. That makes the
  `β` part of the mass coin cancel against its adjoint, and `diracWalk_add_star` gives
  `D + D† = 2 cos m cos k_y cos k_x cos k_z · 1` at every momentum and mass.
* `diracWalk_eigen`, `diracWalk_dispersion`: so every eigenvalue `e^{iE}` of the Dirac walk obeys
  **`cos E = cos m · cos k_y cos k_x cos k_z`**. The relation is even in every `k_i` and in `m`, so the
  massive walk has no `η p³` term (`η = 0`, inside the Crab bound) in any direction. At small momentum
  and mass it gives `E² = m² + k²`, with corrections of relative order `k²` and `m²`, which is the
  quadratic term above.

So this is a **conditional consistency result**, not an experimental validation by proof: the defined
Dirac walk has `η = 0` exactly, and it satisfies the electron bound *if* the electron propagates by this
walk. That identification stays assumed. Also, `realWalk_neg` is a reversal identity,
`W(−k) = W(k)†`. It is what the algebra needs, but physical time-reversal invariance would be a
separate statement about an antiunitary symmetry, which is not proved here.

**The walk is forced, not chosen.** The identification can be narrowed to premises QLF already has.
Take any nearest-neighbour step along one axis: it sends the spin one site forward with some matrix
`A` and one site back with some `B`, so at momentum `k` it is `e^{ik} A + e^{−ik} B`. In
[`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean) §6, with no axioms:

* `step_forced`: if the step is unitary at every momentum, then `A = U P` and `B = U (1 − P)`, with
  `U = A + B` a unitary coin and `P` an orthogonal projector. Unitarity alone forces the realizable
  form.
* `coinless_step_forced`: with no coin (`A + B = 1`, the free step), it is a projector step
  `e^{ik} P + e^{−ik}(1 − P)`.
* `coinless_twist_step`, `fix_iff_generator`: if, in addition, the step's spin generator `2P − 1` is the
  twist `t` (the spin component along the axis moves at `c`), the step **is** `realStep t` at every
  momentum.

So the electron's free step follows from four things: one site per tick, unitarity at every momentum,
no coin at zero momentum, and the twist as the spin generator. The last is QLF's realizability premise
(§1, row A3). The coin `U` is where mass enters. That the coin is the handedness flip `β`, and that
the three axes are composed in the palindromic order (the reversal identity `realWalk_neg`), are still
choices rather than theorems. Two things remain physical identifications: that the electron is a
spin-½ closure that moves this way, and that the lattice tick is the Planck time.


### 5c. Forecasts, pre-registered 2026-11-07

This section records what the proved dispersion anticipates, before any further data is read. Each
forecast assumes two things that are **not** theorems: the lattice spacing is the Planck length (§5a),
and the electron propagates by the palindromic Dirac walk (§5b). Where a forecast is about photons, it
also assumes that photons inherit the walk's dispersion. The Lean anchor fixes the formula, and the
assumptions fix what it is a forecast about.

| # | Forecast | Lean anchor | Kill condition | Status, 2026-11-07 |
|---|---|---|---|---|
| F1 | **No linear Planck-scale term**: `η = 0` exactly for electrons, in `E² = p² + m² + η p³/E_P`, in every direction. | `diracWalk_dispersion`: `cos E = cos m · Π cos k_i` is even in every `k_i`. | Any measured nonzero `η` for electrons, of either sign. For photons (with the extra assumption), any nonzero linear time-of-flight term. | **Consistent.** The Crab bound `η > −7 × 10⁻⁸` and the vacuum-Čerenkov bound `η < 0.01` (Jacobson, Liberati and Mattingly 2003). |
| F2 | **A fixed quadratic term**: `E² = k² − (k⁴/3)(n_x²n_y² + n_y²n_z² + n_z²n_x²)` in Planck units, where `n` is the direction relative to the lattice axes. It is subluminal, exactly zero along the three axes, and largest on the body diagonal (`ξ = 1/9`, `E_QG,2 = 3.0 E_P`). There is no free coefficient. | The exact relation `cos E = Π cos k_i` is proved (`realWalk_trace`, `diracWalk_dispersion`). The fourth-order coefficient is now proved too: `walk_dispersion_quadratic` shows that `cos E` and `cos E_pred` agree to within `(Σ\|k_i\|)⁶/50` for `Σ\|k_i\| ≤ 1` (via `walk_cos_taylor`, [`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean) §7). The last step, from `cos E` to `E`, uses only that `cos` is invertible near zero and is not formalized. | A quadratic effect that is superluminal, isotropic, or nonzero along every direction. Or a bound `E_QG,2 > 3.0 E_P` in every direction. | **Untestable now.** The best time-of-flight bound is `E_QG,2 > 6 × 10⁻⁸ E_P` (LHAASO 2024), about `5 × 10⁷` short. |
| F3 | **Dirac physics at every reachable energy.** Mass and momentum corrections enter only at relative order `(m/E_P)²` and `(k/E_P)²`, which is about `10⁻⁴⁵` for an electron at rest. | `diracWalk_generator`, `diracWalk_dispersion`; the size of the corrections is a low-energy expansion, not a Lean theorem. | Any electron dispersion anomaly at accessible energies attributable to the walk. | **Consistent, but not distinguishing**: the Standard Model forecasts the same. |

**What is not fixed.** F2's direction is measured from the lattice axes, and nothing yet says how those
axes are oriented in the sky. Until a rule fixes them, for example alignment with the CMB rest frame, F2
can be tested only as a pattern: the ratio between directions, and the zeros along three orthogonal
axes. A fixed direction cannot be tested. **What would separate QLF from the Standard Model** is a
consequence at reachable energies, and none of F1–F3 is one. That is the open item.
---

## 6. References

- Nielsen, M. A. and Chuang, I. L. (2000). *Quantum Computation and Quantum Information*, §2.2.
- Einstein, A. (1915). Die Feldgleichungen der Gravitation. *Sitzungsber. Preuss. Akad. Wiss.*
- Bekenstein, J. D. (1972). Black holes and the second law. *Lett. Nuovo Cimento* 4, 737.
- Symanzik, K. (1969). Euclidean quantum field theory. In *Local Quantum Theory*, ed. R. Jost.
- Wilson, K. G. (1971). Renormalization group and critical phenomena. *Phys. Rev. B* 4, 3174.
- Bialynicki-Birula, I. (1994). Weyl, Dirac, and Maxwell equations on a lattice as unitary cellular
  automata. *Phys. Rev. D* 49, 6920.
- Meyer, D. A. (1996). From quantum cellular automata to quantum lattice gases. *J. Stat. Phys.* 85, 551.
- Sorkin, R. D. (1994). Quantum mechanics as quantum measure theory. *Mod. Phys. Lett. A* 9, 3119.
- Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Rev. Mod.
  Phys.* 75, 715.
- Jacobson, T., Liberati, S. and Mattingly, D. (2003). A strong astrophysical constraint on the violation
  of special relativity by quantum gravity. *Nature* 424, 1019. arXiv:astro-ph/0212190.
- LHAASO Collaboration (2024). Stringent tests of Lorentz invariance violation from LHAASO observations
  of GRB 221009A. *Phys. Rev. Lett.* 133, 071501. arXiv:2402.06009.
- Zurek, W. H. (2005). Probabilities from entanglement, Born's rule from envariance. *Phys. Rev. A* 71,
  052105.
