# The Space QLF Lives In — Gaussian-Integer Lattices, not Hilbert Space

Hilbert space is the right home for *general* quantum mechanics, and it is **too general** for [QLF](README.md) — by exactly the same continuum it adds to everything else. A separable Hilbert space `ℂ^∞` has three features QLF rejects:

- the **cardinality of the continuum** (uncountably many states),
- **continuous `U(1)` phases** (an amplitude can be any unit complex number),
- **infinite dimension** (a fixed `ℵ₀` worth of independent directions).

None of these is physically realized — a finite-information region holds finitely many distinguishable states (Bekenstein; machine-checked as `no_continuum_in_finite_region` in [`lean/QLF_Realizability.lean`](lean/QLF_Realizability.lean)). So Hilbert space is not where QLF *lives*; it is the **completion** of where QLF lives. The substrate's state space is the discrete, computable structure underneath:

> **QLF's state space is a finite-rank free module over the Gaussian integers `ℤ[i]` — a Gaussian-integer lattice — with phases in `μ₄ = {±1, ±i}` and rational Born probabilities. Hilbert space `ℂ^∞` is its continuum limit.**

Every clause is grounded in already-verified code.

---

## 1. The phase group is `μ₄`, not `U(1)`

Standard QM lets a state pick up any phase `e^{iθ}`, `θ ∈ [0, 2π)` — a continuous circle. QLF's phases are **discrete**. Every balanced closure folds to a **Pauli scalar** `{+I, −I, +iI, −iI}` (`count_balanced_pauli_closed`, [`lean/QLF_TwistAlphabet.lean`](lean/QLF_TwistAlphabet.lean)), and that four-element set is exactly

$$\{\,i^0,\,i^1,\,i^2,\,i^3\,\} \;=\; \mu_4 \;=\; \text{the 4th roots of unity} \;=\; (\mathbb{Z}[i])^\times,$$

the **units of the Gaussian integers**. This is machine-checked in [`lean/QLF_StateSpace.lean`](lean/QLF_StateSpace.lean): every phase satisfies `p⁴ = 1` (`pauliScalar_pow_four_eq_one`), `i` generates a group of order exactly 4 (`pauliScalar_i_order_four`), and the embedding into `ℂ` lands on the complex 4th roots of unity (`toComplex_pow_four`). The continuous circle `U(1)` is replaced by its four-point cyclic subgroup `μ₄ = ℤ/4`.

---

## 2. Amplitudes are Gaussian integers; Born probabilities are rational

The substrate's generators are the Pauli matrices, and their **entries are Gaussian integers**:

$$\sigma_x = \begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_y = \begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad \sigma_z = \begin{pmatrix}1&0\\0&-1\end{pmatrix} \;\subset\; M_2(\mathbb{Z}[i]).$$

Every twist fold is a product of these, so it lives in `M₂(ℤ[i])`. The Born amplitude is the path sum ([`Born_Rule.md`](Born_Rule.md))

$$\langle \varphi \mid \psi \rangle = \sum_{h} e^{i\theta(h)}, \qquad e^{i\theta(h)} \in \mu_4,$$

a sum of 4th-roots-of-unity — hence a **Gaussian integer** `a + bi ∈ ℤ[i]`. The Born probability is then

$$P(\varphi\mid\psi) = \frac{|\langle\varphi\mid\psi\rangle|^2}{Z} = \frac{a^2 + b^2}{Z},$$

a **ratio of non-negative integers** (a net constructive path-count over the integer partition function `Z`). Probabilities are **rational, computable, RCA₀** — there is no irrational amplitude and no continuum anywhere in the exact substrate. (This is the state-space face of `Shannon_And_Phase.md`: the count is `|a|²`, the phase is `arg ∈ μ₄`.)

---

## 3. Finite-dimensional per causal horizon

A separable Hilbert space has a fixed infinite dimension. QLF's state space is **finite-dimensional at every causal horizon**: the possibility tree at depth `n` is finite (`C(2n,n)` ZFA-stable closures among `4ⁿ`), and a bounded region resolves only finitely many distinguishable states (Bekenstein, [`lean/QLF_Realizability.lean`](lean/QLF_Realizability.lean)). So the state space is a **finite-rank `ℤ[i]`-module**; its rank *grows* with horizon depth but is always finite. Infinite dimension is never instantiated — it is the limit, not the substrate.

---

## 4. The algebra: the Pauli/Clifford `*`-algebra over `ℤ[i]`

The operators are `M₂(ℤ[i])` and its tensor powers; for independent bodies those tensor powers are **derived** from interleaving invariance (`QLF_TensorFromClosure`), not assumed as a many-body rule, and `QLF_TensorConservativeReturn` proves the quotient return on tensor-image classes. The physical selection of that quotient and the entangled-sector return remain open. The **Hermitian conjugate `†`** is the `*`-involution ([`Reversibility.md`](Reversibility.md), `eval_dagger`; a balanced closure is self-adjoint, `H = H†`). This is precisely the **stabilizer / Clifford fragment** of quantum mechanics — the part that is *efficiently classically simulable* (the Gottesman–Knill theorem), i.e. **computable**. QLF's reading is the natural one: the **substrate is the computable `ℤ[i]` (Pauli/Clifford) fragment**, and the continuum amplitudes of *universal* quantum mechanics — the `T`-gate, arbitrary rotations, irrational amplitudes — are the **statistical limit** as the `ℤ[i]`-lattices densify. The discreteness that makes the substrate simulable is the discreteness that makes it physical.

---

## 5. Hilbert space is the completion

As the causal horizon grows, the finite-rank `ℤ[i]`-lattices **nest and densify**; their colimit, metrically completed, is the separable Hilbert space `ℓ²(ℂ)`. So Hilbert space is the **rendering** of the substrate — the continuum closure of a discrete, computable lattice — exactly as the smooth manifold is the rendering of the causal set and `ℝ` is the rendering of the computable reals ([`TheContinuum.md`](TheContinuum.md)). It is "too general" because it contains the entire continuum tail (uncountable states, continuous phases, infinite dimension) that the substrate never realizes. QM works *through* the limit; QLF says the substrate is the discrete object the limit is taken of.

---

## 6. Where `ℤ[i]` meets `ℂ`: the Riemann boundary

The substrate's spectral operators are `M₂(ℤ[i])`-valued (`toSpectralMode`, [`lean/QLF_Spectral.lean`](lean/QLF_Spectral.lean)). But a *zero of `ζ`* — the critical-line eigenvalue `ρ ∈ ℂ` — lives in the analytic continuum. That crossing, from the discrete `ℤ[i]` substrate to the continuous `ℂ`, is *exactly* where QLF's one Riemann bridge axiom sits (`spectral_hilbert_polya`). The state-space picture says precisely why Riemann is a *boundary* problem: the substrate is `ℤ[i]`; `ζ`'s zeros are in `ℂ`; the bridge is the rendering.

---

## 7. The state *is* Minkowski space — the determinant is the spacetime interval

The state space is not only discrete and `ℤ[i]`-valued; its *geometry* is **Minkowski space**, by construction. A QLF state is a 2×2 **Hermitian** matrix — the `Form` of [`SpacetimeDynamics.lean`](lean/SpacetimeDynamics.lean), the spectral mode every closure folds to (`toSpectralMode_hermitian`):

$$X = t\,I + x\,\sigma_x + y\,\sigma_y + z\,\sigma_z = \begin{pmatrix} t+z & x-iy \\ x+iy & t-z \end{pmatrix}.$$

This is the classical isomorphism **Herm₂(ℂ) ≅ Minkowski `ℝ^{1,3}`**: the **1 trace direction is time**, the **3 traceless Pauli directions are space** (the same 3 spatial axes as [`QLF_Generations`](lean/QLF_Generations.lean)). And the metric is the **determinant** — machine-checked in [`lean/QLF_Minkowski.lean`](lean/QLF_Minkowski.lean):

$$\det X = (t+z)(t-z) - (x-iy)(x+iy) = t^2 - x^2 - y^2 - z^2 \;=\; \text{the Minkowski interval}$$

(`det_toMatrix_eq_interval`; the `i`-terms cancel because the form is Hermitian). Three consequences are anchored:

- **Pure states are null — the Bloch sphere is the celestial sphere.** A pure qubit (`t=½`, `x²+y²+z²=¼`) has interval `0` (`pure_qubit_null`): it sits on the **light cone**, so the qubit Bloch sphere *is* the projective null cone — the sphere of null directions, Penrose's celestial sphere / "the sky."
- **The Lorentz group is the state's symmetry.** The action `X ↦ A X A†` with `det A = 1` (i.e. `A ∈ SL(2,ℂ)`) preserves the determinant, hence the interval (`lorentz_preserves_interval`). So `SL(2,ℂ)` acts as the Lorentz group `SO⁺(1,3)`; the unitary subgroup `SU(2)` (preserving the trace = time too) is spatial rotation `SO(3)`. The substrate's half-spin **twists are the 2-spinors**, and `QLF_Spin`'s `SU(2)→SO(3)` double cover (`rotation_360_eq_negI`) is the spatial restriction of the `SL(2,ℂ)→SO⁺(1,3)` spinor double cover.
- **Lorentzian signature `(1,3)` from `1 + 3`.** The `+,−,−,−` signature is the trace/traceless split of the 2×2 Hermitian state: time is the scalar/identity (`±I`, the gauge/closure direction), space is the traceless `σ`-part (the twists). Time being special = time being the *closure* axis (synthesized as `f=1/t`); space = the twist axes.
- **The relativistic `E² = p² + m²` is the same interval.** Read the *same* `Form` as a **4-momentum** `(E, p_x, p_y, p_z)` and its interval `E² − |p|²` is the **invariant mass²** — so `E² = p² + m²` falls straight out of `det_toMatrix_eq_interval` ([`lean/QLF_EnergyMomentum.lean`](lean/QLF_EnergyMomentum.lean): `energy_momentum_relation`). `m² = det(4-momentum)` (`massSq_eq_det`) is a **Lorentz invariant** (`mass_lorentz_invariant`); at rest `E = mc²` (`rest_energy_sq`); and a massless particle is **null**, `E = |p|`, on the same light cone as the pure qubit (`massless_null`). So momentum enters QLF through this verified Lorentzian geometry, not as a bare additive count.

Over the substrate the entries are Gaussian integers (§2), so the substrate Minkowski space is the **discrete integer-Hermitian lattice**: `det X ∈ ℤ`, so the causal sign (timelike `>0` / null `=0` / spacelike `<0`) is **integer-valued and discrete** — the causal-set order of [`QLF_ReachableEvent`](lean/QLF_ReachableEvent.lean) / [`QLF_CausalInterval`](lean/QLF_CausalInterval.lean). Continuum Minkowski `ℝ^{1,3}` is the *rendering* of this `ℤ[i]`-Hermitian lattice — the same continuum-as-completion move as everywhere else. So the answer to "what space does QLF live in" has both faces: **algebraically** a Gaussian-integer lattice with `μ₄` phases; **geometrically** the discrete integer-Hermitian model of Minkowski space, with its determinant the spacetime interval.

### Does this prove Lorentz invariance?

Partly — and it is worth being exact about which part. What is **proven** is the *kinematic / representation-theoretic core*:

1. the QLF state space **carries the Minkowski metric** — the interval is literally the determinant (`det_toMatrix_eq_interval`), not an added structure; and
2. the `SL(2,ℂ)` congruence action `X ↦ A X A†` **preserves that interval** (`lorentz_preserves_interval`). Since the interval-preserving linear maps of `ℝ^{1,3}` *are*, by definition, the Lorentz group, this exhibits the homomorphism `SL(2,ℂ) → SO⁺(1,3)` — the state space is a genuine **Lorentz (spinor) representation**, with the half-spin twists as the 2-spinors. (Congruence also keeps the form Hermitian, `(A X A†)† = A X A†`, so the action stays inside Minkowski space.)

That is the foundation of Lorentz invariance: there is no preferred frame *baked into the state space* — its only invariant is the interval. And the picture is now complete on both the structural fronts:

- **The full double cover `SL(2,ℂ) → SO⁺(1,3)` is machine-checked** ([`lean/QLF_LorentzCover.lean`](lean/QLF_LorentzCover.lean)). The map `A ↦ (X ↦ A X A†)` is a homomorphism (`spinor_hom`); its **kernel is exactly `{±I}`** (`spinor_kernel` — the genuine 2-to-1, proven by basis-state commutation ⟹ `A` scalar ⟹ `A = ±I`); the `SO⁺(1,3)` generators are *exhibited explicitly in the image* — `boostZ_action` realizes a Lorentz boost (the diagonal `diag(a,b)`, `a·b=1`, rescales the null coordinates `u↦a²u`, `v↦b²v`), `rotZ_action` realizes a spatial rotation (`diag(w,w̄)` sends `x−iy↦w²(x−iy)`); and **surjectivity** onto every proper orthochronous Lorentz transformation holds (`spinor_surjective`). The one bridge axiom is the standard Lie-group generation fact (boosts + rotations generate `SO⁺(1,3)` — the differential-geometric input Mathlib lacks; the generators it composes are themselves proven). So the spinor–Lorentz correspondence — half-spin twists as 2-spinors, `±A` over each Lorentz transformation — is established, not asserted.
- **Dynamical** Lorentz invariance (that QLF's *laws* are frame-independent) is the **statistically uniform, stateless-ether** result — [`QLF_SubstrateLightSpeed`](lean/QLF_SubstrateLightSpeed.lean) (`local_light_speed_invariant`: the `ρ`-depth cancels so the local light speed is the substrate `c` in every Markov blanket), Lorentz invariance as an emergent symmetry of a frameless medium, not a postulated metric.

So: the state space is *manifestly Lorentzian by construction*, the `SL(2,ℂ)→SO⁺(1,3)` double cover is machine-checked, and the dynamics respecting that symmetry is the substrate-light-speed / uniform-ether result.

## 8. `ℤ[i]` vs `ℤ[ζ₈]` — resolved: the ring is `ℤ[i]`, the `√2` is a global normalization

Superposition / the Hadamard gate introduce a `1/√2`, which *could* enlarge the Clifford ring to the 8th cyclotomic `ℤ[ζ₈] = ℤ[1/\sqrt2,\,i]` — and QLF's alphabet is, suggestively, 8-twist. The question is whether QLF's exact state ring is `ℤ[i]` or `ℤ[ζ₈]`. **It resolves to `ℤ[i]`**, and the resolution is itself illuminating.

Within the Clifford/stabilizer fragment the substrate lives in, **every *relative* phase is in `μ₄`** (§1), and the only `√2` is the **global** normalization `2^{-k/2}` of the Hadamard. A global factor is **physically inert** — it cancels in the Born ratio, because the Born rule sees only the *projective ray*. This is machine-checked in [`lean/QLF_StateSpace.lean`](lean/QLF_StateSpace.lean): Born probabilities are projective invariants of a Gaussian-integer amplitude vector (`bornProb_global_scale` — scaling all amplitudes by any common Gaussian integer leaves the probability unchanged, via norm-multiplicativity), and the Hadamard split is `1/(1+1) = 1/2` computed over `ℤ[i]` from the unnormalized integer vector `(1,1)` with no `√2` (`hadamard_born_half`). So amplitudes never need leave `ℤ[i]`.

A *relative* `ζ₈ = e^{iπ/4}` phase — one that does **not** cancel — requires the **non-Clifford `T`-gate**, which is exactly the **magic-state / non-Gottesman–Knill resource**: the part of quantum mechanics that is *not* classically simulable. So:

> The `ℤ[i]` ↔ `ζ₈` boundary **is** the Clifford ↔ `T` boundary — the Gottesman–Knill *computable* ↔ *universal* boundary, i.e. the **substrate ↔ continuum** boundary itself.

`ζ₈` lives on the continuum-limit side, with the `T`-gate / magic states — precisely where the irrational amplitudes of universal QM live. This *tightens* the picture rather than complicating it: the discreteness of the state ring (`ℤ[i]`) and the Gottesman–Knill computability boundary are the same line.

## 9. Honest scope

- **Settled (grounded in proven theorems):** the phase group is `μ₄ = (ℤ[i])ˣ` (`QLF_StateSpace.lean`, `count_balanced_pauli_closed`); the `σ`-generators and folds are `ℤ[i]`-valued; Born probabilities are rational projective invariants (`bornProb_global_scale`, `hadamard_born_half`); the `√2` is the inert global normalization, so the state ring is `ℤ[i]` (the `ℤ[ζ₈]` refinement is resolved); the state space is finite-dimensional per horizon (`QLF_Realizability`).
- **The Hilbert-space-as-completion** statement is the continuum-as-limit thesis of [`TheContinuum.md`](TheContinuum.md) applied to the state space — structural, not a new theorem.
- **Not claimed:** that QLF *is only* stabilizer QM. QLF derives *universal* quantum mechanics — but through the continuum *limit* (the `T`-gate / `ζ₈` / magic-state side) of the discrete substrate, not by making the continuum fundamental.

**The one-line answer:** QLF lives in a Gaussian-integer lattice with `μ₄` phases — the computable, finite-dimensional Pauli/Clifford world over `ℤ[i]` — and Hilbert space is the continuum it completes to, the `√2`/`ζ₈` entering exactly at the Clifford↔`T` (computable↔universal) boundary.

## See also

- [`lean/QLF_StateSpace.lean`](lean/QLF_StateSpace.lean) — the `μ₄ = (ℤ[i])ˣ` phase group, machine-checked.
- [`lean/QLF_Pauli.lean`](lean/QLF_Pauli.lean) · [`lean/QLF_TwistAlphabet.lean`](lean/QLF_TwistAlphabet.lean) (`count_balanced_pauli_closed`) — the phase group and the fold.
- [`Born_Rule.md`](Born_Rule.md) · [`Shannon_And_Phase.md`](Shannon_And_Phase.md) — amplitudes as phase-weighted path counts; count vs phase.
- [`TheContinuum.md`](TheContinuum.md) · [`lean/QLF_Realizability.lean`](lean/QLF_Realizability.lean) — the continuum as completion; finite-information realizability.
- [`Shannon_Overfit.md`](Shannon_Overfit.md) — why the continuum has no place in the exact substrate: the reals over-parameterize physics (machine-checked non-identifiability — no real is ever received, every finite record leaves an infinite unconstrained tail).
- [`Reversibility.md`](Reversibility.md) · [`lean/QLF_Spectral.lean`](lean/QLF_Spectral.lean) — the `†`-involution and the spectral mode / Riemann boundary.
