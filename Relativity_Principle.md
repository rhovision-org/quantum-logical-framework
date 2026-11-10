# The Relativity Principle in QLF — what the census proves, and what it does not yet

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Epistemic status.** Every theorem cited is proved in Lean with no axioms:
[`lean/QLF_RelativityScale.lean`](lean/QLF_RelativityScale.lean) (the unsigned census) and
[`lean/QLF_LorentzSymbol.lean`](lean/QLF_LorentzSymbol.lean) (the signed census, its symbol, and
shared-pair interactions). Brute-force cross-check: [`relativity_scale_check.py`](relativity_scale_check.py).
**The relativity principle itself is not proved.** Physical boost covariance is an open obligation,
and the step from the census symbol to a propagation law is an assumption, labelled where it is used.

Einstein's first postulate says the laws of physics are the same for every observer in uniform
motion. QLF does not assume it. What the census of histories proves is narrower:

1. **At one step there is a preferred frame** (§2), so exact invariance under continuous boosts is
   impossible on the substrate.
2. **In the large the unsigned census becomes isotropic in the Euclidean sense** (§3): the
   lattice's cubic anisotropy falls as `4/(3L+1) ≈ (1/3)(L_P/r)²`. Euclidean isotropy is not boost
   invariance, even in the limit (`boost_not_euclidean`).
3. **The signed census carries Lorentz signature in its symbol** (§5): its determinant is the
   Minkowski interval, with no Wick rotation. Reading the symbol's zeros as the propagation law of
   light is an assumption (the kinetic reading), and a second QLF walk gives the opposite off-axis
   sign.
4. **Shared-pair interactions cannot change the time/space spread ratio** when their coupling is
   axis-blind (§6), with stated normalization conditions.

The relativity principle is therefore neither postulated nor yet derived here. What would derive it
is physical boost covariance of the propagation law (T2/T3 of the plan).

## 1. The question is precise because every twist is a spacetime unit vector

`Twist.toMatrix` ([`lean/QLF_TwistAlphabet.lean`](lean/QLF_TwistAlphabet.lean)) sends the gauge
twists `±` to `±I` and the spatial twists to `±σx, ±σy, ±σz`. In the Hermitian `Form`
([`lean/QLF_Minkowski.lean`](lean/QLF_Minkowski.lean)) the identity component is time and the Pauli
components are space. So every twist is a unit vector of `ℤ^{1,3}`: the gauge axis is time. A history
of length `L` is a walk of `L` axis steps, its net displacement is a lattice event, and a closure is a
walk that returns to the origin (the same walk as [`Closure_Walk.md`](Closure_Walk.md), now with its
time axis named).

"Do observers in uniform motion see the same laws?" becomes: is the census of these walks the same
after a Lorentz boost?

## 2. Where it fails: the single step picks a frame

A walk of `L` steps moves at most `L` in the `ℓ¹` norm (`l1_le_length`), and the `ℓ¹` norm is not a
Lorentz invariant. The module builds an exact integer boost, `γ = 3` along `(1,1,0)/√2`:

```
boost = [[3,2,2,0],[2,2,1,0],[2,1,2,0],[0,0,0,1]]
```

It preserves the interval (`boost_preserves_interval`) and has an integer inverse (`unboost_boost`).
It carries the rest observer's tick `e_t = (1,0,0,0)` to `(3,2,2,0)`, an observer moving at
`√8/3 ≈ 0.943 c`. One step reaches `e_t`. No history of fewer than seven steps reaches its boosted
image (`step_census_frame_dependent`). The same event, described by two inertial observers, is reached
in a different number of ways.

So **exact invariance under continuous boosts is impossible on the substrate**. The same wall is
why causal set theory uses Poisson sprinkling; the repo's `order_metric_continuum_limit` bridge
([`lean/QLF_OrderMetric.lean`](lean/QLF_OrderMetric.lean)) sits at the same place.

**Whose frame.** What is proven is that one census, drawn in one set of twist axes, singles out the
frame of those axes. Nothing proven says those axes are shared. Spacetime in QLF is synthesized, not a
background, so the natural reading is that each observer's histories are drawn in that observer's own
twist frame. Then every observer sees the identical census, the `4/(3L+1)` anisotropy and the lattice
light cone of §5a included, each relative to its own axes, and **no local frame is preferred**. What is
ruled out is a single global lattice that every observer sits on. Two consequences: the off-axis
dispersion of §5a has no fixed axes in the sky, and the reading is tested where two bodies in relative
motion share a closure. A shared pair puts both strands on one alphabet, so the two must agree on
whose axes it is drawn in; §6 assumed one common frame. That question belongs to T2 (the Ignatowski
step of the plan).

## 3. What dies with scale: the lattice's cubic anisotropy (Euclidean isotropy)

Summing over all `8^L` histories of length `L`, with `x_i` the displacement on axis `i`
(`i = 0` time, `1..3` space):

| Theorem | Statement | Reading |
|---|---|---|
| `covariance_isotropic` | `4·Σ x_i x_j = δ_ij · L · 8^L`, exactly, at every `L` | Time and each space axis spread equally; no axis is correlated with another |
| `light_speed_from_spread` | `Σ x_t² = Σ x_a²` | Time and space spread equally: the census's natural speed unit is one Planck length per tick. Reading it as an *invariant* speed needs boost covariance, which the unsigned census lacks (compare [`lean/QLF_SubstrateLightSpeed.lean`](lean/QLF_SubstrateLightSpeed.lean), where `c` is cancelled) |
| `first_moment_zero`, `third_moment_zero` | `Σ x_i = Σ x_i³ = 0` | No odd correction: nothing linear in the scale |
| `fourth_moment`, `mixed_fourth_moment` | `16·Σ x_i⁴ = (3L²+L)·8^L`, `16·Σ x_i²x_j² = (L²−L)·8^L` | The first moments that can see the lattice |
| `fourth_moment_anisotropy` | `Σ x_i⁴ − 3·Σ x_i²x_j² = Σ x_i²` | An isotropic distribution sets the left side to zero; the census misses by exactly its own spread |
| `anisotropy_ratio` | relative anisotropy `= 4 / (3L + 1)` | Total at one step (`= 1`), then `4/7, 2/5, 4/13, 1/4, 4/19, …` |
| `anisotropy_vanishes` | below any `ε > 0` beyond some `L₀` | The lattice axes disappear in the large |
| `boost_not_euclidean` | the boost sends `e_t` (Euclidean norm `1`) to `(3,2,2,0)` (norm `17`) | Euclidean isotropy is not boost invariance: the limiting Gaussian `exp(−\|q\|²/8)` takes `exp(−1/8)` and `exp(−17/8)` on a momentum and its boosted image |

The spread grows as `r² = L/4` in Planck units, so the cubic anisotropy is

```
relative anisotropy = 4 / (3L + 1) ≈ (1/3) · (L_P / r)²
```

**quadratic** in the ratio of the Planck length to the scale probed. The vanishing odd moments are
why there is no linear term. This measures how much the lattice's axes show, not how much an
inertial frame does: the unsigned census treats time like space, so it is `O(4)`-symmetric in the
limit and not Lorentz-symmetric (`boost_not_euclidean`). Boosts need the signed census (§5).

## 4. The domain where the lattice does not show

Read in energy, `(L_P/r)²` is `(E/E_P)²`, with `E` the energy in the frame doing the measuring. If
the propagation law is the census symbol's (§5, an assumption) and is boost-covariant at long
wavelength (not yet proved), the lattice's departure from it is of this size wherever `E·γ ≪ E_P`
in every frame compared:

| Regime | `E/E_P` | Predicted deviation `~(E/E_P)²` |
|---|---|---|
| Atomic clocks, Hughes–Drever (eV) | ~10⁻²⁸ | ~10⁻⁵⁶ |
| LHC, LHAASO photons (~10 TeV) | ~10⁻¹⁵ | ~10⁻³⁰ |
| Highest-energy cosmic rays (~3×10²⁰ eV) | ~2×10⁻⁸ | ~10⁻¹⁵ |
| Planck-scale processes | ~1 | ~1: the step frame shows |

**Against the evidence.** No experiment has seen Lorentz violation. A term linear in `E/E_P` is
excluded beyond the Planck scale (Fermi-LAT, GRB 090510, [Abdo et al., *Nature* 462 (2009)](https://www.osti.gov/pages/biblio/1357435-limit-variation-speed-light-arising-from-quantum-gravity-effects);
LHAASO, GRB 221009A, `E_QG,1 > 10 E_P`, [PRL 133, 071501 (2024)](https://arxiv.org/abs/2402.06009v2)).
The census predicts no linear term (`first_moment_zero`, `third_moment_zero`). A quadratic term is
bounded only at `E_QG,2 > 6×10⁻⁸ E_P` (same LHAASO paper), so a Planck-scale quadratic term passes by
about seven orders of magnitude. The full list of bounds is
[Kostelecký & Russell, *Data Tables for Lorentz and CPT Violation*](https://arxiv.org/pdf/0801.0287).

## 5. Lorentz signature: the phases carry it

Sections 2 and 3 count ways, and counting treats time and space alike: the momentum symbol of the
unsigned census is `2 Σ_μ cos k_μ`, a Euclidean form. The whole distribution becomes isotropic in
that Euclidean sense, not just its moments: at the diffusive scale `k = q/√L` its characteristic
function tends to `exp(−|q|²/8)`, a function of `|q|²` alone (`characteristic_isotropic`).

Lorentz signature comes from the amplitudes. Weight each history by a plane wave and keep its
Pauli fold, the amplitude QLF gives it. Then the census is a power of a one-step symbol
(`census_symbol`), and that symbol is

```
H(k) = 2i · Form(sin k₀, sin k₁, sin k₂, sin k₃)        (symbol_eq_form)
```

the Hermitian `Form` of the lattice momentum, time on the identity and space on the Pauli
matrices, because the gauge twists are `±I` and the spatial twists `±σ`. Its determinant is the
Minkowski interval of the momentum, by `det_toMatrix_eq_interval`:

```
det H(k) = −4 (sin²k₀ − sin²k₁ − sin²k₂ − sin²k₃)        (symbol_det)
```

and it is singular exactly on the lattice light cone `sin²k₀ = Σ sin²k_a` (`symbol_light_cone`).

**The kinetic reading is an assumption.** `census_symbol` gives the powers `H(k)^L`, and
`symbol_light_cone` says where `H` is singular. Calling that singular set the dispersion law of
light assumes a kinetic equation, the Weyl-type `H(k)ψ = 0`, which the census does not supply. The
generating resolvent of the powers, `(I − zH)⁻¹`, has its poles elsewhere: at `k = 0`, `H = 0` and
the resolvent is `I`. Everything below that speaks of light, dispersion or black holes is
conditional on this reading. A second QLF propagation law, the palindromic Weyl walk of
[`QM_Postulates_QLF.md`](QM_Postulates_QLF.md) §5b, gives the opposite off-axis sign, so which law
light follows is open.

For small `k`, `H(k) ≈ 2i · Form(k) = 2i σ^μ k_μ`,
the Weyl operator, which `SL(2,ℂ)` transforms covariantly
([`lean/QLF_LorentzCover.lean`](lean/QLF_LorentzCover.lean)). Each component deviates from the
covariant `k_μ` by at most `|k|³/6 + |k|⁵/100` (`symbol_deviation`), a relative correction
quadratic in `k`, the same `(L_P/r)²` as §3. So **no Wick rotation is needed**: counting ways is
Euclidean, and the phases make it Lorentzian. The zeros of `sin` at `k = π` are the lattice
doublers, as in lattice fermions.

## 5a. The lattice light cone, and what black holes would see of it

*Conditional throughout on the kinetic reading of §5, and opposite in sign to the palindromic walk.*

The light cone `sin²ω = Σ sin²k_a` is not round at the Planck scale. Along a lattice axis it is
exact: `ω = |k|` (`axis_light_exact`). Along a diagonal, light outruns `c`: momentum `(κ, κ, 0)`
gives `ω > √2 κ = |k|` (`diagonal_light_superluminal`, proved for `0 < κ ≤ 1/2`). Expanding,

```
ω² ≈ |k|² + (|k|⁴ − Σ k_a⁴) / 3
```

so the phase velocity is never below `c` and equals it only on the axes; sampling 20,000 random
in-band modes finds no exception ([`lattice_hawking.py`](lattice_hawking.py)). The excess is
quadratic in `k L_P`. Note the distinction: `c` varying from place to place relative to distant
observers is gravity, and QLF has it already (`local_light_speed_invariant`). This is different:
a direction dependence at one place, set by the lattice.

**Black holes make the scale concrete.** A black hole of mass `M` radiates at the Hawking
temperature `T = 1/(8πM)` in Planck units, so it probes exactly the regime where the light cone
bends. [`lattice_hawking.py`](lattice_hawking.py) computes thermal emission with the census
dispersion. It assumes the horizon emits at the Hawking temperature in the lattice rest frame, with
no greybody factor. For `T ≪ 1`, the robustness of that temperature under modified short-distance
dispersion is the result of [Jacobson, *PRD* 44, 1731 (1991)](https://link.aps.org/doi/10.1103/PhysRevD.44.1731),
[Unruh, *PRD* 51, 2827 (1995)](https://arxiv.org/abs/gr-qc/9409008) and
[Corley & Jacobson, *PRD* 54, 1568 (1996)](https://arxiv.org/abs/hep-th/9601073).

| Black hole | `T` (Planck) | Body-diagonal vs axis power |
|---|---|---|
| Sun (10³⁸ `M_P`) | 4×10⁻⁴⁰ | −7×10⁻⁷⁹ |
| 10¹⁵ g primordial | 9×10⁻²² | −3×10⁻⁴² |
| 100 `M_P` | 4×10⁻⁴ | −0.0001 % |
| 10 `M_P` | 4×10⁻³ | −0.007 % |
| 1 `M_P` | 0.04 | −0.66 % |
| 0.3 `M_P` | 0.13 | −7.3 % |

Leading order is `−40 δ ζ(6)/ζ(4) · T²` with `δ = (1 − Σ n_a⁴)/6`, matched by the full numerics.
Along an axis the spectrum is the continuum Planck spectrum up to the band edge `ω = π/2`.

So, under the kinetic reading, **large black holes see no lattice effect**, and the departure appears only in the last moments
of evaporation, as a direction-dependent dimming of the final burst along the lattice diagonals
(the faster-than-`c` directions fit fewer modes below a given frequency). Two cautions. Near the
Planck mass the semiclassical picture of a horizon is itself in doubt, so the bottom rows are
indicative only. And the axes are read as the hole's own twist frame (§2), so the effect has no
fixed direction in the sky and averages away over many black holes. And the palindromic walk of
[`QM_Postulates_QLF.md`](QM_Postulates_QLF.md) §5b would brighten the diagonals instead, so even the
sign of the effect waits on which propagation law light follows. The lattice also
removes the trans-Planckian problem: no mode exceeds `k = π`.

## 6. Interactions: shared pairs cannot change the spread ratio

[Collins, Perez, Sudarsky, Urrutia & Vucetich, *PRL* 93, 191301 (2004)](https://arxiv.org/abs/gr-qc/0403053)
showed that a Planck-scale preferred frame leaks into low-energy physics through quantum loops at
about the percent level unless something forbids it. Everything above §6 is free propagation. The
question is whether interactions undo it.

`quadratic_form_frame_invariant` reduces that question to one number. Any quadratic form on
momentum space that the substrate's frame group leaves invariant is `diag(a, b, b, b)`, so the only
Lorentz violation the symmetry allows at that order is the ratio `b/a`, the speed of light in each
species. The census sets it to `1` for free propagation (`light_speed_from_spread`,
`symbol_eq_form`). The frame group alone does not hold it there, because it never mixes time with
space. So the question is what interactions do to `b/a`.

Joint closures are already proven: the two-spin joint closure is the singlet
([`lean/QLF_JointClosure.lean`](lean/QLF_JointClosure.lean)), the composite fold of `N` bodies is the
tensor product, and a shared pair folds to `t ⊗ t†`
([`lean/QLF_TensorFromClosure.lean`](lean/QLF_TensorFromClosure.lean)). The new part is their
momentum-space side, in [`lean/QLF_LorentzSymbol.lean`](lean/QLF_LorentzSymbol.lean) §5, no axioms.

Two histories `A` and `B` run side by side. On a free tick each takes its own twist. On a shared
tick they close a Hermitian pair between them, `t` on `A` and `t†` on `B`, with coupling `g_t`. The
joint census sums every interleaving of free and shared ticks, so it is exact to all orders in `g`:
every loop of the interaction is in it.

| Result | Statement |
|---|---|
| `joint_census` | the joint census is `(one-tick symbol)^L` |
| `shared_wave` | a shared tick carries `e^{i(k_A − k_B)·e_t}`: the pair has zero net displacement, so it sees only the relative momentum |
| `marginal_symbol` | summing over where `B` ends, `A` sees `Σ_t (8 + g_t) e^{i k_A·e_t}` |
| `marginal_uniform` | if `g` is the same on all eight twists, `A`'s census is `(8 + g)^L` times its free census (an unnormalized identity, any `g : ℂ`) |
| **`marginal_normalized`** | when `8 + g ≠ 0`, `A`'s census divided by the total joint weight is exactly the free census `usym^L/8^L`: **the interaction changes the count, never the normalized spread** |
| **`marginal_proportional_iff`** | with `g₀` on the gauge pair and `g_s` on the spatial pairs, `A`'s census is proportional to the free one **iff `g₀ = g_s`**; otherwise the time/space spread ratio becomes `(8 + g₀)/(8 + g_s)` and `c` shifts |
| **`shared_pair_fold_axis_blind`** | every shared pair folds to the same `−I`, gauge or spatial |
| `joint_symbol_swap` | with a coupling equal on `t` and `t†`, swapping which strand takes which half leaves the joint census unchanged |

**Domain.** At `g = −8` the marginal vanishes identically and has no normalization, so no moments
exist there. For real `g > −8` the marginal weight on each of `A`'s twists, `8 + g`, is positive,
so `A`'s marginal is a genuine probability distribution, the free one (for `g ≥ 0` the joint
weights are positive too, and for `−8 < g < 0` only the marginal is). For complex `g` the
normalized census is a complex weight, not a probability, and "spread" means its normalized second
moment.

So Collins's leak has an exact substrate form for the spread ratio of §3, the census's `c`. A
coupling that weighs time-like and space-like pairs differently changes it, at any strength. The
substrate's own weight on a shared pair, its fold, does not distinguish them. **If a shared pair is
weighted by its fold, the spread ratio stays `1` for every species and every coupling with
`8 + g ≠ 0`**, because the protection comes from axis-blindness, not from the size of `g`. This is
about the unsigned spread; that the spread ratio is the physical, boost-invariant `c` is the open
obligation of §3. The brute-force check (`relativity_scale_check.py`, `check_shared_pairs`) enumerates
the joint histories and reads `A`'s spread directly, without the symbol.

**Emitter and absorber.** `joint_symbol_swap` answers a question from
[`Collective_Electrodynamics.md`](Collective_Electrodynamics.md) §6: which half of a shared pair
belongs to the emitter and which to the absorber. Within the pair, nothing decides it. The census
sums both assignments with equal weight (the Wheeler–Feynman time symmetry), and the fold weights
them equally too, since `t·t†` and `t†·t` both fold to `−I`. By method rule 4 the assignment changes
no count here, so it is a label. If it is physical, it has to come from outside the pair: from which
strand's other closures come first, the priority order of `closedAtHorizon_mono`.

What this leaves open. The model has two strands that persist. Strands that are created or
destroyed (pair creation, a variable number of histories) are not covered, and those are where
Collins's loop integrals live in field theory. That a pair's weight is its fold is the reading
`shared_pair_fold_axis_blind` supports, not a theorem about every possible coupling. These two
points are now the whole of the open question.

## 7. How this fits the rest

- The state-space side of relativity was already proven: the interval is `det(Form)`
  ([`lean/QLF_Minkowski.lean`](lean/QLF_Minkowski.lean)), `SL(2,ℂ)` acts as the Lorentz group
  ([`lean/QLF_LorentzCover.lean`](lean/QLF_LorentzCover.lean)), and invariant mass is frame-independent
  ([`lean/QLF_EnergyMomentum.lean`](lean/QLF_EnergyMomentum.lean)). This module adds the law side:
  how the census of histories transforms.
- [`lean/QLF_MultiObserver.lean`](lean/QLF_MultiObserver.lean) proves that closure and phase are the
  same for the 96 discrete frames (signed axis permutations × gauge swap). Those frames contain no
  boosts; this module is where boosts enter.
- [`Inertia.md`](Inertia.md) kill condition 2 asked for "exact Lorentz invariance at constant
  velocity" to be proven, not asserted. The answer is that it is not exact: it holds to
  `~(L_P/r)²`.
- The prose arguments in [`SpaceTime.md`](SpaceTime.md) §4 and
  [`UniversalRelativity.md`](UniversalRelativity.md) (a uniform, stateless ether makes dilation
  reciprocal) are the intuition this module makes quantitative.
- Register: [`Open_Problems.md`](Open_Problems.md).
