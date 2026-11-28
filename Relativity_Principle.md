# The Relativity Principle in QLF — what the census proves, and what it does not yet

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Epistemic status.** Every theorem cited is proved in Lean with no axioms:
[`lean/QLF_RelativityScale.lean`](lean/QLF_RelativityScale.lean) (the unsigned census) and
[`lean/QLF_LorentzSymbol.lean`](lean/QLF_LorentzSymbol.lean) (the signed census, its symbol, and
shared-pair interactions), and [`lean/QLF_BoostCovariance.lean`](lean/QLF_BoostCovariance.lean) (boost
covariance of the Dirac walk), and [`lean/QLF_InteractingKinematics.lean`](lean/QLF_InteractingKinematics.lean)
(interacting kinematics and umklapp, §6a). Brute-force cross-check: [`relativity_scale_check.py`](relativity_scale_check.py).
**The relativity principle is proved for free propagation in the large, and not beyond that** (§5b).
With interactions it is open, and for the census symbol the step to a propagation law is still an
assumption, labelled where it is used.

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

5. **Free propagation is boost-covariant in the large** (§5b). The unitary Dirac walk has a derived
   energy–momentum law, and that law agrees with the Lorentz-invariant mass shell `E² = |k|² + m²`
   up to a relative correction of order `(L_P/λ)²`, in every frame where the wavelengths stay long
   (`shell_lorentz_invariant`, `diracWalk_boost_covariant`).

6. **Interacting kinematics is boost-covariant in the large** (§6a). At long wavelength a lattice
   process conserves energy–momentum exactly, so the set of allowed processes is the same in every
   frame to the same order (`process_boost_covariant`). The elementary umklapp vectors along a
   boost axis are carried off the reciprocal lattice by any non-trivial boost
   (`umklapp_x_not_covariant`); whether that is the main source of frame dependence in loops is
   open.

So the principle is not postulated. It is derived for one free particle on the Dirac walk, as an
approximation with a stated error, and for which interacting processes are allowed. It is open for
interacting amplitudes and loops.

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

## 5b. Boost covariance of free propagation: the Dirac walk

*The sign, axis pattern and coefficient of this walk's Planck-scale correction are turned into a registered prediction, with comparator and kill condition, in [`Planck_Dispersion_Prediction.md`](Planck_Dispersion_Prediction.md).*

§5 needed an assumption because a census symbol is not a propagation law. The repo has a dynamics
whose propagation law is a theorem: the unitary Dirac walk of
[`lean/QLF_DiracWalk.lean`](lean/QLF_DiracWalk.lean) ([`Closure_Unitarity.md`](Closure_Unitarity.md)
§15). It is built from twist steps, it is unitary at every step (`diracWalk_unitary`), and every
eigenvalue `e^{iE}` at momentum `k` and mass `m` satisfies the exact relation
(`diracWalk_dispersion`)

    cos E = cos m · cos k_y · cos k_x · cos k_z.

This is the palindromic walk of [`QM_Postulates_QLF.md`](QM_Postulates_QLF.md) §5b, the one whose
dispersion has no term linear in `L_P`.
[`lean/QLF_BoostCovariance.lean`](lean/QLF_BoostCovariance.lean) compares that relation with the
relativistic one. Write `S = E² + |k|² + m²` in Planck units, so `S` is about `(L_P/λ)²`.

| Theorem | Statement |
|---|---|
| `shell_taylor` | For `S ≤ 1`, the walk's shell function differs from half the Minkowski form `(E² − \|k\|² − m²)/2` by at most `S²/4` |
| `onShell_minkowski` | On the walk's shell, `\|E² − \|k\|² − m²\| ≤ S²/2` |
| `shell_lorentz_invariant` | If `(E, k)` is on the walk's shell and `(E′, k′)` has the same Minkowski form, then `(E′, k′)` satisfies the walk's shell equation up to `S²/4 + S′²/4` |
| `boost_form`, `shell_boost_invariant` | A boost along `x` with `γ² − u² = 1` preserves the form, so the boosted energy–momentum is on-shell to the same accuracy |
| `diracWalk_boost_covariant` | On the walk itself: if `e^{iE}` is an eigenvalue at `k` and `e^{iE″}` one at the boosted momentum, then `\|cos E″ − cos E′\| ≤ S²/4 + S′²/4`, where `E′` is the boosted energy |

The shell function is of order `S` and the error is of order `S²`, so the relative error is of
order `S ≈ (L_P/λ)²`. `shell_lorentz_invariant` covers every Lorentz transformation at once, boosts
in any direction and rotations, because it only uses that the form is preserved.

**What this settles.** For a free particle on the Dirac walk, an observer moving at constant
velocity finds the same energy–momentum law, to `(L_P/λ)²`. That is the relativity principle for
free propagation, with the propagation law derived and the boost physical. Both obligations left
open by §3 and §5 are met for this dynamics.

**The domain.** The bound needs `S′ ≤ 1` as well as `S ≤ 1`: the wavelength must stay long compared
with `L_P` in the boosted frame too. A boost with `γ` near `λ/L_P` blue-shifts the mode to the
lattice scale, and there the theorem says nothing. So the principle is a close approximation that
fails for boosts large enough to resolve the lattice, which is the challenge to exact relativity
that §2 began. At `γ = 10¹¹` (the highest-energy cosmic-ray protons) the lattice is still `10⁸`
times finer than the boosted proton's Compton wavelength.

**What stays open.**

- *Interactions.* This is one free particle. §6 gives a partial result for shared pairs in the
  census; boost covariance of interacting histories is not proved.
- *One way, not the way.* The Dirac walk is a unitary dynamics the substrate carries. That nature's
  propagation is this walk and no other is not proved, and the census symbol of §5 is a different
  object whose off-axis sign disagrees with it.
- *Exactness.* The error term is real: `shell_taylor` is a bound on a non-zero remainder, and §2
  already shows exact invariance is impossible.

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

## 6a. Interacting processes: the kinematic layer, and where the lattice frame enters

§5b is one free mode. An interaction adds a vertex, and a vertex has to conserve energy–momentum.
On a translation-invariant lattice with a time-periodic step it conserves **lattice**
energy–momentum: incoming total minus outgoing total is a reciprocal-lattice vector `2π·n`,
`n ∈ ℤ⁴` (Bloch's theorem; quasi-energy is a phase `e^{iE}`, so it is conserved mod `2π` too).
Processes with `n ≠ 0` are **umklapp** processes. [`lean/QLF_InteractingKinematics.lean`](lean/QLF_InteractingKinematics.lean)
takes that conservation law as the definition of a lattice process and proves, with no axioms:

| Theorem | Statement |
|---|---|
| `no_umklapp` | if, for every component, the legs' total `Σ\|p\|` is below `2π`, a lattice process conserves energy–momentum **exactly** |
| `umklapp_needs_short_wave` | so a genuine umklapp process has a component whose **leg total** reaches `2π`. This bounds the sum over legs, not any single leg |
| `umklapp_leg_bound` | in an umklapp process with `N + M` legs, some leg has a component of magnitude at least `2π/(N + M)`: a lattice-scale leg is forced only at bounded valence |
| `soft_umklapp` | the bound is needed: four incoming legs of `π/2` along `x` are an umklapp process with no leg at the lattice scale (and `n` legs of `2π/n` work for any `n`) |
| `map_exactConserving` | exact conservation is linear, so every Lorentz map (linear, preserving `E² − \|k\|²`) keeps it |
| **`process_boost_covariant`** | a long-wavelength lattice process with every leg on the Dirac walk's shell, seen from any Lorentz frame that keeps the legs long-wavelength, is again an exactly conserving lattice process, with every leg on the walk's shell to `S²/4 + S′²/4` |
| `walk_leg_onShell` | the walk's actual eigenmodes meet the leg hypothesis |
| `twoBody_translation_commute`, `twoBody_conserves_momentum` | a two-body walk with any contact interaction (a phase depending on relative position) commutes with joint translation, so it carries a state of definite total lattice momentum to one of the same momentum: the conservation law above, for an actual interacting step |
| `planeWave_jointShift`, `char_unique`, `momChar_eq` | on `ℤ³` a two-body plane wave has the character of its total momentum `k₁ + k₂`; a non-zero state has one character; two momenta give the same character exactly when they differ by a reciprocal vector |
| **`twoBody_lattice_conservation`** | so if the interacting step sends the plane wave `(k₁, k₂)` to a non-zero state of total momentum `K′`, then `k₁ + k₂ − K′ ∈ 2π ℤ³`: lattice momentum conservation **derived** for this walk |
| `quasiEnergy_mod`, `scattering_latticeConserving` | equal step phases have energies differing by a multiple of `2π`, and a two-to-two scattering with both properties is a lattice-conserving `Process` in the sense of the first rows |
| **`umklapp_x_not_covariant`**, **`umklapp_t_not_covariant`** | for every boost along `x` with `u ≠ 0`, the elementary umklapp vectors `2π e_x` and `2π e_t` are carried **off** the reciprocal lattice, so the boosted observer sees a process that conserves nothing, exactly or mod `2π` (the proof reduces to: integers with `a² − b² = 1` have `b = 0`) |

The number of incoming and outgoing legs is arbitrary, so pair creation and annihilation are
covered **as kinematics**.

**What this settles.** Which interacting processes are allowed is the same in every frame, in the
long-wavelength sector, to the order of §5b. Umklapp is one place the lattice frame shows in
interacting kinematics: the two elementary umklapp vectors along a boost axis do not survive a
boost. It is not shown to be the only place. The finite-spacing shell corrections of §5b are frame
dependence that is present even when momentum is conserved exactly, and the two no-go theorems do
not classify every reciprocal vector (a boost with rational `γ`, `u` can map some of them into the
lattice, for example `γ = 5/3`, `u = 4/3` takes `2π·(3,0,0,0)` to `2π·(5,4,0,0)`). Nor does umklapp
need a Planck-scale leg in general: at a vertex of valence `N + M` the forced scale is
`2π/(N + M)` (`umklapp_leg_bound`, `soft_umklapp`).

**What it does not settle.** This is tree-level kinematics, not dynamics. No amplitude is compared
between frames, and no loop is treated. A loop sums over every intermediate momentum, including the
lattice-scale ones where neither `no_umklapp` nor the shell bound of §5b applies. That region is
where the [Collins et al. (2004)](https://arxiv.org/abs/gr-qc/0403053) leakage would come from.
Loops are not constructed here, so no decomposition of a loop into frame-dependent and
frame-independent parts is proved; bounding the lattice-scale contribution to low-energy
observables is an open obligation, and a test the framework could fail.
For a two-body contact-interaction walk on `ℤ³` the conservation law is now derived, not assumed (`twoBody_lattice_conservation`). For more than two bodies it is still the definition of a process, and which out-momenta a given step actually produces is dynamics, not covered.

**The dependency chain to interacting boost covariance.**

| Stage | Status | What it needs |
|---|---|---|
| 1. Free propagation covariant in the large | proved (§5b, `diracWalk_boost_covariant`) | — |
| 2. Interacting kinematics covariant in the large, given lattice conservation and the summed long-wavelength bound; elementary umklapp vectors along a boost axis are not boost-stable | proved (this section, `process_boost_covariant`, `umklapp_x_not_covariant`) | — |
| 3. Lattice conservation derived for a concrete interacting walk | **proved for two bodies on `ℤ³`** with any contact interaction (`twoBody_lattice_conservation`, `scattering_latticeConserving`) | `N` bodies: the same argument with an `N`-fold joint shift; labour |
| 4. Amplitudes covariant at tree level | **4a done**: the frame-comparison map is defined (§6b, approved 2026-11-22), its algebra is proved (`QLF_BoostStates`), and the walk's band is covariant to `O(κ²)` on the half-step slice (pre-registered, PASS). **4b done on its grid**: the relative boost defect of the two-body tree-level vertex proxy scales as `κ²` for scalar, vector and nearest-neighbour scalar contacts (pre-registered, PASS); the spin-blind contact of stage 3 has an `O(1)` defect (predicted, confirmed); the spin-blind vertex is not boost invariant (`QLF_BoostAmplitudes`) | **4c**: stage-3 conservation extended to a matrix-valued contact (`QLF_SpinorContact`); the half-step slice is its own time reverse, the structural reason for `O(κ²)` (`QLF_HalfStepReversal`). Open: the analytic `O(κ²)` bound; energy-conserving amplitudes; which contact the substrate gives (§6b, "Which contact?") |
| 5. Loops: lattice-scale contribution small at low energy (Collins) | open, **blocked on a definition and on analysis** | a loop expansion of the interacting walk, and a bound on the lattice-scale part of the Brillouin-zone sum (umklapp and finite-spacing shell corrections both). §6's axis-blind result is the census-side partial answer |
| 6. Pair creation as a change in census strand number | open, **blocked on a definition** | the census with a variable number of strands; §6 has two persistent strands only |
| 7. Conservative return: interacting record → closure invariants | `NOT_STARTED` | stages 3–6 |

## 6b. Stage 4: how a boost acts on the walk's states

Stage 4 compares amplitudes between frames, and an amplitude is an inner product of states. The
lattice fixes one frame, so no operator on the walk's states is a boost. The comparison map has to
be defined. Jim approved this definition on 2026-11-22:

1. **States.** A finite sum of plane waves `Σ |k⟩ ⊗ v_k`, each spinor `v_k` in the walk's
   positive-energy band at `k`, with `k` and the mass of size at most `κ`.
2. **Energy.** Each mode carries the walk's own energy `E(k)` (`diracWalk_dispersion`).
3. **Momentum.** A Lorentz map `Λ` (`QLF_InteractingKinematics.Lorentz`) sends `(E(k), k)` to
   `(E′, k′)`, and the mode lands at `k′`.
4. **Spin.** With `A ∈ SL(2,ℂ)` covering `Λ` ([`lean/QLF_LorentzCover.lean`](lean/QLF_LorentzCover.lean)),
   the spinor turns by `S(A) = fix slash ⊗ A + fix slash̄ ⊗ (Aᴴ)⁻¹`, using the walk's own
   handedness split.
5. **Landing.** `S(A) v_k` is projected onto the walk's positive band at `k′` and rescaled by
   `√(E(k)/E(k′))`.
6. **Domain.** Defined only while the boosted packet stays long-wavelength (`S′ ≤ 1`, §5b).

The spin part is borrowed from the continuum for now. Deriving it from a moving closure loop
([`lean/QLF_Inertia.lean`](lean/QLF_Inertia.lean)) is the native alternative, not yet attempted.

### Pre-registration: does the walk's band carry Dirac covariance to second order?

The map is a covariant comparison only if the walk's band transforms like a Dirac band up to
`O(κ²)`. A first-order defect would be a frame dependence at `O(L_P/λ)`, which breaks the
principle at low energy. [`boost_states_check.py`](boost_states_check.py) measures it. This
section was committed before the script was run on the walk. Only the continuum calibration was
run beforehand, to fix the sign conventions.

**Quantity.** For a walk step with positive-band projector `P(k)` and energy `E(k)`, the covariant
projector is `Π(k) = E(k) P(k) β`, the walk analogue of `(p̸ + m)/2`. For a boost of rapidity `η`
along axis `i`, `S = exp(η α_i / 2)`, the defect is `‖S Π(k) S⁻¹ − Π(k′)‖_max / E′`. It vanishes
for the continuum Dirac operator.

**Grid.** Twelve directions (seed `20261122`), mass ratios `m/|k| ∈ {0.5, 1}`, the three boost
axes, `η = 0.5`, and `κ ∈ {0.08, 0.04, 0.02, 0.01, 0.005}`. The graded number is the log–log slope
of the worst defect against `κ`.

**Slices.** The same walk is graded at two time slices: `raw` (`massStep(m) · handed(k)`, the
Lean `diracWalk`) and `half` (`massStep(m/2) · handed(k) · massStep(m/2)`). They differ by a
`k`-independent unitary and have the same spectrum.

**Criteria.**

| Check | Pass | Fail |
|---|---|---|
| Calibration: continuum Dirac defect | below `10⁻¹²` | otherwise the script is wrong and nothing is graded |
| **Graded: `half` slope** | `≥ 1.8`: covariance holds to second order, and stage 4 proceeds on the half-step slice | `< 1.5`: a first-order frame dependence. Stage 4b fails as defined and is reported as failed, not redefined |
| `raw` slope (expectation, not graded) | about `1`, because the product `massStep · handed` has a second-order term `[mβ, α·k]` that the symmetric slice removes | — |

A slope between `1.5` and `1.8` is inconclusive and leads to a finer grid, not a verdict.

### Result

| Check | Measured | Verdict |
|---|---|---|
| Calibration: continuum Dirac defect | `3.0 × 10⁻¹⁶` | the script is sound |
| **`half` slope** | **`2.000`** (worst defect `4.9 × 10⁻⁴` at `κ = 0.08`, `1.9 × 10⁻⁶` at `κ = 0.005`) | **PASS** |
| `raw` slope | `1.000` (worst defect `2.4 × 10⁻²` at `κ = 0.08`) | as expected: first order, not graded |

Data: [`data/boost_states_check.json`](data/boost_states_check.json). **The walk's band is Dirac covariant to
second order on the half-step slice, so stage 4 proceeds there.** The raw slice is first order
only because its time slice sits inside the mass step. The two slices differ by the fixed unitary
`massStep(m/2) = 1 + O(κ)`, so the raw slice's spinors are rotated by a first-order amount, and the
borrowed `S(A)` does not see that rotation. The definition above is therefore read on the
half-step slice. This is a refinement of step 4 recorded after the run, not a change to the
criteria.

**Clarifications after review (2026-11-24).** These do not change the registered grid, criteria
or readings; they make the quantity and the gates explicit.

- In the defect, `Π(k′)` is `E′ P(k′) β`, where `E′` is the **boosted continuum energy**
  `E(k) cosh η + kᵢ sinh η`, not the walk's own energy `E(k′)` at the boosted momentum. The two
  differ by the stage-1 shell error.
- The script now fails closed. It reports `INVALID, NOT_GRADED` and exits non-zero unless the
  calibration is finite and below `10⁻¹²`, every walk step has a positive band of rank exactly 2,
  every graded defect sample is finite and non-zero, every calibration and control sample is
  finite, and the fitted slope is finite. Each sample is checked before the max or min is taken, so
  one bad sample cannot be hidden by the reduction.
- A negative control was added: the continuum Dirac band boosted with the wrong spinor sign
  `exp(−η αᵢ/2)` must give a defect of at least `10⁻²` at every `κ`. It gives `0.342` at every `κ`,
  so the defect detects a wrong boost. [`tests/test_boost_states_check.py`](tests/test_boost_states_check.py)
  checks each gate trips.
- The fitted slope is evidence on this finite grid. It is not a uniform asymptotic theorem, and it
  does not test the projected and rescaled packet map's composition law or any interacting
  amplitude.

How strong is the pass? It is structural, not a surprise. A symmetric product `e^{X/2} e^{Y} e^{X/2}`
has no second-order term in its logarithm, so the half-step generator is the Dirac operator plus
`O(κ³)`, and the band follows to `O(κ²)`. The raw slice shows the check could have failed.

### Stage 4a: the algebra, proved

[`lean/QLF_BoostStates.lean`](lean/QLF_BoostStates.lean) proves the map's algebra, with no axioms:

| Theorem | Statement |
|---|---|
| `chiral_mul`, `chiral_one`, `handed_eq_chiral` | `chiral R L` acts by `R` on the right-handed part and `L` on the left-handed; it is multiplicative, and the walk's own handed step is `chiral (W k) (W (−k))` |
| `beta_chiral_beta` | the mass generator `β` swaps the two parts |
| `chiralAct_mul`, `chiralAct_one` | `chiralAct A = chiral A (Aᴴ)⁻¹` is a homomorphism |
| `chiralAct_neg` | `−A` acts as minus `A`: the double cover on spinors |
| `chiralAct_chirality` | the action preserves handedness |
| `chiralAct_of_unitary` | a unitary `A` (a rotation) acts as `1 ⊗ A`, alike on both parts; a boost does not |
| `halfWalk_eq_conj`, `halfWalk_unitary`, `halfWalk_dispersion` | the half-step slice is the Lean walk conjugated by `massStep(m/2)`, so it is unitary with the same shell `cos E = cos m Π cos kᵢ` |
| `dirac_boostZ_covariant` | for a boost along `z`, `S (E + H(k, m)) β S⁻¹` is exactly the boosted `(E′ + H(k′, m)) β`: the continuum anchor the walk is compared against |

**What this settles.** The approved map is well defined, is a representation of `SL(2,ℂ)` up to
the double-cover sign, and is exact on the continuum Dirac form. On the walk it is covariant to
`O(κ²)` at the half-step slice, numerically on the pre-registered grid.

**What it does not settle.** The `O(κ²)` bound is numerical, not proved. Stage 4b, the comparison
of interacting amplitudes, is below. The spin part is borrowed from
the continuum, not derived from a moving closure loop.

### Stage 4b pre-registration: tree amplitudes of the two-body contact walk

Stage 4b compares an interacting amplitude between frames. [`boost_amplitudes_check.py`](boost_amplitudes_check.py)
measures it. This subsection was committed before the script was run on the walk. Only the
continuum calibration and control were run beforehand, to fix sign conventions and the control's
statistic.

**Amplitude.** Two walk particles `A` and `B` (masses `m_A`, `m_B`) meet on one site and pick up a
contact phase `exp(i g Γ)`, with `Γ` acting on the joint spinor space. To first order in `g`, the
tree level, the amplitude from `(k₁, k₂)` to `(k₁′, k₂′)` is the matrix element of `Γ` between band
states, times the coupling's Fourier transform `ĝ(q)` at the transfer `q = k₁′ − k₁`. Band
eigenvectors carry arbitrary phases, so the graded quantity is the spin-summed square

`W(p) = |ĝ(q)|² Tr[(Π₁′ ⊗ Π₂′) Γ (Π₁ ⊗ Π₂) Γ†]`, with `Π = E P(k)`.

For the continuum Dirac operator and a Lorentz-scalar vertex, `W` is invariant. Each leg is
carried by the stage-4a map: frame 1 uses the walk's own energy `E(k)`, frame 2 the boosted
`(E′, k′) = Λ(E(k), k)` with the walk's projector at `k′`. The defect is
`|W(Λp) − W(p)| / |W(p)|`.

**Vertices.**

| Arm | `Γ` | Continuum reading | Prediction |
|---|---|---|---|
| `scalar` | `β ⊗ β` | `ψ̄ψ ψ̄ψ`, a Lorentz scalar | covariant to `O(κ²)`, as the band |
| `vector` | `1 ⊗ 1 − Σᵢ αᵢ ⊗ αᵢ` | `J^μ J_μ`, a Lorentz scalar | covariant to `O(κ²)` |
| `range` | `β ⊗ β` with `ĝ(q) = 1 + ½ Σᵢ 2 cos qᵢ` (nearest-neighbour range) | instantaneous finite range: `ĝ` depends on the 3-vector `q` | covariant to `O(κ²)`: `q` is of size `κ`, so `ĝ(q′)/ĝ(q) − 1 = O(κ²)` |
| `blind` | `1 ⊗ 1` | `J⁰ J⁰`, the time component of a vector current only | **frame dependent at `O(1)`**, not suppressed by `κ` |

The `blind` arm is the contact of `QLF_InteractingKinematics.twoBodyStep` as written (stage 3): a
scalar `g(x₁ − x₂)` that ignores spin. In the continuum, a spin-blind density contact is a `J⁰ J⁰`
coupling, which is not a Lorentz scalar. So the prediction is that the stage-3 walk, as written, is
**not** covariant at tree level, for a reason that has nothing to do with the lattice: its vertex
picks a frame. The fix it points to is a contact that carries spinor structure (`β ⊗ β` or the
vector form).

**Grid.** Twelve sample pairs of unit directions `d, d′` (seed `20261125`), centre-of-momentum
elastic kinematics `k₁ = p d`, `k₂ = −p d`, `k₁′ = p d′`, `k₂′ = −p d′`, with `|(p, m_A)| = κ`,
`m_A/p ∈ {0.5, 1}`, `m_B = 0.6 m_A`; the three boost axes; `η = 0.5`;
`κ ∈ {0.08, 0.04, 0.02, 0.01, 0.005}`. Half-step slice graded; raw slice reported, not graded.
The graded number is the log–log slope of the worst defect against `κ`.

**Criteria.**

| Check | Pass | Fail |
|---|---|---|
| Calibration: continuum `scalar` and `vector` | below `10⁻¹²` (measured before registration: `9 × 10⁻¹⁶`, `5 × 10⁻¹⁶`) | otherwise nothing is graded |
| Control: continuum `blind`, median defect | `≥ 10⁻²` at every `κ` (measured before registration: `0.78`; the least sample is `0.0047`, which is why the median is used) | otherwise nothing is graded |
| **Graded: `scalar`, `vector`, `range` slopes** | `≥ 1.8`: tree amplitudes covariant to second order | `< 1.5`: a first-order frame dependence; stage 4b fails for that vertex and is reported as failed |
| **Graded: `blind`** | prediction confirmed if the slope is below `0.5` and the worst defect stays `≥ 10⁻²` at every `κ` | otherwise the prediction failed, and is reported as failed |

A slope between `1.5` and `1.8` is inconclusive and leads to a finer grid, not a verdict. Every
sample is checked before reduction (finite non-zero `W`, finite positive defect), and a non-finite
slope makes the run `INVALID`.

### Stage 4b result

| Check | Measured | Verdict |
|---|---|---|
| Calibration: continuum `scalar`, `vector` | `9.1 × 10⁻¹⁶`, `5.1 × 10⁻¹⁶` | the script is sound |
| Control: continuum `blind`, median defect | `0.78` at every `κ` | the defect detects a frame-dependent vertex |
| **`scalar` slope** | **`2.001`** (worst defect `2.9 × 10⁻³` at `κ = 0.08`, `1.1 × 10⁻⁵` at `κ = 0.005`) | **PASS** |
| **`vector` slope** | **`2.000`** (`1.8 × 10⁻³` to `7.1 × 10⁻⁶`) | **PASS** |
| **`range` slope** | **`2.001`** (`3.0 × 10⁻³` to `1.2 × 10⁻⁵`) | **PASS** |
| **`blind`** | slope `0.000`, worst defect `6.43` at every tested `κ` | **prediction confirmed**: frame dependent at `O(1)` on the grid |
| raw slice (not graded) | `scalar`, `vector`, `range` slopes `2.00`; `blind` `0.00` | the spin-summed `W` does not see the raw slice's fixed spinor rotation at first order |

Data: [`data/boost_amplitudes_check.json`](data/boost_amplitudes_check.json).

**On the tested grid, the relative boost defect of the two-body contact walk's tree-level vertex proxy
`W` scales as `κ²` for the three Lorentz-scalar vertices tested**: the scalar `ψ̄ψ ψ̄ψ` form, the vector
`J^μ J_μ` form, and the scalar form with a nearest-neighbour range. An instantaneous finite range is
not Lorentz invariant at finite `κ`; it enters through `ĝ(q)` at `q ~ κ`, and its frame dependence
scales as `κ²` on this grid. The finite range was the predicted failure point in the stage-4 plan,
and on this grid it does not show at first order. These are observed scalings on four vertices and
five values of `κ`, not a classification of vertices and not an all-`κ` result.

**The stage-3 walk as written fails.** Its contact is a scalar phase `g(x₁ − x₂)` that ignores
spin, which is a `J⁰ J⁰` coupling. Its tree amplitude changes by order one under a boost at every
`κ`, in the continuum as much as on the walk. This is not a lattice effect. The vertex itself picks
a frame. The natural candidates for a covariant two-body walk are contacts with spinor structure,
`exp(i g β ⊗ β)` or the vector form. These are matrix-valued, and `twoBodyStep` takes a scalar
`g(x₁ − x₂)`, so the stage-3 conservation theorems do not yet cover them: extending
`twoBody_translation_commute` and `twoBody_lattice_conservation` to a matrix-valued contact that
depends only on relative position is a stated generalization still to be checked in Lean.

[`lean/QLF_BoostAmplitudes.lean`](lean/QLF_BoostAmplitudes.lean) proves the vertex part, with no
axioms:

| Theorem | Statement |
|---|---|
| `chiral_conjTranspose` | `(chiral R L)ᴴ = chiral Rᴴ Lᴴ` |
| `scalar_bilinear_invariant` | for every `A` with invertible determinant, `Sᴴ β S = β`: the scalar density is the same in every frame |
| `scalar_vertex_invariant` | so `S ⊗ S` preserves the scalar contact `β ⊗ β` |
| `blind_density_not_invariant` | for a `z`-boost with `a·b = 1`, `a² ≠ 1`, `Sᴴ S ≠ 1`: the spin-blind density changes with the frame |
| `blind_vertex_not_invariant` | so the spin-blind contact `1 ⊗ 1` is not preserved by any genuine boost |

**What this settles.** At tree level, with the approved map and on the tested grid, the vertex
proxy's relative boost defect scales as `κ²` for the scalar, vector and nearest-neighbour scalar contacts, and the
spin-blind contact of stage 3 has an order-one defect at every tested `κ`. Proved, independent of
`κ`: the spin action preserves the scalar vertex and no genuine boost preserves the spin-blind one.

**Clarifications after review (2026-11-26).** These do not change the registered grid, criteria
or readings.

- `W` is a **vertex proxy**, not an energy-conserving S-matrix element. The grid is elastic for
  the continuum shell, but the walk's shell `cos E = cos m Π cos kᵢ` is not isotropic, so equal
  `|k|` in different directions need not give equal quasi-energy. The script now reports the
  worst relative mismatch `|E₁ + E₂ − E₁′ − E₂′| / (E₁ + E₂)` on the half-step slice as a
  diagnostic, not graded: `1.0 × 10⁻⁴` at `κ = 0.08` falling to `4.0 × 10⁻⁷` at `κ = 0.005`, i.e.
  `O(κ²)`, the stage-1 shell error.
- `W` is a spin-summed square, so every sample must now be real and positive, with a relative
  imaginary residual of at most `10⁻¹²`, or the run is `INVALID`. The largest residual on the grid
  is `1.5 × 10⁻¹⁶`. Tests cover a negative and a complex `W`.

**What it does not settle.** The `O(κ²)` bounds are numerical on a finite grid, not proved. The
vector vertex's invariance is numerical only. Tree level is first order in `g`; loops are
stage 5. Which contact the substrate itself selects, scalar, vector or spin-blind, is not derived
here: §6's shared pair folds to `−I` on every axis, which is a statement about the census weight,
not about the spinor structure of a contact on the walk.

### Stage 4c: the matrix contact, and why the half-step slice is second order

**Conservation for a contact with spinor structure.** [`lean/QLF_SpinorContact.lean`](lean/QLF_SpinorContact.lean)
restates stage 3 for a contact `G(x₁ − x₂)` that is any linear map on the joint spinor space, with no
axioms. The scalar contact of `twoBodyStep` is the case `G r = g r • id` (`spinorStep_of_scalar`).
The step commutes with joint translation (`spinorStep_translation_commute`), conserves total
lattice momentum as a character (`spinorStep_conserves_momentum`), and on `ℤ³` conserves it mod
the reciprocal lattice (`spinorStep_lattice_conservation`). The proof uses only that `G` depends
on the relative position and is linear; unitarity is not needed. The stage-4b scalar contact
`exp(i g β ⊗ β) = cos g + i sin g β ⊗ β` is unitary (`scalarContact_unitary`). This closes the
obligation recorded in the 4b review: the covariant contacts carry the stage-3 conservation law.

**The structural reason for `O(κ²)`.** [`lean/QLF_HalfStepReversal.lean`](lean/QLF_HalfStepReversal.lean)
proves, with no axioms, that the half-step slice is its own time reverse:

| Theorem | Statement |
|---|---|
| `handed_neg` | `handed(−k) = handed(k)ᴴ` |
| `massStep_neg` | `massStep(−m) = massStep(m)ᴴ` |
| **`halfWalk_reversal`** | `halfWalk(−k, −m) = halfWalk(k, m)ᴴ` |
| `halfWalk_reversal_inv` | so `halfWalk(−k, −m) · halfWalk(k, m) = 1` |

Write the step as `exp(−i H(p))` with `p = (k, m)` and eigenphases in `(−π, π)`. Reversal says
`U(−p) = U(p)⁻¹`, so the generator is odd in `p` and has no `κ²` term; its first-order term is the
Dirac operator (`realWalk_generator` and the mass step), so `H = H_Dirac + O(κ³)` and the band
follows the Dirac band to `O(κ²)`. The raw slice is not its own reverse: its adjoint is
`handed(−k) · massStep(−m)`, the factors in the opposite order. Numerically, at
`k = (0.03, −0.02, 0.05)`, `m = 0.04`, the reversal defect is `4.0 × 10⁻³` for the raw slice and
`1.1 × 10⁻¹⁶` for the half-step slice. This is why stage 4a found slope 1 on one slice and 2 on the
other, and why stage 4b's scalings are 2.

**What stays open.** The analytic step, a matrix logarithm of `U` near `1` with a Taylor bound on
its cubic remainder, is not formalized, so the `O(κ²)` bounds of 4a and 4b are still numerical.
The reversal theorem is the reason they hold; it is not the bound.

### Which contact? Substrate readings, not yet a derivation

Stage 4b showed that the contact must be a Lorentz scalar. Nothing yet says which contact the
substrate's own shared pairs give. Two checks, both **exploratory and not pre-registered**
(`python3 boost_amplitudes_check.py --exploratory`), narrow the question:

| Candidate reading | Vertex | Continuum worst defect | Half-slice slope |
|---|---|---|---|
| Axis-blind shared pairs, every axis with the same sign (§6: every shared pair folds to `−I`) | `1 ⊗ 1 + Σᵢ αᵢ ⊗ αᵢ` | `11.8` at every `κ` | `0.00` |
| Pseudoscalar | `γ⁵`-type `⊗` `γ⁵`-type | `2 × 10⁻¹⁴` | `2.00` |

So the most direct reading, a shared pair on each of the four axes weighted alike, gives the
**Euclidean** combination, and it picks a frame at order one. A Lorentz-scalar contact needs either
the **Minkowski relative sign** between the gauge channel and the spatial channels, which is what
turns the Euclidean sum into the vector form `1 ⊗ 1 − Σᵢ αᵢ ⊗ αᵢ`, or a contact through the **mass
channel** alone, `β ⊗ β`. Both have a substrate source to try. The signed census already carries
the Minkowski sign in free propagation (`symbol_det`), so a shared pair weighted by its signed
phase, rather than by its unsigned fold, may inherit it. And the mass step `exp(i m β)` is the
walk's only closure between the two chiral halves, so a shared mass tick gives `β ⊗ β`. Which
reading the substrate takes is a definition to be chosen and then tested. It is not derived here,
and the axis-blind result of §6 does not settle it, because §6 is about the unsigned census weight.

## 7a. Claim-record status and open obligations

This result is **formal `F` for free propagation** and **`B-OPEN` for the physical/interacting bridge**. The detailed record is [`claim_records/relativity_boost.json`](claim_records/relativity_boost.json).

| Component | Status |
|---|---|
| Free Dirac-walk shell covariance in the long-wavelength regime | `F`; anchors in the 375-entry baseline (`shell_taylor`, `shell_lorentz_invariant`, `shell_boost_invariant`, `diracWalk_boost_covariant`) |
| Census limits / Lorentz-symbol determinant | `F`; anchors in the same baseline |
| Interacting kinematics (allowed processes) covariant in the large, conditional on lattice conservation; elementary umklapp vectors not boost-stable | `F`; `QLF_InteractingKinematics` (§6a), audit anchors added |
| Frame-comparison map for the walk's states (stage 4a) | `F` for its algebra (`QLF_BoostStates`); `N` for `O(κ²)` covariance of the band on the half-step slice (pre-registered PASS, [`boost_states_check.py`](boost_states_check.py)) |
| Tree amplitudes of the two-body contact walk (stage 4b) | `F` for the vertex part: the scalar contact is preserved by the spin action, the spin-blind one is not (`QLF_BoostAmplitudes`); `N` for `O(κ²)` covariance of scalar, vector and finite-range amplitudes, and `O(1)` frame dependence of the spin-blind one (pre-registered, [`boost_amplitudes_check.py`](boost_amplitudes_check.py)) |
| Interacting boost covariance (amplitudes, loops) | `B-OPEN`; conservative return `NOT_STARTED`; dependency chain in §6a |
| Kinetic reading of the census symbol | assumption, not a theorem |
| Census-vs-walk off-axis sign | open; the palindromic walk has the opposite sign |
| Identification of the spread ratio with physical `c` | open; requires the interacting case |

**No Paper I bridge is promoted.** The free-shell theorem is a reusable formal fact; it is not a physical validation of the relativity principle. The open obligations are tracked in issue [#207](https://github.com/rhovision-org/quantum-logical-framework/issues/207), [`Open_Problems.md`](Open_Problems.md), and the [FlowChart](FlowChart.md).

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
  velocity" to be proven, not asserted. The answer is that it is not exact: for free propagation it
  holds to `~(L_P/λ)²` (§5b).
- The prose arguments in [`SpaceTime.md`](SpaceTime.md) §4 and
  [`UniversalRelativity.md`](UniversalRelativity.md) (a uniform, stateless ether makes dilation
  reciprocal) are the intuition this module makes quantitative.
- Register: [`Open_Problems.md`](Open_Problems.md).
