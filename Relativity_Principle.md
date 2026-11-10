# The Relativity Principle in QLF — exact in the large, broken at the Planck step

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Epistemic status: proved in Lean, no axioms, including Lorentz signature.** Modules:
[`lean/QLF_RelativityScale.lean`](lean/QLF_RelativityScale.lean) (the unsigned census) and
[`lean/QLF_LorentzSymbol.lean`](lean/QLF_LorentzSymbol.lean) (the signed census and the Lorentz
signature). Brute-force cross-check: [`relativity_scale_check.py`](relativity_scale_check.py). One
question remains open, reduced to a single number (§5).

Einstein's first postulate says the laws of physics are the same for every observer in uniform
motion. QLF does not assume it. It proves two things about the census of histories instead: the
census **has** a preferred frame at the scale of a single step, and every trace of that frame
**dies away** with scale at an exact, computed rate. So the relativity principle is not a
postulate here and not exact. It is a large-scale theorem with a stated domain.

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

## 3. Where it holds: every frame-dependence dies with scale

Summing over all `8^L` histories of length `L`, with `x_i` the displacement on axis `i`
(`i = 0` time, `1..3` space):

| Theorem | Statement | Reading |
|---|---|---|
| `covariance_isotropic` | `4·Σ x_i x_j = δ_ij · L · 8^L`, exactly, at every `L` | Time and each space axis spread equally; no axis is correlated with another |
| `light_speed_from_spread` | `Σ x_t² = Σ x_a²` | The invariant speed is one Planck length per Planck tick, computed from the census rather than cancelled as in [`lean/QLF_SubstrateLightSpeed.lean`](lean/QLF_SubstrateLightSpeed.lean) |
| `first_moment_zero`, `third_moment_zero` | `Σ x_i = Σ x_i³ = 0` | No odd correction: nothing linear in the scale |
| `fourth_moment`, `mixed_fourth_moment` | `16·Σ x_i⁴ = (3L²+L)·8^L`, `16·Σ x_i²x_j² = (L²−L)·8^L` | The first moments that can see the lattice |
| `fourth_moment_anisotropy` | `Σ x_i⁴ − 3·Σ x_i²x_j² = Σ x_i²` | An isotropic distribution sets the left side to zero; the census misses by exactly its own spread |
| `anisotropy_ratio` | relative anisotropy `= 4 / (3L + 1)` | Total at one step (`= 1`), then `4/7, 2/5, 4/13, 1/4, 4/19, …` |
| `anisotropy_vanishes` | below any `ε > 0` beyond some `L₀` | The frame disappears in the large |

The spread grows as `r² = L/4` in Planck units, so the leading frame-dependence is

```
relative anisotropy = 4 / (3L + 1) ≈ (1/3) · (L_P / r)²
```

**quadratic** in the ratio of the Planck length to the scale probed. The vanishing odd moments are
why there is no linear term.

## 4. The domain where relativity works

Read in energy, `(L_P/r)²` is `(E/E_P)²`, with `E` the energy in the frame doing the measuring. The
relativity principle holds wherever `E·γ ≪ E_P` in every frame compared:

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

and it is singular exactly on the lattice light cone `sin²k₀ = Σ sin²k_a` (`symbol_light_cone`):
the census's massless modes travel at `c = 1`. For small `k`, `H(k) ≈ 2i · Form(k) = 2i σ^μ k_μ`,
the Weyl operator, which `SL(2,ℂ)` transforms covariantly
([`lean/QLF_LorentzCover.lean`](lean/QLF_LorentzCover.lean)). Each component deviates from the
covariant `k_μ` by at most `|k|³/6 + |k|⁵/100` (`symbol_deviation`), a relative correction
quadratic in `k`, the same `(L_P/r)²` as §3. So **no Wick rotation is needed**: counting ways is
Euclidean, and the phases make it Lorentzian. The zeros of `sin` at `k = π` are the lattice
doublers, as in lattice fermions.

## 6. What remains open: one number

[Collins, Perez, Sudarsky, Urrutia & Vucetich, *PRL* 93, 191301 (2004)](https://arxiv.org/abs/gr-qc/0403053)
showed that a Planck-scale preferred frame leaks into low-energy physics through quantum loops at
about the percent level unless something forbids it. Everything above is free propagation. The
question is whether interactions undo it.

`quadratic_form_frame_invariant` reduces that question to one number. Any quadratic form on
momentum space that the substrate's frame group leaves invariant is `diag(a, b, b, b)`, so the only
Lorentz violation the symmetry allows at that order is the ratio `b/a`, the speed of light in each
species. The census sets it to `1` for free propagation (`light_speed_from_spread`,
`symbol_eq_form`). If interactions shift it differently for different species, QLF has Collins's
problem. If something holds it at `1`, the problem is absent. The frame group alone does not hold
it, because it never mixes time with space.

Joint closures themselves are already proven: the two-spin joint closure is the singlet
([`lean/QLF_JointClosure.lean`](lean/QLF_JointClosure.lean)), the composite fold of `N` bodies is the
tensor product, and a shared pair folds to `t ⊗ t†`
([`lean/QLF_TensorFromClosure.lean`](lean/QLF_TensorFromClosure.lean)). Those are the joint
*states* and their algebra. What this question needs is their *momentum-space* side: the census
symbol of two histories that share pairs, and whether the shared pairs move the time/space ratio.
One structural fact points the right way: a shared pair puts `t` on one body and `t†` on the
other, so its net displacement is zero and it cannot depend on the total momentum. That is a lead,
not yet a theorem.

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
