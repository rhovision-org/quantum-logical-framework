# The Mizohata–Takeuchi conjecture, resurrected without the continuum

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**The question (Jim, 2026-11-02).** *"Can we resurrect a version of the conjecture that denies a
continuum? … Mizohata–Takeuchi! … 17 year old falsified."*

**Short answer.** Yes. The Mizohata–Takeuchi conjecture (MT) is false in the continuum, and every
known counterexample uses the continuum in an essential way: either the scale `R` grows without bound,
or the frequency surface has non-analytic structure tuned at every scale. Remove both and a precise
version survives. In a finite-information world the scale is capped, and the physical frequency
surface is the algebraic mass shell of QLF's `Form`. On that surface MT holds up to a factor of at
most about `C·141^c` across the whole observable universe, provided the logarithmic loss Cairo found
is the true order for analytic surfaces. That last proviso is open mathematics, and it is where the
resurrected conjecture can fail (§4).

---

## 1. The conjecture and its history

For a compact `C²` hypersurface `Σ ⊂ ℝ^n` with surface measure `σ`, the **extension operator** turns
a function `f` on `Σ` into a wave on `ℝ^n`:

```
Ef(x) = ∫_Σ f(ξ) e^{2πi x·ξ} dσ(ξ)
```

It is a superposition of plane waves whose frequencies lie on `Σ`. When `Σ` is a paraboloid,
`Ef` is a free Schrödinger wave; when `Σ` is a sphere or a cone, it is a Helmholtz or wave-equation
solution. The **Mizohata–Takeuchi conjecture**, named after Mizohata and Takeuchi and arising from
their work on well-posedness of dispersive (Schrödinger-type) equations, says that for every weight
`w ≥ 0`

```
∫_{ℝ^n} |Ef|² w  ≲  ‖f‖²_{L²(Σ)} · ‖Xw‖_∞ ,        Xw(ℓ) = ∫_ℓ w   (the X-ray transform)
```

So the energy a wave deposits on any arrangement of mass is bounded by the mass on the heaviest
**straight line**. The local form restricts to a ball `B_R` and allows a loss growing with `R`.

**Falsified, twice.**

1. **Hannah Cairo, 2025, aged 17** ([arXiv:2502.06137](https://arxiv.org/abs/2502.06137)): a
   counterexample with loss `log R` for every `C²` hypersurface that does not lie in a hyperplane. It
   takes `N ≈ log R` frequencies `ξ_1, …, ξ_N` on `Σ`, separated at scale `1/R`, and forms the set of
   **half-balanced sums** `Q = { Σ c_i ξ_i : c ∈ {0,1}^N, Σ c_i = ⌊N/2⌋ }`, of size about `2^N/√N`.
   The weight is built from `Q`. Shifting `Q` by any `ξ_i` lands about half of it back in a set of
   the same kind, so wave packets add constructively there, while an incidence lemma shows that no
   hyperplane meets more than `2^{n−1}` of the balls around `Q`, so every line carries little weight.
   The ratio is about `N ≈ log R`.
2. **Cairo and Ruixiang Zhang, 2025** ([arXiv:2512.08064](https://arxiv.org/abs/2512.08064)): a
   **power** loss `R^α` for every `α < (n−1)/(n−1+k)`, on a family of convex `C^k` hypersurfaces dense
   in the `C^k` topology, built by projecting a higher-rank lattice. For `C²` the exponent
   `(n−1)/(n+1)` matches the upper bound of Carbery, Iliopoulou and Wang up to the endpoint.

**Two facts that the rest of this page uses.**

- Cairo's loss needs `R → ∞`. At any fixed scale it is a finite number, `≈ log R`.
- Cairo–Zhang's power exponent shrinks as smoothness grows: `(n−1)/(n−1+k) → 0` as `k → ∞`. Their
  abstract does not address `C^∞` or analytic surfaces (the sphere, the paraboloid, the cone), and for
  those only Cairo's `log R` lower bound is known to us.

---

## 2. Where the counterexamples use the continuum

QLF's realizability rule is that a bounded region holds finitely many distinguishable states
(Bekenstein; the `[Finite R]` hypothesis of `no_continuum_in_finite_region`,
[`QLF_Realizability`](lean/QLF_Realizability.lean)). Applied to MT it touches both counterexamples.

**The scale is capped.** The local inequality at scale `R` compares structure on `B_R` with
frequency resolution `1/R`. Physically, `R` is a length in Planck units, and it is bounded by the
largest region there is. For the observable universe (radius about `4.4·10²⁶ m`, Planck length
`1.6·10⁻³⁵ m`) the ratio is `R_max ≈ 2.7·10⁶¹`, so

```
ln R_max ≈ 141,      and for a one-metre laboratory   ln R ≈ 80.
```

Cairo's counterexample is real, but in a finite world its loss is a bounded number. It uses
`N ≈ log R` separated frequencies, so even at the universe's own resolution it never uses more
than about 141.

**The physical frequency surface is algebraic.** In QLF the state is a 2×2 Hermitian `Form`, and its
determinant is the Minkowski interval (`det_toMatrix_eq_interval`,
[`QLF_Minkowski`](lean/QLF_Minkowski.lean)). A free mode of mass `m` therefore has its frequencies on
the quadric `det = m²`: a sheet of the two-sheeted hyperboloid for `m > 0`, the light cone for
`m = 0`, whose nonrelativistic limit is the paraboloid. These surfaces are algebraic, so in
particular analytic. A `C^k` surface that is not `C^{k+1}`, with structure tuned at every scale, is
specified by unboundedly many independent numbers. That is a continuum object, and no closure has it
as its dispersion relation.

So the two continuum ingredients are exactly the two that the counterexamples need: unbounded `R`
for Cairo, and non-analytic surfaces for the power loss.

---

## 3. The resurrected conjecture

> **MT-A (mathematics, open).** For every compact analytic hypersurface `Σ ⊂ ℝ^n` with nonvanishing
> Gaussian curvature, and for the light cone, there are `C, c` such that for all `R ≥ 2`, all `f` and
> all `w ≥ 0`,
>
> ```
> ∫_{B_R} |Ef|² w  ≤  C (log R)^c · ‖f‖²_{L²(Σ)} · ‖Xw‖_∞ .
> ```
>
> That is, on analytic surfaces the loss is polylogarithmic, and Cairo's `log R` is the right order up
> to the power `c`.

> **MT-Q (the continuum-denying reading).** Every physically realizable wave has its frequencies on the
> mass shell `det(Form) = m²` and lives at a scale `R ≤ R_max`. If MT-A holds for the mass shell, then
> every physically realizable wave satisfies Mizohata–Takeuchi with the universal constant
> `C·(ln R_max)^c ≈ C·141^c`. MT fails only in the continuum: as `R → ∞` (Cairo), or on non-analytic
> surfaces (Cairo–Zhang).

**What is assumed.** That nature is logical, plus the Bekenstein premise. QLF's `Form` is one model of
the mass shell; the mass shell itself is standard special relativity, so MT-Q does not depend on
nature being QLF's construction.

**What MT-Q adds to the mathematics.** MT-A is a statement about harmonic analysis and stands or falls
there. MT-Q is the claim that MT-A is the *whole* physical content of Mizohata–Takeuchi: the
counterexamples are real theorems about continuum objects, and they do not reach any wave that a
finite-information world can contain. This is the pattern of [`TheContinuum.md`](TheContinuum.md):
consistent mathematics, unrealizable in the case that breaks.

**Contrast, once.** Nothing here contradicts Cairo or Cairo–Zhang. Their theorems are correct
statements about `ℝ^n`. MT-Q says which of those statements describe a physical wave.

---

## 4. Kill conditions

- **K1 (power loss on an analytic surface).** A counterexample with loss `R^δ`, `δ > 0`, on the sphere,
  paraboloid, hyperboloid or cone refutes MT-A. The physical constant would then be at least
  `10^{61δ}`, and MT-Q would carry no useful bound. This is the decisive test, and it belongs to
  harmonic analysts. Cairo–Zhang's exponent `(n−1)/(n−1+k)` tending to `0` with smoothness is
  consistent with MT-A, but it does not prove it.
- **K2 (large polylog).** A proof that the analytic loss is `(log R)^c` with large `c` keeps MT-A but
  weakens MT-Q: `141^c` stops being small.
- **K3 (non-analytic physics).** A physical dispersion relation that is genuinely non-analytic at all
  scales would put Cairo–Zhang's power loss within reach of real waves. QLF predicts none.
- **K4 (realizability).** Any physical region holding more distinguishable states than its Bekenstein
  bound refutes the scale cap.

---

## 5. The QLF connections, and how strong each one is

- **Cairo's interference set is a balance condition.** `Q` uses exactly half of the `N` frequencies,
  a central-binomial family of size about `2^N/√N`. QLF's one-axis closure census is the same count,
  `C(2n, n)` balanced words. This is a **resemblance**, not a derivation. Nothing here produces
  Cairo's construction from closures.
- **The failure is a straight-line failure.** The X-ray transform is a bound by straight lines, and
  the counterexamples defeat it with coherence that no line sees. In the census no closure is a
  straight line at all, and straight histories are at most `16·2^{−L}` of all histories (proved in
  [`No_Continuum_Conjecture.md`](No_Continuum_Conjecture.md) §3).
- **The census does not reproduce the mechanism.** A discrete MT test on the census wave from a point
  source, with the substrate's nine straight lines, failed as registered: the coherent wave focuses in
  space no more than the classical random walk ([`No_Continuum_Conjecture.md`](No_Continuum_Conjecture.md)
  §5a, [`discrete_mt.py`](discrete_mt.py)). This is consistent with MT-Q: a finite census of a
  point source is not where MT breaks.
- **What would connect them.** A census construction of Cairo's weight: take `N` twist directions,
  form the half-balanced sums as closures, and measure the ratio of the signed amplitude on them to
  the heaviest substrate line, as `N` grows to the capacity limit. MT-Q predicts the ratio grows like
  `N` and stops at about 141. Not run.

---

## 6. Status at a glance

| Claim | Status |
|---|---|
| MT is false in the continuum, with `log R` loss on every non-planar `C²` surface | **Theorem** (Cairo 2025) |
| Power loss `R^α`, `α < (n−1)/(n−1+k)`, on a `C^k`-dense family | **Theorem** (Cairo–Zhang 2025) |
| Physical scale capped at `ln R_max ≈ 141` | **Follows** from the Bekenstein premise and the observed size of the universe |
| Physical frequency surface is the algebraic mass shell | **Proved** for QLF's `Form` (`det_toMatrix_eq_interval`); standard in relativity |
| MT-A: polylog loss on analytic surfaces | **Open** (mathematics) |
| MT-Q: MT holds for every realizable wave, constant `≈ C·141^c` | **Conjecture**, conditional on MT-A |
| Cairo's half-balanced set and the `C(2n,n)` census | **Resemblance** only |

---

## 7. What not to say

- Not "QLF rescues Mizohata–Takeuchi" or "Cairo was wrong". Cairo's theorems are correct; MT-Q is
  about which waves are physical.
- Not "MT holds". MT-Q is conditional on MT-A, which is open.
- Not "QLF predicted the counterexample".
- Not "the continuum is inconsistent". It is consistent; the claim is that the waves which break MT
  are not realizable.

---

## See also

- [`No_Continuum_Conjecture.md`](No_Continuum_Conjecture.md): the general continuum denial, the
  straight-line failure, and the census coherence.
- [`TheContinuum.md`](TheContinuum.md): consistency is not realizability.
- [`QLF_Minkowski`](lean/QLF_Minkowski.lean): the determinant of the state is the interval.
- [`Collective_Electrodynamics.md`](Collective_Electrodynamics.md) §5: frequencies as discrete counts.

## References

- H. Cairo, *A counterexample to the Mizohata–Takeuchi conjecture*, arXiv:2502.06137 (2025).
- H. Cairo and R. Zhang, *Power loss for the Mizohata–Takeuchi conjecture on `C^k` convex hypersurfaces*, arXiv:2512.08064 (2025).
- J. D. Bekenstein, *Universal upper bound on the entropy-to-energy ratio for bounded systems*, Phys. Rev. D **23** (1981) 287–298.
