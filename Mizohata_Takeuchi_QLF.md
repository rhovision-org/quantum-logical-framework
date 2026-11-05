# The Mizohata–Takeuchi conjecture, resurrected without the continuum

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**The question (Jim, 2026-11-02).** *"Can we resurrect a version of the conjecture that denies a
continuum? … Mizohata–Takeuchi! … 17 year old falsified."*

**Short answer.** A conditional version can be stated, and this page states it with its hypotheses
explicit. The Mizohata–Takeuchi conjecture (MT) is false in the continuum. The known counterexamples are
stated for unbounded scale `R`, and the power-loss ones for surfaces with limited smoothness. A
bounded physical domain, which is an assumption chosen separately from QLF's finite-capacity premise,
caps `R`, but **a cap alone recovers nothing**: it makes every scale-dependent
loss finite, power losses included, and it does not restore a scale-independent estimate. So the
resurrected statement has two parts. MT-A is a mathematical conjecture (open): on analytic, curved,
compact surfaces the loss is only polylogarithmic. MT-Q says that **if** MT-A holds, then free on-shell
modes in such an assumed bounded domain satisfy MT with a constant that is polylogarithmic in `R_max`, about
`C_Σ·141^c`. MT-Q adds a physical scale and a physical surface class to MT-A. It does not prove
anything MT-A does not.

---

## 1. The conjecture and its history

For a compact `C²` hypersurface `Σ ⊂ ℝ^n` with surface measure `σ`, the **extension operator** turns
a function `f ∈ L²(Σ)` into a wave on `ℝ^n`:

```
Ef(x) = ∫_Σ f(ξ) e^{2πi x·ξ} dσ(ξ)
```

When `Σ` is a piece of a paraboloid, `Ef` is a free Schrödinger wave. When it is a piece of a sphere or a
cone, it solves a Helmholtz or wave equation. The **Mizohata–Takeuchi conjecture**, named after
Mizohata and Takeuchi and arising from their work on well-posedness of dispersive (Schrödinger-type)
equations, says that for every weight `w ≥ 0`

```
∫_{ℝ^n} |Ef|² w  ≲_Σ  ‖f‖²_{L²(Σ)} · ‖Xw‖_∞ ,        Xw(ℓ) = ∫_ℓ w   (the X-ray transform)
```

So the energy a wave deposits on an arrangement of mass is bounded by the mass on the heaviest
**straight line**. The **local** form integrates over a ball `B_R` and allows a loss growing with `R`;
this page always means the local form.

**Falsified, twice.**

1. **Hannah Cairo, 2025, aged 17** ([arXiv:2502.06137](https://arxiv.org/abs/2502.06137)): a
   counterexample with loss `log R`, for every `C²` hypersurface that does not lie in a hyperplane. It
   takes `N ≈ log R` frequencies `ξ_1, …, ξ_N` on `Σ`, separated at scale `1/R`, and forms the set of
   **half-balanced sums** `Q = { Σ c_i ξ_i : c ∈ {0,1}^N, Σ c_i = ⌊N/2⌋ }`, of size about `2^N/√N`.
   The weight is built from `Q`. Shifting `Q` by any `ξ_i` lands about half of it back in a set of the
   same kind, so wave packets add constructively, while an incidence lemma shows that no hyperplane
   meets more than `2^{n−1}` of the balls around `Q`, so lines carry little weight. The ratio is about
   `N ≈ log R`.
2. **Cairo and Ruixiang Zhang, 2025** ([arXiv:2512.08064](https://arxiv.org/abs/2512.08064)): a
   **power** loss `R^α` for every `α < (n−1)/(n−1+k)`, on a family of convex `C^k` hypersurfaces dense
   in the `C^k` topology, built by projecting a higher-rank lattice. For `C²` the exponent
   `(n−1)/(n+1)` matches the upper bound of Carbery, Iliopoulou and Wang up to the endpoint.

**What these do and do not settle.** Cairo's `log R` lower bound applies to every non-planar `C²`
surface, analytic ones included. Cairo–Zhang's exponent shrinks with smoothness, but that is a property
of their construction: the limit of their exponent as `k → ∞` is **not** an upper bound for analytic
surfaces, and their abstract does not address `C^∞` or analytic surfaces. Whether analytic surfaces
(the sphere, compact paraboloid caps) can have a power loss is, as far as we know, open.

---

## 2. What a finite world does and does not change

**The premise.** QLF's realizability rule is that a bounded region holds finitely many distinguishable
states (Bekenstein; the `[Finite R]` hypothesis of `no_continuum_in_finite_region`,
[`QLF_Realizability`](lean/QLF_Realizability.lean)). That theorem proves only that an infinite set
cannot inject into a finite one. It proves no extension inequality and no constant.

**The scale cap: a separate assumption, not a consequence.** Finite distinguishability within a
bounded region does not entail a maximal radius, a Planck-length cutoff, or any identification of the
analytic `R` with a physical length. So three assumptions are kept apart:

- **(a) Finite capacity** (the Bekenstein premise above), conditional and used only as motivation.
- **(b) A bounded physical domain**, chosen separately, together with a dimensionless map from the
  analytic `R` (the ball radius measured in units of the inverse frequency scale of `Σ`) to physical
  length. Taking the shortest length to be the Planck length and the domain to be the observable
  universe is one such choice, not a theorem.
- **(c) MT-A**, the independent analytic assumption (§3).

Under choice (b), with the observable universe (radius about `4.4·10²⁶ m`) and the Planck length
(`1.6·10⁻³⁵ m`), `R_max ≈ 2.7·10⁶¹`, so

```
ln R_max ≈ 141,      and for a one-metre laboratory   ln R ≈ 80.
```

This turns Cairo's loss into a number, about 141 at most. But it turns a power loss `R^δ` into a number
too, `10^{61δ}`, which is astronomically large for any fixed `δ > 0`. **The cap is useful only if the
loss is polylogarithmic.** That is why MT-Q is conditional on MT-A and cannot replace it.

**The surface class (a named bridge, not a derivation).** In QLF the state is a 2×2 Hermitian `Form`,
and `det_toMatrix_eq_interval` ([`QLF_Minkowski`](lean/QLF_Minkowski.lean)) proves that its
determinant is the Minkowski interval when the `Form` is read as a **spacetime** vector. MT-Q needs
something different: a `Form` read as a **four-momentum**, with the free mode's Fourier support on the
quadric `det = m²` (a hyperboloid sheet for `m > 0`, the light cone for `m = 0`). That reading is
standard special relativity for free particles, but QLF has not derived it. No construction here takes
a census state to a momentum, or a closure to a Fourier-supported solution. So MT-Q is stated for an
**assumed** class: free on-shell modes. Interacting, off-shell, boundary and medium-dependent waves are
outside it.

**What is not claimed.** That the known counterexamples need non-realizable physics; that MT "fails
only in the continuum"; or that analyticity by itself bounds the information a surface carries at a
fixed finite resolution. None of these follows from the premises above.

---

## 3. The resurrected conjecture

**Surface classes, kept separate.**

- **(Σ1)** Compact analytic hypersurfaces with nonvanishing Gaussian curvature: a sphere, a compact
  cap of a paraboloid, a compact piece of one sheet of a mass hyperboloid. All three are compact pieces
  of algebraic quadrics.
- **(Σ2)** Compact truncated pieces of the light cone, away from the vertex. These have one vanishing
  principal curvature, so they are not in Σ1 and need their own statement.

**Weights and data.** `f ∈ L²(Σ)` and any measurable `w ≥ 0` with `‖Xw‖_∞ < ∞`. The frequency cutoff
is the compactness of `Σ` itself: the whole mass hyperboloid and the whole cone are noncompact and are
not covered. The spatial cutoff is the ball `B_R`.

> **MT-A (mathematics, open).** For each `Σ` in Σ1 there are constants `C_Σ, c_Σ` such that for all
> `R ≥ 2`, all `f ∈ L²(Σ)` and all `w ≥ 0`,
>
> ```
> ∫_{B_R} |Ef|² w  ≤  C_Σ (log R)^{c_Σ} · ‖f‖²_{L²(Σ)} · ‖Xw‖_∞ .
> ```
>
> **MT-A′** is the same statement for Σ2, posed separately.

The constants may depend on `Σ` (on its curvature bounds and its analytic data). MT-A says Cairo's
`log R` is the right order up to the power `c_Σ`, on analytic curved surfaces.

> **MT-Q (conditional physical reading).** Assume (i) MT-A for the compact pieces of the mass shell
> that are in Σ1, (ii) the momentum reading of the `Form` in §2, and (iii) a chosen bounded domain with its
> length map, giving `R ≤ R_max` (assumption (b) of §2). Then every free on-shell mode of mass `m > 0` whose momenta lie on a fixed compact piece
> `Σ` of the shell satisfies the local inequality at every physical scale with constant
> `C_Σ (ln R_max)^{c_Σ} ≈ C_Σ · 141^{c_Σ}`. The same holds for `m = 0` on Σ2 if MT-A′ holds.

**What MT-Q adds.** Only a physical scale and a physical surface class. Its entire mathematical
content is MT-A. If MT-A is true, the counterexamples are real theorems whose losses, for free on-shell
modes on compact shell pieces, stay polylogarithmic in `R_max`. If MT-A is false, MT-Q says nothing.

**Contrast, once.** Nothing here contradicts Cairo or Cairo–Zhang. Their theorems are correct
statements about `ℝ^n`.

---

## 4. Kill conditions

- **K1 (power loss on Σ1).** A counterexample with loss `R^δ`, `δ > 0`, on any surface in Σ1 (for
  example the sphere or a paraboloid cap) refutes MT-A, and MT-Q then carries no useful bound. This is
  the decisive test, and it belongs to harmonic analysts.
- **K1′ (power loss on Σ2).** The same for a truncated cone refutes MT-A′ and the `m = 0` clause.
- **K2 (large polylog).** A proof that the loss on Σ1 is `(log R)^c` with large `c` keeps MT-A but
  weakens MT-Q, since `141^c` stops being small.
- **K3 (the bridge).** If QLF's census, once a realization map is built, does not give the momentum
  reading of §2, MT-Q loses its surface class.
- **K4 (the domain choice).** The scale cap is an assumed domain (assumption (b)), so no experiment
  refutes it as such. If physical waves were shown to need scales beyond the chosen `R_max` (or a length
  map different from the Planck one), the constant changes with the new `R_max`. A violation of the
  Bekenstein capacity bound would remove the motivation (a) but would not by itself refute the
  separately assumed domain.

---

## 5. Connections to QLF, and how strong each one is

- **Cairo's interference set is a balance condition.** `Q` uses exactly half of the `N` frequencies,
  a central-binomial family of size about `2^N/√N`. QLF's one-axis closure census is the same count,
  `C(2n, n)` balanced words. This is a **resemblance**. Nothing here produces Cairo's construction
  from closures.
- **The failure is a straight-line failure.** The X-ray transform is a bound by straight lines, and
  the counterexamples defeat it with coherence that no line sees. In QLF's census, no closure is a
  straight line and straight histories are at most `16·2^{−L}` of all histories (proved for the census
  definitions in [`No_Continuum_Conjecture.md`](No_Continuum_Conjecture.md) §3). This is a thematic
  parallel, not an argument for MT-A or MT-Q.
- **The toy diagnostic.** A discrete test on the census wave from a point source, against nine
  substrate line families (D-MT, [`No_Continuum_Conjecture.md`](No_Continuum_Conjecture.md) §5a,
  [`discrete_mt.py`](discrete_mt.py)), failed its registered prediction: the coherent wave focuses no
  more than the classical random walk. D-MT is not the Fourier-extension inequality and has no bearing
  on MT-A or MT-Q in either direction.
- **A possible census experiment.** Build Cairo's weight from closures: take `N` twist directions,
  form the half-balanced sums, and compare the signed amplitude on them with the heaviest line, as `N`
  grows. Not run, and its relation to MT-A would itself need an argument.

---

## 6. Status at a glance

| Claim | Status |
|---|---|
| MT is false, with `log R` loss on every non-planar `C²` surface | **Theorem** (Cairo 2025) |
| Power loss `R^α`, `α < (n−1)/(n−1+k)`, on a `C^k`-dense family | **Theorem** (Cairo–Zhang 2025) |
| A bounded region has finitely many distinguishable states | **Proved** given the Bekenstein premise; it implies no extension inequality |
| Physical scale `ln R ≤ 141` | **Assumed** domain choice: observable universe in Planck units (assumption (b)); not a consequence of the Bekenstein premise; useful only with a polylog loss |
| `Form` read as four-momentum, free modes on `det = m²` | **Named bridge**, assumed (standard relativity, not derived in QLF) |
| MT-A on Σ1, MT-A′ on Σ2 | **Open** (mathematics) |
| MT-Q for free on-shell modes on compact shell pieces | **Conditional conjecture** on MT-A, the bridge and the assumed domain |
| Cairo's half-balanced set and the `C(2n,n)` census | **Resemblance** only |

---

## 7. What not to say

- Not "MT fails only in the continuum", or "the counterexamples need non-realizable physics".
- Not "a finite world rescues MT". A bounded scale makes every loss finite, including power losses.
- Not "MT holds for every physical wave". MT-Q covers assumed free on-shell modes on compact shell
  pieces, and only if MT-A holds.
- Not "Cairo–Zhang shows analytic surfaces have no power loss".
- Not "QLF predicted the counterexample", and not "D-MT supports MT-Q".

---

## See also

- [`No_Continuum_Conjecture.md`](No_Continuum_Conjecture.md): the general continuum denial, straight-line
  histories in the census, and census coherence.
- [`TheContinuum.md`](TheContinuum.md): consistency is not realizability.
- [`QLF_Minkowski`](lean/QLF_Minkowski.lean): the determinant of the state is the interval.
- [`Collective_Electrodynamics.md`](Collective_Electrodynamics.md) §5: frequencies as discrete counts.

## References

- H. Cairo, *A counterexample to the Mizohata–Takeuchi conjecture*, arXiv:2502.06137 (2025).
- H. Cairo and R. Zhang, *Power loss for the Mizohata–Takeuchi conjecture on `C^k` convex hypersurfaces*, arXiv:2512.08064 (2025).
- J. D. Bekenstein, *Universal upper bound on the entropy-to-energy ratio for bounded systems*, Phys. Rev. D **23** (1981) 287–298.
