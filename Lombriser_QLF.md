# Lombriser's Cosmology Read on the [QLF](README.md) Substrate

Lucas Lombriser (University of Geneva) has two proposals about the cosmological constant. This doc
records what QLF says about each one, whether QLF can derive it, and the pre-registered test of the
one that could have changed a count. The test is in [`Cosmological_Constant.md`](Cosmological_Constant.md)
§5.9, proved in [`lean/QLF_GlobalConstraint.lean`](lean/QLF_GlobalConstraint.lean) (no axioms) and
run in [`global_constraint_epochs.py`](global_constraint_epochs.py). Status labels follow
[`ScientificApproach.md`](ScientificApproach.md) §3.

| Proposal | What QLF says | Status |
|---|---|---|
| [**Minkowski frame**](#1) (2023): static space, evolving masses | Derivable from logic alone as a choice of units, so it changes no count | **bookkeeping** (rule 4) |
| [**Global constraint**](#2) (2019): the gravitational action of the whole spacetime vanishes | A zero-action condition, as ZFA is. The only average QLF can use, over what has closed so far, gives `Ω_Λ = 0.52` at recombination | **rejected route** (kill condition met) |
| [**Future-including average**](#3) | Lombriser's own reading, which needs the future to contribute to a closure | **open** |

<a id="1"></a>

## 1. Cosmology in Minkowski space (2023)

**The claim.** Lombriser, *Cosmology in Minkowski space*, Class. Quantum Grav. (2023),
arXiv:2306.16868. A spatially flat expanding universe is conformally flat. The transformation
`g̃ = Ω²g` maps it onto static Minkowski space, where length, time and mass scales vary instead. In
that frame the "constants" evolve. A field pervading spacetime sets the particle masses. Distant atoms
had smaller masses and emitted lower-frequency light, and that is the redshift. Observations are
unchanged, because they are dimensionless ratios. In his words, the cosmological constant problem
"simply seems to disappear in this new perspective on the cosmos." Dark energy need not be a
substance, and fluctuations of the field could act like an axion field, a dark-matter candidate.

The homogeneous part is a reformulation of ΛCDM. The testable part is **conformal inhomogeneities**,
proposed to ease the `H₀`, `S₈` and CMB lensing-amplitude tensions. They predict enhanced redshifts to
distant galaxy clusters, and lensing masses that exceed kinematic or dynamical masses.

**What QLF already says.**

- **Redshift is time dilation.** QLF reads redshift as clock rate (`f = 1/t`,
  [`UniversalRelativity.md`](UniversalRelativity.md)). A rest mass is a closed null circulation, so
  `m = hf/c²` ([`lean/QLF_Inertia.lean`](lean/QLF_Inertia.lean)). "Masses evolve" and "clock rates
  evolve" are one statement.
- **Expansion is a count.** [`Time.md`](Time.md) §6 states `R_H/l_P = T_U/Δt_P`. What grows is a
  dimensionless count of synthesized events ([`SpaceTime.md`](SpaceTime.md) §6).
- **No conflict with the drift bound.** [`AgeOfUniverse.md`](AgeOfUniverse.md) excludes a Planck tick
  that drifts *relative to atomic clocks*. That bound is on a dimensionless ratio. Lombriser's scaling
  moves every mass together, the Planck mass included, so no ratio changes.

**The derivation, and why it is cheap.** An observation is a ratio of counts. So any rescaling that
multiplies every length, time and inverse mass by the same spacetime-dependent factor leaves every
observation fixed. Holding `R_H` fixed while `l_P` shrinks (masses grow) and holding `l_P` fixed while
`R_H` grows describe the same count `N = R_H/l_P`. This uses no assumption that nature *is* QLF's
construction, only that observations are logical ratios
([`Philosophy.md`](Philosophy.md) §3d).

It fails the method's rule 4. The equivalence holds for every history, because it is a change of
units, so it supports neither QLF nor Lombriser. QLF reaches the same verdict for colour frames
([`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) §35): no closure count distinguishes the
frames, so the frame is a gauge choice.

**Where the reading differs.** Lombriser keeps a continuum metric and a scalar field as primitives. In
QLF a field is a reading of closure counts, and the continuum is its rendering. The difference matters
only where it changes a prediction, which is the inhomogeneous sector. QLF's analogue of a spatially
varying mass scale is the spatially varying clock rate that QLF identifies with gravity. Whether that
gives Lombriser's two signs (a cluster redshift excess, lensing mass greater than dynamical mass) has
not been computed.

<a id="2"></a>

## 2. The global constraint (2019): tested, and it fails

**The claim.** Lombriser, *On the cosmological constant problem*, Phys. Lett. B (2019), 134804,
arXiv:1901.08588. Promote the Planck mass to a global variable and vary the action with respect to it.
That forces `∫√−g (R − 2Λ) d⁴x = 0`. With the trace of Einstein's equations it becomes
`M_p²Λ = ½⟨T⟩`, the four-volume average of the matter trace (`⟨T⟩ = ⟨ρ_m⟩` for dust in his
convention). Vacuum energy drops out of what gravitates, and `Λ` is constant. A typicality argument over
the formation of bound structures gives `Ω_Λ ≈ 0.704`.

**Why it bears on QLF.** It is a global zero-action condition, and ZFA is a zero-action condition
([`Lagrangian_Formulation.md`](Lagrangian_Formulation.md)). If ZFA could supply it, QLF would get the
constant `Λ` the data favor. Every horizon reading in [`Cosmological_Constant.md`](Cosmological_Constant.md)
§5.7–§5.8 failed to give one.

**Two steps, stated before any computation (§5.9).**

1. *Identification:* QLF's free action is the Einstein–Hilbert density `R − 2Λ`. QLF has no
   gravitational action density, so this step was not attempted. Making it by definition would be
   naming, not deriving (R6a).
2. *Average:* closure is irrevocable (`closedAtHorizon_mono`) and the future is not yet synthesized,
   so the average QLF can use runs over what has closed so far:
   `⟨ρ_m⟩_t = ∫₀ᵗ ρ_m a³ dt′ / ∫₀ᵗ a³ dt′`. That makes `Λ` epoch-dependent.

**Kill condition:** `Ω_Λ > 0.06` at recombination (Doran & Robbers 2006).

**Result.** Proved in [`lean/QLF_GlobalConstraint.lean`](lean/QLF_GlobalConstraint.lean), no new
axioms:

- **G1** `lombriser_relation`, `lombriser_relation_avg`: the trace relation and the constraint give
  `M²Λ = ½⟨T⟩`. This is algebra, the anchor of his relation, and bookkeeping by rule 4.
- **G2** `closedAvg_matter_era`: in a matter era, the closed-so-far average is exactly `3 ρ_m(t)`.
- **G3** `omegaLambda_matter_era`, `omegaLambda_exceeds_bound`: so `ρ_Λ = (3/2) ρ_m` and
  `Ω_Λ = 3/5` at every matter-era epoch, above `0.06`.

The self-consistent history with radiation ([`global_constraint_epochs.py`](global_constraint_epochs.py)):

| `z` | `Ω_m` | `Ω_r` | `Ω_Λ` | `ρ_Λ/ρ_m` | `q` |
|---|---|---|---|---|---|
| `10⁵` | 0.032 | 0.928 | 0.040 | 1.26 | 0.96 |
| `3400` | 0.299 | 0.293 | 0.408 | 1.37 | 0.64 |
| `1100` | 0.364 | 0.116 | **0.520** | 1.43 | 0.55 |
| `0` | 0.400 | 0.000 | **0.600** | 1.50 | 0.50 |

`Ω_Λ(z = 1100) = 0.52`, nine times the bound. Today's `0.60` is 12σ below Planck's `0.685 ± 0.007`. The
term redshifts like matter (`ρ_Λ/ρ_m` runs from `5/4` in the radiation era to `3/2`), so `q = +½` and
the expansion never accelerates. That is reading A's failure in §5.7, reached by a different route.

<a id="3"></a>

## 3. What is left open

Lombriser's constant `Λ` comes from averaging over the whole four-volume, future included. QLF can
keep his mechanism only by saying what a not-yet-synthesized future contributes to a closure. That is
the objection §5.7 raised against the future-event-horizon reading C, now in sharper form. Step 1 (free
action = `R − 2Λ`) matters only for that reading. The inhomogeneous sector of §1 is open on both sides.

## 4. Side by side

| | Lombriser | QLF |
|---|---|---|
| What redshift is | evolving masses in static space (one frame) | clock rate; redshift = time dilation |
| Status of the frame choice | physically equivalent reformulation | gauge choice; changes no count |
| Primitive | continuum metric plus a scalar field | closure counts; field and continuum are readings |
| Why vacuum energy doesn't gravitate | global zero-action constraint | holographic surface counting, `(R_H/L_P)²` |
| `Λ` over time | constant (future-including average) | not derived; the closed-so-far version is excluded (§2) |
| Today's `Ω_Λ` | `≈ 0.704` (typicality argument) | `log 2 ≈ 0.693` (a fit, no longer derived) |
| Dark matter | axion-like field fluctuations (proposed) | MOND-like `a₀ = cH₀/2π` ([`DarkMatter.md`](DarkMatter.md)) |
| Testable signature | cluster redshift excess; lensing mass > dynamical mass | none computed for these observables |

## Sources

- Lombriser, L. (2023). *Cosmology in Minkowski space*. Class. Quantum Grav., doi:10.1088/1361-6382/acdb41,
  arXiv:2306.16868.
- Lombriser, L. (2019). *On the cosmological constant problem*. Phys. Lett. B, 134804,
  doi:10.1016/j.physletb.2019.134804, arXiv:1901.08588.
- Space.com (2023), *The expansion of the universe could be a mirage, new theoretical study suggests*,
  https://www.space.com/universe-expansion-could-be-a-mirage, for Lombriser's own statements.
- Doran, M., & Robbers, G. (2006). *Early dark energy cosmologies*. JCAP 0606:026.
- Planck Collaboration (2020). *Planck 2018 results. VI. Cosmological parameters*. A&A 641, A6.

Related: [`Cosmological_Constant.md`](Cosmological_Constant.md), [`Curvature.md`](Curvature.md) §8,
[`Open_Problems.md`](Open_Problems.md), [`Mysteries_Of_Physics.md`](Mysteries_Of_Physics.md).
