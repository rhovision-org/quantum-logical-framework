# The Lumina Simulation Read on the [QLF](README.md) Substrate

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Lumina** (October 2026) is the largest cosmological radiation-hydrodynamics simulation yet run: the
first ~2 billion years of cosmic history in a box 500 comoving Mpc (about 1.5 billion light-years) on a
side, with hydrogen and helium reionization followed together for the first time. This doc asks what
QLF's proved results say about what Lumina simulates, and keeps the two apart: what is a theorem, what is
bookkeeping, what is a prediction, and what QLF cannot yet say. Every number below is computed by
[`lumina_qlf.py`](lumina_qlf.py) (pure Python, no fitted parameter, under a second).

**The one contrast, stated once.** Lumina runs standard ΛCDM: cold dark matter particles, a constant
`Λ`, Planck initial conditions, and the IllustrisTNG galaxy model. QLF does not reproduce Lumina and
does not derive its initial conditions. What QLF has is a set of machine-checked statements about four
of Lumina's ingredients (expansion, dark matter, the ionizing atomic physics, and discreteness), and
two of those statements make predictions that Lumina's epoch can test.

---

## At a glance

| Lumina ingredient | QLF result | Lean anchor | Status |
|---|---|---|---|
| A finite mesh (2 × 6000³ cells, 6 frequency bins) standing in for a continuum | A finite-information region holds no faithful copy of a continuum; whatever is realized is finite | [`no_continuum_in_finite_region`](lean/QLF_Realizability.lean), `realized_state_space_is_finite` | **Proved**, but bookkeeping (§1) |
| Constant `Λ` in the expansion history | Two QLF readings put `Ω_Λ ≈ 0.6–0.7` throughout reionization; a third puts 4–9 % there | [`omegaLambda_eq_log_two`](lean/QLF_InflationObserver.lean), [`omegaLambda_matter_era`](lean/QLF_GlobalConstraint.lean), [`rhoLambda_prop_Hsq`](lean/QLF_DynamicalDarkEnergy.lean) | Readings A, B and closed-so-far **rejected**; reading C an **open candidate** (§2) |
| Cold dark matter particles | Closure-balance law `g_obs² = g_bar(g_obs + a₀)` with `a₀ = cH/2π`, scaling with `H(z)` | [`radialAccel_self_consistent`](lean/QLF_DarkMatter.lean), `radialAccel_ge_baryonic`, `mond_acceleration_horizon_form` | **Prediction**: at `z ≈ 6`, `a₀` is 10× today's. A post hoc look at six JADES galaxies is consistent (§3) |
| Ionizing thresholds 13.6 eV (H I) and 54.4 eV (He II) | `Ry = ½α²m_ec²` from Coulomb-by-gauge-twist plus closure-depth quantization | [`Hydrogen.md`](Hydrogen.md) §4 (structural), [`QLF_DiracCorrection`](lean/QLF_DiracCorrection.lean) | **Consistency**; the `Z²` He II scaling is the standard Bohr step (§4) |
| Thomson optical depth `τ = 0.055` | QLF's `1/α = 137.032` moves `σ_T` by `6 × 10⁻⁵`, so `τ` by `3 × 10⁻⁶` | [`QLF_FineStructureSubstrate`](lean/QLF_FineStructureSubstrate.lean) | **Predicted null**: invisible in reionization data (§4) |
| Helium abundance, hence the helium electrons | `Y_p = 2r/(1+r)`, so `Y_p = 1/4` at `r = 1/7`; He III adds 1/14 of the final electrons | [`helium_fraction_one_seventh`](lean/QLF_Nucleosynthesis.lean) | **Proved funnel**, `r` imported (§4) |
| AGN and the first supermassive black holes | Hadron horizons are Planck-scale Markov blankets; nothing on seeding | [`QLF_QuantumBlackHole`](lean/QLF_QuantumBlackHole.lean) | **Open**: no QLF result bears on it (§5) |
| Growth of structure after recombination | Local closure-balance contraction against the global expansion | [`radialAccel`](lean/QLF_DarkMatter.lean), [`structure_growth_qlf.py`](structure_growth_qlf.py) | **Pre-registered test failed** (overshoot: 50 Mpc collapses at `z = 14`) (§7) |
| Initial conditions (`n_s`, amplitude, transfer functions) | No inflaton; inflation and dark energy share the `w = −1` field; observables not derived | [`cosmic_inflation_in_progress`](lean/QLF_CosmicInflation.lean) | **Open** (§5) |

---

## What Lumina is

From the methods paper (Zier, Smith, Shen, Liu, Kannan, Koehler, Springel, Pakmor, Vogelsberger,
Bulichi & Hernquist, arXiv:2605.15310; MNRAS 552, DOI 10.1093/mnras/stag1469):

- **Code.** The AREPO moving mesh with the IllustrisTNG galaxy-formation model and a GPU M1
  radiation-transport solver in six frequency bins, run on more than 15,000 GPUs on Frontier.
- **Scale.** `2 × 6000³` resolution elements in a 500 cMpc box; baryon mass resolution
  `3.6 × 10⁶ M☉`, dark matter `1.9 × 10⁷ M☉`. Baryon–dark-matter streaming is in the initial conditions.
- **Reionization.** Hydrogen reionization is late and mostly driven by stars: the median sub-volume is
  ionized by `z ≈ 5.2`, with neutral patches to `z ≈ 4.75`. Helium II reionization is driven by AGN
  and nearly complete by `z = 3`.
- **Optical depth.** The companion paper (arXiv:2605.18939) finds a mean light-cone CMB optical depth
  `⟨τ_LOS⟩ = 0.0550`, about 7 % above the volume-weighted `0.0515`. The mass-weighted value `0.0544`
  recovers most of the gap, sightline-to-sightline scatter is at least 5 %, and smoothing the ionization
  field on scales of about 3 cMpc or more biases `τ` low.

---

## 1. A simulation is a finite closure inventory

**Proved.** [`no_continuum_in_finite_region`](lean/QLF_Realizability.lean): no injection from an
infinite state space into a finite one. With the Bekenstein bound as the physical premise, a bounded
region holds only finitely many distinguishable states, so any faithful realization of physics in it is
finite (`realized_state_space_is_finite`). Lumina is such a realization: `4.3 × 10¹¹` cells, six photon
bins, a finite number of time steps. Its continuum equations are a rendering that the code never
evaluates. That is QLF's reading of the continuum in general ([`TheContinuum.md`](TheContinuum.md)).

**Why this is bookkeeping.** By rule 4 of [`Philosophy.md`](Philosophy.md) §3a, a claim earns physical
content only when it changes a count of ways. Every simulation ever run is finite, whether nature is
discrete or not, so Lumina's finiteness is no evidence for QLF. It is recorded here because it is true
and because it sets up the point that follows.

**A methodological match, also not evidence.** Lumina's own optical-depth result is an instance of rule 3
in the same section: pick the statistic the question demands before measuring. The volume-weighted mean
ionized fraction is the wrong statistic for `τ`, because electrons sit where the gas is dense and dense
gas ionizes on its own schedule. The light-cone integral is the observable, and the mass-weighted mean
is the summary that tracks it. Smoothing on 3 cMpc or more averages the density–ionization correlation
away, and `τ` comes out low. QLF would make the same choice, but the result is ordinary convexity and
needs no QLF premise.

---

## 2. The expansion clock during reionization

Lumina holds the expansion history fixed at Planck ΛCDM, where dark energy is negligible during
reionization: `Ω_Λ = 0.6 %` at `z = 6` and `3.3 %` at `z = 3`. QLF's dark-energy readings differ from
that in this window, and the proved theorems say by how much.

**Reading A** (`L = c/H`, the literal `Ω_Λ = log 2`). [`omegaLambda_eq_log_two`](lean/QLF_InflationObserver.lean)
proves that with `ρ_Λ ∝ H²` ([`rhoLambda_prop_Hsq`](lean/QLF_DynamicalDarkEnergy.lean)) the fraction is
`log 2` at every epoch. Holding today's `H₀` and matter, the expansion during reionization is `1.77×`
ΛCDM's, so the clock runs short:

| `z` | age, ΛCDM (Gyr) | age, reading A (Gyr) | `H_A / H_ΛCDM` |
|---|---|---|---|
| 3.0 (He II done) | 2.14 | 1.21 | 1.75 |
| 5.2 (H I done) | 1.11 | 0.63 | 1.77 |
| 8.0 (`τ` excess peaks) | 0.64 | 0.36 | 1.78 |

Lumina's "first two billion years" ends at `z ≈ 3` in ΛCDM. Under reading A the same redshift arrives
at 1.2 Gyr, and the stars have about 56 % of the time to ionize the same gas. Reading A was already
rejected ([`Cosmological_Constant.md`](Cosmological_Constant.md) §5.7: no acceleration, and BBN fails);
this is a further, independent conflict.

**Closed-so-far global constraint.** [`omegaLambda_matter_era`](lean/QLF_GlobalConstraint.lean) proves
`Ω_Λ = 3/5` at every matter-era epoch, so the whole reionization window is covered too. Already rejected
([`Lombriser_QLF.md`](Lombriser_QLF.md) §2).

**Reading C** (future event horizon, same `C² = log 2`). This is the one surviving candidate, and
reionization is where it differs most visibly from ΛCDM at early times:

| `z` | `Ω_de`, reading C | `Ω_Λ`, ΛCDM | `H_C / H_ΛCDM` |
|---|---|---|---|
| 3.0 | 8.7 % | 3.3 % | 1.016 |
| 5.2 | 4.5 % | 0.9 % | 1.005 |
| 8.0 | 2.7 % | 0.3 % | 0.999 |
| 10.0 | 2.0 % | 0.2 % | 0.996 |

The dark-energy fraction is several times ΛCDM's, but the expansion rate stays within 2 % because
reading C also has slightly less matter (`Ω_m = 1 − log 2 = 0.307`). **Expected null:** a 2 % shift in
`H(z)` moves the reionization clock by about 2 %, well inside the uncertainty from the escape fraction
and the galaxy model. Lumina-class runs will not separate reading C from ΛCDM. Its live test remains the
CMB shift parameter, where it is currently 7.2σ low before a refit
([`Cosmological_Constant.md`](Cosmological_Constant.md) §5.7).

---

## 3. Dark matter at `z ≈ 6`: where QLF and Lumina disagree

Lumina's dark matter is particles. In QLF there are none: the extra pull is the closure environment,
written as a ZFA conjunction. A closure must satisfy both the local condition (sourced by the baryons)
and the cosmological one (the background closure rate `a₀`), which gives

`g_obs² = g_bar · (g_obs + a₀)`, with `a₀ = cH/2π`.

**Proved** in [`QLF_DarkMatter`](lean/QLF_DarkMatter.lean): `radialAccel_self_consistent` (the root
satisfies the balance), `radialAccel_newtonian` (Newton when `a₀ = 0`), `radialAccel_ge_baryonic` (the
apparent extra mass is never negative), `radialAccel_ge_geometric_mean` (the Tully–Fisher floor), and
`mond_acceleration_horizon_form` (`a₀ = c²/2πR_H`).

**What QLF adds over standard MOND: `a₀` follows `H(z)`.** Every local observer measures
`a₀/(cH) = 1/2π`. Seen from today, `a₀` therefore scales as `H(z)/H₀`. The pre-registered test in
[`DarkMatter.md`](DarkMatter.md) §5c preferred this expansion clock over an age clock and over a
constant `a₀` out to `z = 1.3`. Lumina's window pushes it much further:

| `z` | `H(z)/H₀` | `a₀` (10⁻¹⁰ m/s²), `H₀ = 67.4` | `a₀`, `H₀ = 72.9` |
|---|---|---|---|
| 0 | 1.0 | 1.04 | 1.13 |
| 3.0 | 4.6 | 4.8 | 5.2 |
| 6.0 | 10.4 | 10.9 | 11.8 |
| 10.0 | 20.5 | 21.4 | 23.1 |

At `z = 6`, `a₀ ≈ 10⁻⁹ m/s²`. A compact galaxy with `g ≈ 10⁻⁹` is Newtonian today and halfway into the
low-acceleration regime at `z = 6`. So QLF predicts that early galaxies show a large mass discrepancy at
accelerations where local galaxies show almost none. Constant-`a₀` MOND predicts a small one, and CDM
predicts whatever the halo concentration and baryon fraction give, which is what Lumina computes.

**A post hoc look at existing data.** de Graaff et al. (2024, A&A 684, A87) measured ionized-gas
kinematics of six JADES galaxies at `z = 5.5–7.4` and found dynamical masses about 3× the total
baryonic mass (3–4 for all but one object). The balance law gives
`M_dyn / M_bar = g_obs / g_bar = 1 + a₀(z)/g_obs`, with `g_obs = G M_dyn / (1.8 r_e²)` from their
Table 3 and Eq. 4:

| galaxy | `z` | `r_e` (kpc) | `g_obs` (10⁻¹⁰) | QLF, `H₀ = 67.4` | QLF, `H₀ = 72.9` | constant `a₀` |
|---|---|---|---|---|---|---|
| NS-00016745 | 5.57 | 1.94 | 3.5 | 3.8 | 4.1 | 1.3 |
| NS-00019606 | 5.89 | 0.69 | 2.4 | 5.4 | 5.8 | 1.5 |
| NS-00022251 | 5.80 | 0.72 | 2.5 | 5.2 | 5.5 | 1.5 |
| NS-00047100 | 7.43 | 0.67 | 12.3 | 2.2 | 2.3 | 1.1 |
| NS-10016374 | 5.50 | 0.51 | 8.3 | 2.2 | 2.3 | 1.1 |
| NS-20086025 | 7.26 | 1.88 | 4.5 | 4.1 | 4.4 | 1.3 |

QLF gives 2.2–5.4 (median 4.0) against an observed ~3. Constant-`a₀` MOND gives 1.1–1.5. **This is not
evidence.** The data were seen before this calculation, the gas masses are inferred from star-formation
rates (the authors' alternative reading moves `M_bar` by a factor of ~3), `k_tot = 1.8` can vary by a
factor of 2, and the sample is six objects. What it shows is that the expansion clock gets the size of
the discrepancy right where constant `a₀` does not, so the test is worth running properly.

**Proposed test, frozen in the commit that adds this doc.** On any kinematic sample at `z > 4` not
used here, with per-galaxy baryonic masses:

- **Statistic.** `Q = (M_dyn/M_bar − 1) · g_obs / a₀(z)`, per galaxy, with `a₀(z) = cH(z)/2π` on Planck
  ΛCDM `H(z)` at `H₀ = 67.4`. QLF predicts `Q = 1` for every galaxy, whatever its `z` or `g_obs`.
- **Kill condition.** The sample median of `Q` lies outside `[0.4, 2.5]` (the band allows for the
  factor-2 `k_tot` and factor-3 gas-mass systematics the source names), **or** `Q` correlates with `z`
  at fixed `g_obs` (that would mean `a₀` is not following `H(z)`).
- **The CDM comparison** is Lumina's own mock kinematics, or zoom runs on the same model where the
  `3.6 × 10⁶ M☉` mass resolution does not resolve kiloparsec cores.

**What QLF lacks here, and it is the larger gap.** Lumina's cosmic web grows from Planck initial
conditions through cold-dark-matter gravitational collapse. QLF has no derived linear growth, no
matter power spectrum and no transfer function, so it cannot build Lumina's initial conditions or its
web. Every MOND-like account must still explain the CMB acoustic peaks and early structure growth
without particle dark matter, and QLF has not done that. It is open, not a principled boundary.

---

## 4. The atomic physics of reionization

**The thresholds.** Hydrogen ionizes at `Ry = 13.6 eV`, helium I at 24.6 eV, helium II at 54.4 eV.
[`Hydrogen.md`](Hydrogen.md) §4 derives `Ry = ½α²m_ec²` structurally (Coulomb as gauge-twist exchange,
plus closure-depth quantization), numerically within the Bohr model's own 0.05 %; the Dirac step is
[`QLF_DiracCorrection`](lean/QLF_DiracCorrection.lean). Helium II is hydrogen-like with charge 2, so its
threshold is `4 Ry`, which is the standard Bohr scaling and is not separately anchored in the repo.
That factor of 4 is why Lumina needs AGN for helium: stellar spectra run out of photons above 54 eV,
and only accreting black holes supply them. QLF agrees and adds nothing new here.

**The optical depth is blind to QLF's α.** Thomson scattering has `σ_T = (8π/3) r_e²` with
`r_e = αħ/(m_e c)`. QLF's structural value `1/α = 137.032` (`w = ½`,
[`Alpha_Residual.md`](Alpha_Residual.md)) differs from CODATA 2022 `137.035999177(21)` by `0.004`.
That moves `σ_T` by `5.8 × 10⁻⁵`, and `τ = 0.055` by `3 × 10⁻⁶`. Lumina's own sightline scatter is
`3 × 10⁻³` and Planck's error on `τ` is about `7 × 10⁻³`. **Predicted null:** no α effect is visible in
reionization data. A `τ` anomaly attributed to `α` would contradict QLF.

**Helium electrons.** [`helium_fraction_one_seventh`](lean/QLF_Nucleosynthesis.lean) proves
`Y_p = 2r/(1+r) = 1/4` at the freeze-out ratio `r = 1/7`. Then `n_He/n_H = Y/(4(1−Y)) = 1/12`, and the
electrons per hydrogen nucleus are 1 (H II), `13/12` (plus He II), `7/6` (plus He III). Helium II
reionization, the part Lumina is first to follow with hydrogen, adds 1/14 of the final free electrons
(13/12 → 7/6), and adds them late (`z ≲ 4`), where they contribute little to `τ`. The funnel is proved; `r` is imported
from the standard weak rates ([`Open_Problems.md`](Open_Problems.md)), so the 1/4 is not a QLF
prediction.

---

## 5. What QLF does not say about Lumina

- **Black-hole seeds and AGN.** [`QLF_QuantumBlackHole`](lean/QLF_QuantumBlackHole.lean) proves that
  Compton and Schwarzschild radii cross only at the Planck mass (`compton_eq_schwarzschild_iff`), so a
  hadron's horizon is a Planck-scale Markov blanket ([`BLACK-HOLES.md`](BLACK-HOLES.md)). Nothing in it
  bears on how million-solar-mass black holes formed by `z ≈ 7`, which the Lumina project treats in its own AGN paper,
  from quasars to JWST's "little red dots" (arXiv:2605.24112).
- **Initial conditions.** [`QLF_CosmicInflation`](lean/QLF_CosmicInflation.lean) unifies inflation
  with dark energy as one `w = −1` event-synthesis field (`inflation_and_dark_energy_same_field`), but
  the e-folds, `n_s` and `r` are open (`cosmic_inflation_in_progress`). Lumina imports `n_s = 0.965`, and
  so would any QLF-based run.
- **The start.** [`QLF_LogicalBang`](lean/QLF_LogicalBang.lean) replaces the singular origin by the
  minimal closure (`first_distinction_closes`) and proves the causal order is partial
  (`causal_order_not_total`): there is no global time line. Lumina's comoving time coordinate is a
  rendering choice, and that changes no observable it reports. Bookkeeping.

---

## 6. Summary

Of QLF's proved results, the ones that touch Lumina sort into three groups.

- **Rejections that Lumina's window adds to.** Readings A and B, and the closed-so-far constraint, put
  60–70 % dark energy into reionization and shorten the clock to 56 %. They were already out.
- **Predicted nulls.** Reading C shifts `H(z)` by under 2 %, and QLF's `α` shifts `τ` by `3 × 10⁻⁶`.
  Neither is visible in reionization data, and a contrary result would count against QLF.
- **One live, discriminating prediction.** `a₀ = cH(z)/2π` makes high-redshift galaxies show a large
  mass discrepancy at accelerations that are Newtonian today. Six JADES galaxies are consistent post hoc;
  the frozen test in §3 is the real one, with Lumina as the cold-dark-matter comparison.

The gap that matters most is structure formation itself. Until QLF derives the growth of the cosmic web
without particle dark matter, Lumina's main output, the web and its reionization topology, lies outside
what QLF can compute.

---

## 7. Critical contraction against global expansion: a growth test — *pre-registered 2026-10-27*

§3 named the larger gap: baryons alone grow too slowly after recombination to make galaxies. Each
ZFA event has two faces, local contraction and future expansion (`event_duality_balanced`,
[`QLF_CosmicInflation`](lean/QLF_CosmicInflation.lean)). Read cosmologically, a lump contracts locally
under the closure balance while the global expansion carries distant masses apart. Where contraction
wins, the lump turns around and collapses into matter and black holes. Where expansion wins, the lump is
isolated and stays linear. This section asks whether that split, with nothing added, gives galaxies
in time and keeps the largest scales smooth. Model and kill conditions are fixed here, in a commit
made before [`structure_growth_qlf.py`](structure_growth_qlf.py) is run.

**Model.**

- **Global expansion** is taken as measured: flat ΛCDM `H(z)` with Planck 2018 parameters
  (`Ω_m = 0.315`, `H₀ = 67.4`, radiation as in [`omega_lambda_epochs.py`](omega_lambda_epochs.py)).
  QLF does not derive `H(z)`, so it enters as data, not as a ΛCDM claim about what fills it.
- **The lump** is a spherical shell of baryon mass `M` in a background of mean baryon density
  `ρ̄_b = Ω_b ρ_crit,0 (1+z)³`, `Ω_b = 0.0493`. Its peculiar Newtonian pull is
  `g_N = GM/R² − (4πG/3) ρ̄_b R`.
- **Local contraction** is the closure balance applied to that peculiar pull:
  `g = radialAccel(|g_N|, a₀) · sign(g_N)`, with `a₀ = cH(t)/2π` at each epoch (`radialAccel`,
  [`QLF_DarkMatter`](lean/QLF_DarkMatter.lean)).
- **The shell** obeys `R̈ = (ä/a) R − g`, starting at `z = 1100` on the Hubble flow
  (`Ṙ = HR`, no peculiar velocity) with overdensity `δ_i`. Turnaround is `Ṙ = 0`. Collapse is `R → 0`.
- **Control:** the same run with `a₀ = 0` (Newton, baryons only).

**Kill conditions.** Both must pass.

- **K1, enough growth.** A lump of `M = 10¹⁰ M☉` with `δ_i = 10⁻⁵` collapses before `z = 10`. If it
  does not, the closure balance does not supply the missing growth.
- **K2, no overshoot.** A lump of comoving radius `50 Mpc` with `δ_i = 10⁻⁵` does not turn around
  before `z = 0`. If it does, the law makes the largest scales clump, against the observed homogeneity
  above about 100 Mpc.

Other masses (`10⁸`, `10¹²`, `10¹⁴ M☉`) and `δ_i = 10⁻⁴` are reported, not judged.

**Assumptions named before the run.**

- **A1.** Applying the balance to the *peculiar* pull, relative to the Hubble flow, is a modelling
  choice. MOND-type laws are ambiguous here, and the external-field effect of neighbouring lumps is
  ignored.
- **A2.** `δ_i = 10⁻⁵` on galaxy scales assumes the seeds survive to recombination. In a universe with no
  dark matter, photon diffusion (Silk damping) erases small-scale baryon fluctuations before then. So
  passing K1 is necessary, not sufficient.
- **A3.** Before recombination the baryons are held by photon pressure, so this test says nothing about
  the CMB acoustic peaks.

**Result (2026-10-27, run after commit `78c236b`).** **K1 passes and K2 fails, so the test fails.**

| Baryon mass | comoving radius | turnaround `z` | collapse `z` | control (Newton): `δ` at `z = 0` |
|---|---|---|---|---|
| `10⁸ M☉` | 0.16 Mpc | 491 | 332 | `5 × 10⁻⁵` |
| `10¹⁰ M☉` | 0.73 Mpc | 313 | **199** | `5 × 10⁻⁵` |
| `10¹² M☉` | 3.4 Mpc | 162 | 97 | `5 × 10⁻⁵` |
| `10¹⁴ M☉` | 15.7 Mpc | 64 | 37 | `5 × 10⁻⁵` |
| `3 × 10¹⁵ M☉` | **50 Mpc** | **25** | **14** | `5 × 10⁻⁵` |

(`δ_i = 10⁻⁵`. With `δ_i = 10⁻⁴` every collapse moves only slightly earlier, for example `10¹⁰ M☉` at
`z = 206`.)

The control confirms the gap. With baryons alone and Newton, a `10⁻⁵` seed grows only fivefold by
today. The closure balance more than closes it, though, and it overshoots. Galaxy-mass lumps collapse at
`z ≈ 200`, long before the first stars JWST sees at `z ≈ 10–15`. A 50 Mpc lump turns around at `z = 25`
and collapses at `z = 14`, where the universe is observed to be smooth.

**Why.** Every growing lump starts deep in the low-acceleration regime, where the pull is `√(g_N a₀)`
and so scales as `√δ`. Growth is then nearly independent of the seed, which is why a tenfold larger
`δ_i` barely moves the collapse. Local contraction wins on every scale up to the largest tested, and
global expansion isolates nothing below hundreds of Mpc.

**Not an artefact of taking `H(z)` as data.** Exploratory runs with the background replaced (not part
of the pre-registration):

- **Einstein–de Sitter** (`H ∝ a^−3/2`): `10¹⁰ M☉` collapses at `z = 93`, and 50 Mpc turns around at
  `z = 3.5`. K2 still fails. 200 Mpc reaches `δ = 4` by today.
- **QLF's `f = 1/t` clock**, coasting `a ∝ t`: weaker early expansion, so everything collapses earlier.
  `10¹⁰ M☉` collapses at `z = 908`, and 200 Mpc at `z = 553`.

**A phase change does not rescue it (exploratory scan, post hoc).** Suppose the balance switches on only
below some redshift `z_on`, with Newton before that. Then:

| `z_on` | `10¹⁰ M☉` collapses at `z` | 50 Mpc turns around at `z` |
|---|---|---|
| 100 | 28.6 | 5.6 |
| 30 | **9.8** | 1.9 |
| 20 | 6.7 | 1.2 |
| 10 | 3.3 | **0.07** |
| 5 | 1.5 | never |

For galaxies to collapse before `z = 10` the switch has to come at `z_on ≳ 30`. For 50 Mpc to stay
unturned it has to come at `z_on ≲ 10`. No single epoch does both. The ratio between scales is fixed by
the law, and a switch in time only slides the whole sequence along. A fix has to act on scale, not on
time: an acceleration threshold such as the external-field effect.

**What this changes.** The closure-balance law, applied to the peculiar pull of baryons after
recombination, makes structure far too early and on scales far too large. The dark-matter law of §3 is
untouched where it was tested (galaxy rotation curves, `a₀(z)` to `z = 1.3`, lensing). But it is not
yet a cosmology, and its plain extension fails. The external-field effect (A1), in which the summed pull
of neighbours lifts each region out of the low-acceleration regime, is the obvious candidate to slow the
growth. It is not adopted here after the fact. If it is tried, it gets its own pre-registration.

---

## 8. Relative space depends on density: the density-suppressed floor — *pre-registered 2026-10-27*

§7 failed because the closure-balance floor `a₀` is the same everywhere, so the law has no scale and
cannot tell a galaxy from a supercluster. The fix proposed here (Jim, 2026-10-27) adds the missing
scale through density: **a region's own overdensity suppresses the relative space it synthesizes, so the
de Sitter closure floor it feels is reduced.** Each ZFA event has a constructing (transverse, spatial
handedness) face and a destroying (lateral, gauge/charge handedness) face, balanced at zero
(`event_duality_balanced`, [`QLF_CosmicInflation`](lean/QLF_CosmicInflation.lean); charge is the gauge
component of handedness, [`QLF_Handedness`](lean/QLF_Handedness.lean)). A denser region runs more lateral
closures, so it constructs less space relative to the background and the background floor it feels drops.
That returns dense, collapsing regions to the Newtonian regime (`g → g_bar`), where growth is linear
rather than the `√δ` runaway, while underdense regions keep the full floor.

**Model.** Exactly the §7 spherical collapse, same global `H(z)`, same peculiar pull `g_N`, with the one
change

`a₀_eff = a₀ / (1 + δ)`,  `a₀ = cH(t)/2π`,  `δ = (x a / R)³ (1 + δ_i) − 1`

(`δ` the shell's instantaneous overdensity; `g = radialAccel(|g_N|, a₀_eff) · sign(g_N)`). The exponent
`p = 1` is the primary; `p = 2` is reported, not judged.

**Kill conditions.** The same two as §7, both required: K1 (`10¹⁰ M☉`, `δ_i = 10⁻⁵` collapses before
`z = 10`) and K2 (`50 Mpc`, `δ_i = 10⁻⁵` does not turn around before `z = 0`).

**What is a free choice.** The functional form `1/(1+δ)` and the exponent `p` are mine, not forced by any
theorem; Jim's principle is only that relative space falls with density. So a pass is evidence the
*principle* can carry the scale, with the form to be derived; a fail of this specific form does not kill
the principle. The run and verdict follow in the commit after this one.

**Result (2026-10-27, run after freezing commit `e9d2357`).** **This form fails: K1 passes, K2 still
fails.** The 50 Mpc lump turns around at `z = 17.7` (`p = 1`) or `z = 11.1` (`p = 2`), against §7's
`z = 25` — barely moved, and never prevented.

| | `10¹⁰ M☉` collapses at | 50 Mpc turns around at |
|---|---|---|
| §7, uniform floor | 199 | 25.2 |
| §8, `a₀/(1+δ)` | 160 | 17.7 |
| §8, `a₀/(1+δ)²` | 128 | 11.1 |

**Why it fails, and what it says about the principle.** In the amplified `√δ` regime the overdensity
`δ` stays well below 1 through almost the whole growth and only reaches order 1 just before turnaround.
So `1/(1+δ)` is close to 1 for most of the history and engages too late to stop the turnaround. Worse,
`δ(z)` runs nearly the same on every scale during the linear phase, so a floor that depends on the
region's *own* density is almost scale-free — the same defect as the §7 phase change, which slid every
scale together. Raising `p` only sharpens the late suppression; it does not make the brake act earlier or
pick out large scales.

The diagnosis points past the specific form. A brake that separates a galaxy from a supercluster must
depend on something that *already differs by scale early*, when `δ` is still tiny on every scale. The
region's own density is not that quantity; the **ambient** field from larger scales is (it is larger for
a region embedded in a bigger overdensity, from the start). So the surviving candidate is still the
external-field effect — `a₀_eff` set by the *surrounding* density, not the local one — which needs a
two-scale model, not a single top-hat, and its own pre-registration. Jim's principle (relative space
falls with density) is not killed; the reading that the *local* density sets the floor is.

---

## 9. The ambient field sets the floor: the external-field effect — *pre-registered 2026-10-27*

§8 established that the suppressing density must be the **ambient** one, because only the ambient field
already differs by scale while every region's own `δ` is still `10⁻⁵`. The physical reading of Jim's
principle: the relative space a region synthesizes is set by the lateral-closure density of its
**surroundings**, so a region embedded in a strong ambient field feels a reduced closure floor and
reverts to Newtonian growth — while a dense, compact region whose own pull beats the ambient field keeps
the full floor. This is the external-field effect, with the construct/destroy duality of §8 as its
mechanism. It is the one candidate that engages where the object's own pull `g_bar` is *below* the
ambient field — which is exactly the large, diffuse scales that overshot, and not the compact galaxies
that must still form.

**Model.** A single **ambient shell** of comoving radius `X_amb = 100 Mpc`, `δ_i = 10⁻⁵`, evolves by the
§7 closure balance and sources a common ambient field

`g_ext(z) = (4π/3) G ρ̄_b(z) δ_amb(z) R_amb(z)`.

Every target shell (the §7 cases) evolves as in §7 but with the floor suppressed by that ambient field,

`a₀_eff = a₀² / (a₀ + g_ext)`,  `a₀ = cH(t)/2π`

(so `g_ext ≪ a₀ ⟹ a₀_eff ≈ a₀`, full amplification; `g_ext ≫ a₀ ⟹ a₀_eff → a₀²/g_ext → 0`, Newtonian).
`g = radialAccel(|g_N|, a₀_eff) · sign(g_N)`.

**Kill conditions.** The same two, both required: K1 (`10¹⁰ M☉` collapses before `z = 10`) and K2
(`50 Mpc` does not turn around before `z = 0`). `X_amb = 50` and `200 Mpc` are reported for sensitivity,
not judged.

**Free choices, named before the run.** The ambient scale `X_amb`, the EFE form `a₀²/(a₀+g_ext)`, and
sourcing `g_ext` from one evolving shell rather than a power spectrum (which QLF does not have) are all
mine. A pass is evidence the external-field reading can carry the scale; a fail of this form leaves the
principle open but removes the simplest construction.

**Result (2026-10-27, run after the freezing commit).** _[pending]_

---

## Sources

- O. Zier et al., *Introducing the Lumina project: large-volume radiation-hydrodynamic simulations of the
  epochs of hydrogen and helium reionization*, arXiv:2605.15310; MNRAS 552 (2026), DOI
  10.1093/mnras/stag1469.
- The Lumina Project, *CMB optical depth fluctuations from patchy reionization*, arXiv:2605.18939.
- A. de Graaff et al., *Ionised gas kinematics and dynamical masses of z ≳ 6 galaxies from JADES/NIRSpec
  high-resolution spectroscopy*, A&A 684, A87 (2024), DOI 10.1051/0004-6361/202347755.
- The Lumina Project, *The demographics of active galactic nuclei from quasars to little red dots at
  z ≥ 3*, arXiv:2605.24112.
- Press coverage: [ScienceDaily](https://www.sciencedaily.com/releases/2026/10/261026225600.htm),
  [MIT Physics](https://physics.mit.edu/news/watch-the-universe-emerge-from-the-dark-ages-with-lumina/).
