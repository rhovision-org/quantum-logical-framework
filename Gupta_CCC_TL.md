# QLF–Gupta CCC+TL falsification program

[QLF](README.md) · [Theory index](Theory_Of_Everything.md) · [Flow chart](FlowChart.md)

**Status: B-OPEN; external reference benchmark under development.** The question is whether QLF independently derives, permits, or excludes the CCC+TL observable relations. Neither 13.8 nor 26.7 Gyr is a target for choosing QLF rules. This branch implements stage 1 and specifies the later stages; it does not adopt a new substrate rule.

## 1. Evidence and exposure

Keep formal **F**, numerical **N**, and empirical **E** evidence separate, following [Proof_to_Physics.md](Proof_to_Physics.md), [Claim_Status.md](Claim_Status.md) and [claim_records/README.md](claim_records/README.md). Published parameters and age targets were known before this work. A commit freezes the analysis before execution, but cannot make these targets blind or prospective. The [draft test ledger](claim_records/gupta_ccc_tl.json) is deliberately a `test_ledger`: the current claim schema requires a nonempty theorem list, and inventing a theorem to populate a numerical reference record would misstate F evidence. A later claim record needs an honest applicable formal scope or a separately reviewed schema change.

The [frozen specification](verification/gupta-ccc-tl/specification.json) records source version/digest, fitted inputs, target precision, algorithms and failure policy. A self-run result cannot satisfy the independent/collaborator review gate. Hashes establish byte identity, not execution authenticity or preregistration.

## 2. Reference model and equation contract

Primary source: Rajendra P. Gupta, *JWST early Universe observations and ΛCDM cosmology*, [MNRAS 524, 3385–3395 (2023), stad2032](https://doi.org/10.1093/mnras/stad2032), [arXiv v1](https://arxiv.org/abs/2309.13100v1). This source reports ages 26.7, 5.8 and 3.5 Gyr at observed redshifts 0, 10 and 20. Use its fitted expansion rate `Hc = 59.51 km/s/Mpc` and `r = alpha/Hc = -0.7997`; do not use the total low-redshift slope as Hc. These inputs are external fits, not QLF predictions.

The dimensionless implementation uses `u = Hc(t−t0)` and `x = exp(−r u/2)`. Equations 25–26 become `a^(3/2) = A x³ + C x`, with `C = 3(1+r)/(2r)` and `A = 1−C`. Select the branch continuous from `a=x=1`. The past endpoint is the nonzero root `x_B = sqrt(−C/A)` for the frozen `−1 < r < 0` regime. Equation 20 gives `E(a) = H/Hc = (1+r)a^(−3/2)x−r`, and `f=x^(−2)`. The flat modified Friedmann constraint is `(H+alpha)² = 8πG epsilon/(3c²)` (equation 19, with the source's density convention).

Let `I(zc) = integral[0,zc] dzc/E`. Equations 35, 42–44 give `Ht/Hc = (1+r)(3+r)/2`, `H0=Hc+Ht`, and `log(1+z_obs)=log(1+zc)+(Ht/Hc)I(zc)`. Solve this monotone equation for expansion redshift `zc`; `zt=(1+z_obs)/(1+zc)−1`. **Observed redshift is not expansion redshift.** The age from the same solution is `−2 log(x/x_B)/(r Hc)`; verify against equation 50 by independent integration. Report H as the expansion rate evaluated at the emission epoch, never as a direct cosmic-chronometer measurement.

Equation 45 supplies `dL = dp sqrt((1+z_obs)(1+zc))`; equation 49 supplies `dA = a f dp`. Keep these source conventions distinct from an assumed distance-duality law. Distances, pulse stretching, spectral redshift and clock aging need separate operational maps.

The 2023 scaling is not a common equal power for every dimensionful constant: its discussion specifies `c ~ f`, `G ~ f³`, `h ~ f²`, `k_B ~ f²`. Dimensionless invariance requires a complete unit/observable map; it does not follow by assertion. In particular, distinguish the CCC rate alpha from the fine-structure constant alpha_EM. Later CCC versions must have separate specifications; do not splice their equations into this reference.

## 3. Five review stages

| Stage | Deliverable | Acceptance / stop rule |
|---|---|---|
| 1: reference | Source-pinned implementation, deterministic output, residuals, convergence checks and independent age quadrature | All three known ages within 0.05 Gyr, convergence below 1e−6 Gyr; no retuning. A failed reproduction blocks acceptance and is not evidence against QLF. |
| 2: time bridge | Explicit forward map from finite clock records to rates/redshifts; return map preserving identified finite records; assumptions and domain | A rate-ratio identity alone is bookkeeping. Derive a process/measure selecting the required evolution or report underdetermination. A proved counterexample rejects the specified map, not every possible QLF realization. |
| 3: SPARC | Common sample and two separate comparisons: forward prediction and inverse reconstruction | Freeze nuisance priors, galaxy split, error model, scoring and complexity accounting before running; inverse CCC cannot enter a forward contest without a uniquely specified inversion. |
| 4: ages / high z | Independently selected count N and operational clock map; jointly predicted age, H and distances | No H0- or age-calibrated N may be called an independent age prediction. Compare curves with propagated uncertainty, not a nearest-age vote. |
| 5: verdict | Component evidence table and scoped derivation, compatibility or obstruction result | Keep numerical reproduction, QLF compatibility and empirical adequacy as three separate verdicts. Missing evidence stays INCOMPLETE. |

### Stage 2: obligations that can fail

Start with [Frequency_Synchronization.md](Frequency_Synchronization.md), [Kitada_Local_Time_GR.md](Kitada_Local_Time_GR.md) and [AgeOfUniverse.md](AgeOfUniverse.md) §4. Specify which clocks measure emission frequency, reception frequency and pulse interval, their synchronization convention, units, endpoint and rate orientation. For `f_Gupta ↔ nu_QLF(N)/nu_QLF(N0)`, derive the orientation rather than choosing it for the desired sign. Require identity calibration at the present epoch, positive monotone clocks, composition and a return preserving the finite clock/closure records. Supply finite-resolution error bounds before asserting a continuum correspondence.

An arbitrary positive clock reparameterization can reproduce a chosen age; that establishes representability, not a selected physical mechanism. Exhibit distinct admissible rate histories as an underdetermination witness where possible. A derivation must select the history and its dimensional scale independently of the Gupta targets. A restricted-family obstruction must state its quantifiers and assumptions.

Test conservative rate composition before introducing dissipative photon leakage. Global unitarity does not by itself forbid reduced-system damping: an exclusion must identify the photon plus environment, conservation law, channel and exact QLF theorem. Conversely, a ratio identity supplies no scattering mechanism or pulse-stretch prediction. Logical conservativity in RCA₀ is not a numerical bound on physical memory.

### Stage 3: fair rotation-curve comparison

Gupta and Nikolaos Samaras, [arXiv:2608.11575v1](https://arxiv.org/abs/2608.11575v1), [MNRAS stag1777](https://doi.org/10.1093/mnras/stag1777), use an inverse comparison on 175 galaxies and fit a turn-off density per galaxy. This is a different task from QLF's retrospective forward RAR on 147 galaxies / 2696 points ([SPARC.md](SPARC.md), [sparc_rar.json](claim_records/sparc_rar.json), [DarkMatter.md](DarkMatter.md)).

Use identical eligible galaxies, radii, distance/inclination treatment and disk/bulge M/L inputs. Count global and per-galaxy fitted parameters for CCC, MOND and NFW; QLF has declared global H0 and external M/L inputs. Partition by galaxy, not by radius, to prevent within-galaxy leakage. Fit nuisance quantities on training galaxies only; any test-galaxy calibration must have a separately declared task. Report paired galaxy-level losses, galaxy bootstrap intervals and held-out predictive scores. Do not compare published reduced chi-squares across different response variables/error propagation. Define a practical equivalence margin before scoring; lack of significance alone is not equivalence. Freeze selection informed by observed velocity as target-informed, not blind. Do not modify the existing SPARC record until this comparison actually runs.

### Stage 4: age as a clock-specific observable

[AgeOfUniverse.md](AgeOfUniverse.md) already distinguishes cosmic proper age from Hubble time and leaves the substrate count N open. The proton cube is too small to be the proposed cosmic tick count. It remains a failed candidate for that clock, not an age bound. If constants vary, `N tau_P(today)` needs justification: a variable tick requires an accumulated-time map. Using `1/(H0 tau_P)` to obtain N reuses H0 and is calibration.

A QLF value near 13.8 Gyr disfavors the Gupta value only for the **same clock definition**, with a derived uncertainty and an independently fixed bridge. A value near 26.7 Gyr is similarly only conditional support. Different proper-time or operational clocks may coexist only if the equations derive their relation. Keep formation age and elapsed cosmic age separate, and reanalyse stellar-age/chronometer calibration consistently under changing constants.

### Stage 5: verdict vocabulary

- **Derived:** an independently selected QLF process/count fixes the observable relation and scale; theorem assumptions and approximation error are explicit.
- **Permitted but underdetermined:** an admissible conservative realization exists, but QLF does not select it uniquely; this is one way and a lower bound on multiplicity.
- **Incompatible within a specified class:** an invariant obstruction or counterexample excludes the frozen map/family. State the domain; do not extrapolate to all QLF constructions.

Empirical rejection is separate: freeze datasets, covariance, nuisance priors, rejection statistic and multiplicity correction before tests. BBN, CMB spectra, BAO, chronometers and supernova pulse stretching are future joint consistency tests, with model-dependent calibration documented. A university announcement is a discovery lead, not acceptance evidence. Later BBN/chronometer papers require individually verified versions and equations before inclusion.

## 4. Run and review

The executable and output are added after the specification-only commit. No Lean code is required for the reference calculation. The later clock-ratio formalization must distinguish algebraic identities from the physical map and pass the existing Lean review workflow. There is no parent issue or five-PR publication created by this branch; these are review stages ready to be split when requested.
