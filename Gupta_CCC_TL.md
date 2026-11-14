# QLF–Gupta CCC+TL falsification program

[QLF](README.md) · [Theory index](Theory_Of_Everything.md) · [Flow chart](FlowChart.md)

**Status: external 2023 numerical benchmark passes at abstract precision; QLF bridge B-OPEN.**

Parent: [issue #234](https://github.com/rhovision-org/quantum-logical-framework/issues/234). Initial review: [PR #233](https://github.com/rhovision-org/quantum-logical-framework/pull/233). [Grok protocol review](verification/gupta-ccc-tl/grok_protocol_review.md), relayed and accepted by Jim, is recorded at document/protocol scope. [Grok's numerical rerun](verification/gupta-ccc-tl/grok_numerical_review.md) is recorded as an independent execution PASS; the source of the Table 1 residual and physical-map review remain open; creating a parent issue does not establish pre-exposure registration. The question is whether QLF independently derives, permits, or excludes the CCC+TL observable relations. Neither 13.8 nor 26.7 Gyr is a target for choosing QLF rules. This branch implements stage 1 and specifies the later stages; it does not adopt a new substrate rule.

## 1. Evidence and exposure

Keep formal **F**, numerical **N**, and empirical **E** evidence separate, following [Proof_to_Physics.md](Proof_to_Physics.md), [Claim_Status.md](Claim_Status.md) and [claim_records/README.md](claim_records/README.md). Published parameters and age targets were known before this work. A commit freezes the analysis before execution, but cannot make these targets blind or prospective. The [draft test ledger](claim_records/gupta_ccc_tl.json) is deliberately a `test_ledger`: the current claim schema requires a nonempty theorem list, and inventing a theorem to populate a numerical reference record would misstate F evidence. A later claim record needs an honest applicable formal scope or a separately reviewed schema change.

The [frozen specification](verification/gupta-ccc-tl/specification.json) records source version/digest, fitted inputs, target precision, algorithms and failure policy. A self-run result cannot satisfy the independent/collaborator review gate. Hashes establish byte identity, not execution authenticity or preregistration.

## 2. Reference model and equation contract

Primary source: Rajendra P. Gupta, *JWST early Universe observations and ΛCDM cosmology*, [MNRAS 524, 3385–3395 (2023), stad2032](https://doi.org/10.1093/mnras/stad2032), [arXiv v1](https://arxiv.org/abs/2309.13100v1). This source reports ages 26.7, 5.8 and 3.5 Gyr at observed redshifts 0, 10 and 20. Use its fitted expansion rate `Hc = 59.51 km/s/Mpc` and `r = alpha/Hc = -0.7997`; do not use the total low-redshift slope as Hc. These inputs are external fits, not QLF predictions.

The dimensionless implementation uses `u = Hc(t−t0)` and `x = exp(−r u/2)`. Equations 25–26 become `a^(3/2) = A x³ + C x`, with `C = 3(1+r)/(2r)` and `A = 1−C`. Select the branch continuous from `a=x=1`. The past endpoint is the nonzero root `x_B = sqrt(−C/A)` for the frozen `−1 < r < 0` regime. Equation 20 gives `E(a) = H/Hc = (1+r)a^(−3/2)x−r`, and `f=x^(−2)`. The flat modified Friedmann constraint is `(H+alpha)² = 8πG epsilon/(3c²)` (equation 19, with the source's density convention).

Let `I(zc) = integral[0,zc] dzc/E`. Equations 35, 42–44 give `Ht/Hc = (1+r)(3+r)/2`, `H0=Hc+Ht`, and `log(1+z_obs)=log(1+zc)+(Ht/Hc)I(zc)`. Solve this monotone equation for expansion redshift `zc`; `zt=(1+z_obs)/(1+zc)−1`. **Observed redshift is not expansion redshift.** The age from the same solution is `−2 log(x/x_B)/(r Hc)`; verify against equation 50 by independent integration. Report H as the expansion rate evaluated at the emission epoch, never as a direct cosmic-chronometer measurement.

Equation 45 supplies `dL = dp sqrt((1+z_obs)(1+zc))`; equation 49 supplies `dA = a f dp`. Keep these source conventions distinct from an assumed distance-duality law. Distances, pulse stretching, spectral redshift and clock aging need separate operational maps.

The 2023 scaling is not a common equal power for every dimensionful constant: its discussion specifies `c ~ f`, `G ~ f³`, `h ~ f²`, `k_B ~ f²`. Dimensionless invariance requires a complete unit/observable map; it does not follow by assertion. In particular, distinguish the CCC rate alpha from the fine-structure constant alpha_EM. Later CCC versions must have separate specifications; do not splice their equations into this reference.

### Reproduced values

| Observed z | Published age (Gyr) | Computed age (Gyr) | Expansion zc | TL zt |
|---|---|---|---|---|
| 0 | 26.7 | 26.667212 | 0 | 0 |
| 10 | 5.8 | 5.832453 | 4.659195 | 0.943739 |
| 20 | 3.5 | 3.463280 | 7.663198 | 1.424047 |

The values pass the specification frozen before computation; the present-age difference from Table 1 at hundredth precision remains unresolved. See the [full report](verification/gupta-ccc-tl/result.json) for f, expansion H, distances, quadrature and convergence residuals.

### Clock and observable audit still required

The 2023 metric (equation 2) includes a lapse f and a spatial scale af. If read with fixed reference c and standard comoving metric proper time, it gives `d tau = f dt` and expansion of the spatial metric `d log(af)/d tau = (H+alpha)/f`. The reproduced equation-50 age integrates the paper's t variable. Identifying that variable with atomic-clock age or QLF proper age requires an operational derivation; a coordinate transformation by itself is not a new age prediction. This is a specific stage-2 obligation, not permission to relabel the 26.7 Gyr target.

When c or h varies in the stated convention, wavelength ratios, frequency ratios and photon-energy ratios are not interchangeable without tracking the emission and reception standards. Keep the source's wavelength-redshift definition and derive its frequency/clock reading. Likewise, test the source's luminosity/angular-distance prescriptions against operational distance duality rather than assuming a standard relation.

### The 2026 follow-up literature

These are verified source leads with their own assumptions; none has been numerically reproduced on this branch. The [2026 discoveries entry](Discoveries_2026.md#p13) connects this program to the wider research index.

| Source | Result relevant to this program | Required next test |
|---|---|---|
| Gupta & Samaras, *A Big Bang Nucleosynthesis Consistency Test of the CCC+TL Cosmology*, [Universe 12(7), 193](https://doi.org/10.3390/universe12070193), 26 June 2026 | Conditional preservation of light-element yields under matched expansion, interaction and decay-rate scaling on the early plateau | Reproduce the network and perturb rate scalings separately; distinguish an invariant rescaling from an independent age test. |
| Gupta, *Testing the CCC+TL cosmology with cosmic-chronometer measurements of the Hubble parameter*, [arXiv:2606.27391v1](https://arxiv.org/abs/2606.27391v1), MNRAS stag1126 | A phenomenological age-calibration factor is proposed to address the reported chronometer tension | Recompute stellar calibrations or test the proposed factor independently; do not treat its introduction as an already-derived clock bridge. |
| Gupta, Samaras & Kumar, *Supernova Time Dilation in Hybrid Expansion-Tired-Light Cosmologies*, [arXiv:2609.10582v1](https://arxiv.org/abs/2609.10582v1) | Adds phenomenological pulse stretch using a hybrid/parent lookback-time ratio | Derive pulse transport and intrinsic light-curve calibration; do not import the 2026 stretch into the 2023 benchmark. |
| Gupta & Samaras, [SPARC study, arXiv:2608.11575v1](https://arxiv.org/abs/2608.11575v1) | Inverse reconstruction with per-galaxy turn-off fitting | Execute the matched forward/inverse protocols in stage 3. |
| Gupta & Samaras, *Gravitational Lensing of the Bullet Cluster in the CCC+TL Cosmology: A Controlled Proof-of-Concept Study*, [Universe 12(10), 308](https://doi.org/10.3390/universe12100308) | Compares a two-parameter density prescription against a simplified lensing reference | Compare matched image-plane likelihoods and mass priors; a source-plane diagnostic is not an equivalent image-plane fit. |

The [University of Ottawa announcement, 6 November 2026](https://www.uottawa.ca/faculty-science/news-all/theory-predicting-older-universe-without-dark-matter-dark-energy-passes-key-cosmological) points to the BBN study. The announcement date is not the publication date, and the 26.7 Gyr result originates in the 2023 model. Separate a reported 2026 consistency test from discovery of a measured older universe.

## 3. Five review stages

| Stage | Deliverable | Acceptance / stop rule |
|---|---|---|
| 1: reference | Source-pinned implementation, deterministic output, residuals, convergence checks and independent age quadrature | All three known ages within 0.05 Gyr, convergence below 1e−6 Gyr; no retuning. A failed reproduction blocks acceptance and is not evidence against QLF. |
| 2: time bridge | Explicit forward map from finite clock records to rates/redshifts; return map preserving identified finite records; assumptions and domain | A rate-ratio identity alone is bookkeeping. Derive a process/measure selecting the required evolution or report underdetermination. A proved counterexample rejects the specified map, not every possible QLF realization. |
| 3: SPARC | Common sample and two separate comparisons: forward prediction and inverse reconstruction | Freeze nuisance priors, galaxy split, error model, scoring and complexity accounting before running; inverse CCC cannot enter a forward contest without a uniquely specified inversion. |
| 4: ages / high z | Independently selected count N and operational clock map; jointly predicted age, H and distances | No H0- or age-calibrated N may be called an independent age prediction. Compare curves with propagated uncertainty, not a nearest-age vote. |
| 5: verdict | Component evidence table and scoped derivation, compatibility or obstruction result | Keep numerical reproduction, QLF compatibility and empirical adequacy as three separate verdicts. Missing evidence stays INCOMPLETE. |

### Stage 2: obligations that can fail

**First item of the next PR:** freeze the operational clock/metric convention described in §2 before constructing or comparing ages. Explicitly identify the paper's t variable, metric lapse, atomic standards and QLF proper-time candidate. The 26.7 Gyr figure keeps its source definition until that map is derived.

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

Empirical rejection is separate: freeze datasets, covariance, nuisance priors, rejection statistic and multiplicity correction before tests. BBN, CMB spectra, BAO, chronometers and supernova pulse stretching are future joint consistency tests, with model-dependent calibration documented. A university announcement is a discovery lead, not acceptance evidence. The 2026 sources above have verified bibliographic entries; their equation sets, data and code still need separate frozen specifications before execution.

## 4. Run and review

The [executable](tools/gupta_ccc_tl_reference.py) follows specification-only commit `7368d89996db38165deb949961082ad83b3b3c2f`. See the [execution record](verification/gupta-ccc-tl/README.md) and [report](verification/gupta-ccc-tl/result.json). Run:

```bash
python3 tools/gupta_ccc_tl_reference.py
python3 -m unittest discover -s tests -p 'test_gupta_ccc_tl*.py' -v
python3 scripts/validate_claim_records.py
python3 scripts/doc_network_check.py
```

The present-age residual against Table 1 is about −0.0328 Gyr. Its exact source—rounded parameters, a published intermediate, or an implementation difference—remains open. The current quadrature agreement does not identify that source; do not widen the frozen tolerance.

The present-age result is 26.6672 Gyr: it recovers 26.7 at abstract precision, but does **not** reproduce Table 1's 26.70 at its extra decimal place. Retain this precision discrepancy; do not change the fitted inputs. The benchmark uses the frozen abstract-precision criterion. The reference calculation is independent of Lean. The first clock-ratio algebra is now formalized in §6; physical-map and finite-record return obligations remain separate. Parent issue #234 tracks the five stages; PR #233 contains the initial work. Later PRs and physical-map/empirical review remain to be scheduled.

## 5. Remaining work and review gates

| Missing item | Completion evidence |
|---|---|
| Independent review scope | Grok reports a successful separate execution of the existing implementation and artifact checks. A second implementation/source-equation audit and explanation of the present-age precision discrepancy remain open. |
| Parameter uncertainty | Published covariance or an explicitly conservative alternative, including parameter rounding and model-regime sensitivity; numerical convergence alone is insufficient. |
| Model controls | Separately pinned CCC-only and LCDM controls; a no-TL limit where mathematically applicable; no reuse of one model's fitted H0 in another. |
| Wider redshift coverage | Frozen grid for f, H, t and distances, plus convergence and approximation-domain checks; current reported targets are z=0,10,20 only. |
| Source version archive | Obtain source equations/code with a durable provenance manifest and reconcile published/arXiv variants; the current source-byte digest is not an archived independent implementation. |
| QLF forward/return maps | Concrete clock/count domain, selected evolution, units, apparatus map and preserved finite invariants; Lean identities alone cannot close the bridge. |
| Independent count N | Substrate selection and a justified accumulated-tick conversion, without fitting H0 or either age target. |
| Empirical protocols | Frozen SPARC sample/splits/scores; BBN network inputs; chronometer recalibration; pulse stretching; BAO ruler and CMB-spectrum calculations with covariance. |
| Statistical decisions | Numerical equivalence margins, uncertainty model, rejection thresholds and multiple-test handling chosen before each new comparison. |
| Review coordination | Parent issue #234 and initial PR #233 exist; Grok protocol/numerical reports are recorded; designate later physical-map/empirical reviewers and scope the later PRs before their work. |

The completed work is the external reference calculation and the improved research protocol. The broader program remains open for the missing evidence above.

## 6. First Lean obligations

[QLF_ClockRedshift](lean/QLF_ClockRedshift.lean) supplies nine algebraic statements:

- `ratio_self`, `ratio_pos`, `ratio_composition`: positive clock-ratio normalization and telescoping.
- `redshift_composition`: multiplicative redshift follows from the declared ratio convention.
- `common_rescaling`: a shared rate-unit rescaling cancels.
- `residual_factor_unique`: the residual is fixed once a nonzero expansion factor is fixed.
- `positive_factorization_not_unique`: without that input, a positive total admits distinct positive factorizations.
- `free_clock_scale_hits_any_age`: an unconstrained positive clock conversion can realize any positive target age.
- `lapse_rate_return`: the algebraic lapse conversion returns the supplied coordinate rate.

The last two are explicit boundaries: an age match with a free scale is not independent selection, and algebraic invertibility is not a return theorem for the finite QLF closure records. No project axiom or physical identification is introduced. The module is registered in the build and exact-footprint audit; all nine statements and their exact footprints passed [CI run 43600320884](https://github.com/rhovision-org/quantum-logical-framework/actions/runs/43600320884) at `7e181c2b1d15f7b7ca4e3cde9a51c0f761751469`. The physical bridge remains B-OPEN.

## 7. CI turnaround

The Lean workflow restores only compatible QLF build outputs/traces after recreating pinned dependency metadata. Lake still checks the target graph and rebuilds affected modules; the full exact-axiom audit always executes. New commits cancel superseded runs for the same PR. On an empty cache, an already successful same-branch artifact may seed it only after an exact diff of Lean sources, toolchain, manifest and build configuration. Otherwise the workflow builds cold. Only successful builds that also pass the footprint gate are saved. This reduces repeated recompilation without treating a cache as a new proof or changing the promotion rules.

**GitHub review:** [aixaria0's review](https://github.com/rhovision-org/quantum-logical-framework/pull/233#pullrequestreview-5904556943) reports a separate adaptive-quadrature comparison matching the ages, f, expansion H and distances to relative differences below approximately 5e−15. The import-order blocker is fixed and the subsequent full build/footprint audit passed. Follow-ups add a positive frozen-spec regression and reconcile the formal-scope summaries. The review's requested-changes state awaits the reviewer's reconsideration; no approval is inferred.
