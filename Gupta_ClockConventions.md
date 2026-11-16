# Gupta CCC+TL clock conventions — stage-2 preparation

[QLF](README.md) · [Theory index](Theory_Of_Everything.md) · [Parent program](Gupta_CCC_TL.md) · [Issue #234](https://github.com/rhovision-org/quantum-logical-framework/issues/234)

**Status: proposed convention contract; physical map B-OPEN / INCOMPLETE.** The source-precision audit excludes ordinary nearest-rounding of the displayed parameters as the sole explanation for Table 1's remaining digits. It does not identify the author's actual intermediate. That prerequisite remains open, so this document prepares the next review rather than declaring stage 2 complete. No new fit, dynamics, conservative-return theorem or QLF age prediction is introduced.

## 1. Which clock does the paper's t denote?

The reference implementation integrates the t variable of equation 50 in [Gupta 2023, arXiv v1](https://arxiv.org/abs/2309.13100v1). Call its elapsed reading `T_paper`. The external age target retains that definition. Its identification with an atomic clock, a received pulse interval or a QLF Markov-blanket clock is **unresolved**.

The quantities to keep separate are:

| Symbol | Convention for this review | Physical identification still needed |
|---|---|---|
| t | Time parameter in the source evolution equations | Which physical clock realizes it |
| tau_metric | Proper-time parameter derived from the specified metric reading below | Relation to an actual calibrated atomic clock |
| tau_atomic | Reading of a named local atomic standard | Transition, unit convention and calibration under covarying constants |
| delta tau_arrival | Separation of received pulse events | Source emission process and propagation/stretch law |
| N | Count of a specified kind of finite QLF closure record | Which closures constitute this clock and its conversion to observed intervals |

Neither `T_paper = tau_atomic` nor `T_paper = N*tau_P(today)` is assumed. The 26.7 Gyr target is not relabeled as a QLF prediction. [AgeOfUniverse.md](AgeOfUniverse.md) leaves N independent of H0 undetermined; Hubble time and integrated cosmic age remain distinct.

## 2. Metric lapse and expansion conventions

For the candidate chart reading

`ds² = c_ref² f(t)² dt² − [a(t) f(t)]² dSigma²`,

use c_ref as a fixed reference conversion and count the factor f exactly once. For a comoving trajectory, define `c_ref² d tau_metric² = ds²`, choose increasing clocks and f positive. Then `d tau_metric = f dt`. This is a conditional metric relation. It does not establish that a varying dimensional c is only a coordinate effect or that the resulting proper time is an atomic-clock reading.

Let `A = a*f`, `H_a = d(log a)/dt`, and `alpha = d(log f)/dt` under the source's exponential convention. Product and chain rules give

`H_A,tau = d(log A)/d tau_metric = (H_a + alpha)/f`.

The stage-1 output named `H_expansion` is H_a. It is not automatically H_A,tau or a cosmic-chronometer measurement. If a different reading places c(t) directly into the metric, write that metric and its clock normalization first; multiplying by f a second time would be a different model.

An invertible algebraic lapse conversion is already covered by `QLF.ClockRedshift.lapse_rate_return`. It does not prove the differential hypotheses above or an operational return on closure records.

## 3. Frequency, wavelength and energy standards

Use endpoint labels e (emission) and o (observation). With explicitly comparable endpoint units, define `R_lambda = lambda_o/lambda_e` and `R_nu = nu_e/nu_o`. The local identities `c_i = lambda_i*nu_i` imply

`R_nu = (c_e/c_o)*R_lambda`.

Thus wavelength-redshift and frequency-redshift conventions agree only after the endpoint c ratio and unit/standard relation have been specified. Similarly, `E_i = h_i*nu_i` gives `E_e/E_o = (h_e/h_o)*R_nu`. Under the source powers c proportional to f and h proportional to f², these algebraic ratios contain extra endpoint factors; they are not themselves a prediction of a measured spectral shift. An observed atomic line comparison also needs its local reference transition and calibration.

Keep spectral ratio, pulse stretching, luminosity distance and angular distance as different observables. No dissipation mechanism or pulse-stretch law follows from multiplying redshift factors. Later phenomenological stretch or stellar-aging corrections require their own source version and test specification.

## 4. Candidate map on finite records and its errors

The proposed input record must contain: event identifiers and ordering; the counted closure type; a count K; a reference interval Delta with its provider and unit; endpoint and acquisition window; counting/interval resolutions epsilon and eta; and calibration provenance. Counts of closure events, period/depth R, and elapsed tick count N must not be used interchangeably. [Frequency_Synchronization.md](Frequency_Synchronization.md) and [QLF_LocalClock](lean/QLF_LocalClock.lean) supply structural clock models; selecting this record type is an additional physical obligation.

A candidate estimator is `nu_hat = K/Delta`, not a cosmological evolution law. If a future apparatus supplies `K−epsilon > 0` and `Delta−eta > 0`, one can bracket its rate by

`nu_low = (K−epsilon)/(Delta+eta)`,
`nu_high = (K+epsilon)/(Delta−eta)`.

An endpoint rate ratio is then bracketed by `nu_e,low/nu_o,high` and `nu_e,high/nu_o,low`. These bounds are conditional on supplied interval/count error bounds; no numerical error bar is assigned before those inputs exist. State whether the interval provider itself assumes the clock relation being tested.

The correspondence to review is

`f_Gupta(t) <-> nu_QLF(N)/nu_QLF(N0)`,

or the cumulative rate-composition alternative, with endpoint orientation, normalization, acquisition windows and coarse-graining error explicit. Neither orientation is chosen for matching an age. No finite QLF clock record or complete forward/return map has been constructed here.

A rate alone loses information: the records `(K,Delta)=(1,1)` and `(2,2)` have the same rate. Merely appending the original record to the rate would make a return tautological. The required return must specify which physically relevant finite invariants are preserved and why its preservation constrains the candidate evolution.

## 5. Outcomes and progression gate

| Outcome for a later frozen map | Required evidence |
|---|---|
| Derived | An independently selected QLF clock process fixes the evolution, scale and operational observable, with preserved finite-record invariants and approximation control |
| Permitted but underdetermined | An admissible realization exists, but multiple physical clock histories or scales remain; an algebraic ratio identity alone does not establish admissibility |
| Incompatible within the stated class | An invariant obstruction or counterexample excludes the specified map under its declared assumptions; state the class and quantifiers |

**Current outcome: INCOMPLETE.** The first Lean results establish algebraic composition and underdetermination boundaries, not any of the above physical outcomes. In particular, `free_clock_scale_hits_any_age` prevents interpreting a match obtained with a free positive scale as independent selection.

Before stage-2 implementation proceeds, obtain a reproducible source intermediate, author code/constants, or an explicit source correction explaining the Table 1 digits. The [source-precision audit](verification/gupta-clock-conventions/README.md) records what has already been excluded. Then review and freeze the operational choices above, construct the finite-record map and its error budget, and designate the physical-map reviewer. The ledger remains DRAFT with empty physical-map theorem anchors until those obligations are met. SPARC, independent N and later empirical tests remain later work.
