# Gupta CCC+TL: what survives an independent clock calibration? (#234)

Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF. Issue #234 asks whether
QLF can derive, permit or exclude Gupta's CCC+TL age and redshift relations without importing them
or fitting to 26.7 Gyr. The stage-1 benchmark is frozen in
[`verification/gupta-ccc-tl/result.json`](verification/gupta-ccc-tl/result.json), and the stage-2
conventions in [Gupta_ClockConventions.md](Gupta_ClockConventions.md) are blocked on the source's
Table 1 digits. [`lean/QLF_ClockRedshift.lean`](lean/QLF_ClockRedshift.lean) proves
`free_clock_scale_hits_any_age`: with a free positive clock scale, an age match is representability,
not selection. The issue asks that clock calibration stay independent of the test. This note does
the step that follows from both: it identifies which numbers in the frozen benchmark a clock
calibration cannot touch, so that a later QLF map has a test that calibration does not decide. It
reads no new data and runs no new fit.

## §1 Pre-registration (committed before the companion script was run)

### Tests

A **clock calibration** multiplies every elapsed reading by one positive scale `s` and every rate
read on that clock by `1/s`.

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| K1 | age ratios are calibration-free | `(s·t₁)/(s·t₂) = t₁/t₂` for every `s > 0` (Lean) | pass |
| K2 | the age–rate product is calibration-free | `(s·t)·(H/s) = t·H` for every `s > 0` (Lean) | pass |
| K3 | a free scale fits one age, not two | for positive model ages `t₁, t₂` and targets `T₁, T₂`, one `s` fits both iff `t₁/t₂ = T₁/T₂` (Lean) | pass |
| K4 | the benchmark's calibration-free numbers | `t(z=10)/t(0)`, `t(z=20)/t(0)` and `H₀·t₀` (with `H₀` the total `72.62…` and with the expansion part `59.51` km/s/Mpc) computed from the frozen result | report only |

**Verdict rule.** If K1 to K3 pass, the frozen benchmark makes three kinds of statement. The absolute
ages are fixed only up to a clock calibration, so by `free_clock_scale_hits_any_age` they test nothing
on their own. The ratios and `H₀·t₀` of K4 are fixed under every calibration, so they are the
benchmark's testable content, and a later QLF clock map is compatible with it only if it reproduces
them. In particular, calibrating a QLF clock count `N` by `H₀` leaves no freedom in the age: it
becomes `H₀·t₀ / H₀`, so the age then tests the model's `H₀·t₀` and nothing else. The outcome for
#234 stays INCOMPLETE: no QLF map is constructed here, so nothing is derived, permitted or excluded.

## §2 Results

To be filled from `gupta_scale_free.py` after this section is committed.
