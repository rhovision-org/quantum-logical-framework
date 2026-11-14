# Clock-conventions preparation and source-precision audit

[Program](../../Gupta_CCC_TL.md) · [Parent #234](https://github.com/rhovision-org/quantum-logical-framework/issues/234) · [Frozen audit specification](audit_specification.json)

This follow-up audits the origin of the present-age digits before stage 2 proceeds. Published targets were already known. The analysis specification is committed before computation; it is retrospective, not a blind preregistration. The original stage-1 implementation, tests, specification, result and checksums remain unchanged. No new fit or physical clock map is authorized by this preparation.

## Derivation and coverage of the audit

From the source's cubic, `x_B² = 3(1+r)/(3+r)` and `x(t0)=1`. Consequently the present coordinate age is

`T = Hc^(-1) * log((3+r)/(3*(1+r)))/(-r)`.

This independent closed form evaluates the same published mathematical quantity; it does not call the frozen implementation or fit any quantity to 26.70. The audit uses 60-digit standard-library Decimal logarithms and the stage-1 unit conversion.

For monotonicity put `q=-r`, with `0<q<1`, and `L(q)=log((3−q)/(3*(1−q)))`. Then `L(0)=0`, `L'(q)=1/(1−q)−1/(3−q)` and `L''(q)=1/(1−q)^2−1/(3−q)^2>0`. Since the derivative of `q*L'(q)−L(q)` is `q*L''(q)>0` and its value at zero is zero, `L(q)/q` increases strictly with q. T decreases with positive Hc. Thus the rounding rectangle's analytic extrema occur at the two corners used by the script. This calculus argument is not a new Lean proof; the reported endpoint evaluations are high-precision numerical values, not a certified interval-arithmetic artifact.

The nearest-rounding model is explicitly `Hc in [59.505,59.515]` and `r in [-0.79975,-0.79965]`. It is about the printed central values, not the reported statistical fit uncertainty or its unknown covariance. Table 1's 26.70 denotes the reporting interval [26.695,26.705] at hundredth precision.

## Result

The nominal closed form agrees with the existing 26.66721185884256 Gyr baseline to floating-point precision. Across the entire specified nearest-rounding rectangle, the numeric evaluations of the analytic extrema are **26.66197756649 to 26.67244792612 Gyr**. They do not reach the Table 1 reporting interval. Ordinary nearest-rounding of the two displayed fit parameters is therefore insufficient within this declared unit/model convention.

The single predeclared diagnostic `r=-0.80` gives **26.68519567394 Gyr**. A 365-day year gives **26.68547707244 Gyr**; a 365.2425-day year gives **26.66775945144 Gyr**. None individually rounds to 26.70. These are specified diagnostic substitutions, not revised fit inputs; combinations or additional alternatives were not searched. No target inversion was performed.

The [paper](https://arxiv.org/abs/2309.13100v1) identifies Matlab curve fitting and cites data sources, but the inspected text does not supply the actual age-calculation code and intermediate constants needed to identify the remaining digits. This audit does not prove that every alternative implementation is excluded. **Historical cause unresolved; source-precision gate stays open.** The nominal benchmark still passes its original, unchanged abstract-precision tolerance.

## Verification and next input

The [implementation](../../tools/gupta_age_precision_audit.py) and [tests](../../tests/test_gupta_age_precision_audit.py) check the nominal value against the stored baseline without rerunning it, the rounding exclusion, specified diagnostics, the matter-dominated limit and invalid input rejection. The implementation is committed before the final report is recorded. Artifact hashes cover this audit separately from the immutable stage-1 manifest.

Needed next: the author-used numerical intermediate/constants or an explicit correction reconciling Table 1. No message has been sent to the author. Until that input or equivalent published evidence exists, [Gupta_ClockConventions.md](../../Gupta_ClockConventions.md) remains a proposed contract and physical mapping is deferred.
