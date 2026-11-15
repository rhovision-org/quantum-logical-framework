# Clock-conventions preparation and source-precision audit

[Program](../../Gupta_CCC_TL.md) · [Parent #234](https://github.com/rhovision-org/quantum-logical-framework/issues/234) · [Frozen audit specification](audit_specification.json)

This follow-up audits the origin of the present-age digits before stage 2 proceeds. Published targets were already known. The analysis specification is committed before computation; it is retrospective, not a blind preregistration. The original stage-1 implementation, tests, specification, result and checksums remain unchanged. No new fit or physical clock map is authorized by this preparation.

## Derivation and coverage of the audit

From the source's cubic, `x_B² = 3(1+r)/(3+r)` and `x(t0)=1`. Consequently the present coordinate age is

`T = Hc^(-1) * log((3+r)/(3*(1+r)))/(-r)`.

This independent closed form evaluates the same published mathematical quantity; it does not call the frozen implementation or fit any quantity to 26.70. The audit uses 60-digit standard-library Decimal logarithms and the stage-1 unit conversion.

For monotonicity put `q=-r`, with `0<q<1`, and `L(q)=log((3−q)/(3*(1−q)))`. Then `L(0)=0`, `L'(q)=1/(1−q)−1/(3−q)` and `L''(q)=1/(1−q)^2−1/(3−q)^2>0`. Since the derivative of `q*L'(q)−L(q)` is `q*L''(q)>0` and its value at zero is zero, `L(q)/q` increases strictly with q. T decreases with positive Hc. Thus the rounding rectangle's analytic extrema occur at the two corners used by the script. This calculus argument is not a new Lean proof; the reported endpoint evaluations are high-precision numerical values, not a certified interval-arithmetic artifact.

Explicitly, with the positive unit-conversion constant C, `T=C*L(q)/(Hc*q)`, so

`dT/dq = C*[q*L'(q)−L(q)]/(Hc*q²) > 0`,
`dT/dHc = −C*L(q)/(q*Hc²) < 0`.

Here `L(q)>0` for `0<q<1`; the argument above proves the first numerator positive. Since `q=−r`, age increases with −r and decreases with Hc throughout the specified rectangle, rather than merely at sampled points.

The nearest-rounding model is explicitly `Hc in [59.505,59.515]` and `r in [-0.79975,-0.79965]`. It is about the printed central values, not the reported statistical fit uncertainty or its unknown covariance. Table 1's 26.70 denotes the conventional nearest-rounding half-unit interval: `26.70 ± 0.005 Gyr`, or [26.695,26.705], at hundredth precision. Both tie endpoints are included conservatively, independently of a tie-breaking rule; the exclusion has a strict gap and does not depend on those endpoints.

## Result

The nominal closed form agrees with the existing 26.66721185884256 Gyr baseline to floating-point precision. Across the entire specified nearest-rounding rectangle, the numeric evaluations of the analytic extrema are **26.66197756649 to 26.67244792612 Gyr**. They do not reach the Table 1 reporting interval. Ordinary nearest-rounding of the two displayed fit parameters is therefore insufficient within this declared unit/model convention.

The single predeclared diagnostic `r=-0.80` gives **26.68519567394 Gyr**. A 365-day year gives **26.68547707244 Gyr**; a 365.2425-day year gives **26.66775945144 Gyr**. None individually rounds to 26.70. These are specified diagnostic substitutions, not revised fit inputs; combinations or additional alternatives were not searched. No target inversion was performed.

The [paper](https://arxiv.org/abs/2309.13100v1) identifies Matlab curve fitting and cites data sources, but the inspected text does not supply the actual age-calculation code and intermediate constants needed to identify the remaining digits. This audit does not prove that every alternative implementation is excluded. **Historical cause unresolved; source-precision gate stays open.** The nominal benchmark still passes its original, unchanged abstract-precision tolerance.

## Candidate cause: a rounded megaparsec (hypothesis, reported by Aria)

After this audit was frozen, @aixaria0 reported a candidate cause in [#234](https://github.com/rhovision-org/quantum-logical-framework/issues/234#issuecomment-6880690413) (2026-11-14): converting with the rounded value **1 Mpc = 3.09e19 km** instead of 3.0856775814913673e19 km. Recomputed here with the unchanged audit function `age_gyr(59.51, -0.7997, mpc_km='3.09e19')`, the central present age is **26.70456730090 Gyr**, which lies inside the reporting interval [26.695, 26.705] and so rounds to Table 1's 26.70. The audit's nominal convention gives 26.66721185884 Gyr; the ratio between them is exactly the ratio of the two megaparsec values, because the age is linear in the Mpc constant. Aria also reports that the same conversion reproduces the rounded CCC and ΛCDM+TL present-age entries; that second claim is recorded as his and has not been rechecked in this follow-up.

Status of this finding:

- It is a **hypothesis**, not an identified cause. A unit conversion that recovers the printed digits is one way to get them; it does not show the author used it. Aria states the same reservation.
- It was found after the published targets were known, so it is a retrospective explanation, not a prediction. It was not produced by an optimizer or a target inversion, but it was not predeclared either.
- The frozen specification, implementation, tests, result and checksums are unchanged. The audit's conclusion (displayed-parameter rounding alone is insufficient under the declared unit convention) still stands; this finding moves the explanation from parameter rounding to the unit constant.
- **The source-precision gate stays open** until the author's constants or code, or an equivalent published statement, confirm the conversion. If confirmed, the gate closes with the cause documented and the frozen benchmark tolerance still unchanged.

Aria's same comment raises two further points for stage 2: distance matching alone permits any positive `q = Ht/Hc`, so equation 43's choice `q = e = (1+r)(3+r)/2` (which removes the second-order term in `zt = q*zc + q*(q−e)*zc²/2 + …`) is an additional assumption; and the elapsed reading depends on an explicit clock convention (`d tau = f dt` under fixed reference `c0`). Both bear on the [proposed convention contract](../../Gupta_ClockConventions.md) and are left for its review rather than edited into the hashed contract here.

## Verification and next input

The [implementation](../../tools/gupta_age_precision_audit.py) and [tests](../../tests/test_gupta_age_precision_audit.py) check the nominal value against the stored baseline without rerunning it, the rounding exclusion, specified diagnostics, the matter-dominated limit and invalid input rejection. The implementation is committed before the final report is recorded. Artifact hashes cover this audit separately from the immutable stage-1 manifest.

Needed next: the author-used numerical intermediate/constants or an explicit correction reconciling Table 1. No message has been sent to the author. Until that input or equivalent published evidence exists, [Gupta_ClockConventions.md](../../Gupta_ClockConventions.md) remains a proposed contract and physical mapping is deferred.

## Reproduce this audit

The specification was frozen at `b85242bedfccac16e3979687e4681f6d0aae83a3`; the implementation was committed at `fe870de41c1e185c6e30c0980bd2cafa134cf65b` before recording the [result](audit_result.json). [SHA256SUMS](SHA256SUMS) covers the specification, audit implementation, tests, result and proposed convention contract.

```bash
python3 tools/gupta_age_precision_audit.py
python3 -m unittest discover -s tests -p 'test_gupta_age_precision_audit.py' -v
sha256sum -c verification/gupta-clock-conventions/SHA256SUMS
sha256sum -c verification/gupta-ccc-tl/SHA256SUMS
```

The five new audit tests pass. Typed-record and document-link validation pass. No Lean source or build input changes are part of this follow-up, and no new kernel assurance is claimed. [Grok's subsequent independent review and execution report](grok_review.md), relayed by Jim, records five passing tests, matching central/bound values and verified checksums.

## Review disposition and progression

[Grok's review](grok_review.md) reports no numerical or formal objections and recommends keeping this draft. The derivative and reporting-interval clarifications are now explicit. **The author intermediate/code or source correction remains a hard prerequisite for subsequent stage-2 physical implementation.** The prepared conventions remain proposed, not frozen or adopted. This review is not an exception to the gate. Any decision to proceed with the residual unexplained must be explicitly recorded by Jim with the revised gate and remaining limitation; no such decision has been supplied.

Merge order: #233 first, then #235, or rebase/retarget #235 onto main after #233 lands. A favorable review of this draft does not authorize either merge or a draft-to-ready transition.
