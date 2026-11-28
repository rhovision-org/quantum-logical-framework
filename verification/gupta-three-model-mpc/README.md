# Three-model megaparsec conversion sensitivity — retrospective reproduction

**Status:** numerical consistency check only. **Source-precision gate OPEN.** No QLF physical bridge, fit, model promotion or author-code attribution.

Source: [Gupta (2023), MNRAS 524, 3385–3395, Table 1](https://doi.org/10.1093/mnras/stad2032); [arXiv:2309.13100v1](https://arxiv.org/abs/2309.13100v1). Follows [#234](https://github.com/rhovision-org/quantum-logical-framework/issues/234), [#235](https://github.com/rhovision-org/quantum-logical-framework/pull/235), and [Aria's originally reported hypothesis](https://github.com/rhovision-org/quantum-logical-framework/issues/234#issuecomment-6880690413), recorded in commit [41d8e7d](https://github.com/rhovision-org/quantum-logical-framework/commit/41d8e7d5d53af300c9d9640643e2e6760b7ac59e).

## Frozen inputs (read from published Table 1, not fitted)

| Model | Hx (km/s/Mpc) | alpha/Hx or Omega_m | Published t0 (Gyr) |
|---|---:|---:|---:|
| CCC | 72.70 | alpha/Hx = -0.4953 | 13.69 |
| LCDM+TL | 60.48 | Omega_m = 0.1351 | 19.25 |
| CCC+TL | 59.51 | alpha/Hx = -0.7997 | 26.70 |

**Explicit conventions:** 365.25 days/year; 86400 seconds/day; two alternative values for the *same* conversion constant: 3.0856775814913673e19 km/Mpc and 3.09e19 km/Mpc. Hx is the expansion component, not H0 = Hx + Ht in the tired-light hybrids. Printed ages represent the half-open two-decimal rounding interval [printed-0.005, printed+0.005). The comparison is at displayed-parameter precision and does not model fitted-parameter covariance.

## Independent equations

For both CCC branches, with r = alpha/Hx and -1 < r < 0:

`t0 = (Mpc_km / (Hx * seconds_per_Gyr)) * ln[(3+r)/(3*(1+r))] / (-r)`.

For flat LCDM+TL expansion (matter plus Lambda, no radiation in this present-age expression), with 0 < Omega_m < 1:

`t0 = (Mpc_km / (Hx * seconds_per_Gyr)) * 2/(3*sqrt(1-Omega_m)) * asinh(sqrt((1-Omega_m)/Omega_m))`.

The LCDM+TL age is evaluated using its *expansion* Hx, not the total redshift slope. Tired light changes the observed-redshift relation, not this specified expansion-age integral. The script uses Decimal logarithms at 60-digit precision and evaluates asinh as a logarithm; it imports no frozen stage-1 implementation. All three age formulas are linear in Mpc_km with other inputs held fixed.

## Results (Gyr)

| Model | Nominal Mpc | Rounded Mpc | Published | Rounded Mpc reproduces printed digits? |
|---|---:|---:|---:|---|
| CCC | 13.66822070507 | 13.68736715463 | 13.69 | YES |
| LCDM+TL | 19.21972916780 | 19.24665217284 | 19.25 | YES |
| CCC+TL | 26.66721185884 | 26.70456730090 | 26.70 | YES |

The closest boundary is CCC+TL: 26.7045673 lies only about 0.0004327 Gyr below the upper rounding threshold 26.705. That sensitivity makes confirmation of the original constants and any unpublished intermediate precision particularly important.

## Reproduce (standard library only)

```bash
python3 tools/gupta_three_model_mpc_audit.py
python3 -m unittest discover -s tests -p 'test_gupta_three_model_mpc_audit.py' -v
```

This script is read-only and prints deterministic JSON; it does not modify source data, freeze artifacts, hashes, fits, or the existing age-audit implementation. Tests check three printed intervals, the exact unit-scaling identity, the frozen CCC+TL baseline, boundary margins, and domain rejection. A successful local run is not a GitHub CI pass; CI must be checked at the final PR head.

## Interpretation and exclusions

The same single rounded conversion constant reproduces all three *published two-decimal ages*, without parameter optimization or inversion. This is a stronger cross-model consistency observation than matching the CCC+TL row alone, **but remains retrospective** because the targets were known. It does **not** prove the author used 3.09e19 km/Mpc; other conventions/intermediates could yield similar printed digits. Confirm using author-used constants, code or a published correction. Do not change existing checksum manifests, frozen benchmark tolerances or the physical QLF bridge status. No conclusion about the Gupta time-reversal/half-total hypothesis follows.
