# Retrospective SPARC rotation-curve benchmark

This is a reproducible public-data comparison of the declared QLF RAR formula
with Newtonian baryonic acceleration and a per-galaxy NFW grid fit. It is related
to [issue #77](https://github.com/rhovision-org/quantum-logical-framework/issues/77).
The pipeline is [`sparc/sparc_blind_pipeline.py`](sparc/sparc_blind_pipeline.py);
its historical filename does not establish an information-isolated experiment.

## Inputs and numerical model

The QLF predictor uses `g = (g_bar + sqrt(g_bar² + 4 g_bar a0))/2`, with
`a0 = c H0/(2π)`, declared `H0 = 73 km/s/Mpc`, and external global mass-to-light
values `0.5` (disk) and `0.7` (bulge). No per-galaxy QLF parameter is optimized by
this script. That does not establish that the model form or declared inputs were
historically chosen without access to the public data.

Lean proves the defined RAR's algebraic self-consistency. The physical mapping of
closure-balance variables onto observed accelerations and uniqueness of the
interpolation remain separate bridge questions; see
[`Proof_to_Physics.md`](Proof_to_Physics.md).

## Information access and seal

`load_mass()` reads observed velocities and errors. The quality cut uses
`eV < 0.1 Vobs`, and `points()` computes `gobs` before the prediction CSV is
written. For an admitted point, the QLF prediction formula uses its baryonic
inputs. The hash seal is written before residual scoring, but does not establish
that targets were inaccessible, first revealed afterwards, or independently
unseen. Target-informed quality selection is not by itself proof of fitting.

The appropriate status is **retrospective public-data benchmark / numerical
reproduction**. Historical blinding, third-party chronology and independent
physical confirmation are not established by this workflow. Read as a
strange loop, the return is a descriptive residual summary, not a predeclared
prediction; see [`Strange_Loops.md`](Strange_Loops.md) §4.

## Reproduced descriptive results

The cuts `Q ≤ 2`, `Inc ≥ 30°`, positive radii/velocities and
`0 < eV < 0.1 Vobs` admit 147 galaxies and 2696 points with valid baryonic inputs.
Residuals are `log10(gobs) − log10(gpred)`; scatter is population standard
deviation about the model's own mean, not inferred intrinsic scatter.

| Model | Parameters optimized in this run | Mean, dex | Scatter, dex |
|---|---:|---:|---:|
| Newton, baryonic acceleration only | 0 | 0.4309 | 0.2809 |
| NFW, two grid-searched parameters per galaxy | 294 | −0.0050 | 0.0593 |
| QLF form with fixed external `g_dag = 1.2e−10` | 0 | −0.0094 | 0.1326 |
| QLF form with declared `a0 = c H0/(2π)` | 0 | −0.0002 | 0.1327 |

The external `g_dag` was not refitted by this script; it should not be described
as this form's newly computed best fit. The receipt's legacy `free_params` label
is qualified by `parameter_accounting`. Smaller residuals or fewer fitted
parameters alone do not establish model equivalence, an observational error
floor, overfitting, physical uniqueness or a Bayesian model preference.

## Reproduce at a frozen revision

Both input datasets are already committed. Do not replace them with a moving
mirror download when reproducing a recorded result.

```bash
cd sparc
python3 sparc_blind_pipeline.py
```

The script writes `predictions_sealed.csv` and `receipt.json` in its working
directory; use a temporary copy when preserving the committed historical files.
The regression tests perform that isolated reproduction. The full CSV hash and
the body-only seal (without header/trailing newline) hash different byte strings.
The [claim record](claim_records/sparc_rar.json) carries the data provenance and
open bridge. A future blinded test needs a frozen selection/analysis policy,
controlled target access and an independently inspectable chronology.

## References

- Lelli, McGaugh & Schombert, *SPARC: Mass Models for 175 Disk Galaxies*, AJ 152 (2016) 157.
- McGaugh, Lelli & Schombert, *Radial Acceleration Relation*, PRL 117 (2016) 201101.
- [`lean/QLF_DarkMatter.lean`](lean/QLF_DarkMatter.lean), [`lean/QLF_MondScale.lean`](lean/QLF_MondScale.lean), [`lean/QLF_RarBalance.lean`](lean/QLF_RarBalance.lean).
