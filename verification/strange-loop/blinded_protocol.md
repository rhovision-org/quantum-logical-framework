# Blinded three-polarizer bridge check — protocol draft

**Status:** `AWAITING_DATA`. No measurement was performed for this repository. This is a protocol, not a result and not evidence for QLF.

**Purpose.** Test the **operational map** used by the three-polarizer bridge: the mapping from polarizer settings and detector outcomes to the ideal-optics comparator. This is a calibration/consistency test of the bridge, not a QLF-specific discrimination, because the current framework does not predict a deviation from Malus's law for this stack. A conventional-optics pass therefore does **not** confirm QLF; a calibrated failure would reject the operational map as implemented.

## Frozen predictions

For an ideal unpolarized input and ideal polarizers, the comparator predicts:

| Stack | Predicted transmission relative to unpolarized input |
|---|---:|
| 0° | 1/2 |
| 0° → 90° | 0 |
| 0° → 45° → 90° | 1/8 |
| 0° → 90° → 45° | 0 |

These are imported ideal-optics numbers. They are not derived from MO2 or ZFA.

## Protocol

1. **Freeze this file.** Record its SHA-256 in the apparatus log before target data are taken.
2. **Apparatus.** Single-mode laser at a fixed wavelength; three calibrated polarizers; a photodetector with a linearity check; dark-count and stray-light measurement; angle readout with stated uncertainty.
3. **Randomization.** Randomize the order of the four stacks and the nominal angles; record the realized angles and uncertainties. Do not adjust the analysis after seeing the transmission ratios.
4. **Blinding.** A custodian holds the target ratios until the frozen predictions and analysis script are committed. The analyst receives only the randomized stack labels and the calibrated detector counts.
5. **Analysis.** Compute transmission ratios with a stated uncertainty budget (angle, extinction, detector linearity, background). The primary test is whether each ratio lies within the predeclared interval around the comparator prediction.
6. **Rejection rule.** A calibrated ratio outside the predeclared interval rejects the operational map as implemented. A pass is a consistency check only.

## What would make it QLF-specific

A QLF-specific test would need a predeclared deviation from the comparator — a predicted angular dependence, extinction signature or order effect that differs from ideal Malus optics. The current repository does not supply one. Until it does, this protocol calibrates the bridge; it does not test QLF against conventional optics.

## Relation to the claim records

This protocol corresponds to `claim_records/three_polarizer.json`. Its `proof_obligation.conservative_return_status` remains `PARTIAL`: the toy Lean interface proves the shape, while the operational map and detector record remain `B-OPEN`.

**No target data exist in this repository, so the check is not executed and no numerical result is claimed.**
