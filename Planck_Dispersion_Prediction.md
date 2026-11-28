# A registered prediction for issue #11: the walk's Planck-scale dispersion

Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF. This document answers, in part, [issue #11](https://github.com/rhovision-org/quantum-logical-framework/issues/11)
("the framework makes no testable predictions"), using the five-part standard: a machine-checked
substrate theorem, an explicit observable map, a number, a conventional comparator, and a kill
condition stated before the comparison.

## 0. The result in one paragraph

The free propagation law QLF derives, the unitary Dirac walk, is exactly light-like along its three
axes and slower than light off them, and its group velocity never exceeds `c` in any direction
(proved). The deficit is quadratic in energy over the Planck energy, with
a fixed coefficient and no linear term. In the standard parametrisation of Lorentz-invariance
violation this is a subluminal quadratic effect at `E_QG,2 = 3 E_P` along a body diagonal and
`√15 E_P ≈ 3.9 E_P` averaged over directions. Current gamma-ray-burst limits reach
`E_QG,2 > 6×10⁻⁸ E_P` ([LHAASO, GRB 221009A](https://arxiv.org/abs/2402.06009)). The prediction
therefore sits about `5×10⁷` beyond present reach in energy scale, `2.5×10¹⁵` in speed. It is a
falsifiable number, but it cannot be told apart from special relativity by any experiment now
running. It is also conditional on several bridges (§2.3), and the verified comparators are photon
measurements while the walk is a fermion law. That is the honest size of this answer to issue #11.

## 1. Why not the other suggested routes

Five routes were proposed. Each was checked against the repository; each lacks one named link
before it can give a number.

| Route | What is proved | The missing link |
|---|---|---|
| Relational memory (winding of cyclic rotations, #327/#329) | `winding_not_rotation_invariant`, `winding_not_additive`, `delay_colour_blind`, `same_census_different_latency` all exist and say what they claim | Winding depends on where a closed loop is read from, so it is not an invariant of the closure. A lab observable would need a physically marked start, and a map from that to a measured statistic that standard QM does not retain. Neither exists |
| α running vs MUonE ([PR #332](https://github.com/rhovision-org/quantum-logical-framework/pull/332), [`Alpha_Residual.md`](Alpha_Residual.md)) | N0/V0/V1/H1; `w = ½` structural | The census mass carries no logarithm ([`alpha_residual_bridge.py`](alpha_residual_bridge.py)); QLF's running is the imported continuum running. MUonE measures the hadronic part, which needs a census-to-`Δα_had(q²)` map. None exists. V0 holds only for common-mode insertion |
| Electron threshold | `H1` electron-class loops (#332) | No closure-to-mass map; the Koide phase is open ([`Lepton_Mass_Ratio_Protocol.md`](Lepton_Mass_Ratio_Protocol.md)) |
| Holographic factorization for a strong-field observable ([issue #296](https://github.com/rhovision-org/quantum-logical-framework/issues/296)) | `phase_blind_record_fails`, the river-model horizon algebra ([`Falling_Into_Black_Holes.md`](Falling_Into_Black_Holes.md)), and now RC0 (§5) | The horizon theorems are standard GR algebra; no map from a finite-capacity boundary to a ringdown, echo or polarisation number exists |
| Low-energy D–D fusion branching in metals ([`Fusion.md`](Fusion.md) §3d) | Nothing nuclear yet; the colour-closure results (#327) are substrate theorems | No closure census of the ⁴He, ³He and tritium channels (CF2–CF3), and no derivation that the environment changes their amplitudes (CF4). The observable `R(E,B)` is well posed and lab-accessible, so this is the strongest experimental route if those gates close |

The dispersion route is the one where every link but the declared step size is already a theorem.

## 2. The five parts

### 2.1 Substrate theorem (`F`, no axioms)

The Dirac walk ([`lean/QLF_DiracWalk.lean`](lean/QLF_DiracWalk.lean)) is unitary at every step and
its eigenvalues `e^{iE}` satisfy exactly `cos E = cos m · cos k_y · cos k_x · cos k_z`
(`diracWalk_dispersion`). [`lean/QLF_BoostCovariance.lean`](lean/QLF_BoostCovariance.lean) shows this
is the Minkowski shell up to a remainder of order `S²`, `S = E² + |k|² + m²` (`onShell_minkowski`),
so there is no correction linear in the step. New here, [`lean/QLF_WalkDispersionBound.lean`](lean/QLF_WalkDispersionBound.lean):

| Theorem | Statement (massless mode, first band) |
|---|---|
| `diracWalk_axis_exact` | along a lattice axis, `E = k` exactly |
| `walk_face_subluminal` | along a face diagonal `(κ, κ, 0)`, `0 < κ ≤ ½`: `E < √2 κ` |
| `walk_body_subluminal` | along a body diagonal `(κ, κ, κ)`, `0 < κ ≤ ½`: `E < √3 κ` |
| `walk_body_deficit_bounded` | and `√3 κ (1 − κ²/2) < E`: the deficit is at most quadratic |
| `diracWalk_body_bracket` | both bounds, for an actual eigenvalue of the walk |
| `walk_group_velocity_le_one` | **every direction**: wherever `P = ∏ cos kᵢ ≠ ±1`, the partial derivatives of `E = arccos P` satisfy `|∇E|² ≤ 1` |

The phase-velocity theorems cover the axes and diagonals; the group-velocity theorem covers every
momentum. Its proof is a census inequality: with `aᵢ = sin² kᵢ`, `|∇E|² = Σᵢ aᵢ ∏_{j≠i}(1 − aⱼ) /
(1 − ∏ᵢ(1 − aᵢ))`, the weight of exactly one active axis over the weight of at least one
(`one_axis_le_some_axis`). The group-velocity *coefficient* below is `N`, not `F`.

### 2.2 Exact coefficient (`N`, exact series checked numerically)

For direction `n` with `P₄ = Σ n_a⁴`, equating `log cos E` with `Σ log cos(n_a k)` gives

```
E² = k² − (1 − P₄) k⁴ / 6 + O(k⁶)
v_phase = 1 − (1 − P₄) k² / 12        v_group = 1 − (1 − P₄) k² / 4
```

[`planck_dispersion_prediction.py`](planck_dispersion_prediction.py) checks both coefficients against
the exact dispersion (relative error below `10⁻³` at `k = 0.02`), finds no in-band mode with phase
velocity above `c` in 20,000 samples, and confirms `⟨P₄⟩ = 3/5` on the sphere. Output:
[`data/planck_dispersion_prediction.json`](data/planck_dispersion_prediction.json).

### 2.3 Observable map (`B`, declared bridges)

There are four bridges, not one. None is derived.

1. **One walk step is one Planck time.** Then `k = E/E_P` to leading order, with
   `E_P = 1.2209×10¹⁹ GeV`. It is the repository's standing identification of the step with the
   Planck scale.
2. **Free fermions propagate by the Dirac walk.** The walk is built from twist steps and its
   generator is the Dirac operator (`diracWalk_generator`); reading it as the propagation law of a
   free neutrino or electron is a bridge.
3. **A frame prescription.** The direction pattern is set by the walk's axes. Whether observers
   share one lattice frame (Hypothesis P) or each perspective counts in its own frame
   (Hypothesis R) is open ([`Everything_Is_Relative.md`](Everything_Is_Relative.md),
   [`Relativity_Principle.md`](Relativity_Principle.md)). Under R the anisotropy has no fixed sky
   direction and only the direction average is observable. The direction-average row below is the
   one to use until the frame question is settled.
4. **For photons the law is open.** [`Relativity_Principle.md`](Relativity_Principle.md) §5 shows
   the census-symbol reading (`sin²ω = Σ sin²k_a`) gives the opposite sign, superluminal off-axis,
   with `v_group = 1 + (1 − P₄) k²/2`. A photon measurement tests QLF only under an adopted photon
   law, so photon kill conditions below are stated per reading.

### 2.4 The number

In the standard form `v = 1 − s (n+1)/2 (E/E_QG,n)ⁿ`:

| Reading | Direction | `E_QG,2 / E_P` | sign |
|---|---|---|---|
| Dirac walk | body diagonal | **3.00** | subluminal |
| Dirac walk | face diagonal | 3.46 | subluminal |
| Dirac walk | direction average | **3.87** (`√15`) | subluminal |
| Dirac walk | axis | ∞ (no effect) | — |
| census symbol (photon, if this reading holds) | body diagonal | 2.12 | superluminal |

Linear term: **none**, `E_QG,1 = ∞`.

Worked case: a 10 TeV photon from GRB 221009A (`z = 0.151`), body diagonal, walk reading: predicted
delay `8.6×10⁻¹⁵ s` relative to low-energy photons.

### 2.5 Conventional comparators

- **Special relativity**: no dispersion at any order. QLF differs from it, by the table above.
- **Linear-LIV quantum-gravity models** (`n = 1` at `E_QG,1 ~ E_P`): QLF predicts no linear term.
  Data already exclude `n = 1` up to `E_QG,1 > 10 E_P` ([LHAASO](https://arxiv.org/abs/2402.06009))
  and `> 7.6 E_P` ([Fermi-LAT, GRB 090510](https://arxiv.org/abs/1305.3463)). This agreement is
  **retrospective**: it was known before this registration, so it is consistency, not a test passed.
- **Present quadratic limits**: `E_QG,2 > 6×10⁻⁸ E_P` (LHAASO) and `E_QG,2 > 1.3×10¹¹ GeV`
  (Fermi-LAT, GRB 090510). Both are far below the predicted `3 E_P`.

**Fermion comparators.** The walk is a fermion law, and the verified limits above are for photons.
Neutrino and electron limits on quadratic Lorentz violation exist but are not compiled or checked
here, so no fermion comparison is claimed yet. Flavour-mixing limits do not apply: the walk's effect
is the same for every flavour.

**Conditional consequence.** *If* photons followed the walk, the effect would scale as the square of
the step, and the LHAASO limit would require the step to be shorter than about `5×10⁷` Planck times.

## 3. Kill conditions (stated before any new comparison)

Ledger entry `planck_dispersion` in [`claim_records/kill_conditions.json`](claim_records/kill_conditions.json).

All conditions refer to the **leading** coefficient fitted at `E ≪ E_P`. Higher orders are present
and the expansion is not a bound at arbitrary energy.

Fermions (free neutrinos or electrons; conditional on bridges 1–3):

- **K1f, linear term.** A confirmed energy-dependent speed linear in `E/E_P`.
- **K2f, magnitude.** A confirmed leading quadratic coefficient `|ξ₂| > 1/6` in
  `Δv = ξ₂ (E/E_P)²`, i.e. `E_QG,2 < 3 E_P` (the walk's largest, on the body diagonal).
- **K3f, sign.** A confirmed energy-dependent superluminal speed. The walk's group velocity never
  exceeds `c` (`walk_group_velocity_le_one`).

Photons (only under an adopted photon law):

- **K1γ.** A confirmed linear term, under either reading.
- **K2γ.** `|ξ₂| > 1/3` (`E_QG,2 < 2.1 E_P`) under the census reading, `> 1/6` under the walk reading.
- **K3γ.** Under the walk reading only, a superluminal energy-dependent photon speed.

What does **not** kill it: a null result at any foreseeable sensitivity. A null is what special
relativity also predicts, so it confirms nothing distinctive either. The prediction becomes a
discriminating test only within about a factor of 3 of `E_P` in `E_QG,2`.

## 4. Status

| Part | Label |
|---|---|
| Axis exactness, diagonal phase bounds, all-direction group velocity `≤ c` | `F` (proved, no axioms) |
| Coefficients `(1 − P₄)/12`, `(1 − P₄)/4`, direction average | `N` (exact series, numerical check) |
| Step = Planck time; fermions follow the walk; frame prescription | `B` (declared bridges) |
| Fermion comparator data | not compiled (photon limits only) |
| Photon sign | open (two QLF readings disagree) |
| Agreement with the linear-LIV exclusions | retrospective consistency, not evidence |
| Discrimination from special relativity | in principle only; about `5×10⁷` in `E_QG,2` beyond current reach |

The ledger entry stays `DRAFT`: the comparison data are already public, so the registration cannot
be marked as made before data access.

## 5. RC0: the relational-capacity bridge, first gate

The bridge proposed for issues #296 and #11 asks first whether identical perspective records can
hide different closure clocks (RC0). They can, proved in
[`lean/QLF_RelationalClock.lean`](lean/QLF_RelationalClock.lean), no axioms. Three perspectives each
contribute the ordered word `+ −`:

| Arrangement | History | Closure depth |
|---|---|---|
| adjacent | `A+ A− B+ B− C+ C−` | 1 |
| nested | `A+ B+ C+ C− B− A−` | 3 |

- `same_records`: each perspective's own ordered word is identical in both.
- `different_clocks`: the adjacent arrangement closes at horizon 1; the nested one first at 3.
- `rc0_record_does_not_determine_clock`: no function of the per-perspective records gives the
  closure depth, so the factorization condition of issue #296 fails for the closure clock.
- `shuffle_reconstructs`: the records plus the interleaving (who acts at each step) rebuild the
  history, so they do fix the clock.

**Reconciling both ends.** If actions of different perspectives commute, the nested tree is not a
different history. Swapping neighbouring actions of different perspectives never changes a record
(`record_swap`), and six such swaps carry nested to adjacent (`nested_commutes_to_adjacent`). The
computable `reconcile` does this for any tagged history: it closes each perspective's opening and
closing ends together by laying the records end to end. It keeps every record (`reconcile_record`,
proved for all histories) and maps nested to adjacent, depth 3 to depth 1 (`reconcile_lowers_depth`).
So the depth-3 clock is real only if the cross-perspective order is a genuine dependence, one
perspective's action waiting on another's. RC0's gap lives in that dependence relation, not in the
records. For fully independent perspectives the commutation class is fixed by the records, so its
least depth is a function of them.

This strengthens `census_cannot_determine_first_passage` in
[`lean/QLF_ClosureDepthTime.lean`](lean/QLF_ClosureDepthTime.lean) from the multiset of events to
the ordered record each perspective holds. That module already proves the inventory version at every
depth `d`; the perspective-record version here is for three perspectives.

**RC1, the serialization-free capacity.** `reconcile` keeps the records but need not minimise
depth: `A = ++−−`, `B = −−++` laid end to end have depth 2, interleaved depth 1, with the same
records (`reconcile_not_always_minimal`). The serialization-free quantity is the least depth over
the interleavings the dependencies allow, `τ_rel = min_{h ∈ LinExt(P)} maxExcursion(h)`. For two
independent perspectives this is the minimum over all shuffles of their records (`relCapacity`,
`1` in the example, `relCapacity_example`), so it is a function of the records alone. A dependency
only removes interleavings, so every admitted one has depth at least that (`dependency_increases_capacity`),
and "A closes before B starts" raises it strictly from 1 to 2 (`dependency_strict_increase`). That
nature realises the minimum is a proposed reading, not a theorem; the general partial-order version
and three or more perspectives are not yet formalised.

**Open.** RC2 to RC6, which would carry the clock to an observable. The black-hole
entropy ratio `4 ln 2` between the uncorrected boundary count and Bekenstein–Hawking remains the
normalization gap recorded in [`Holography_Audit.md`](Holography_Audit.md). Reading it as relational
redundancy, `N_eff/N = 1/(4 ln 2)`, is a conjecture with no derivation yet. RC0 gives no laboratory
number on its own. Of the routes examined, the dispersion in §2 is the only one that reaches one.

## 6. Files

- [`lean/QLF_WalkDispersionBound.lean`](lean/QLF_WalkDispersionBound.lean): §2.1
- [`lean/QLF_RelationalClock.lean`](lean/QLF_RelationalClock.lean): §5
- [`planck_dispersion_prediction.py`](planck_dispersion_prediction.py), [`data/planck_dispersion_prediction.json`](data/planck_dispersion_prediction.json): §2.2, §2.4
- [`claim_records/kill_conditions.json`](claim_records/kill_conditions.json): §3
- Background: [`Relativity_Principle.md`](Relativity_Principle.md) §5–§5b, [`Closure_Unitarity.md`](Closure_Unitarity.md) §15, [`Claim_Status.md`](Claim_Status.md)
