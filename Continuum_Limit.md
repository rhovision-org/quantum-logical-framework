# Continuum Limit: the fluxoid→Regge toy model

Part of the [Quantum Logical Framework (QLF)](README.md). This doc is milestone 1 of issue #301 (the
toy continuum limit) and of the bridge-closure roadmap whose plan record is
[`Stationary_Action.md`](Stationary_Action.md). The test is a concrete map from ZFA fluxoid labels to a Regge
geometry. It is run blind against kill conditions that are stated here first.

## §1 Pre-registration (committed before the companion script was run)

### The construction

* **Complex.** The periodic `L × L` lattice (a torus), each square split by one diagonal. It is the
  smallest 1+1D lattice on which a deficit angle is defined at every vertex.
* **Histories.** Twist words on two axes, read as walks from the origin, as in
  [`Closure_Walk.md`](Closure_Walk.md) and [`lean/QLF_LinkClosure.lean`](lean/QLF_LinkClosure.lean).
* **Labeling A (current).** `n_e` = the net signed number of times the walk crosses edge `e`. This is
  `walkCurrent` in `QLF_LinkClosure`. Diagonals carry `0`.
* **Labeling B (axis).** `n_e` = the action-vector component of `e`'s axis, the same on every edge
  of that axis. This is the issue's "drawn from the signed action vector".
* **Face obligation.** `∂f = Σ_{e∈∂f} ±n_e`, the oriented sum around triangle `f`.
* **Lengths.** `ℓ_e = ℓ_ref(e) · g(|n_e|)`, with `ℓ_ref = 1` on axis edges and `√2` on diagonals,
  for the family `g(m) ∈ {1 + m/4, 1 + m/2, 1 + m, √(1 + m)}`. The last is the issue's
  `ℓ² ∝ |n|`, shifted so that no length is zero.
* **Regge curvature.** At each vertex the deficit is `ε_v = 2π − Σ` (triangle angles at `v`), with
  the angles taken from the law of cosines. A triangle that violates the triangle inequality makes
  the geometry undefined. Such cases are counted, not repaired.
* **Smoothing.** The periodic binomial kernel of degree `N` (the discrete Bernstein weights
  `C(N,k)/2^N`), applied to the current field on each axis.
* **Two-body order.** Two-body interleavings as in
  [`lean/QLF_TensorFromClosure.lean`](lean/QLF_TensorFromClosure.lean) (`Step`). The boundary order is
  the order in which each body's projection reaches its closures.

### What equivalence means here

For a single body, the class `[h]_B` is the closure-test class of
[`lean/QLF_PerspectiveHolography.lean`](lean/QLF_PerspectiveHolography.lean): `h ~ h'` iff `h ++ c`
closes exactly when `h' ++ c` does, for every continuation `c`. Closure is count balance, so the
class of `h` is its signed action vector. Every closed history is in one class.

### Kill conditions, stated first

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| K1 | ZFA is the face identity `∂f ≡ 0` (issue #301) | every count-balanced history has `∂f = 0` on every face | **fail**: `QLF_LinkClosure` proves ZFA is the *vertex* identity `div = 0`, and `^>v<` circulates around its plaquette |
| K2 | ZFA flatness implies Regge flatness | every count-balanced history gives `ε_v = 0` at every vertex (labeling A) | fail |
| K3 | the geometry is a function of the class | no two histories in one class give different deficit vectors (labeling A) | fail |
| K4 | no new free parameters | the set of Regge-flat histories is the same for every `g` in the family | unknown |
| K5 | smoothing respects the closure identity | binomial smoothing leaves `div` unchanged, exactly, on every history | pass (the kernel is translation-invariant, so it commutes with differences) |
| K6 | perspectival time is invariant on the class | the per-body closure order is the same across a `Step` class | pass, by construction (Mazurkiewicz trace order) |
| K7 | labeling B carries content inside ZFA | some two count-balanced histories differ in their labeling-B geometry | **fail**: count balance zeroes every label |

**Verdict rule.** The construction is rejected as a fluxoid→Regge identification if labeling A fails
K3 or K4. Labeling B passing K3 does not rescue it if it also fails K7, since a geometry that is the
same for every closed history carries no closure content (method rule 4,
[`ScientificApproach.md`](ScientificApproach.md)). K5 and K6 passing are structural and are not
evidence.

**Recorded beforehand.** In 2D the Regge action `Σ_v ε_v` equals `2πχ` (discrete Gauss–Bonnet), so
it is topological, and on the torus it is `0` for every labeling. The issue's deliverable 4
(Regge → Einstein–Hilbert under refinement) is therefore empty in 1+1D. It needs `d ≥ 3`, where the
hinge is an edge and Cheeger–Müller–Schrader applies. The script checks Gauss–Bonnet as a code
check, not as a result.

## §2 Results

Run: [`fluxoid_regge.py`](fluxoid_regge.py) on the `10 × 10` torus, every two-axis history of length
`≤ 8` (87,381 histories, 5,341 of them closed). The output is
[`data/fluxoid_regge.json`](data/fluxoid_regge.json). Lengths 4 and 6 give the same verdicts.

| | Outcome | What was found |
|---|---|---|
| K1 | **fail** | 2,984 of 5,341 closed histories have a nonzero face obligation. The smallest is `>^<v`, whose current circulates around its plaquette with total `4` (proved: `plaquette_circulates`) |
| K2 | **fail** | the same 2,984 closed histories are Regge-curved under every length map. For `g = 1 + m`, 8 of them violate a triangle inequality instead |
| K3 | **fail** | 137 of the 145 closure classes hold more than one geometry. The closed class alone holds 143 different deficit vectors (140 for `g = 1 + m`). The Lean core is `current_not_class_function`: `[]` and `>^<v` share a class and differ in current |
| K4 | pass | the Regge-flat closed histories are the same set under all four maps. It is exactly the set with zero current, the retraced walks (`<>`, `^v`, `<>^v`, …): 2,357 of 5,341 |
| K5 | pass (structural) | binomial smoothing of degrees 2 and 4 commutes with the divergence on every history and leaves `div = 0` on every closed one, in exact arithmetic. Proved for every kernel: `div_smooth`, `smooth_preserves_closure`. On an open history it smears the endpoint charges. It never keeps integrality, so the smoothed field is no longer a fluxoid labeling |
| K6 | pass (structural) | the per-body closure order is the same across each of the 4,097 `Step` classes. The cross-body order is not: in all 672 classes where both bodies close, some interleaving reorders the two bodies' closures |
| K7 | **fail** | labeling B gives one geometry, the flat reference, for every closed history (proved: `axisLabel_closed`) |

Gauss–Bonnet held to `9·10⁻¹⁵` on every labeled torus, as a code check.

### Verdict

**The construction is rejected as a fluxoid→Regge identification.** Labeling A fails K3. Labeling B
passes K3 only by being constant on closure, so it fails K7. By the verdict rule the toy model does
not derive Regge geometry from ZFA.

### What the run establishes instead

* **ZFA is the vertex identity, not the face identity.** Closure is `div J = 0`
  (`div_walkCurrent`). The face identity `∂f ≡ 0`, imposed on a closed history, holds exactly when
  the current is zero. It would select only the retraced walks, so it is not ZFA in any form.
* **On this complex, curvature is the circulation.** Under every monotone map tested, a closed
  history is Regge-flat exactly when it carries no current. The flat set is map-independent, so K4
  passes in a strong form, but the deficits themselves change with the map.
* **The geometry is finer than the class.** A deficit vector records the walk's current, which the
  closure tests of [`lean/QLF_PerspectiveHolography.lean`](lean/QLF_PerspectiveHolography.lean)
  cannot see: the closed class alone holds 143 geometries. A post-hoc note, not pre-registered: the
  fold phase cannot repair this, because it takes two values and the class holds 143 geometries.
  This is the #296 failure mode from the other side. Here the interior observable is too fine for
  the boundary record, where #296's scalar records were too coarse.
* **Perspectival time is a partial order, never a total one.** K6 is Mazurkiewicz trace order: each
  body's own closures keep their order, and the order between bodies is not invariant. That is the
  issue's "partial order of residual-obligation discharges", and it holds by construction.
* **Smoothing is harmless and empty.** It preserves the closure identity for any kernel, so it
  carries no closure content, and it destroys the integer labels it was meant to transport.

### What stays open

* A labeling that is a class function **and** varies on closure. Neither labeling tested is both,
  and K3 with K7 is the test any candidate must pass.
* `d ≥ 3`, where the Regge action is not topological and Cheeger–Müller–Schrader applies (the
  issue's deliverable 4).
* The `Continuum_Limit` claim record,
  [`claim_records/continuum_limit.json`](claim_records/continuum_limit.json), stays `B-OPEN`.

## §3 Lean anchors

[`lean/QLF_FluxoidRegge.lean`](lean/QLF_FluxoidRegge.lean), no axioms, built on
[`lean/QLF_LinkClosure.lean`](lean/QLF_LinkClosure.lean):

| Theorem | Statement |
|---|---|
| `div_smooth` | smoothing a link field by any kernel commutes with the divergence |
| `smooth_div_free`, `smooth_preserves_closure` | so the smoothed current of a returning history is divergence-free everywhere (K5) |
| `plaquette_closed`, `plaquette_balanced` | `>^<v` on `(ℤ₃)²` returns and is count-balanced |
| `plaquette_circulates` | yet its current circulates around its plaquette with total `4` (K1) |
| `current_not_class_function` | `[]` and `>^<v` share a closure class and differ in current (K3) |
| `axisLabel_closed` | the axis labeling is zero on every count-balanced history (K7) |

The angle computations (K2, K3 on deficits, K4) are numerical: floats compared at `10⁻⁹`.

## §4 Milestone 2: a map that factors through the class (pre-registration)

Committed before any milestone-2 code exists and before any milestone-2 number has been computed.
Stage 2a is frozen here. Stage 2b is described but **not** frozen: it needs its own
pre-registration once 2a has run.

### 4.1 What a single closed history can carry (proved first)

[`lean/QLF_ClassFactoring.lean`](lean/QLF_ClassFactoring.lean), no axioms. The phased closure class
of a single history is `(net, fold)`, so on closed histories a class-factoring map is a function of
the fold. `fold_eq_classBit` shows the fold of a closed history is one bit: negative-twist parity
plus the parity of the three projected areas. `class_function_factors`: any map of closed histories
that respects the fold is a function of that bit. `circulation_invisible`: `[]` and `^>v<^>v<` share
the bit but enclose areas `0` and `−2`.

So K3 and K7 can hold together for single closed histories only with a two-valued geometry. The
milestone-1 failure was not a bad choice of labels: **no** labeling of one closed history can be
both a class function and carry curvature. Geometry has to be read from the **census**, the count of
all the ways, which is a class function by construction because it counts every representative.
This is the reading of "a closure's frequency is its multiplicity" applied to distance.

### 4.2 Stage 2a: the vacuum census geometry (calibration, frozen)

* **Ways between two places.** A way from site `x` to site `y` of `ℤ³` is any twist history whose
  spatial displacement is `y − x`. The three spatial axes move the walk one step; the gauge pair
  `+ −` does not move it.
* **Census weight.** `G(x) = Σ_L 8^{−L} · #{histories of length L with displacement x}`, the
  Kraft-weighted count ([`lean/QLF_KraftMeasure.lean`](lean/QLF_KraftMeasure.lean)). It is finite
  because the spatial walk is transient. It counts every representative, so it is a class function.
* **Length.** `ℓ(x, y) = 1 / G(y − x)`, the length at which the inverse census weight grows like
  distance in three dimensions. Only ratios of lengths enter the curvature, so no scale is fitted.
* **Sensitivity reading (not a decision input).** `G₄(x) = Σ_L 8^{−L} · #{histories with
  displacement x and zero gauge net}` with `ℓ = G₄^{−1/2}`, the four-axis walk read at gauge balance.
* **Complex.** The Freudenthal (Kuhn) triangulation of `sℤ³`: each cube of side `s` split into six
  tetrahedra along its main diagonal. Edges are the three axis directions, three face diagonals and
  one body diagonal. Hinges are edges, so the Regge action is not topological.
* **Curvature.** The deficit at each edge type is `2π` minus the sum of the dihedral angles of the
  tetrahedra around it. The lattice is infinite and the lengths are translation-invariant, so every
  edge of a type has the same deficit and there is no boundary. Dihedral angles come from the Cayley–Menger formulas, in
  floating point, compared at `10⁻⁹`.
* **Scales.** `s = 1, 2, 4, 8, 16, 32`.

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| M1 | the census length is a geometry | every tetrahedron of the complex has positive Cayley–Menger volume at every `s` | pass |
| M2 | the vacuum is flat in the large | the largest absolute edge deficit decreases with `s` and is below `10⁻³` at `s = 32` | pass |
| M3 | the approach is the census's own anisotropy | the deficits fall like `s^{−p}` with a fitted `p ≥ 1.5` over `s = 4 … 32` | pass, with `p ≈ 2` from the cubic harmonic in the lattice Green's function |
| M4 | class factoring | `G` is unchanged by permuting the letters of any history it counts | pass by construction (structural) |

**Verdict rule.** If M1 or M2 fails, the census length is rejected as a vacuum geometry and stage 2b
is not run on it. M3 and M4 are recorded, not decisive.

**What 2a can and cannot show.** It is a calibration. `G` is, up to a constant, the classical
simple-cubic lattice Green's function, and its approach to `1/|x|` is known mathematics. A pass shows
the map is well defined and flat in the vacuum. It is not evidence that the census produces gravity.

### 4.3 Stage 2b: sourced geometry (not frozen)

The physical test is whether a source changes the census so that the curvature has the right sign
and falloff. That needs a source model, which is a choice with physical content, so it gets its own
pre-registration after 2a. Candidates already in the repository:

1. **Exclusion.** Sites held by a persistent closure are unavailable to other ways (Pauli exclusion,
   as in the crystal and chemistry models). `G` becomes a taboo Green's function.
2. **Delay.** Ways through a source's sites take longer, weighting them by an extra `8^{−k}`
   ([`Gravity_From_Delay.md`](Gravity_From_Delay.md)).
3. **Shared closures.** Ways that close jointly with the source count once per closure, so the count
   near the source changes through `QLF_EntanglementPrimacy`'s joint closures.

Kill conditions for 2b will include: the sign of the curvature around a source, its falloff with
distance, and linearity in the source size. A 2b result that depends on which of the three models is
chosen will be reported as such.

## §5 Stage 2a result

Run: [`census_geometry.py`](census_geometry.py) (about 100 s; needs `mpmath`). Output:
[`data/census_geometry.json`](data/census_geometry.json). Regression test:
[`tests/test_census_geometry.py`](tests/test_census_geometry.py). The census weight is evaluated
from its Bessel-integral form to 40 digits. A check at 60 digits agreed to `2·10⁻²¹`, and `G(0)`
reproduces Watson's integral.

**Registered verdict: FAIL (stage 2a).** M1 passes and M2 fails, so by the verdict rule the length
`ℓ = 1/G` is rejected as a vacuum geometry under the registered test, and stage 2b is not run on it.

| | Outcome | What was found |
|---|---|---|
| M1 | pass | every tetrahedron has positive volume at every scale |
| M2 | **fail** | the largest deficit is `0.80, 0.82, 0.21, 0.044, 0.011, 0.0026` at `s = 1, 2, 4, 8, 16, 32`. It rises from `s = 1` to `2`, and at `s = 32` it is `2.6·10⁻³`, above the registered `10⁻³` |
| M3 | pass | the deficits fall like `s^{−2.10}` over `s = 4 … 32` (sensitivity reading: `s^{−2.16}`) |
| M4 | pass (structural) | `G` counts every history with a given displacement |

The edge-length ratios approach the Euclidean ones: `b/a = 1.41460` and `c/a = 1.73257` at `s = 32`,
against `√2 = 1.41421` and `√3 = 1.73205`. The deficits keep the cubic pattern at every scale:
positive on the axis and body-diagonal edges, negative on the face diagonals.

**Reading.** The census length is flat in the large, but more slowly than registered.
`s² × deficit` settles near `2.7` (`2.79, 2.70, 2.68` at `s = 8, 16, 32`), so the registered
`10⁻³` would be reached near `s ≈ 52`. The `10⁻³` threshold was an absolute number chosen without a
computed coefficient, and the coefficient turned out larger than the threshold allowed. This is
recorded as the registered failure. A scale-free criterion (deficit times `s²` bounded) would have
passed, but it was not the registered test, and adopting it now would be post hoc.

What does stand: the census length is a positive geometry at every scale (M1), and its curvature is
the census's own cubic anisotropy, falling as `s^{−2}` (M3). That is the expected behaviour of a
lattice Green's function and is not evidence of gravity. Whether to re-register the calibration with
a scale-free criterion and go on to 2b is a decision for the issue, not part of this result.

## §6 Re-registered calibration (2a′) and sourced stage 2b (pre-registration)

Jim chose on 2026-11-23 to re-register the vacuum calibration with a scale-free criterion and then
pre-register 2b. Both are frozen here, before any new number is computed.

### 6.1 Stage 2a′: a scale-free vacuum test on fresh scales (post hoc, disclosed)

The criterion is chosen **after** seeing §5, so it is tested only on scales §5 did not compute.
From §5, `s² × max deficit = 2.68` at `s = 32`.

| | Claim | Passes if |
|---|---|---|
| V1 | the vacuum curvature is the census's `s^{−2}` anisotropy | at `s = 64` and `s = 128`, `s² × max deficit` lies in `[2.4, 3.0]` |
| V2 | the length ratios converge to the Euclidean ones | at `s = 128`, `b/a` is within `2·10⁻⁴` of `√2` and `c/a` within `2·10⁻⁴` of `√3` |

If V1 or V2 fails, 2b is not run. Same code as §5, scales `64` and `128` added.

### 6.2 Stage 2b: does a local source act like a mass?

**Source model (primary): exclusion.** A source is a set `S` of lattice sites held by a persistent
closure, which no other way may visit (Pauli exclusion, as in the crystal and chemistry models). The
census weight becomes the taboo count `G_S(x, y)` of ways from `x` to `y` that avoid `S`. For a
finite `S` it is exact: `G_S(x, y) = G(y − x) − Σ_{a,b∈S} G(x − a) [G_SS⁻¹]_{ab} G(b − y)`.
Lengths `ℓ(x, y) = 1/G_S(x, y)` on the edges of the Freudenthal triangulation of `ℤ³` (`s = 1`).

**Sensitivity model: delay.** Instead of being forbidden, a step onto a source site costs one extra
twist (weight `1/8` more). This is a finite-rank change of the same kind. Reported, not a decision
input.

**Sources:** a single site (`n = 1`), a `2×2×2` cube (`n = 8`) and a `3×3×3` cube (`n = 27`),
centred at the origin.

**Measured.**

* `δℓ/ℓ` on edges at distance `r` from the source centre (midpoint distance), and its falloff
  exponent `k`, fitted to the mean over axis edges in shells `r ∈ [4, 10]`.
* The Regge integrated curvature `K(R) = Σ ℓ_e ε_e` over interior edges whose midpoint lies within
  `R` of the centre, minus the same sum in the vacuum: `ΔK(R)`, for `R = 4, 6, 8, 10`. Edges with a
  tetrahedron touching `S` are excluded. The computational box has half-width `12`.

**What a mass would do.** In general relativity the spatial metric of a static mass perturbs lengths
like `M/r`, so its integrated scalar curvature tends to a positive limit proportional to `M`.

| | Claim | Passes if | Prior |
|---|---|---|---|
| B1 | the source curves space with one sign | `ΔK(R) > 0` at every `R` and every `n` | unknown |
| B2 | the perturbation falls like a mass's | `k ∈ [0.8, 1.2]` for every `n` | **fail**: a local change of the walk alters the Green's function by a finite-rank term `∝ G(x)G(y)`, so a nearest-neighbour length changes like `r^{−2}` |
| B3 | the curvature is linear in the source | fitting `ΔK(10) ∝ n^q` over `n = 1, 8, 27` gives `q ∈ [0.8, 1.2]` | **fail**: the taboo correction scales with the source's capacity, roughly its linear size, so `q ≈ 1/3` |

**Verdict rule.** The census length with an exclusion source acts as a mass only if B1, B2 and B3
all pass. If B2 fails for both the exclusion and the delay model, the reading is that **no local
modification of the walk produces a mass-like `1/r` perturbation in this length map**, and a 2b
that wants gravity needs a nonlocal source (a persistent closure whose ways reach to infinity), which
would be a separate pre-registration.

## §7 Results: stage 2a′ and stage 2b

Run: [`census_geometry.py`](census_geometry.py) (2a′, stored under `stage_2a_prime` in
[`data/census_geometry.json`](data/census_geometry.json)) and [`census_source.py`](census_source.py)
(2b, output [`data/census_source.json`](data/census_source.json); the Green's-function table is
cached in [`data/census_source_green.json`](data/census_source_green.json)). Regression tests:
[`tests/test_census_geometry.py`](tests/test_census_geometry.py),
[`tests/test_census_source.py`](tests/test_census_source.py).

### 7.1 Stage 2a′: PASS

| scale | `s² × max deficit` | `b/a − √2` | `c/a − √3` |
|---|---|---|---|
| 64 | 2.672 | `9.7·10⁻⁵` | `1.3·10⁻⁴` |
| 128 | 2.671 | `2.4·10⁻⁵` | `3.2·10⁻⁵` |

V1 and V2 pass. The vacuum curvature of the census length is the lattice's own `s^{−2}`
anisotropy with coefficient `2.67`, and the geometry is Euclidean in the large. The registered
failure of §5 stands as the record of the absolute threshold.

### 7.2 Stage 2b: a local source does not act as a mass

**Registered verdict: neither model acts as a mass.** B1, B2 and B3 fail for the exclusion source
and for the delay source.

| | exclusion `n = 1, 8, 27` | delay `n = 1, 8, 27` | Verdict |
|---|---|---|---|
| B2 falloff `k` of `δℓ/ℓ` | 1.99, 2.11, 2.21 | 1.99, 2.10, 2.20 | **fail, as predicted**: `r^{−2}`, not `r^{−1}` |
| B1 `ΔK(R) > 0` | negative at `R = 8, 10` for every `n` | the same | **fail** |
| B3 `q` | undefined (`ΔK(10) < 0`) | undefined | **fail** |

The source does stretch nearby lengths: `δℓ/ℓ` on axis edges is positive, `1.8·10⁻²` at `r = 4` and
`2.9·10⁻³` at `r = 10` for a single excluded site. But it falls like `r^{−2}`, which is the finite-rank
structure predicted in §6.2: a local change of the walk alters `G(x, y)` by a term `∝ G(x)G(y)`, and a
nearest-neighbour length sees it at second order in `1/r`. A static mass perturbs lengths like
`M/r`. So by the verdict rule, **no local modification of the walk produces a mass-like perturbation
in this length map.** A 2b that wants gravity needs a nonlocal source, a persistent closure whose
ways reach to infinity, and that is a separate pre-registration.

The strength does not grow linearly with the source either. At `r = 10`, `δℓ/ℓ` is `2.9, 8.3, 14.4`
(×`10⁻³`) for `n = 1, 8, 27`, roughly `n^{0.5}`.

**Disclosed deviations and design gaps.**

1. *Degenerate tetrahedra.* Near the source some tetrahedra have no Euclidean realisation: 24, 78 and
   312 for exclusion (276 for delay at `n = 27`), all within distance `3.3` of the centre. The
   pre-registration did not say how to treat them. As in milestone 1 they are counted, not repaired,
   and their edges are excluded like edges touching `S`. This only affects edges inside every `R`
   used.
2. *The `ΔK` measure is contaminated by the background.* At `s = 1` the vacuum deficits are large
   (`≈ 0.8`, §5), so `ΔK` contains a term `(ℓ − ℓ₀) ε₀` that is the source's stretch times the
   lattice anisotropy, not curvature made by the source. Summed over shells, that term grows with
   `R`. A post-hoc diagnostic (not a decision input) keeps only `ℓ₀ (ε − ε₀)`. It is negative at every
   `R ≥ 8` for every source and model, and for `n = 1` it has settled (`−8.07`, `−8.08` at `R = 8, 10`).
   So B1's failure is not an artefact of the contamination: the curvature the source makes outside
   its core is negative in total, the opposite sign to a mass.

### 7.3 What milestone 2 establishes

* **A geometry read from one closed history can carry one bit** (`QLF_ClassFactoring`). Geometry has
  to come from the census.
* **The census length `1/G` is a good vacuum geometry**: positive at every scale, Euclidean in the
  large, with curvature equal to the lattice's own anisotropy falling as `2.67/s²` (2a′).
* **Local sources in it are not masses**: exclusion and delay both stretch nearby lengths, but like
  `r^{−2}`, with negative integrated curvature outside the core.

Open, and the next registered step if #301 continues: a nonlocal source. In this map, a `1/r` length
perturbation needs a change to the census that reaches every scale, such as a persistent closure that
is itself a walk, rather than a set of forbidden or slowed sites. The claim record stays `B-OPEN`.

## §8 Stage 2c: sources that add ways, balancing, and the far field (pre-registration)

Jim, 2026-11-23, after §7: *"close interaction can expand space balancing. closer or further
contracts space depending on non-magnetic mass."* In the census-length map the sign of the response
should be the sign of the change in the number of ways: §7's sources remove ways and stretch lengths.
This stage tests the other sign, a source that mixes both, and whether the far field depends only on
one number. Frozen before any 2c number is computed.

### 8.1 Sources

All use the general finite-rank form. A step onto a source site `a` is weighted by `w_a`, so with
`Λ = diag(1 − w_a)` on the source set `S`,

`G'(x, y) = G(x, y) − g_xᵀ Λ (I + (G_SS − I) Λ)⁻¹ g_y` for `x, y ∉ S`,

which is §7's exclusion for `w = 0` and delay for `w = 1/8`. A **shared** site has `w = 9/8`: a
shared closure supplies one more way at that site, one extra option among the eight twists.

| source | sites | weights |
|---|---|---|
| `share1` | the origin | shared |
| `line4` | `0, e_y, 2e_y, 3e_y` (the sites `^^^vvv` visits, no circulation) | shared |
| `plaq4` | `0, e_y, e_x + e_y, e_x` (the sites `^>v<` visits, one circulation) | shared |
| `mixed` | the origin excluded, its six neighbours shared | `0` and `9/8` |

Same lattice, triangulation, box and lengths as §7. Measured: the shell mean of `δℓ/ℓ` on axis
edges at midpoint distance `r = 2 … 10` from the source centroid.

**Ways charge.** `Q = 1ᵀ Λ (I + (G_SS − I) Λ)⁻¹ 1`. Far from the source `g_x ≈ G(x)·1`, so the
far-field prediction for an edge `(u, v)` is `δℓ/ℓ ≈ Q ḡ(u) ḡ(v) / G(v − u)`, with `ḡ(u)` the mean
of `G(u − a)` over the source sites. `Q > 0` (ways removed) predicts expansion and `Q < 0` (ways
added) predicts contraction.

### 8.2 Tests

| | Claim | Passes if | Prior |
|---|---|---|---|
| C1 | adding ways contracts space | for `share1`, `line4`, `plaq4`, the shell mean `δℓ/ℓ < 0` at every `r = 2 … 10` | pass |
| C2 | the far field is the monopole | for all four sources, measured / predicted shell mean lies in `[0.85, 1.15]` at `r = 8, 9, 10` | pass |
| C3 | far away, only `Q` matters, not the shape | at `r = 10`, `(δℓ/ℓ)/Q` for `line4` and `plaq4` agree within 5% | pass |
| C4 | balancing: near and far responses differ in sign | for `mixed`, the shell mean changes sign between `r = 2` and `r = 10`, and its sign at `r = 10` is the sign of `Q` | unknown |

Also reported, not decision inputs: the falloff exponent of each source (expected near 2, as in §7)
and `Q` itself. If a source makes `I + (G_SS − I)Λ` singular or any `G'` non-positive in the box, it is
reported as invalid and its rows are dropped.

**Reading rule.** C1–C3 together support: *the sign of the spatial response is the sign of the change
in ways, and the far field depends only on the net ways charge*. C4 tests the balancing reading:
a source can expand space close in and contract it further out, or the reverse. None of this can
give a `1/r` law, since every finite source falls like `r^{−2}` here (§7). In the unsigned census a
circulation is invisible (§4.1), so C3 tests shape, not magnetism; a magnetic test needs the signed
census and its own registration.

## §9 Stage 2c result

Run by [`census_source_2c.py`](census_source_2c.py) against §8 as frozen in `414d010`; data in
[`data/census_source_2c.json`](data/census_source_2c.json), regression test in
[`tests/test_census_source_2c.py`](tests/test_census_source_2c.py). All four sources are valid: every
`I + (G_SS − I)Λ` is invertible and every `G'` in the box is positive.

| source | `Q` | `δℓ/ℓ` at `r = 2` | `δℓ/ℓ` at `r = 10` | measured / monopole at `r = 2` | at `r = 10` | falloff `k` |
|---|---|---|---|---|---|---|
| `share1` | −0.1433 | −2.05e-2 | −8.40e-4 | 0.977 | 0.999 | 1.97 |
| `line4` | −0.7293 | −8.85e-2 | −4.28e-3 | 0.952 | 0.999 | 2.00 |
| `plaq4` | −0.7753 | −1.07e-1 | −4.55e-3 | 0.909 | 0.997 | 1.98 |
| `mixed` | +0.0788 | +1.90e-3 | +4.47e-4 | 0.172 | 0.966 | 1.76 |

| | Verdict | Numbers |
|---|---|---|
| C1 adding ways contracts space | **PASS** | every shell mean of `share1`, `line4`, `plaq4` is negative |
| C2 far field is the monopole | **PASS** | all twelve ratios at `r = 8 … 10` lie in `[0.946, 0.999]` |
| C3 shape-blind far away | **PASS** | `(δℓ/ℓ)/Q` at `r = 10`: `line4` 0.005863, `plaq4` 0.005870 (0.1% apart) |
| C4 balancing sign change | **FAIL** | `mixed` is positive (expanding) at every `r = 2 … 10`, the sign of its `Q` |

**What this establishes** (numerical evidence, exact up to float, on one lattice and box). In the
census-length map the spatial response has the sign of the change in ways: removing ways (§7)
stretches lengths, adding ways contracts them, and far from the source the response is fixed by one
number, the ways charge `Q`, to within 1% at `r = 10` whatever the shape. So the far field carries
one scalar charge; every source falls as `r^{−2}` (here `k = 1.76 … 2.00`), not `1/r`.
The steeper `k` of `mixed` is its near field approaching the monopole from below.

**Relation to the proved orientation ledger.** [`QLF_MagneticOrientation`](lean/QLF_MagneticOrientation.lean)
already proves that like poles make space and unlike poles destroy it (`like_poles_expand`,
`opposite_poles_destroy`, `bodies_expand_iff`), and [`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean)
that like charges admit no joint closure while opposite charges can (`like_charges_do_not_close`).
That is a boolean ledger, not a metric ([`Spatial_Response_QLF.md`](Spatial_Response_QLF.md) §2). 2c is
its counterpart in the census-length geometry: a pairing that admits no joint closure removes ways and
stretches lengths, one that closes adds ways and contracts them, and the measured effect falls as
`r^{−2}` with a strength set by `Q`. So the ledger's sign now has a geometric reading with a
distance law. What 2c adds is the law and the shape blindness; the sign was already proved.

**What it does not.** The registered balancing source shows no sign change. Close in, its shared
shell pulls the response down to 17% of the monopole at `r = 2`, but not through zero, and the far
sign is the sign of `Q` as predicted. So the reading *close interaction expands and further
contracts, or the reverse* is not supported for this source. A source whose near field overturns its
`Q` would need a different geometry and its own registration; it is not ruled out. And C3's line
and plaquette differ in circulation, which the unsigned census cannot see (§4.1): the shape
blindness found here says nothing about magnetism.

**Open after 2c.** (1) A `1/r` law: no finite source in this map gives one, so it must come from an
extended or nonlocal source, or from a different length map. (2) Magnetism: needs the signed census.
Each needs a pre-registration before any number is computed.

## §10 Stage 2d: geometry from joint closures with the source (pre-registration)

Jim, 2026-11-23, after §9: *"is the joint closure 1/r?"* and *"joint closure is not arbitrary it is
necessary."* The count of joint closures between two places is the census Green's function, and it
falls as `1/r`: `r·G(r)` is 0.686, 0.649, 0.639, 0.638, 0.637 at `r = 2, 4, 8, 10, 15`, tending to
`2/π` (the table of §7). §7–§9 read an edge length from the ways *between the edge's ends*, so a source
enters only through ways source → `u` and source → `v`, two legs, and the response is `r^{−2}`. A
source can reach a place only through joint closures with it ([`QLF_SharedEvent`](lean/QLF_SharedEvent.lean),
[`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean)), so the response at a place is fixed by the
one leg, the source's joint closures with that place. That map is taken as forced, not chosen for its
falloff. Frozen before any 2d number is computed.

### 10.1 Map

For a source with weights as in §8.1, `K = Λ (I + (G_SS − I) Λ)⁻¹`, and the **joint-closure field**
of the source at `x ∉ S` is

`φ(x) = 1ᵀ K g_x`, so `φ(x) ≈ Q G(x)` far away.

`φ` is the change in the number of ways the source shares with `x`, weighted as `Q` is: positive when
the source removes ways. An edge `(u, v)` has

`ℓ(u, v) = ℓ₀(u, v) (1 + λ (φ(u) + φ(v)) / 2)`, `ℓ₀ = 1/G(v − u)`,

with `λ = 10⁻³`, so the response is first order. The coupling `λ` is not derived, and only results
independent of it at first order are decision inputs.

### 10.2 Sources and measure

The four sources of §8.1 (`share1`, `line4`, `plaq4`, `mixed`) and the three exclusion sources of §6.2
(`n = 1, 8, 27`, `w = 0`). Same lattice, triangulation, box and interior-edge rule as §7.

Primary measure, chosen in the light of §7's background contamination: the **curvature change**
`ΔK(R) = (1/λ) Σ ℓ₀ (ε − ε₀)` over interior edges with midpoint within `R` of the source centroid.
Reported, not a decision input: the full `(1/λ) Σ (ℓ ε − ℓ₀ ε₀)`. Validity check: rerun at `λ = 2·10⁻³`;
if any `ΔK(10)` changes by more than 2%, the run is not first order and is reported as invalid. Any
degenerate tetrahedron is counted and excluded as in §7.

### 10.3 Tests

| | Claim | Passes if | Prior |
|---|---|---|---|
| D1 | vacuum outside the source: curvature sits at the source | for every source, `ΔK(6)` and `ΔK(8)` lie within 10% of `ΔK(10)` | unknown |
| D2 | Gauss law: the enclosed curvature is the ways charge | `ΔK(10)/Q` lies within 10% of its median over the seven sources | pass if D1 passes |
| D3 | removing ways is positive curvature | `sign ΔK(10) = sign Q` for every source | pass |

Calibration, not a test: the shell mean `δℓ/ℓ` falls with exponent `k ≈ 1`, which the map builds in.

**Reading rule.** D1–D3 together: the one-leg joint-closure geometry is flat outside a source and
carries the source's ways charge as its enclosed curvature, the structure of the spatial part of a
Newtonian mass (linearized Schwarzschild in isotropic coordinates, where an expanding `1/r` conformal
factor encloses positive curvature). D3 then reads sign: removing ways is positive mass, adding ways
(joint closure, unlike poles) is negative. **Kill:** if D1 fails, the curvature is spread through the
vacuum and the one-leg map does not give a mass. Not claimed by any outcome: the time part of the
metric, light bending, or the value of the coupling.

## §11 Stage 2d result

Run by [`census_source_2d.py`](census_source_2d.py) against §10 as frozen in `abba91c`; data in
[`data/census_source_2d.json`](data/census_source_2d.json), regression test in
[`tests/test_census_source_2d.py`](tests/test_census_source_2d.py). The run is first order: at
`λ = 2·10⁻³` every `ΔK(10)` agrees with `λ = 10⁻³` to better than 0.1%. No tetrahedron is degenerate.
The calibration holds: every shell falloff is `k = 0.99 … 1.01`.

| source | `Q` | `ΔK(6)` | `ΔK(8)` | `ΔK(10)` | `ΔK(10)/Q` |
|---|---|---|---|---|---|
| `share1` | −0.1433 | −1.361 | −1.335 | −1.340 | 9.35 |
| `excl1` | +0.4946 | +4.696 | +4.607 | +4.625 | 9.35 |
| `line4` | −0.7293 | −4.954 | −4.959 | −4.928 | 6.76 |
| `plaq4` | −0.7753 | −5.386 | −5.437 | −5.430 | 7.00 |
| `excl8` | +1.3887 | +8.319 | +8.420 | +8.588 | 6.18 |
| `excl27` | +2.3672 | +11.606 | +11.185 | +11.274 | 4.76 |
| `mixed` | +0.0788 | +0.288 | +0.274 | +0.277 | 3.51 |

| | Verdict | Numbers |
|---|---|---|
| D1 plateau of the enclosed scalar proxy (registered as "vacuum outside the source") | **PASS** | every `ΔK(6)`, `ΔK(8)` within 4% of `ΔK(10)` |
| D2 Gauss law across sources | **FAIL** | `ΔK(10)/Q` runs from 3.51 to 9.35 (median 6.76) |
| D3 removing ways is positive curvature | **PASS** | the sign of `ΔK(10)` is the sign of `Q` for all seven |

**What this establishes** (numerical evidence on one lattice and box). The `1/r` falloff of `δℓ/ℓ` is
built into the map: `φ` is a sum of Green's functions, and `G(r) ∝ 1/r` (§10), so `k ≈ 1` is the
calibration, not a derived law. What is measured is D1: the **signed cumulative** curvature change
`ΔK(R)`, a scalar proxy summed over all interior edges within `R`, has a plateau from `R = 6` to `10`.
That says the net scalar contribution of the shells between `6` and `10` is small. It does not say
the space there is flat: `ΔK` is a sum of signed deficits, so a plateau is compatible with
cancellation between edges, and it carries no information about the Ricci or Riemann tensor. In
three dimensions a first-order conformal perturbation `h_ij = 2u δ_ij` has
`R_ij = −∂_i∂_j u − δ_ij ∇²u` and `R = −4∇²u`; for `u ∝ 1/r` outside the source the scalar vanishes
but the Ricci tensor does not. So D1 is consistent with a vanishing scalar curvature outside the
source and does not test vacuum geometry. D3: the sign of the plateau is the sign of `Q` for all seven
sources, so removing ways gives a positive enclosed scalar proxy and adding ways (joint closure) a
negative one.

*Correction to the §10 reading rule, which is left as frozen.* §10 read D1–D3 together as "flat outside
a source … the structure of the spatial part of a Newtonian mass". That reading is withdrawn: with D2
failing and D1 a cumulative scalar proxy, nothing here supports a physical mass or a spacetime
reading.

**What failed, and a post-hoc reading.** The enclosed curvature is not one constant times `Q` across
sources, so the Gauss law as registered fails. A diagnostic run after the verdict (not a decision
input) shows the constant depends on the source's **site set**, not its weights: `share1` and `excl1`
(one site, opposite weights) give 9.352 and 9.351; the shared cube `share8` gives 6.183 against
`excl8`'s 6.184; the excluded line gives 6.84 against `line4`'s 6.76. Within a site set the curvature
is linear in `Q` to 1% or better, whatever its sign. The likely cause is the measure, not the
geometry: edges touching the source are dropped (§7), so part of the curvature at the source is not
counted, and a larger site set hides more of it. Whether the full enclosed curvature is `Q` times one
constant needs a measure that keeps the source's own edges, and its own registration.

**Open after 2d.** (0) A discriminating test of vacuum geometry: a pre-registered local test (per-edge deficits or a tensor reconstruction, or absolute shell residuals) with scale and boundary controls, to separate cancellation from genuine flatness. (1) The Gauss constant: a measure that counts the source's edges. (2) The time part
of the metric and light bending, which no stage so far measures. (3) The coupling `λ`, which is not
derived. (4) Magnetism, which needs the signed census.

## §12 Stage 2e: local curvature outside a source (pre-registration)

Committed before any 2e code exists and before any 2e number has been computed. It answers open item
(0) of §11: §11's D1 plateau is a signed cumulative sum, so it cannot tell flat space from curvature
that cancels in the sum. Stage 2e reads the curvature **locally**, at each vertex and on each edge,
and asks which of three geometries sits outside a source:

* **flat**: every deficit change outside the source vanishes;
* **vacuum**: the scalar curvature vanishes at each place, while a tidal (traceless Ricci) part
  remains, as on the spatial slice of a mass in general relativity;
* **cancellation**: the scalar curvature is non-zero at each place, of both signs, and only its sum
  is small.

**Prior, stated plainly.** `φ` is exactly harmonic off the source on the lattice: `G` is the Green's
function of the eight-twist walk, `6G(x) − Σ_nbrs G = 8δ_x0`, so `φ = Σ_a w_a G(· − a)` has zero
lattice Laplacian outside `S`. In the continuum a conformal metric `(1 + 2u)δ` with harmonic `u` has
`R = −4∇²u = 0` and Ricci `−∂_i∂_j u`, traceless and falling as `r^{−3}`. That is linearized
Schwarzschild's spatial slice in isotropic coordinates. So continuum reasoning predicts **vacuum**,
not flat. The test checks whether the lattice Regge reading realizes this locally. It tests the map
and its discretization, not new physics.

### 12.1 Map, sources, measures

Map, coupling, lattice, box, triangulation and the seven sources are those of §10. `Δε_e = ε_e − ε⁰_e`
for each counted edge (complete ring, no vertex in `S`, no degenerate tetrahedron, as in §10).

* **Vertex measures.** A vertex `x` qualifies if all 14 of its incident edges (seven types, two
  directions) are counted. Its **local scalar** is `s(x) = (1/λ) Σ_{e∋x} ½ ℓ⁰_e Δε_e`, so that summing
  `s` over vertices gives §10's `ΔK`. Its **local unsigned curvature** is
  `t(x) = (1/λ) Σ_{e∋x} ½ ℓ⁰_e |Δε_e|`.
* **Shells.** `r = round(|x − c|)`, `c` the source centroid, `r = 4 … 10`.
* **Cancellation index.** `χ(r) = mean |s| / mean t` over the shell. `χ = 1` when every edge at a
  vertex has the same sign (a pure local scalar); `χ` near `0` when the edges at each vertex cancel
  (a traceless, tidal field).
* **Tidal orientation.** Axis edges with midpoint `m` (relative to `c`) are **radial** if the edge's
  axis has `|m_i|/|m| ≥ 0.95` and **tangential** if `|m_i|/|m| ≤ 0.10`. Pooled over midpoints with
  `6 ≤ |m| ≤ 10`, `ρ = mean(Δε·|m|³) radial / mean(Δε·|m|³) tangential`. For a harmonic `u ∝ 1/r` the
  sectional curvature orthogonal to an edge with direction `t` is `t·∂∂u·t`, which is `2u/r²` radially
  and `−u/r²` tangentially, so the continuum value is `ρ = −2`.

### 12.2 Controls (same `ℓ⁰` background, same `λ`, same formula with `φ` replaced by `f`)

* **V, vacuum control**, one per source on that source's qualifying vertex set:
  `f(x) = Q · (2/π) / |x − c|`, the continuum monopole with the source's own `Q` (`G(r) → 2/(πr)`,
  §10). Continuum-harmonic, so it shows what a genuine vacuum gives after this discretization.
* **N, non-vacuum control** (zero-sum ripple): source-free, `c = 0`, vertices with `|x| ≥ 4`,
  `f(x) = (2/π)/|x| + b cos(πx/8) cos(πy/8) cos(πz/8)`, `b = 0.005`. Its Laplacian is non-zero and
  changes sign, so its local scalar cancels in shell sums. It shows the test can see cancellation.
* **F, flat control**: `f ≡ 1`, a uniform rescaling, which must give `|Δε| < 10⁻⁹` everywhere.

**Validity gates.** The test has power only if (i) every V has `χ_V(r) ≤ 0.10` at `r = 6, 8, 10`,
(ii) N has `χ_N(r) ≥ 0.30` at `r = 6, 8, 10`, (iii) F passes, and (iv) rerunning the census at
`λ = 2·10⁻³` changes no shell `mean t` at `r = 8` by more than 2%. If (i) or (ii) fails, L2 is reported
as uninformative, not as a pass or fail. If a V has `ρ_V` outside `[−2.5, −1.5]`, L3 is reported as
uninformative for that source.

### 12.3 Tests (each must hold for all seven sources)

| | Claim | Passes if | Prior |
|---|---|---|---|
| L1 | not flat: a tidal field remains outside the source | `mean t` falls with a fitted exponent `p ∈ [2.5, 3.5]` over `r = 4 … 10` | pass |
| L2 | local vacuum, not cancellation | `χ(r) ≤ 0.10` at `r = 6, 8, 10` | pass |
| L3 | the tidal pattern of a point mass | `ρ ∈ [−2.5, −1.5]` | pass |
| L4 | the local tidal strength is the ways charge | `mean t / mean t_V` at `r = 8` lies in `[0.80, 1.25]` | pass |

Reported, not decision inputs: `χ(r)` and `χ_V(r)` for `r = 4 … 10` and their falloff (a
discretization residual should fall about like `r^{−2}`); the sign of the radial `Δε` against the sign
of `Q`; the mean signed `s` per shell.

**Reading rule.** L1–L4 together: outside a source the census-length geometry is, at first order and
locally, the spatial slice of linearized Schwarzschild in isotropic coordinates, with strength set by
`Q`: not flat, and not a cancellation. L1 failing reads flat. L2 failing with the gates passing reads
cancellation, which withdraws any vacuum reading of §11 D1. L4 is local, so it is independent of
§11's D2 failure, which concerned an enclosed sum with source edges excluded. Not claimed by any
outcome: the time part of the metric, light bending, the value of `λ`, or that the conformal form of
the map is forced.

## §13 Stage 2e result

Run by [`census_source_2e.py`](census_source_2e.py) against §12 as frozen in `3600c5c`; data in
[`data/census_source_2e.json`](data/census_source_2e.json), regression test in
[`tests/test_census_source_2e.py`](tests/test_census_source_2e.py). One code fix was made after the
first run started and before any verdict was read: the flat control F has no tangential deficit, so
`ρ` divided by zero; it is now reported as undefined for F (F's gate uses only `max |Δε|`).

**Gates.** F passes (`max |Δε| = 3.6·10⁻¹⁵`). The run is first order (every `mean t` at `r = 8` moves
by under 1% at `2λ`). Every vacuum control V has `χ_V ≤ 0.10` (0.066 … 0.069) and `ρ_V ∈ [−1.91, −1.88]`,
so L3 is informative for every source. **The non-vacuum control N fails its gate:** `χ_N` is 0.085,
0.124, 0.231 at `r = 6, 8, 10`, below the registered 0.30. So **L2 is uninformative as registered.**
The ripple amplitude was set for `r = 8`; at `r = 6` its Laplacian is about 0.4 of the monopole's
tidal field, too weak to reach the threshold there.

| source | `Q` | `p` (L1) | `χ` at `r = 6, 8, 10` | `ρ` (L3) | `ρ_V` | `mean t / mean t_V` at `r = 8` (L4) |
|---|---|---|---|---|---|---|
| `share1` | −0.1433 | 3.04 | 0.068, 0.066, 0.067 | −1.954 | −1.913 | 1.005 |
| `line4` | −0.7293 | 3.07 | 0.066, 0.068, 0.067 | −1.917 | −1.907 | 1.006 |
| `plaq4` | −0.7753 | 3.09 | 0.066, 0.067, 0.067 | −1.937 | −1.902 | 1.004 |
| `mixed` | +0.0788 | 3.04 | 0.068, 0.066, 0.067 | −1.954 | −1.913 | 1.005 |
| `excl1` | +0.4946 | 3.04 | 0.068, 0.066, 0.067 | −1.954 | −1.913 | 1.005 |
| `excl8` | +1.3887 | 3.09 | 0.067, 0.066, 0.066 | −1.918 | −1.878 | 1.006 |
| `excl27` | +2.3672 | 3.00 | 0.068, 0.066, 0.067 | −1.958 | −1.913 | 1.003 |

| | Verdict | Numbers |
|---|---|---|
| L1 not flat | **PASS** | the local unsigned curvature falls as `r^{−p}`, `p = 3.00 … 3.09` |
| L2 local vacuum | **uninformative** (gate N failed) | `χ = 0.066 … 0.068`, which would pass the `0.10` threshold |
| L3 tidal pattern of a point mass | **PASS** | `ρ = −1.92 … −1.96`; continuum value `−2` |
| L4 local strength is the ways charge | **PASS** | `mean t / mean t_V = 1.003 … 1.006` |

Reported: the radial `Δε` has the sign of `Q` for all seven sources. The mean signed `s` per shell is
below `10⁻⁴` of `mean t` at `r ≥ 8`.

**What this establishes** (numerical evidence on one lattice and box). Outside every source the
census-length geometry is **not flat**: a local curvature remains and falls as `r^{−3}`, the falloff
of a tidal field. Its orientation is that of a point mass: edges pointing at the source and edges
across it respond with opposite signs in the ratio `−1.9 : 1` (continuum `−2 : 1`), and the radial
sign is the sign of `Q`. Its local strength is fixed by the ways charge alone: per unit `Q` it matches
the continuum monopole `Q·(2/π)/r` to under 1% at `r = 8` for all seven sources, whatever their site
set. That is a local Gauss law, and it supports §11's post-hoc reading that D2 failed through the
measure (excluded source edges), not the geometry.

**What it does not.** The registered test cannot separate local vacuum from local cancellation,
because the cancellation control did not reach its threshold. The measure also has a floor that the
prereg did not anticipate: `χ ≈ 0.067` in the continuum-vacuum control too, constant from `r = 4` to
`10` instead of falling like `r^{−2}`. So the vertex-local scalar `s` carries about 7% of the tidal
magnitude at every distance, of both signs. A likely cause, not checked, is that the 14-edge vertex
star of the Freudenthal lattice is not isotropic, so a traceless Hessian leaks into `s`.
*Post hoc, not a decision input:* every local measure of the census matches its own vacuum control V
to 1% (`χ/χ_V` within 1% and `t/t_V` within 2% at `r = 6, 8, 10`), while the ripple N departs from
the same monopole by a factor that grows to 3.5 at `r = 10` (`χ_N = 0.231`, `ρ_N = −0.72`). So the
census field is locally indistinguishable from a discretized vacuum in this triangulation, but that
comparison was chosen after the gate failed.

**Open after 2e.** (0′) A re-registered L2 with a measure that has no anisotropy floor (for example a
least-squares fit of a symmetric tensor to the seven edge types at each vertex, reading its trace) and
a cancellation control sized at every registered radius. (1)–(4) of §11 are unchanged.

## §14 Stage 2e′: re-registered local vacuum test (pre-registration)

Jim, 2026-11-26, on §13's next step: *"do it."* Committed before any 2e′ code exists and before any
2e′ number has been computed. **Disclosed:** this re-registration follows §13, so its author has seen
that the census's `χ` matches its vacuum control to 1% and that the vertex-sum `χ` has a ~7% floor.
The new measure is designed to remove that floor. The census itself, sources, map, `λ`, lattice and
box are unchanged from §12.

### 14.1 Measure: a calibrated tensor fit at each vertex

The Regge response is linear in the field `f` at first order. At a qualifying vertex `x` (§12.1),
let `y_t(x)` be the mean of `Δε/λ` over the two edges of type `t` at `x` (forward and backward), for
the seven edge types. Inverting the lattice through `x` maps the triangulation to itself and swaps
those two edges, so a field that is linear about `x` contributes nothing to `y_t(x)`.

* **Calibration.** For each of the six quadratic fields `f_ij(z) = ½ z_i z_j` (`i ≤ j`, both orders
  summed for `i ≠ j`), compute `y_t` at the origin on the same `ℓ⁰` background. This gives a `7 × 6`
  matrix `C` with `y = C h` for a constant Hessian `h = (H_xx, H_yy, H_zz, H_xy, H_xz, H_yz)`. It
  carries the lattice's anisotropy exactly, which the vertex sum `s` did not.
* **Fit.** At each vertex, `h(x)` is the least-squares solution of `C h = y(x)`.
  `τ(x) = |H_xx + H_yy + H_zz|` is the local trace (the continuum `−R/4` up to `λ`), and
  `η(x) = ‖H‖_F`, the Frobenius norm with off-diagonals counted twice.
* **Index.** `χ′(r) = mean τ / mean η` over shell `r` (§12.1 shells). A harmonic field gives `χ′ → 0`;
  a field whose Laplacian is of the size of its Hessian gives `χ′` of order 1.

### 14.2 Controls

* **V**: §12.2's vacuum control, one per source.
* **N′**: §12.2's ripple with `b = 0.06` instead of `0.005`. At peak its Laplacian `3(π/8)²b ≈ 0.028`
  exceeds the monopole's Hessian norm `√6·(2/π)/r³` at every registered radius (`0.024` at `r = 4`),
  so it is sized for every shell, not one.
* **F**: §12.2's flat control, unchanged.

**Validity gates.** (i) `C` has rank 6 with condition number below `10³`; (ii) every V has
`χ′_V ≤ 0.05` at `r = 6, 8, 10`; (iii) N′ has `χ′_N ≥ 0.30` at `r = 6, 8, 10`; (iv) F gives
`|Δε| < 10⁻⁹`; (v) the fit reproduces the calibration: applied to `f_xx` on a vertex `|x| ≥ 4` from the
origin it returns `H_xx` within `10⁻⁶`. If any gate fails, L2′ is uninformative.

### 14.3 Test

| | Claim | Passes if | Prior |
|---|---|---|---|
| L2′ | local vacuum, not cancellation | for all seven sources, `χ′(r) ≤ 0.05` at `r = 6, 8, 10` | pass |

Reported, not decision inputs: `χ′(r)` for `r = 4 … 10` and its falloff (a discretization residual
should fall about like `r^{−2}`); the least-squares residual `‖C h − y‖ / ‖y‖` per shell; the fitted
eigenvalue ratio of `H` on the axis (continuum `2 : −1 : −1`).

**Reading rule.** L2′ passing: outside every source the census-length geometry has zero local scalar
curvature up to discretization while its tidal Hessian is non-zero (§13 L1, L3), the local vacuum of
linearized Schwarzschild's spatial slice. L2′ failing with the gates passing: the local scalar is
non-zero and cancels only in sums, so §11's D1 plateau and §13's L1–L4 describe a non-vacuum field.
Not claimed either way: the time part, light bending, `λ`, or that the conformal form of the map is
forced.
