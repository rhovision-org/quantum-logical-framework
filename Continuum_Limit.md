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
