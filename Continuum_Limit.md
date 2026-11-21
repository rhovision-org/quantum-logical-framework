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

To be filled from `fluxoid_regge.py` after this section is committed.
