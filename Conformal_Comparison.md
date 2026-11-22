# Conformal Comparison: does ZFA have a local scale symmetry? (#302, C1)

Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF. Issue #302 asks whether
conformal (Weyl) gravity is an alternative to QLF's Einstein limit, an approximation of it, or an
emergent sector. Its first milestone is **C1**: prove or disprove a nontrivial *local* conformal
transformation induced by ZFA. If none exists, the issue says the intrinsic Weyl² → Bach →
Mannheim–Kazanas route has no justification. This note runs C1 on a stated finite class.

## §1 Pre-registration (committed before the companion script was run)

### The class of transformations

A **position-dependent letter substitution** acts on a twist history `h = t₀ t₁ … t_{L−1}` letter by
letter. Position `p` carries a frame `σ_p`, one of the 384 signed permutations of the four axes
(gauge included), and an odd or even multiplicity `k_p ≥ 1`. Letter `t_p` is replaced by
`σ_p(t_p)` repeated `k_p` times.

* **Global** means `σ_p` and `k_p` do not depend on `p`.
* A constant `k` is a **dilation** of the walk, `x ↦ k x`. It is a global scale transformation (item
  2 of #302's list), not a local one.
* A position-dependent `k_p` is the discrete analogue of a local Weyl rescaling (item 4), and a
  position-dependent `σ_p` is a local frame change.

### What must be preserved

The ZFA verdict (count balance) on every history, and the Pauli fold on every balanced history.

### Tests

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| W1 | odd dilations are symmetries | `k` odd and constant preserves ZFA and the fold on every history of length `≤ 6` | pass: every twist matrix squares to `I`, so `t^k` folds like `t` for odd `k` |
| W2 | even dilations | `k` even and constant preserves ZFA, and every balanced history then folds to `+I` | pass: the phase is erased, so even dilation is not a symmetry of the fold |
| W3 | local rescaling | among all fields `k_p ∈ {1, 2, 3}` on `L ≤ 6`, those preserving ZFA on every balanced history of length `L` are exactly the constant ones | pass, so **no local rescaling** |
| W4 | local frames | among all pairs `(σ_i, σ_j)` at two positions of a length-4 history, those preserving ZFA on every balanced history are exactly `σ_i = σ_j` | pass, so **no local frame change** |
| W5 | the global frames | count the constant `σ` that preserve the fold on every balanced history of length `≤ 6` | the 96 frames of [`lean/QLF_MultiObserver.lean`](lean/QLF_MultiObserver.lean) (48 signed spatial permutations × the gauge swap) |

**Verdict rule.** If W3 and W4 pass, ZFA admits no local scale or frame symmetry in this class. Its
symmetry is then global: the frames of W5 times the odd dilations of W1. This is outcome 2
("a global scale transformation") of #302 C1, and it meets the issue's failure criterion for C1,
which asks for more than unit or global invariance. The intrinsic Weyl route would then lack its
first step. That is a statement about this class. A local symmetry built from other primitives,
such as closure-respecting rewrites that are not letter substitutions, is not excluded.

**Recorded beforehand.** The odd dilation is consistent with
[`lean/QLF_PhaseAction.lean`](lean/QLF_PhaseAction.lean): the phase `π(L/2 + Φ)` sends `L ↦ kL` and
`Φ ↦ k²Φ`, and both parities are unchanged for odd `k`.

## §2 Results

To be filled from `conformal_comparison.py` after this section is committed.
