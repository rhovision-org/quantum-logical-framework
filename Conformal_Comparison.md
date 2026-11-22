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

Run by [`conformal_comparison.py`](conformal_comparison.py) (`--max-len 6`); output in
[`data/conformal_comparison.json`](data/conformal_comparison.json). The dilation facts are proved in
[`lean/QLF_ConformalComparison.lean`](lean/QLF_ConformalComparison.lean), no axioms.

| | Result | Verdict |
|---|---|---|
| W1 | `k = 1, 3, 5`: 0 ZFA failures, 0 fold failures; folds on balanced histories are `±I` | **pass** (`fold_dilate_odd`, `dilate_balanced`) |
| W2 | `k = 2, 4`: 0 ZFA failures; every balanced history folds to `+I`, so 3,664 of 5,296 folds change | **pass** (`fold_dilate_even`) |
| W3 | fields `k_p ∈ {1,2,3}`: 3 of 9, 3 of 81 and 3 of 729 preserve ZFA at `L = 2, 4, 6`, all constant | **pass** (`local_dilation_breaks_balance` is the smallest witness) |
| W4 | at every position pair of a length-4 history, 1 of 147,456 frame pairs preserves ZFA: `σ_i = σ_j = id` | see below |
| W5 | 96 of the 384 global frames preserve the fold; all 96 fix the gauge axis | **pass**, the 96 of `QLF_MultiObserver` |

**W4.** The pre-registered pass condition, "exactly the pairs with `σ_i = σ_j`", was mis-posed. The
other two positions were held at the identity, so a pair `σ_i = σ_j = τ` with `τ ≠ id` is itself a
non-constant field on the whole history, and it fails. The measured survivors are a single pair, the
identity, which is the only constant field in the family tested. The literal condition is not met.
The measured result is stronger than the one it stood for: no frame field that differs anywhere from
its background preserves ZFA, so there is no local frame change in this class.

**Verdict.** W1, W2, W3 and W5 pass as stated, and W4 gives the stronger result above. ZFA admits no
local scale or frame symmetry among position-dependent letter substitutions. Its symmetry is global:
the 96 frames times the odd dilations, with even dilations preserving ZFA but erasing the phase. This
is outcome 2 of #302 C1, and it meets the issue's failure criterion. The intrinsic Weyl² → Bach →
Mannheim–Kazanas route has no first step in this class. Conformal gravity can still be compared with
QLF's Einstein limit as an external continuum candidate, which the issue's later tests allow. A local symmetry built from closure-respecting rewrites that are not
letter substitutions is not excluded.
