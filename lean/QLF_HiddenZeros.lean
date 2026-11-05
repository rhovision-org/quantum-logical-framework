import Mathlib

/-!
# QLF_HiddenZeros — the first hidden-zero benchmark (PZ4)

Issue #207, **PZ4**: *implement the first Figueiredo hidden-zero kinematic benchmark*. This module
states the benchmark exactly, in the planar variables of the `Tr(φ³)` amplitudes where hidden zeros
were found, so that a closure construction has a fixed target to meet. It does **not** derive the
zeros from closures; that is G2c, and issue #207's kill condition is that the zeros must emerge,
not be inserted.

Planar variables `X_{ij}` sit on the diagonals of an `n`-gon (`X = 0` on its sides), and the mesh
variables are `c_{ij} = X_{ij} + X_{i+1,j+1} − X_{i,j+1} − X_{i+1,j}`. A tree amplitude is the sum,
over triangulations, of the product of `1/X` along the chosen diagonals: one term per planar cubic
gluing, the kinematic counterpart of [`QLF_GluonGluing`](QLF_GluonGluing.lean)'s channels.

* **`A4_eq`, `A4_zero`.** `A₄ = 1/X₁₃ + 1/X₂₄ = c₁₃ / (X₁₃ X₂₄)`: it vanishes on `c₁₃ = 0`, a zero
  of the sum of two channels that neither channel has.
* **`A5_zero`.** `A₅`, the sum over the five triangulations of the pentagon, vanishes when
  `c₁₃ = c₁₄ = 0`, at generic `X`.
* **`A5_near_zero`.** On `c₁₃ = 0` alone, `A₅ = c₁₄ · (1/X₂₄ + 1/X₃₅) / (X₁₃ X₂₅)`: the zero is simple
  in the remaining mesh variable, and its coefficient carries the four-point amplitude of the
  quadrilateral `(2, 3, 4, 5)`, a factorization away from any pole.

No axioms.

**Credit.** Arkani-Hamed, Cao, Dong, Figueiredo and He, *Hidden zeros for particle/string
amplitudes and the unity of colored scalars, pions and gluons* (arXiv:2312.16282, *JHEP* **10**
(2024) 231); the planar and mesh variables are those of the `Tr(φ³)` / associahedron literature
(Arkani-Hamed, Bai, He and Yan, *JHEP* **05** (2018) 096). Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.HiddenZeros

variable {K : Type*} [Field K]

/-- The four-point amplitude: two planar channels. -/
def A4 (X13 X24 : K) : K := 1 / X13 + 1 / X24

/-- **Two channels sum to the mesh variable over both poles.** -/
theorem A4_eq (X13 X24 : K) (h13 : X13 ≠ 0) (h24 : X24 ≠ 0) :
    A4 X13 X24 = (X13 + X24) / (X13 * X24) := by
  unfold A4; field_simp; ring

/-- **The four-point hidden zero**: `c₁₃ = X₁₃ + X₂₄ = 0` kills the amplitude. -/
theorem A4_zero (X13 X24 : K) (hc : X13 + X24 = 0) : A4 X13 X24 = 0 := by
  have : X24 = -X13 := by linear_combination hc
  simp [A4, this]

/-- The five-point amplitude: the five triangulations of the pentagon. -/
def A5 (X13 X14 X24 X25 X35 : K) : K :=
  1 / (X13 * X14) + 1 / (X24 * X25) + 1 / (X13 * X35) + 1 / (X14 * X24) + 1 / (X25 * X35)

/-- Mesh variables `c₁₃ = X₁₃ + X₂₄ − X₁₄` and `c₁₄ = X₁₄ + X₂₅ − X₂₄` (sides are zero). -/
def c13 (X13 X14 X24 : K) : K := X13 + X24 - X14
def c14 (X14 X24 X25 : K) : K := X14 + X25 - X24

/-- **The five-point hidden zero**: `c₁₃ = c₁₄ = 0` kills the amplitude. -/
theorem A5_zero (X13 X14 X24 X25 X35 : K) (h13 : X13 ≠ 0) (h14 : X14 ≠ 0) (h24 : X24 ≠ 0)
    (hc13 : c13 X13 X14 X24 = 0) (hc14 : c14 X14 X24 X25 = 0) :
    A5 X13 X14 X24 X25 X35 = 0 := by
  unfold c13 at hc13; unfold c14 at hc14
  have e24 : X24 = X14 - X13 := by linear_combination hc13
  have e25 : X25 = -X13 := by linear_combination hc14 + hc13
  unfold A5
  rw [e25]
  have hpair : 1 / (X13 * X35) + 1 / (-X13 * X35) = 0 := by
    rw [neg_mul, one_div_neg_eq_neg_one_div]; ring
  have htri : 1 / (X13 * X14) + 1 / (X24 * -X13) + 1 / (X14 * X24) = 0 := by
    field_simp
    rw [e24]; ring
  linear_combination hpair + htri

/-- **Near the zero the amplitude factors**: on `c₁₃ = 0`,
    `A₅ = c₁₄ · A₄(X₂₄, X₃₅) / (X₁₃ X₂₅)`. -/
theorem A5_near_zero (X13 X14 X24 X25 X35 : K) (h13 : X13 ≠ 0) (h14 : X14 ≠ 0) (h24 : X24 ≠ 0)
    (h25 : X25 ≠ 0) (h35 : X35 ≠ 0) (hc13 : c13 X13 X14 X24 = 0) :
    A5 X13 X14 X24 X25 X35 = c14 X14 X24 X25 * A4 X24 X35 / (X13 * X25) := by
  unfold c13 at hc13
  have e14 : X14 = X13 + X24 := by linear_combination -hc13
  unfold A5 c14 A4
  rw [e14]
  have h' : X13 + X24 ≠ 0 := e14 ▸ h14
  field_simp
  ring

end QLF.HiddenZeros
