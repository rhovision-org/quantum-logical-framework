import QLF_Tsirelson

set_option linter.unusedVariables false

/-!
# QLF_Mass — **mass is what flips handedness**

Continues [`QLF_RealizableWalk`](QLF_RealizableWalk.lean) and [`QLF_Tsirelson`](QLF_Tsirelson.lean)
(issue #207). See [`Closure_Unitarity.md`](../Closure_Unitarity.md) §14.

The realizable walk of `QLF_RealizableWalk` renders a massless (Weyl) particle: its generator is
momentum along the three spatial twists, and

> **`weyl_sq`** — `(k_y·up + k_x·left + k_z·slash)² = |k|²`, i.e. `E² = p²`.

**No mass fits on two components.** A mass term must anticommute with all three momentum
directions, and

> **`no_weyl_mass`** — a 2×2 matrix anticommuting with all three spatial twists is zero.

The three spatial twists exhaust the 2×2 Clifford algebra. So a mass needs a second factor. Take
it to be **handedness** (the primitive of [`QLF_Handedness`](QLF_Handedness.lean)): spin ⊗
handedness, four components. With twists on both factors,

* `alpha t = slash ⊗ t` — momentum along twist `t`, labelled by handedness;
* `beta = right ⊗ 1` — the mass generator;
* `chirality = slash ⊗ 1` — the handedness label.

> **`dirac_sq`** — `(k_y α_y + k_x α_x + k_z α_z + m β)² = (k² + m²)`, i.e. `E² = p² + m²`,
> exactly, from the Clifford relations of the twists (`cliff4_sq`).

> **`chirality_comm_dirac`** — `[chirality, D] = 2m · chirality · β`: momentum keeps handedness and
> mass flips it, so **`massless_keeps_handedness`** holds exactly when `m = 0`.

> **`massStep_unitary`** — the mass step `cos m + i sin m · β` is unitary for every real `m`.

This is the chiral (Weyl) representation of the Dirac algebra, standard physics; the reading is
QLF's: a massive particle is one whose history keeps switching handedness (Feynman's checkerboard,
in Feynman and Hibbs 1965), and the rate of switching is the mass. No continuum. No axioms.
-/

namespace QLF.Mass

open Matrix Kronecker
open QLF.ClosureChannels

section Clifford

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **Clifford square, three generators.** Involutions that pairwise anticommute square any
linear combination to the sum of squares of its coefficients. -/
theorem cliff3_sq {e1 e2 e3 : A} (s1 : e1 * e1 = 1) (s2 : e2 * e2 = 1) (s3 : e3 * e3 = 1)
    (a12 : e2 * e1 = -(e1 * e2)) (a13 : e3 * e1 = -(e1 * e3)) (a23 : e3 * e2 = -(e2 * e3))
    (a b c : ℂ) :
    (a • e1 + b • e2 + c • e3) * (a • e1 + b • e2 + c • e3) = (a ^ 2 + b ^ 2 + c ^ 2) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, s1, s2, s3, a12, a13, a23,
    smul_neg]
  module

/-- **Clifford square, four generators.** -/
theorem cliff4_sq {e1 e2 e3 e4 : A} (s1 : e1 * e1 = 1) (s2 : e2 * e2 = 1) (s3 : e3 * e3 = 1)
    (s4 : e4 * e4 = 1)
    (a12 : e2 * e1 = -(e1 * e2)) (a13 : e3 * e1 = -(e1 * e3)) (a23 : e3 * e2 = -(e2 * e3))
    (a14 : e4 * e1 = -(e1 * e4)) (a24 : e4 * e2 = -(e2 * e4)) (a34 : e4 * e3 = -(e3 * e4))
    (a b c d : ℂ) :
    (a • e1 + b • e2 + c • e3 + d • e4) * (a • e1 + b • e2 + c • e3 + d • e4) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, s1, s2, s3, s4, a12, a13,
    a23, a14, a24, a34, smul_neg]
  module

end Clifford

/-! ## The Weyl sector: two components, no mass -/

abbrev M := Matrix (Fin 2) (Fin 2) ℂ

theorem anti_of {t s : Twist} (h : anti t s = true) : t.toMatrix * s.toMatrix =
    -(s.toMatrix * t.toMatrix) := by
  rw [twist_mul_comm, h]; simp

theorem up_left : Twist.left.toMatrix * Twist.up.toMatrix = -(Twist.up.toMatrix * Twist.left.toMatrix) :=
  anti_of (by decide)
theorem up_slash : Twist.slash.toMatrix * Twist.up.toMatrix =
    -(Twist.up.toMatrix * Twist.slash.toMatrix) := anti_of (by decide)
theorem left_slash : Twist.slash.toMatrix * Twist.left.toMatrix =
    -(Twist.left.toMatrix * Twist.slash.toMatrix) := anti_of (by decide)
theorem right_slash : Twist.slash.toMatrix * Twist.right.toMatrix =
    -(Twist.right.toMatrix * Twist.slash.toMatrix) := anti_of (by decide)

/-- The massless (Weyl) generator: momentum along the three spatial twists. -/
noncomputable def weyl (ky kx kz : ℂ) : M :=
  ky • Twist.up.toMatrix + kx • Twist.left.toMatrix + kz • Twist.slash.toMatrix

/-- **`E² = p²`** for the two-component walk generator. -/
theorem weyl_sq (ky kx kz : ℂ) : weyl ky kx kz * weyl ky kx kz = (ky ^ 2 + kx ^ 2 + kz ^ 2) • (1 : M) :=
  cliff3_sq (ClosureUnitarity.twist_sq _) (ClosureUnitarity.twist_sq _)
    (ClosureUnitarity.twist_sq _) up_left up_slash left_slash ky kx kz

/-- **No mass term fits on two components.** A matrix that anticommutes with all three spatial
twists is zero: the three twists exhaust the 2×2 Clifford algebra. -/
theorem no_weyl_mass (X : M)
    (hy : X * Twist.up.toMatrix = -(Twist.up.toMatrix * X))
    (hx : X * Twist.left.toMatrix = -(Twist.left.toMatrix * X))
    (hz : X * Twist.slash.toMatrix = -(Twist.slash.toMatrix * X)) : X = 0 := by
  have z00 := congrFun (congrFun hz 0) 0
  have z11 := congrFun (congrFun hz 1) 1
  have x00 := congrFun (congrFun hx 0) 0
  have y00 := congrFun (congrFun hy 0) 0
  simp [Twist.toMatrix, σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
    dotProduct] at z00 z11 x00 y00
  ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.zero_apply]
  · linear_combination z00 / 2
  · linear_combination (-Complex.I / 2) * (y00 - Complex.I * x00) + X 0 1 * Complex.I_sq
  · linear_combination -x00 + (Complex.I / 2) * (y00 - Complex.I * x00) - X 0 1 * Complex.I_sq
  · linear_combination -z11 / 2

/-! ## The Dirac sector: spin ⊗ handedness -/

open QLF.Tsirelson (Q)

theorem kron_neg_left (X Y : M) : (-X) ⊗ₖ Y = -(X ⊗ₖ Y) := by
  ext ⟨i, j⟩ ⟨k, l⟩; simp [kroneckerMap_apply]

theorem kron_neg_right (X Y : M) : X ⊗ₖ (-Y) = -(X ⊗ₖ Y) := by
  ext ⟨i, j⟩ ⟨k, l⟩; simp [kroneckerMap_apply]

/-- Momentum generator along twist `t`: handedness `σ_z` on the first factor, `t` on the spin. -/
noncomputable def alpha (t : Twist) : Q := Twist.slash.toMatrix ⊗ₖ t.toMatrix
/-- The mass generator: it flips handedness and leaves the spin alone. -/
noncomputable def beta : Q := Twist.right.toMatrix ⊗ₖ (1 : M)
/-- The handedness (chirality) label. -/
noncomputable def chirality : Q := Twist.slash.toMatrix ⊗ₖ (1 : M)

theorem alpha_sq (t : Twist) : alpha t * alpha t = 1 := by
  rw [alpha, ← mul_kronecker_mul, ClosureUnitarity.twist_sq, ClosureUnitarity.twist_sq,
    one_kronecker_one]

theorem beta_sq : beta * beta = 1 := by
  rw [beta, ← mul_kronecker_mul, ClosureUnitarity.twist_sq, one_mul, one_kronecker_one]

theorem alpha_anti {t s : Twist} (h : s.toMatrix * t.toMatrix = -(t.toMatrix * s.toMatrix)) :
    alpha s * alpha t = -(alpha t * alpha s) := by
  rw [alpha, alpha, ← mul_kronecker_mul, ← mul_kronecker_mul, h, kron_neg_right]

theorem beta_alpha (t : Twist) : beta * alpha t = -(alpha t * beta) := by
  rw [alpha, beta, ← mul_kronecker_mul, ← mul_kronecker_mul, right_slash, kron_neg_left, neg_neg,
    one_mul, mul_one]

/-- The Dirac generator: momentum along the three spatial twists plus a mass. -/
noncomputable def dirac (ky kx kz m : ℂ) : Q :=
  ky • alpha Twist.up + kx • alpha Twist.left + kz • alpha Twist.slash + m • beta

/-- **`E² = p² + m²`**, exactly, from the Clifford relations of the twists. -/
theorem dirac_sq (ky kx kz m : ℂ) :
    dirac ky kx kz m * dirac ky kx kz m = (ky ^ 2 + kx ^ 2 + kz ^ 2 + m ^ 2) • (1 : Q) :=
  cliff4_sq (alpha_sq _) (alpha_sq _) (alpha_sq _) beta_sq (alpha_anti up_left)
    (alpha_anti up_slash) (alpha_anti left_slash) (beta_alpha _) (beta_alpha _) (beta_alpha _)
    ky kx kz m

theorem chirality_alpha (t : Twist) : chirality * alpha t = alpha t * chirality := by
  rw [alpha, chirality, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one]

theorem chirality_beta : chirality * beta = -(beta * chirality) := by
  rw [beta, chirality, ← mul_kronecker_mul, ← mul_kronecker_mul, right_slash, kron_neg_left,
    one_mul]

/-- **Mass is what flips handedness.** The commutator of the handedness label with the Dirac
generator is exactly the mass term (times `2 · chirality`): momentum keeps handedness, mass does not. -/
theorem chirality_comm_dirac (ky kx kz m : ℂ) :
    chirality * dirac ky kx kz m - dirac ky kx kz m * chirality = (2 * m) • (chirality * beta) := by
  have hb : beta * chirality = -(chirality * beta) := by rw [chirality_beta, neg_neg]
  simp only [dirac, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, chirality_alpha, hb, smul_neg]
  module

/-- So the walk generator keeps handedness exactly when it is massless. -/
theorem massless_keeps_handedness (ky kx kz : ℂ) :
    chirality * dirac ky kx kz 0 = dirac ky kx kz 0 * chirality := by
  have := chirality_comm_dirac ky kx kz 0
  rw [mul_zero, zero_smul, sub_eq_zero] at this
  exact this

theorem beta_herm : betaᴴ = beta := by
  rw [beta, conjTranspose_kronecker, ClosureUnitarity.twist_herm, conjTranspose_one]

/-- A mass coin `c + i s · β` with real `c, s`. -/
noncomputable def coin (c s : ℝ) : Q := (c : ℂ) • (1 : Q) + (Complex.I * (s : ℂ)) • beta

theorem coin_unitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    coin c s ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star (coin c s) = (c : ℂ) • (1 : Q) - (Complex.I * (s : ℂ)) • beta := by
    rw [coin, star_add, star_smul, star_smul, star_one]
    change _ + _ • betaᴴ = _
    rw [beta_herm]
    simp [sub_eq_add_neg]
  rw [hs, coin]
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, beta_sq]
  have h1 : (c : ℂ) * (c : ℂ) - (Complex.I * (s : ℂ)) * (Complex.I * (s : ℂ)) = 1 := by
    have hc : ((c ^ 2 + s ^ 2 : ℝ) : ℂ) = 1 := by rw [h]; simp
    push_cast at hc
    linear_combination hc - (s : ℂ) ^ 2 * Complex.I_sq
  calc _ = ((c : ℂ) * (c : ℂ) - (Complex.I * (s : ℂ)) * (Complex.I * (s : ℂ))) • (1 : Q) := by
        module
    _ = 1 := by rw [h1, one_smul]

/-- The mass step `cos m + i sin m · β`. -/
noncomputable def massStep (m : ℝ) : Q := coin (Real.cos m) (Real.sin m)

/-- **The mass step is unitary** for every real mass. -/
theorem massStep_unitary (m : ℝ) : massStep m ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  coin_unitary _ _ (Real.cos_sq_add_sin_sq m)

end QLF.Mass
