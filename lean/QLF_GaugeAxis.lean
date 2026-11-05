import QLF_DiracWalk

/-!
# QLF_GaugeAxis — the gauge axis is the clock, and closure puts the walk on the mass shell

Issue #207. The realizable walks of [`QLF_RealizableWalk`](QLF_RealizableWalk.lean) and
[`QLF_DiracWalk`](QLF_DiracWalk.lean) used the three spatial axes and left the fourth, gauge, axis
out. This module puts it back.

* **`fix_plus`, `fix_minus`.** The gauge twists `+` and `−` map to `1` and `−1`, so the realizable part
  of `+` is everything and of `−` is nothing. A gauge step has no spin direction to choose.
* **`gaugeStep_eq`.** The realizable gauge step is a pure phase, `e^{iω}·1`, and it commutes with
  every step (`gaugeStep_central`). It is the tick of a clock: it advances every state alike.
* **`tick`, `spacetimeWalk`.** Adding the tick to the Dirac walk gives a 3+1 walk, unitary at every
  momentum, mass and frequency (`spacetimeWalk_unitary`), whose generator is `i(ω + k·α + mβ)`
  (`spacetimeWalk_generator`).
* **`mass_shell`.** A state the generator annihilates, a zero of `ω + k·α + mβ`, has
  `ω² = k² + m²`. So the states whose tick exactly cancels their spatial phase, which is zero free
  action per step, lie on the mass shell. With no mass, **`light_cone`** gives `ω² = k²` on two
  components.

The mass shell is not put in: it comes from the Clifford square `dirac_sq` and nothing else. No
axioms, and no continuum beyond the derivative in the momentum label that reads off a generator.
-/

namespace QLF.GaugeAxis

open Matrix Kronecker
open QLF.ClosureChannels

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev Q := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The realizable part of `+` is the whole space. -/
theorem fix_plus : fix Twist.plus = 1 := by
  unfold fix
  rw [show Twist.plus.toMatrix = (1 : M) from rfl]
  rw [← two_smul ℂ (1 : M), smul_smul]
  norm_num

/-- The realizable part of `−` is nothing. -/
theorem fix_minus : fix Twist.minus = 0 := by
  unfold fix
  rw [show Twist.minus.toMatrix = (-1 : M) from rfl, add_neg_cancel, smul_zero]

/-- **The gauge step is a pure phase**: a clock tick that moves every state alike. -/
theorem gaugeStep_eq (w : ℝ) : realStep Twist.plus w = Complex.exp (w * Complex.I) • (1 : M) := by
  unfold realStep
  rw [show Twist.plus.conj = Twist.minus from rfl, fix_plus, fix_minus, smul_zero, add_zero]

/-- The gauge step commutes with every step. -/
theorem gaugeStep_central (w : ℝ) (X : M) : realStep Twist.plus w * X = X * realStep Twist.plus w := by
  rw [gaugeStep_eq, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- The tick on the spin ⊗ handedness space. -/
noncomputable def tick (w : ℝ) : Q := Complex.exp (w * Complex.I) • (1 : Q)

theorem tick_unitary (w : ℝ) : tick w ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, tick, star_smul, star_one, smul_mul_smul_comm, one_mul]
  rw [show star (Complex.exp (w * Complex.I)) = Complex.exp (-(w * Complex.I)) from
    QLF.ClosureChannels.star_exp_kI w]
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

/-- The 3+1 walk: a tick at frequency `ω` after a Dirac step. -/
noncomputable def spacetimeWalk (w ky kx kz m : ℝ) : Q :=
  tick w * DiracWalk.diracWalk ky kx kz m

/-- **The 3+1 walk is unitary** at every frequency, momentum and mass. -/
theorem spacetimeWalk_unitary (w ky kx kz m : ℝ) :
    spacetimeWalk w ky kx kz m ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  Submonoid.mul_mem _ (tick_unitary w) (DiracWalk.diracWalk_unitary _ _ _ _)

/-- **The generator of the 3+1 walk** is `i(ω + k·α + mβ)`. -/
theorem spacetimeWalk_generator (w ay ax az m : ℝ) :
    HasDerivAt (fun s : ℝ => spacetimeWalk (s * w) (s * ay) (s * ax) (s * az) (s * m))
      (Complex.I • ((w : ℂ) • (1 : Q) + Mass.dirac ay ax az m)) 0 := by
  have hp := DiracWalk.hasDerivAt_phase w
  have hd := DiracWalk.diracWalk_generator ay ax az m
  have h := hp.smul hd
  have e : (fun s : ℝ => spacetimeWalk (s * w) (s * ay) (s * ax) (s * az) (s * m)) =
      (fun s : ℝ => Complex.exp (((s * w : ℝ) : ℂ) * Complex.I) •
        DiracWalk.diracWalk (s * ay) (s * ax) (s * az) (s * m)) := by
    funext s
    simp only [spacetimeWalk, tick, smul_mul_assoc, one_mul]
  rw [e]
  refine h.congr_deriv ?_
  have h0 : DiracWalk.diracWalk (0 * ay) (0 * ax) (0 * az) (0 * m) = 1 := by
    simp only [zero_mul, DiracWalk.diracWalk, DiracWalk.massStep_zero, DiracWalk.handed_zero,
      one_mul]
  rw [h0]
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_smul]
  rw [smul_add, smul_smul, mul_comm, add_comm]

/-- **Closure lies on the mass shell.** A non-zero state annihilated by `ω + k·α + mβ` has
    `ω² = k² + m²`. -/
theorem mass_shell (w ky kx kz m : ℂ) (ψ : Fin 2 × Fin 2 → ℂ) (hψ : ψ ≠ 0)
    (h : (w • (1 : Q) + Mass.dirac ky kx kz m) *ᵥ ψ = 0) :
    w ^ 2 = ky ^ 2 + kx ^ 2 + kz ^ 2 + m ^ 2 := by
  set D := Mass.dirac ky kx kz m
  have hD : D *ᵥ ψ = -w • ψ := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have h2 : (D * D) *ᵥ ψ = (w ^ 2) • ψ := by
    rw [← Matrix.mulVec_mulVec, hD, Matrix.mulVec_smul, hD, smul_smul]
    congr 1; ring
  rw [Mass.dirac_sq, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  have h3 : ((ky ^ 2 + kx ^ 2 + kz ^ 2 + m ^ 2) - w ^ 2) • ψ = 0 := by
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact (sub_eq_zero.mp h4).symm
  · exact absurd h4 hψ

/-- **Massless closure lies on the light cone.** On two components, a non-zero state annihilated by
    `ω + k·σ` has `ω² = k²`. -/
theorem light_cone (w ky kx kz : ℂ) (ψ : Fin 2 → ℂ) (hψ : ψ ≠ 0)
    (h : (w • (1 : M) + Mass.weyl ky kx kz) *ᵥ ψ = 0) :
    w ^ 2 = ky ^ 2 + kx ^ 2 + kz ^ 2 := by
  set D := Mass.weyl ky kx kz
  have hD : D *ᵥ ψ = -w • ψ := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have h2 : (D * D) *ᵥ ψ = (w ^ 2) • ψ := by
    rw [← Matrix.mulVec_mulVec, hD, Matrix.mulVec_smul, hD, smul_smul]
    congr 1; ring
  rw [Mass.weyl_sq, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  have h3 : ((ky ^ 2 + kx ^ 2 + kz ^ 2) - w ^ 2) • ψ = 0 := by
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact (sub_eq_zero.mp h4).symm
  · exact absurd h4 hψ

end QLF.GaugeAxis
