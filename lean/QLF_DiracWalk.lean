import QLF_Mass
import QLF_RealizableWalk

set_option linter.unusedVariables false

/-!
# QLF_DiracWalk — **the walks' generators are the Weyl and Dirac operators**

Continues [`QLF_RealizableWalk`](QLF_RealizableWalk.lean) and [`QLF_Mass`](QLF_Mass.lean)
(issue #207). See [`Closure_Unitarity.md`](../Closure_Unitarity.md) §15.

A unitary walk step `W(k)` at momentum `k` has a **generator**: its derivative at `k = 0`, so that
for small momenta `W(k) ≈ 1 + i·H(k)`. Here the generators are computed exactly.

> **`realStep_generator`** — a realizable step along twist `t` has generator `i·a·M(t)`: its twist.
> **`realWalk_generator`** — the three-axis realizable walk has generator `i·(a_y up + a_x left +
> a_z slash)`, the Weyl operator `Mass.weyl`, whose square is `|a|²` (`Mass.weyl_sq`).

Assembling the Dirac walk from pieces already proved unitary:

* `handed k = fix slash ⊗ W(k) + fix slash̄ ⊗ W(−k)` — the right-handed part walks at `k`, the
  left-handed at `−k` (**`handed_unitary`**);
* `diracWalk k m = massStep m · handed k` (**`diracWalk_unitary`**).

> **`diracWalk_generator`** — along any direction in momentum and mass, the Dirac walk's generator is
> `i·(a_y α_y + a_x α_x + a_z α_z + m β)`, the Dirac operator `Mass.dirac`, whose square is
> `a² + m²` (`Mass.dirac_sq`).

So the walks are unitary at every step, and what they generate is exactly the Weyl and Dirac
operators. A derivative in the momentum label is the one continuum notion used; it reads off the
finite step's generator and assumes nothing about space. Prior art: Bialynicki-Birula (1994),
Arrighi, Nesme and Forets (2014), D'Ariano and Perinotti (2014), Feynman's checkerboard. No axioms.
-/

namespace QLF.DiracWalk

open Matrix Kronecker
open QLF.ClosureChannels

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

abbrev M := Matrix (Fin 2) (Fin 2) ℂ

theorem hasDerivAt_phase (a : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (((s * a : ℝ) : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => ((s * a : ℝ) : ℂ) * Complex.I) ((a : ℂ) * Complex.I) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp.mul_const Complex.I
    simpa using this
  simpa using h1.cexp

theorem fix_sub_conj (t : Twist) : fix t - fix t.conj = t.toMatrix := by
  unfold fix; rw [ClosureUnitarity.conj_toMatrix]; module

theorem realStep_zero (t : Twist) : realStep t 0 = 1 := by
  simp [realStep, fix_add_conj]

/-- **The generator of a realizable step is its twist.** -/
theorem realStep_generator (t : Twist) (a : ℝ) :
    HasDerivAt (fun s : ℝ => realStep t (s * a)) (((a : ℂ) * Complex.I) • t.toMatrix) 0 := by
  have h1 := (hasDerivAt_phase a).smul_const (fix t)
  have h2 := (hasDerivAt_phase (-a)).smul_const (fix t.conj)
  have e : (fun s : ℝ => realStep t (s * a)) =
      (fun y : ℝ => Complex.exp (((y * a : ℝ) : ℂ) * Complex.I) • fix t) +
      (fun y : ℝ => Complex.exp (((y * -a : ℝ) : ℂ) * Complex.I) • fix t.conj) := by
    funext s; simp [realStep, mul_neg]
  rw [e]
  refine (h1.add h2).congr_deriv ?_
  rw [← fix_sub_conj]; push_cast
  simp only [neg_mul, neg_smul, sub_eq_add_neg, smul_add, smul_neg]

/-- **The generator of the realizable walk is the Weyl operator.** Along any momentum direction
`(a_y, a_x, a_z)`, the walk's derivative at zero momentum is `i·(a_y up + a_x left + a_z slash)`,
the massless Weyl generator of [`QLF_Mass`](QLF_Mass.lean). -/
theorem realWalk_generator (ay ax az : ℝ) :
    HasDerivAt (fun s : ℝ => realWalk (s * ay) (s * ax) (s * az))
      (Complex.I • Mass.weyl ay ax az) 0 := by
  have hy := realStep_generator Twist.up ay
  have hx := realStep_generator Twist.left ax
  have hz := realStep_generator Twist.slash az
  have e : (fun s : ℝ => realWalk (s * ay) (s * ax) (s * az)) =
      (fun s : ℝ => realStep Twist.up (s * ay)) * (fun s : ℝ => realStep Twist.left (s * ax)) *
        (fun s : ℝ => realStep Twist.slash (s * az)) := by
    funext s; simp [realWalk]
  rw [e]
  refine ((hy.mul hx).mul hz).congr_deriv ?_
  simp only [Pi.mul_apply, zero_mul, realStep_zero, one_mul, mul_one, Mass.weyl, smul_add,
    smul_smul]
  ring_nf

/-! ## The Dirac walk -/

open QLF.Tsirelson (Q)

/-- `Y ↦ X ⊗ Y` as a real-linear map. -/
noncomputable def kronL (X : M) : M →ₗ[ℝ] Q where
  toFun Y := X ⊗ₖ Y
  map_add' Y Z := kronecker_add _ _ _
  map_smul' r Y := by ext ⟨i, j⟩ ⟨k, l⟩; simp [kroneckerMap_apply]; ring

theorem kron_hasDerivAt (X : M) {f : ℝ → M} {f' : M} (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun s => X ⊗ₖ f s) (X ⊗ₖ f') 0 := by
  have := (LinearMap.toContinuousLinearMap (kronL X)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf
  exact this

/-- The handedness-labelled walk: the right-handed part walks at `k`, the left-handed at `−k`. -/
noncomputable def handed (ky kx kz : ℝ) : Q :=
  fix Twist.slash ⊗ₖ realWalk ky kx kz + fix Twist.slash.conj ⊗ₖ realWalk (-ky) (-kx) (-kz)

theorem handed_zero : handed 0 0 0 = 1 := by
  rw [handed, neg_zero, realWalk_zero, ← add_kronecker, fix_add_conj, one_kronecker_one]

theorem unitary_star_mul {U : M} (h : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : U * star U = 1 :=
  Matrix.mem_unitaryGroup_iff.mp h

/-- **The handedness-labelled walk is unitary.** -/
theorem handed_unitary (ky kx kz : ℝ) : handed ky kx kz ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, handed, star_add, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_kronecker, fix_herm,
    fix_herm, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]
  simp only [add_mul, mul_add, ← mul_kronecker_mul, fix_idem, fix_mul_conj, fix_conj_mul,
    zero_kronecker, add_zero, zero_add, unitary_star_mul (realWalk_unitary _ _ _)]
  rw [← add_kronecker, fix_add_conj, one_kronecker_one]

/-- **The Dirac walk:** a mass step after the handedness-labelled walk. -/
noncomputable def diracWalk (ky kx kz m : ℝ) : Q := Mass.massStep m * handed ky kx kz

/-- **The Dirac walk is unitary** at every momentum and mass. -/
theorem diracWalk_unitary (ky kx kz m : ℝ) :
    diracWalk ky kx kz m ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  Submonoid.mul_mem _ (Mass.massStep_unitary m) (handed_unitary _ _ _)

theorem massStep_zero : Mass.massStep 0 = 1 := by
  simp [Mass.massStep, Mass.coin]

/-- The mass step's generator is `i m β`. -/
theorem massStep_generator (m : ℝ) :
    HasDerivAt (fun s : ℝ => Mass.massStep (s * m)) (((m : ℂ) * Complex.I) • Mass.beta) 0 := by
  have hc := (((hasDerivAt_id (0 : ℝ)).mul_const m).cos.ofReal_comp).smul_const (1 : Q)
  have hs := ((((hasDerivAt_id (0 : ℝ)).mul_const m).sin.ofReal_comp).const_mul
    Complex.I).smul_const Mass.beta
  have e : (fun s : ℝ => Mass.massStep (s * m)) =
      (fun s : ℝ => ((Real.cos (id s * m) : ℝ) : ℂ) • (1 : Q)) +
      (fun s : ℝ => (Complex.I * ((Real.sin (id s * m) : ℝ) : ℂ)) • Mass.beta) := by
    funext s; simp [Mass.massStep, Mass.coin]
  rw [e]
  refine (hc.add hs).congr_deriv ?_
  simp; ring_nf

/-- The handedness-labelled walk's generator is `i Σ a·α`. -/
theorem handed_generator (ay ax az : ℝ) :
    HasDerivAt (fun s : ℝ => handed (s * ay) (s * ax) (s * az))
      (Complex.I • (Mass.dirac ay ax az 0)) 0 := by
  have h1 := kron_hasDerivAt (fix Twist.slash) (realWalk_generator ay ax az)
  have h2 := kron_hasDerivAt (fix Twist.slash.conj) (realWalk_generator (-ay) (-ax) (-az))
  have e : (fun s : ℝ => handed (s * ay) (s * ax) (s * az)) =
      (fun s : ℝ => fix Twist.slash ⊗ₖ realWalk (s * ay) (s * ax) (s * az)) +
      (fun s : ℝ => fix Twist.slash.conj ⊗ₖ realWalk (s * -ay) (s * -ax) (s * -az)) := by
    funext s; simp [handed, mul_neg]
  rw [e]
  refine (h1.add h2).congr_deriv ?_
  have wn : Mass.weyl ((-ay : ℝ) : ℂ) ((-ax : ℝ) : ℂ) ((-az : ℝ) : ℂ) = -Mass.weyl ay ax az := by
    simp only [Mass.weyl]; push_cast; module
  have dz : Mass.dirac ay ax az 0 = Twist.slash.toMatrix ⊗ₖ Mass.weyl ay ax az := by
    simp only [Mass.dirac, Mass.alpha, Mass.weyl, kronecker_add, kronecker_smul, zero_smul, add_zero]
  rw [wn, dz, kronecker_smul, kronecker_smul, Mass.kron_neg_right,
    ← fix_sub_conj, sub_eq_add_neg, add_kronecker, Mass.kron_neg_left, smul_add]

/-- **The generator of the Dirac walk is the Dirac operator.** Along any direction in momentum and
mass, the walk's derivative at zero is `i·(a_y α_y + a_x α_x + a_z α_z + m β)`, whose square is
`a² + m²` (`Mass.dirac_sq`). -/
theorem diracWalk_generator (ay ax az m : ℝ) :
    HasDerivAt (fun s : ℝ => diracWalk (s * ay) (s * ax) (s * az) (s * m))
      (Complex.I • Mass.dirac ay ax az m) 0 := by
  have e : (fun s : ℝ => diracWalk (s * ay) (s * ax) (s * az) (s * m)) =
      (fun s : ℝ => Mass.massStep (s * m)) * (fun s : ℝ => handed (s * ay) (s * ax) (s * az)) := by
    funext s; rfl
  rw [e]
  refine ((massStep_generator m).mul (handed_generator ay ax az)).congr_deriv ?_
  simp only [zero_mul, massStep_zero, handed_zero, one_mul, mul_one, Mass.dirac,
    zero_smul, add_zero, smul_add, smul_smul]
  ring_nf
  abel

end QLF.DiracWalk
