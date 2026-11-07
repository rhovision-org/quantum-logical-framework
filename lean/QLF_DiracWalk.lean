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
  have hy := realStep_generator Twist.up (ay / 2)
  have hx := realStep_generator Twist.left (ax / 2)
  have hz := realStep_generator Twist.slash (az / 2)
  have e : (fun s : ℝ => realWalk (s * ay) (s * ax) (s * az)) =
      (fun s : ℝ => realStep Twist.up (s * (ay / 2))) *
        (fun s : ℝ => realStep Twist.left (s * (ax / 2))) *
        (fun s : ℝ => realStep Twist.slash (s * (az / 2))) *
        (fun s : ℝ => realStep Twist.slash (s * (az / 2))) *
        (fun s : ℝ => realStep Twist.left (s * (ax / 2))) *
        (fun s : ℝ => realStep Twist.up (s * (ay / 2))) := by
    funext s; simp only [realWalk, Pi.mul_apply, mul_div_assoc]
  rw [e]
  refine (((((hy.mul hx).mul hz).mul hz).mul hx).mul hy).congr_deriv ?_
  simp only [Pi.mul_apply, zero_mul, realStep_zero, one_mul, mul_one, Mass.weyl, smul_add,
    smul_smul]
  push_cast
  module

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


/-! ## The Dirac walk's exact dispersion

The generator fixes the walk only to first order. At finite momentum and mass the whole step is fixed
by one identity: `D + D† = 2 cos m cos k_y cos k_x cos k_z · 1`. So every eigenvalue `λ = e^{iE}`
obeys `cos E = cos m · Π cos k_i`, which is even in every `k_i` and in `m`: the massive walk has no
odd, linear-in-energy term in any direction (`QM_Postulates_QLF.md` §5b). -/

theorem sigmaX_fix_slash :
    Twist.right.toMatrix * fix Twist.slash * Twist.right.toMatrix = fix Twist.slash.conj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [fix, Twist.toMatrix, Twist.conj, σx, σz, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
    dotProduct]
  all_goals norm_num

theorem sigmaX_fix_slash_conj :
    Twist.right.toMatrix * fix Twist.slash.conj * Twist.right.toMatrix = fix Twist.slash := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [fix, Twist.toMatrix, Twist.conj, σx, σz, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
    dotProduct]
  all_goals norm_num

theorem beta_kron (A B : M) :
    Mass.beta * (A ⊗ₖ B) * Mass.beta = (Twist.right.toMatrix * A * Twist.right.toMatrix) ⊗ₖ B := by
  rw [Mass.beta, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one]

theorem handed_star (ky kx kz : ℝ) :
    star (handed ky kx kz) =
      fix Twist.slash ⊗ₖ realWalk (-ky) (-kx) (-kz) + fix Twist.slash.conj ⊗ₖ realWalk ky kx kz := by
  have h2 : star (realWalk (-ky) (-kx) (-kz)) = realWalk ky kx kz := by
    rw [realWalk_neg, star_star]
  rw [handed, star_add, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    conjTranspose_kronecker, conjTranspose_kronecker, fix_herm, fix_herm,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, h2, realWalk_neg]

/-- **The mass generator swaps the two handednesses**: conjugating by `β` reverses the momentum,
which is the adjoint. -/
theorem beta_handed_beta (ky kx kz : ℝ) :
    Mass.beta * handed ky kx kz * Mass.beta = star (handed ky kx kz) := by
  rw [handed_star, handed, mul_add, add_mul, beta_kron, beta_kron, sigmaX_fix_slash,
    sigmaX_fix_slash_conj, add_comm]

theorem handed_add_star (ky kx kz : ℝ) :
    handed ky kx kz + star (handed ky kx kz) =
      (2 * ((Real.cos ky * Real.cos kx * Real.cos kz : ℝ) : ℂ)) • (1 : Q) := by
  have hW : realWalk (-ky) (-kx) (-kz) + realWalk ky kx kz =
      (2 * ((Real.cos ky * Real.cos kx * Real.cos kz : ℝ) : ℂ)) • (1 : M) := by
    rw [add_comm, realWalk_neg, realWalk_add_star]
  rw [handed_star, handed]
  calc fix Twist.slash ⊗ₖ realWalk ky kx kz + fix Twist.slash.conj ⊗ₖ realWalk (-ky) (-kx) (-kz) +
        (fix Twist.slash ⊗ₖ realWalk (-ky) (-kx) (-kz) + fix Twist.slash.conj ⊗ₖ realWalk ky kx kz)
      = fix Twist.slash ⊗ₖ (realWalk (-ky) (-kx) (-kz) + realWalk ky kx kz) +
        fix Twist.slash.conj ⊗ₖ (realWalk (-ky) (-kx) (-kz) + realWalk ky kx kz) := by
        rw [kronecker_add, kronecker_add]; abel
    _ = _ := by
        rw [← add_kronecker, fix_add_conj, hW, kronecker_smul, one_kronecker_one]

/-- **`D + D† = 2 cos m cos k_y cos k_x cos k_z · 1`** for the Dirac walk, at every momentum and
mass. The mass coin's `β` part cancels against its adjoint because `β` swaps the handednesses. -/
theorem diracWalk_add_star (ky kx kz m : ℝ) :
    diracWalk ky kx kz m + star (diracWalk ky kx kz m) =
      ((2 * Real.cos m * Real.cos ky * Real.cos kx * Real.cos kz : ℝ) : ℂ) • (1 : Q) := by
  have hb : star Mass.beta = Mass.beta := by rw [Matrix.star_eq_conjTranspose, Mass.beta_herm]
  have hsH : star (handed ky kx kz) * Mass.beta = Mass.beta * handed ky kx kz := by
    rw [← beta_handed_beta, mul_assoc, Mass.beta_sq, mul_one]
  have hc : star (Complex.I * ((Real.sin m : ℝ) : ℂ)) = -(Complex.I * ((Real.sin m : ℝ) : ℂ)) := by
    rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have hr : star ((Real.cos m : ℝ) : ℂ) = ((Real.cos m : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [diracWalk, Mass.massStep, Mass.coin, star_mul, star_add, star_smul, star_smul, star_one, hb,
    hc, hr, add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_mul_assoc,
    mul_smul_comm, hsH]
  have key : ((Real.cos m : ℝ) : ℂ) • handed ky kx kz +
      (Complex.I * ((Real.sin m : ℝ) : ℂ)) • (Mass.beta * handed ky kx kz) +
      (((Real.cos m : ℝ) : ℂ) • star (handed ky kx kz) +
        (-(Complex.I * ((Real.sin m : ℝ) : ℂ))) • (Mass.beta * handed ky kx kz)) =
      ((Real.cos m : ℝ) : ℂ) • (handed ky kx kz + star (handed ky kx kz)) := by
    rw [smul_add, neg_smul]; abel
  rw [key, handed_add_star, smul_smul]
  congr 1
  push_cast
  ring

/-- **The Dirac walk's exact dispersion.** If `D v = λ v` with `v ≠ 0`, then `λ ≠ 0` and
`λ + λ⁻¹ = 2 cos m Π cos k_i`. Every eigenvalue of a unitary is `e^{iE}`, so `cos E = cos m Π cos k_i`
(`diracWalk_dispersion`). -/
theorem diracWalk_eigen (ky kx kz m : ℝ) (v : Fin 2 × Fin 2 → ℂ) (lam : ℂ) (hv : v ≠ 0)
    (h : diracWalk ky kx kz m *ᵥ v = lam • v) :
    lam ≠ 0 ∧
      lam + lam⁻¹ = ((2 * Real.cos m * Real.cos ky * Real.cos kx * Real.cos kz : ℝ) : ℂ) := by
  set D := diracWalk ky kx kz m
  have hU : star D * D = 1 := Matrix.mem_unitaryGroup_iff'.mp (diracWalk_unitary ky kx kz m)
  have hback : lam • (star D *ᵥ v) = v := by
    rw [← Matrix.mulVec_smul, ← h, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hlam : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hback
    exact hv hback.symm
  have hstar : star D *ᵥ v = lam⁻¹ • v := by
    rw [← hback, smul_smul, inv_mul_cancel₀ hlam, one_smul, hback]
  refine ⟨hlam, ?_⟩
  have hsum := congrArg (· *ᵥ v) (diracWalk_add_star ky kx kz m)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hsum
  change D *ᵥ v + star D *ᵥ v = _ at hsum
  rw [h, hstar, ← add_smul] at hsum
  have hz : (lam + lam⁻¹ - ((2 * Real.cos m * Real.cos ky * Real.cos kx * Real.cos kz : ℝ) : ℂ)) • v
      = 0 := by rw [sub_smul, hsum, sub_self]
  rcases smul_eq_zero.mp hz with hz | hz
  · exact sub_eq_zero.mp hz
  · exact absurd hz hv

/-- **`cos E = cos m · cos k_y cos k_x cos k_z`** for every eigenvalue `e^{iE}` of the Dirac walk. -/
theorem diracWalk_dispersion (ky kx kz m E : ℝ) (v : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0)
    (h : diracWalk ky kx kz m *ᵥ v = Complex.exp (E * Complex.I) • v) :
    Real.cos E = Real.cos m * (Real.cos ky * Real.cos kx * Real.cos kz) := by
  have h2 := (diracWalk_eigen ky kx kz m v _ hv h).2
  rw [← Complex.exp_neg, ← neg_mul, ← Complex.two_cos, ← Complex.ofReal_cos] at h2
  have h3 : 2 * Real.cos E = 2 * Real.cos m * Real.cos ky * Real.cos kx * Real.cos kz := by
    exact_mod_cast h2
  linear_combination h3 / 2

end QLF.DiracWalk
