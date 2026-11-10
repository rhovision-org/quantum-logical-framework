import QLF_NullTensorReconstruction
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_MetricSinglet — **the Minkowski metric is the singlet, and null vectors are product states**

[`QLF_NullTensorReconstruction`](QLF_NullTensorReconstruction.lean) closes the algebraic step of
Jacobson's derivation of the Einstein equations: a symmetric tensor `S_ab` with `S_ab k^a k^b = 0` on
every null `k` is a multiple of the metric. There `SymTensor4` is ten reals with no further origin.
This module reads the same statement in two-body language, using the tensor product that
[`QLF_TensorFromClosure`](QLF_TensorFromClosure.lean) derives (`M ⊗ M ≅ Mat₄`).

A `Form` is a `2×2` Hermitian matrix, `t·I + x·σx + y·σy + z·σz`, and its determinant is the
Minkowski interval (`QLF_Minkowski`). So a rank-2 tensor `S_ab` is the two-body observable
`Ŝ = Σ S_ab σ_a ⊗ σ_b` on `ℂ² ⊗ ℂ²` (`twoBody`). Three facts follow, all proved here:

* **The metric is the singlet** (`metric_is_singlet`): `Σ η_ab σ_a ⊗ σ_b = 4 |s⟩⟨s|`, where
  `|s⟩ = (|01⟩ − |10⟩)/√2`. In the unnormalised form used below, `twoBody (f·g) = 2f · |v⟩⟨v|` with
  `v = |01⟩ − |10⟩`.
* **A null vector is a pure state** (`kForm_null`, `expect_twoBody`): a qubit `ψ = (a, b)` gives the
  null vector `k(ψ)` with `k^a = ⟨ψ|σ_a|ψ⟩ / 2`, and the product state `ψ ⊗ ψ` reads the tensor on it:
  `⟨ψψ| Ŝ |ψψ⟩ = 4 · S_ab k^a k^b`.
* **The null-cone step is a statement about two bodies** (`product_annihilator_iff_singlet`): an
  observable built from a symmetric tensor vanishes on every product state `ψ ⊗ ψ` exactly when it is
  a multiple of the singlet projector. Product states are orthogonal to the singlet
  (`product_orthogonal_singlet`), which is the easy direction; the nine integer null probes of
  `QLF_NullTensorReconstruction` are nine product states with Gaussian-integer amplitudes
  (`kForm_probe_*`), which is the hard one.

This is the same shape as rung 6 of `QLF_TensorFromClosure` (`split_strong_iff_singlet`: the singlet
is the unique state every shared strong pair fixes). Read together: the metric is the shared pair,
and the null directions are the unshared ones.

## Scope

This changes the *reading* of the middle arrow of Jacobson's derivation, not the number of open
arrows. The first arrow (horizon thermodynamics to `S_ab k^a k^b = 0`, via the local Rindler
construction and Raychaudhuri focusing) and the instance of `DivergenceCalculus` needed by
`QLF_BianchiClosure` are untouched. That `S_ab = R_ab − κ T_ab` is a two-body observable of the
substrate is a reading of the proven isomorphism, not a derivation of curvature.

No axioms.
-/

namespace QLF.MetricSinglet

open QLF.NullTensor Matrix

/-- One-body operators. -/
abbrev Op := Matrix (Fin 2) (Fin 2) ℂ
/-- Two-body operators on `ℂ² ⊗ ℂ²`. -/
abbrev Op2 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The Pauli basis, with `σ_t = I`. -/
noncomputable def s0 : Op := !![1, 0; 0, 1]
noncomputable def sx : Op := !![0, 1; 1, 0]
noncomputable def sy : Op := !![0, -Complex.I; Complex.I, 0]
noncomputable def sz : Op := !![1, 0; 0, -1]

/-- The tensor (Kronecker) product of two one-body operators. -/
noncomputable def kron (A B : Op) : Op2 := Matrix.kroneckerMap (· * ·) A B

/-- The symmetrised product `A ⊗ B + B ⊗ A`. -/
noncomputable def sym (A B : Op) : Op2 := kron A B + kron B A

/-- **A symmetric rank-2 tensor as a two-body observable**: `Ŝ = Σ S_ab σ_a ⊗ σ_b`. -/
noncomputable def twoBody (S : SymTensor4) : Op2 :=
  (S.tt : ℂ) • kron s0 s0 + (S.tx : ℂ) • sym s0 sx + (S.ty : ℂ) • sym s0 sy
  + (S.tz : ℂ) • sym s0 sz + (S.xx : ℂ) • kron sx sx + (S.xy : ℂ) • sym sx sy
  + (S.xz : ℂ) • sym sx sz + (S.yy : ℂ) • kron sy sy + (S.yz : ℂ) • sym sy sz
  + (S.zz : ℂ) • kron sz sz

/-- The (unnormalised) singlet `v = |01⟩ − |10⟩`. -/
def sv (p : Fin 2 × Fin 2) : ℂ := ![![0, 1], ![-1, 0]] p.1 p.2

/-- The singlet projector, unnormalised: `|v⟩⟨v|` (twice the projector). -/
def singletOuter : Op2 := fun p q => sv p * star (sv q)

/-- The one-body expectation `⟨ψ|A|ψ⟩` for `ψ = (a, b)`. -/
def expect1 (A : Op) (a b : ℂ) : ℂ :=
  ∑ i, ∑ k, star (![a, b] i) * A i k * ![a, b] k

/-- The product-state expectation `⟨ψψ|M|ψψ⟩` for `ψ = (a, b)`. -/
def expect2 (M : Op2) (a b : ℂ) : ℂ :=
  ∑ p, ∑ q, star (![a, b] p.1 * ![a, b] p.2) * M p q * (![a, b] q.1 * ![a, b] q.2)

/-- **The null vector of a qubit**: `k^a = ⟨ψ|σ_a|ψ⟩ / 2`, written in real coordinates. -/
def kForm (a b : ℂ) : Form :=
  ⟨(a.re ^ 2 + a.im ^ 2 + b.re ^ 2 + b.im ^ 2) / 2,
   a.re * b.re + a.im * b.im,
   a.re * b.im - a.im * b.re,
   (a.re ^ 2 + a.im ^ 2 - b.re ^ 2 - b.im ^ 2) / 2⟩

/-! ### Every qubit gives a null vector -/

/-- `k(ψ)` is null: `t² − x² − y² − z² = 0` (the Hopf map lands on the light cone). -/
theorem kForm_null (a b : ℂ) : IsNull (kForm a b) := by
  unfold IsNull QLF.Minkowski.Form.interval kForm
  ring

/-! ### Linearity of the product-state expectation -/

theorem expect2_add (M N : Op2) (a b : ℂ) :
    expect2 (M + N) a b = expect2 M a b + expect2 N a b := by
  simp only [expect2, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem expect2_smul (c : ℂ) (M : Op2) (a b : ℂ) :
    expect2 (c • M) a b = c * expect2 M a b := by
  unfold expect2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **A product state factorises a product observable**: `⟨ψψ|A⊗B|ψψ⟩ = ⟨ψ|A|ψ⟩⟨ψ|B|ψ⟩`. -/
theorem expect2_kron (A B : Op) (a b : ℂ) :
    expect2 (kron A B) a b = expect1 A a b * expect1 B a b := by
  simp only [expect2, expect1, kron, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, star_mul']
  ring

theorem expect2_sym (A B : Op) (a b : ℂ) :
    expect2 (sym A B) a b = 2 * (expect1 A a b * expect1 B a b) := by
  rw [sym, expect2_add, expect2_kron, expect2_kron]
  ring

/-! ### Pauli expectations are twice the null vector's components -/

theorem expect1_s0 (a b : ℂ) : expect1 s0 a b = 2 * ((kForm a b).t : ℂ) := by
  simp only [expect1, s0, kForm, Fin.sum_univ_two]
  apply Complex.ext <;> simp <;> ring

theorem expect1_sx (a b : ℂ) : expect1 sx a b = 2 * ((kForm a b).x : ℂ) := by
  simp only [expect1, sx, kForm, Fin.sum_univ_two]
  apply Complex.ext <;> simp <;> ring

theorem expect1_sy (a b : ℂ) : expect1 sy a b = 2 * ((kForm a b).y : ℂ) := by
  simp only [expect1, sy, kForm, Fin.sum_univ_two]
  apply Complex.ext <;> simp <;> ring

theorem expect1_sz (a b : ℂ) : expect1 sz a b = 2 * ((kForm a b).z : ℂ) := by
  simp only [expect1, sz, kForm, Fin.sum_univ_two]
  apply Complex.ext <;> simp <;> ring

/-- **A product state reads the tensor on its null vector**:
    `⟨ψψ| Ŝ |ψψ⟩ = 4 · S_ab k^a k^b` with `k = k(ψ)`. -/
theorem expect_twoBody (S : SymTensor4) (a b : ℂ) :
    expect2 (twoBody S) a b = ((4 * contract S (kForm a b) : ℝ) : ℂ) := by
  simp only [twoBody, expect2_add, expect2_smul, expect2_sym, expect2_kron,
    expect1_s0, expect1_sx, expect1_sy, expect1_sz]
  simp only [contract]
  push_cast
  ring

/-! ### The metric is the singlet -/

/-- **The Minkowski metric is the singlet.** `twoBody (f·η) = 2f · |v⟩⟨v|` with `v = |01⟩ − |10⟩`,
    i.e. `Σ η_ab σ_a ⊗ σ_b = 4 |s⟩⟨s|` for the normalised singlet. -/
theorem metric_is_singlet (f : ℝ) :
    twoBody (metricMultiple f) = (2 * (f : ℂ)) • singletOuter := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [twoBody, metricMultiple, sym, kron, s0, sx, sy, sz, singletOuter, sv,
      Matrix.kroneckerMap_apply] <;>
    ring

/-- **Product states are orthogonal to the singlet**: `⟨v|ψψ⟩ = ab − ba = 0`, so every multiple of
    the singlet projector vanishes on every product state `ψ ⊗ ψ`. -/
theorem product_orthogonal_singlet (c : ℂ) (a b : ℂ) :
    expect2 (c • singletOuter) a b = 0 := by
  have h0 : expect2 singletOuter a b = 0 := by
    simp only [expect2, singletOuter, sv, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, star_zero, star_neg, star_one]
    ring
  rw [expect2_smul, h0, mul_zero]

/-! ### The nine integer null probes are nine product states

Each probe of `QLF_NullTensorReconstruction` is `k(ψ)` for a qubit with Gaussian-integer
amplitudes, so the finite reconstruction runs on product states. -/

theorem kForm_probe_xP : kForm ⟨1, 0⟩ ⟨1, 0⟩ = kxP := by norm_num [kForm, kxP]
theorem kForm_probe_xM : kForm ⟨1, 0⟩ ⟨-1, 0⟩ = kxM := by norm_num [kForm, kxM]
theorem kForm_probe_yP : kForm ⟨1, 0⟩ ⟨0, 1⟩ = kyP := by norm_num [kForm, kyP]
theorem kForm_probe_yM : kForm ⟨1, 0⟩ ⟨0, -1⟩ = kyM := by norm_num [kForm, kyM]
theorem kForm_probe_zP : kForm ⟨1, 1⟩ ⟨0, 0⟩ = kzP := by norm_num [kForm, kzP]
theorem kForm_probe_zM : kForm ⟨0, 0⟩ ⟨1, 1⟩ = kzM := by norm_num [kForm, kzM]
theorem kForm_probe_xy : kForm ⟨1, 2⟩ ⟨-1, 2⟩ = kxy := by norm_num [kForm, kxy]
theorem kForm_probe_xz : kForm ⟨3, 0⟩ ⟨1, 0⟩ = kxz := by norm_num [kForm, kxz]
theorem kForm_probe_yz : kForm ⟨3, 0⟩ ⟨0, 1⟩ = kyz := by norm_num [kForm, kyz]

/-- A vanishing product-state expectation is a vanishing contraction on that state's null vector. -/
theorem contract_zero_of_expect {S : SymTensor4} {a b : ℂ} (h : expect2 (twoBody S) a b = 0) :
    contract S (kForm a b) = 0 := by
  rw [expect_twoBody] at h
  have h4 : (4 * contract S (kForm a b) : ℝ) = 0 := by exact_mod_cast h
  linarith

/-! ### The null-cone step, as a statement about two bodies -/

/-- **Jacobson's algebraic step in tensor language.** A symmetric tensor's two-body observable
    vanishes on every product state `ψ ⊗ ψ` exactly when the tensor is a metric multiple. -/
theorem product_annihilator_iff_metric (S : SymTensor4) :
    (∀ a b : ℂ, expect2 (twoBody S) a b = 0) ↔ ∃ f : ℝ, S = metricMultiple f := by
  constructor
  · intro h
    refine ⟨S.tt, finite_null_probes_force_metric S ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · rw [← kForm_probe_xP]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_xM]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_yP]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_yM]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_zP]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_zM]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_xy]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_xz]; exact contract_zero_of_expect (h _ _)
    · rw [← kForm_probe_yz]; exact contract_zero_of_expect (h _ _)
  · rintro ⟨f, rfl⟩ a b
    rw [metric_is_singlet]
    exact product_orthogonal_singlet _ a b

/-- **The null-cone step is singlet uniqueness.** A symmetric tensor's two-body observable vanishes
    on every product state exactly when it is a multiple of the singlet projector. -/
theorem product_annihilator_iff_singlet (S : SymTensor4) :
    (∀ a b : ℂ, expect2 (twoBody S) a b = 0) ↔
      ∃ c : ℂ, twoBody S = c • singletOuter := by
  constructor
  · intro h
    obtain ⟨f, rfl⟩ := (product_annihilator_iff_metric S).mp h
    exact ⟨2 * (f : ℂ), metric_is_singlet f⟩
  · rintro ⟨c, hc⟩ a b
    rw [hc]
    exact product_orthogonal_singlet c a b

end QLF.MetricSinglet
