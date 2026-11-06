import QLF_RealizableWalk
import QLF_ClosureUnitarity

/-!
# QLF_OpticalTheorem — the finite optical theorem, and where the raw census breaks it

Issue #207, target **U3b**. Write a channel matrix as `S = 1 + iT`. For any finite channel set:

* **`defect_eq`.** `SᴴS − 1 = TᴴT + i(T − Tᴴ)`, exactly.
* **`optical_iff`.** So `S` is unitary **iff** `TᴴT = −i(T − Tᴴ)`, the matrix form of
  `2 Im T = T†T`.
* **`forward_defect`, `optical_forward`.** On the diagonal, `Re(SᴴS)ₐₐ − 1 = Σ_c |T_ca|² − 2 Im Tₐₐ`;
  for unitary `S` the right side is zero: **the imaginary part of the forward amplitude is half the
  sum over every intermediate channel `c` of `|T_ca|²`**. This is the optical theorem with the
  total cross-section a finite sum over channels.

QLF instances, each from a unitarity theorem already proved:

* **`history_optical`.** Every finite twist history (`history_unitary`, #208).
* **`realWalk_optical`.** The realizable walk at every momentum (`realWalk_unitary`).
* **`coneStep_optical`.** The light-cone step (`coneStep_unitary`).
* **`raw_optical_defect`.** The raw coherent census step `r3⁻¹ • rawPhaseSum` **violates** the
  optical theorem: in the forward channel, `Σ_c |T_c0|² − 2 Im T₀₀ = 2/3`. The excess is the norm
  the raw sum creates (`rawStep_not_unitary`).

The identity itself is algebra. What QLF supplies is which channel matrices satisfy it: those built
from realizable histories do, and the raw census does not. The momentum-space walk is one block of
the translation-invariant position-space walk, so the theorem holds there block by block; a
statement on the full position-space channel space is not here. No axioms.

**Credit.** The optical theorem is Bohr, Peierls and Placzek's (1939) in its general form, after
Feenberg (1932); its diagrammatic form is Cutkosky's cutting rules (*J. Math. Phys.* **1**, 429
(1960)). Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.OpticalTheorem

open Matrix Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The unitarity defect in terms of `T`.** -/
theorem defect_eq (T : Matrix ι ι ℂ) :
    (1 + I • T)ᴴ * (1 + I • T) - 1 = Tᴴ * T + I • (T - Tᴴ) := by
  rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, Complex.star_def, conj_I]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub]
  rw [smul_add, smul_smul, show I * -I = (1 : ℂ) by rw [mul_neg, I_mul_I, neg_neg], one_smul,
    neg_smul]
  abel

/-- The transition matrix `T = −i(S − 1)` of a channel matrix `S`. -/
noncomputable def tmat (S : Matrix ι ι ℂ) : Matrix ι ι ℂ := -I • (S - 1)

omit [Fintype ι] in
lemma S_eq (S : Matrix ι ι ℂ) : 1 + I • tmat S = S := by
  unfold tmat
  rw [smul_smul, show I * -I = 1 by rw [mul_neg, I_mul_I, neg_neg], one_smul]
  abel

/-- **The optical theorem, matrix form.** `S` is unitary iff `TᴴT = −i(T − Tᴴ)`. -/
theorem optical_iff (S : Matrix ι ι ℂ) :
    Sᴴ * S = 1 ↔ (tmat S)ᴴ * tmat S = -I • (tmat S - (tmat S)ᴴ) := by
  have h := defect_eq (tmat S)
  rw [S_eq] at h
  constructor
  · intro hS
    rw [hS, sub_self] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h.symm
  · intro hT
    rw [hT, neg_smul, neg_add_cancel] at h
    exact sub_eq_zero.mp h

/-- **The forward defect**: `Re(SᴴS)ₐₐ − 1 = Σ_c |T_ca|² − 2 Im Tₐₐ`. -/
theorem forward_defect (S : Matrix ι ι ℂ) (a : ι) :
    ((Sᴴ * S) a a).re - 1 = ∑ c, normSq (tmat S c a) - 2 * (tmat S a a).im := by
  have h := congrFun (congrFun (defect_eq (tmat S)) a) a
  rw [S_eq] at h
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.mul_apply, conjTranspose_apply, smul_eq_mul] at h
  have h2 := congrArg Complex.re h
  rw [Complex.sub_re, Complex.one_re] at h2
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [h2]
  simp only [Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring_nf

/-- **The optical theorem, forward form**: for unitary `S`,
    `2 Im Tₐₐ = Σ_c |T_ca|²`, a sum over every intermediate channel. -/
theorem optical_forward (S : Matrix ι ι ℂ) (hS : S ∈ unitaryGroup ι ℂ) (a : ι) :
    2 * (tmat S a a).im = ∑ c, normSq (tmat S c a) := by
  have h := forward_defect S a
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose] at hS
  rw [hS, one_apply_eq, Complex.one_re, sub_self] at h
  linarith

/-! ## QLF instances -/

open QLF.ClosureChannels in
/-- **Every finite twist history satisfies the optical theorem.** -/
theorem history_optical (ts : List QLF.Twist) (a : Fin 2) :
    2 * (tmat (QLF.twistMatrixFold ts) a a).im =
      ∑ c, normSq (tmat (QLF.twistMatrixFold ts) c a) :=
  optical_forward _ (QLF.ClosureUnitarity.history_unitary ts) a

open QLF.ClosureChannels in
/-- **The realizable walk satisfies the optical theorem at every momentum.** -/
theorem realWalk_optical (ky kx kz : ℝ) (a : Fin 2) :
    2 * (tmat (realWalk ky kx kz) a a).im = ∑ c, normSq (tmat (realWalk ky kx kz) c a) :=
  optical_forward _ (realWalk_unitary ky kx kz) a

open QLF.ClosureChannels in
/-- **The light-cone step satisfies the optical theorem.** -/
theorem coneStep_optical (a : Fin 2) :
    2 * (tmat coneStep a a).im = ∑ c, normSq (tmat coneStep c a) :=
  optical_forward _ coneStep_unitary a

open QLF.ClosureChannels in
/-- **The raw census step violates the optical theorem**, by exactly `2/3` in the forward
    channel: the norm the raw sum creates. -/
theorem raw_optical_defect :
    ∑ c, normSq (tmat (r3⁻¹ • rawPhaseSum) c 0) - 2 * (tmat (r3⁻¹ • rawPhaseSum) 0 0).im =
      2 / 3 := by
  rw [← forward_defect, conjTranspose_smul, smul_mul_smul_comm, star_r3_inv, Matrix.smul_apply,
    rawPhaseSum_gram, smul_eq_mul]
  have h3 : r3⁻¹ * r3⁻¹ = 1 / 3 := by rw [← mul_inv, r3_sq]; norm_num
  rw [h3]
  norm_num

end QLF.OpticalTheorem
