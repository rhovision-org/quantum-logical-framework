import QLF_JointClosure
import QLF_TensorFromClosure

/-!
# QLF_PerspectiveLocality — only local information changes local statistics

Gates L3 and L5 of issue #315. Part of the [Quantum Logical Framework (QLF)](../README.md);
the write-up is [`Locality.md`](../Locality.md).

## The model

A two-body history is a word of tokens `(false, t)` (body `A`) and `(true, t)` (body `B`),
interleaved in any order (`QLF_TensorFromClosure.Tok`). The **global** dynamics folds the whole
word, letting `A`'s twists act on the first tensor factor and `B`'s on the second:
`jointFold w = ∏ tokOp`. A joint state `ψ` lives on `ℂ² ⊗ ℂ²` and may be entangled, for example
the singlet `s` of `QLF_JointClosure`, the unique state whose halves close together on every
axis. `A`'s local statistic is the expectation of an `A`-observable **in the globally evolved
state**, `expect (onA X) (jointFold w *ᵥ ψ)`.

The statistic is defined from the global state and not from `A`'s projection. That is what
keeps the locality theorem from being circular, which was the concern raised for Gate 3.

## Results

* **`jointFold_factorizes`**: the global fold of any interleaving is
  `onA (fold (projA w)) * onB (fold (projB w))`. Interleaving order across bodies is invisible
  (`indexed_factors_commute`, here as `onA_onB`).
* **`fold_unitary`**: every twist word folds to a unitary.
* **`local_expectation_local`**: `A`'s expectation after `w` equals the expectation, in the
  **initial** state, of `A`'s Heisenberg-evolved observable `Fᴴ X F` with `F = fold (projA w)`.
* **`perspective_locality`** (P7, Gate 3, Tests D and F): if two global histories agree on `A`'s
  projection, then for **every** joint state, entangled or not, and every `A`-observable,
  `A`'s expectations agree. `B`'s tokens, their number, and how they interleave with `A`'s
  change nothing `A` can measure.
* **`perspective_locality_nontrivial`**: the restriction is not vacuous. One `B` token changes
  `B`'s own expectation (from `1` to `−1` on `|00⟩`).
* **`no_signalling`** (P8, Gate 5): with projective two-outcome measurements `(1 ± X)/2`,
  `A`'s outcome marginal after any history is independent of `B`'s setting `Y`, for every
  `Y`, every joint state, and every `B` word.
* **`singlet_outcome_dependent`** (Bell audit): on the singlet with both settings `σz`,
  `P(+,+) = 0` while `P(+) = P(+) = 1/2`. **Outcome independence fails.**
* **`locality_profile`**: parameter independence holds (`no_signalling`), outcome independence
  fails, and the singlet reaches CHSH `2√2` (`singlet_saturates`), above the bound `2` that
  jointly valued (commuting) observables obey (`QLF_Tsirelson.chsh_classical`). Bell locality is
  the conjunction of parameter and outcome independence (Jarrett 1984), so the condition that
  fails here is outcome independence. A preassigned joint value for incompatible Pauli contexts
  is not available either, because `σz` and `σx` anticommute.

## Scope

* The probabilities are **Born weights on the twist operator algebra**. This is a
  representation result. The census-level measure is tested separately in
  `QLF_LocalityDefinitions.census_postselection_signals` (P6), and there uniform counting over
  joint closures **does** signal.
* Measurement independence is a modelling input: settings `X`, `Y` and the state `ψ` are
  independent variables of every theorem. It is stated here, not derived.
* The two-body split is given. Where a perspective's boundary comes from (accessibility) is
  open (`QLF_SharedReality`, `Holography_Audit.md` §5).

No axioms.
-/

noncomputable section

namespace QLF.PerspectiveLocality

open QLF Matrix QLF.Tsirelson QLF.TensorFromClosure

/-! ## §1 The global dynamics factorizes -/

/-- A token acts on its own body's factor. -/
def tokOp : Tok → Q
  | (false, t) => onA t.toMatrix
  | (true, t) => onB t.toMatrix

/-- The **global** fold of a two-body word, in its interleaved order. -/
def jointFold (w : List Tok) : Q := (w.map tokOp).prod

lemma fold_cons (t : Twist) (l : List Twist) :
    twistMatrixFold (t :: l) = t.toMatrix * twistMatrixFold l := rfl

lemma fold_nil : twistMatrixFold [] = 1 := rfl

/-- **The global fold factorizes into the two bodies' own folds.** -/
theorem jointFold_factorizes (w : List Tok) :
    jointFold w = onA (twistMatrixFold (projA w)) * onB (twistMatrixFold (projB w)) := by
  induction w with
  | nil => simp [jointFold, fold_nil, onA_one, onB_one]
  | cons tk w ih =>
    obtain ⟨b, t⟩ := tk
    have hw : jointFold ((b, t) :: w) = tokOp (b, t) * jointFold w := by
      simp [jointFold]
    rw [hw, ih]
    cases b
    · simp only [tokOp, projA_consA, projB_consA, fold_cons]
      rw [← mul_assoc, onA_mul]
    · simp only [tokOp, projA_consB, projB_consB, fold_cons]
      rw [← mul_assoc, ← onA_onB, mul_assoc, onB_mul]

/-- **Every twist word folds to a unitary.** -/
theorem fold_unitary (l : List Twist) : (twistMatrixFold l)ᴴ * twistMatrixFold l = 1 := by
  induction l with
  | nil => simp [fold_nil]
  | cons t l ih =>
    rw [fold_cons, conjTranspose_mul, ClosureUnitarity.twist_herm]
    calc (twistMatrixFold l)ᴴ * t.toMatrix * (t.toMatrix * twistMatrixFold l)
        = (twistMatrixFold l)ᴴ * (t.toMatrix * t.toMatrix) * twistMatrixFold l := by
          simp only [mul_assoc]
      _ = 1 := by rw [ClosureUnitarity.twist_sq, mul_one, ih]

lemma onA_conjTranspose (X : M) : (onA X)ᴴ = onA Xᴴ := by
  rw [onA, conjTranspose_kronecker, conjTranspose_one]; rfl

lemma onB_conjTranspose (X : M) : (onB X)ᴴ = onB Xᴴ := by
  rw [onB, conjTranspose_kronecker, conjTranspose_one]; rfl

/-! ## §2 Expectations in the globally evolved state -/

/-- The (unnormalized) expectation of `O` in the state `φ`. -/
def expect (O : Q) (φ : Fin 2 × Fin 2 → ℂ) : ℂ := star φ ⬝ᵥ (O *ᵥ φ)

/-- Evolving the state is evolving the observable (Heisenberg picture). -/
theorem expect_evolve (O U : Q) (ψ : Fin 2 × Fin 2 → ℂ) :
    expect O (U *ᵥ ψ) = expect (Uᴴ * O * U) ψ := by
  unfold expect
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

/-- **`A`'s expectation after a global history depends on `A`'s twists only**, through the
    Heisenberg-evolved observable `Fᴴ X F`. -/
theorem local_expectation_local (X : M) (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) :
    expect (onA X) (jointFold w *ᵥ ψ) =
      expect (onA ((twistMatrixFold (projA w))ᴴ * X * twistMatrixFold (projA w))) ψ := by
  rw [expect_evolve, jointFold_factorizes]
  set FA := twistMatrixFold (projA w)
  set FB := twistMatrixFold (projB w)
  congr 1
  rw [conjTranspose_mul, onA_conjTranspose, onB_conjTranspose]
  calc onB FBᴴ * onA FAᴴ * onA X * (onA FA * onB FB)
      = onB FBᴴ * (onA (FAᴴ * X * FA) * onB FB) := by
        simp only [← onA_mul, mul_assoc]
    _ = onA (FAᴴ * X * FA) * (onB FBᴴ * onB FB) := by
        rw [← mul_assoc, ← onA_onB, mul_assoc]
    _ = onA (FAᴴ * X * FA) := by rw [onB_mul, fold_unitary, onB_one, mul_one]

/-- **P7 — perspective locality.** Two global histories that agree on `A`'s projection give `A`
    the same expectation for every `A`-observable and every joint state, entangled or not. -/
theorem perspective_locality (X : M) {w w' : List Tok} (h : projA w = projA w')
    (ψ : Fin 2 × Fin 2 → ℂ) :
    expect (onA X) (jointFold w *ᵥ ψ) = expect (onA X) (jointFold w' *ᵥ ψ) := by
  rw [local_expectation_local, local_expectation_local, h]

/-- `|00⟩`. -/
def e00 : Fin 2 × Fin 2 → ℂ := Pi.single (0, 0) 1

/-- **Nontrivial.** A single `B` token (`left = −σx`) leaves `A`'s projection empty and flips
    `B`'s `σz` expectation on `|00⟩` from `1` to `−1`. So the theorem restricts something that
    really moves. -/
theorem perspective_locality_nontrivial :
    projA [(true, Twist.left)] = projA [] ∧
      expect (onB σz) (jointFold [] *ᵥ e00) = 1 ∧
      expect (onB σz) (jointFold [(true, Twist.left)] *ᵥ e00) = -1 := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [expect, jointFold, e00, onB, σz, mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, kroneckerMap_apply, Pi.single_apply]
  · simp [expect, jointFold, tokOp, e00, onB, σz, σx, Twist.toMatrix, mulVec, dotProduct,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply,
      Pi.single_apply]

/-! ## §3 Operational no-signalling -/

/-- The projector onto outcome `α = ±1` of a two-outcome observable `X`. -/
def proj (X : M) (α : ℂ) : M := (1 / 2 : ℂ) • (1 + α • X)

lemma proj_sum (Y : M) : proj Y 1 + proj Y (-1) = 1 := by
  unfold proj
  rw [← smul_add]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring

/-- The (unnormalized) joint probability of outcomes `α`, `β` for settings `X`, `Y` after the
    history `w`, from the joint state `ψ`. -/
def prob (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (X : M) (α : ℂ) (Y : M) (β : ℂ) : ℂ :=
  expect (onA (proj X α) * onB (proj Y β)) (jointFold w *ᵥ ψ)

/-- **P8 — no signalling.** `A`'s outcome marginal is `A`'s local expectation: it does not depend
    on `B`'s setting `Y`, and by `perspective_locality` not on `B`'s word either. -/
theorem no_signalling (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (X : M) (α : ℂ) (Y : M) :
    prob w ψ X α Y 1 + prob w ψ X α Y (-1) = expect (onA (proj X α)) (jointFold w *ᵥ ψ) := by
  unfold prob expect
  rw [← dotProduct_add, ← add_mulVec, ← mul_add]
  rw [show onB (proj Y 1) + onB (proj Y (-1)) = onB (proj Y 1 + proj Y (-1)) by
    simp [onB, add_kronecker, kronecker_add]]
  rw [proj_sum, onB_one, mul_one]

/-- Remote-setting independence in the form usually written: the marginal is the same for any
    two settings of `B`. -/
theorem marginal_setting_independent (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (X : M) (α : ℂ)
    (Y Y' : M) :
    prob w ψ X α Y 1 + prob w ψ X α Y (-1) = prob w ψ X α Y' 1 + prob w ψ X α Y' (-1) := by
  rw [no_signalling, no_signalling]

/-! ## §4 Bell audit on the singlet -/

open QLF.JointClosure in
/-- **Outcome independence fails on the singlet.** With both settings `σz`, the unnormalized
    joint weight of `(+,+)` is `0`, while each marginal is `1` out of the norm `2`, so
    `P(+,+) = 0 ≠ 1/4 = P(+)·P(+)`. -/
theorem singlet_outcome_dependent :
    expect (onA (proj σz 1) * onB (proj σz 1)) s = 0 ∧
      expect (onA (proj σz 1)) s = 1 ∧ expect (onB (proj σz 1)) s = 1 ∧
      star s ⬝ᵥ s = 2 ∧
      expect (onA (proj σz 1) * onB (proj σz 1)) s * (star s ⬝ᵥ s) ≠
        expect (onA (proj σz 1)) s * expect (onB (proj σz 1)) s := by
  have hA : expect (onA (proj σz 1)) s = 1 := by
    have := singlet_corr (proj σz 1) 1
    rw [onB_one, mul_one] at this
    unfold expect; rw [this]
    simp [proj, σz, trace, Fin.sum_univ_two]; norm_num
  have hB : expect (onB (proj σz 1)) s = 1 := by
    have := singlet_corr 1 (proj σz 1)
    rw [onA_one, one_mul] at this
    unfold expect; rw [this]
    simp [proj, σz, trace, Fin.sum_univ_two]; norm_num
  have hAB : expect (onA (proj σz 1) * onB (proj σz 1)) s = 0 := by
    unfold expect; rw [singlet_corr]
    simp [proj, σz, trace, Fin.sum_univ_two, Matrix.mul_apply]
  refine ⟨hAB, hA, hB, singlet_norm, ?_⟩
  rw [hAB, hA, hB]; norm_num

open QLF.JointClosure in
/-- **The locality profile.** Parameter independence holds for every state, setting and
    history; outcome independence fails on the singlet; and the singlet saturates Tsirelson's
    bound `2√2`. Composed from the theorems above and `singlet_saturates`; no new predicate. -/
theorem locality_profile :
    (∀ (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (X : M) (α : ℂ) (Y Y' : M),
        prob w ψ X α Y 1 + prob w ψ X α Y (-1) = prob w ψ X α Y' 1 + prob w ψ X α Y' (-1)) ∧
      expect (onA (proj σz 1) * onB (proj σz 1)) s * (star s ⬝ᵥ s) ≠
        expect (onA (proj σz 1)) s * expect (onB (proj σz 1)) s ∧
      (star s ⬝ᵥ (chsh (onA σz) (onA σx) (onB b0) (onB b1) *ᵥ s)).re =
        2 * Real.sqrt 2 * (star s ⬝ᵥ s).re :=
  ⟨marginal_setting_independent, singlet_outcome_dependent.2.2.2.2, singlet_saturates⟩

end QLF.PerspectiveLocality
