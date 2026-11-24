import QLF_JointClosure
import QLF_TensorFromClosure

/-!
# QLF_PerspectiveLocality — only local information changes local statistics

**Scope: QLF's two-body operator representation.** Every result here is about the complex
Hilbert-space representation of the twists with Born weights, and about dynamics that are
products of local twists on independent tensor factors. Interacting ZFA evolution, a dynamically
reconstructed perspective boundary, and a closure-census measure with these statistics are not
covered (issue #315).

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
* **`no_signalling`** (P8, Gate 5): the **weight identity** behind no-signalling. For any
  matrices `X`, `Y` and any `α`, `A`'s summed weight is independent of `Y`. These weights need
  not be probabilities.
* **§5, typed measurements.** For `Dichotomic` observables (Hermitian, `X² = 1`) and outcomes
  `±1`, the joint weights are genuine probabilities: real and nonnegative (`probT_nonneg`) and
  summing to the state's squared norm `⟨ψ,ψ⟩`, which every history preserves; they are normalized only for unit-norm `ψ` (`probT_sum`). Then
  `no_signalling_typed` is no-signalling as a probability statement.
* **`singlet_outcome_dependent`** (Bell audit): on the singlet with both settings `σz`,
  `P(+,+) = 0` while `P(+) = P(+) = 1/2`. **Outcome independence fails.**
  This is the *unconditional* statistics; taking the operator state itself as the complete state
  `λ` (the orthodox completeness reading), it is outcome dependence at `λ`.
* **§6, Bell relative to a complete state `λ`.** `chsh_factorizable_le`: every model with a finite
  space of complete states, `λ` distributed independently of the settings, and factorized
  responses `E(x,y|λ) = a_x(λ) b_y(λ)` with `|a|, |b| ≤ 1`, has `|CHSH| ≤ 2`.
  `no_factorizable_model`: no such model reproduces the singlet's operator correlations
  (`2√2`). So, given measurement independence, factorization at `λ` (parameter independence and
  outcome independence at `λ`, Jarrett 1984) fails for **every** finite `λ`, while operational
  parameter independence holds (`no_signalling_typed`). Which conjunct fails at a hidden `λ`
  depends on the model; with `λ` = the operator state it is outcome independence.
* **`locality_profile`**: the weight identity, the unconditional outcome dependence, and CHSH
  `2√2` (`singlet_saturates`) together.

## Scope

* The probabilities are **Born weights on the twist operator algebra**. This is a
  representation result. Finite `Λ` in §6 is a restriction of this formalization; the
  measure-theoretic Bell theorem is not formalized here. The census-level measure is tested separately in
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

lemma onA_add_aux (X Y : M) : onA X + onA Y = onA (X + Y) := by
  simp [onA, add_kronecker]

lemma onB_add_aux (X Y : M) : onB X + onB Y = onB (X + Y) := by
  simp [onB, kronecker_add]

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

/-! ## §5 Typed measurements: genuine probabilities

`proj` and `prob` above accept any matrix and any `α`, so in general `prob` is a **weight**, not a
probability; `no_signalling` is a weight identity. This section restricts to dichotomic
observables (Hermitian, squaring to `1`) and outcomes `±1`, and proves the weights are then real,
nonnegative and sum to the squared norm `⟨ψ,ψ⟩`, which the dynamics preserves (so they are probabilities for unit-norm `ψ`). -/

/-- A **dichotomic observable**: Hermitian with `X² = 1`, so its outcomes are `±1`. -/
structure Dichotomic where
  X : M
  herm : Xᴴ = X
  sq : X * X = 1

/-- The outcome sign of a Boolean outcome. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

/-- The projector for outcome `b` of a dichotomic observable. -/
def P (D : Dichotomic) (b : Bool) : M := proj D.X (sgn b)

lemma P_herm (D : Dichotomic) (b : Bool) : (P D b)ᴴ = P D b := by
  unfold P proj sgn
  cases b <;> simp [conjTranspose_add, conjTranspose_smul, D.herm]

lemma P_idem (D : Dichotomic) (b : Bool) : P D b * P D b = P D b := by
  unfold P proj sgn
  cases b <;>
  · simp only [smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, D.sq]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring

lemma P_sum (D : Dichotomic) : P D true + P D false = 1 := by
  have := proj_sum D.X
  simpa [P, sgn] using this

/-- The joint outcome event `(a, b)` as an operator. -/
def event (DA DB : Dichotomic) (a b : Bool) : Q := onA (P DA a) * onB (P DB b)

lemma event_herm (DA DB : Dichotomic) (a b : Bool) : (event DA DB a b)ᴴ = event DA DB a b := by
  unfold event
  rw [conjTranspose_mul, onA_conjTranspose, onB_conjTranspose, P_herm, P_herm, onA_onB]

lemma event_idem (DA DB : Dichotomic) (a b : Bool) :
    event DA DB a b * event DA DB a b = event DA DB a b := by
  unfold event
  calc onA (P DA a) * onB (P DB b) * (onA (P DA a) * onB (P DB b))
      = onA (P DA a) * (onB (P DB b) * onA (P DA a)) * onB (P DB b) := by simp only [mul_assoc]
    _ = onA (P DA a) * (onA (P DA a) * onB (P DB b)) * onB (P DB b) := by rw [onA_onB]
    _ = onA (P DA a * P DA a) * onB (P DB b * P DB b) := by
        rw [← onA_mul, ← onB_mul]; simp only [mul_assoc]
    _ = _ := by rw [P_idem, P_idem]

/-- The (Born) probability of the joint outcome `(a, b)` after history `w` from state `ψ`. -/
def probT (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (DA DB : Dichotomic) (a b : Bool) : ℂ :=
  expect (event DA DB a b) (jointFold w *ᵥ ψ)

open ComplexOrder in
/-- **Probabilities are real and nonnegative** (as an element of `ℂ` with its star order: zero
    imaginary part, nonnegative real part). -/
theorem probT_nonneg (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (DA DB : Dichotomic) (a b : Bool) :
    0 ≤ probT w ψ DA DB a b := by
  unfold probT
  have h : ∀ φ, expect (event DA DB a b) φ = expect 1 (event DA DB a b *ᵥ φ) := fun φ => by
    rw [expect_evolve, Matrix.mul_one, event_herm, event_idem]
  rw [h]
  unfold expect
  rw [Matrix.one_mulVec]
  exact dotProduct_star_self_nonneg _

/-- The global fold is unitary. -/
lemma jointFold_unitary (w : List Tok) : (jointFold w)ᴴ * jointFold w = 1 := by
  rw [jointFold_factorizes, conjTranspose_mul, onA_conjTranspose, onB_conjTranspose]
  set FA := twistMatrixFold (projA w)
  set FB := twistMatrixFold (projB w)
  calc onB FBᴴ * onA FAᴴ * (onA FA * onB FB)
      = onB FBᴴ * (onA (FAᴴ * FA)) * onB FB := by rw [← onA_mul]; simp only [mul_assoc]
    _ = 1 := by rw [fold_unitary, onA_one, mul_one, onB_mul, fold_unitary, onB_one]

/-- **Normalization.** The four joint weights sum to the squared norm `⟨ψ,ψ⟩`, which every history
    preserves; for a normalized state they sum to `1`. -/
theorem probT_sum (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (DA DB : Dichotomic) :
    probT w ψ DA DB true true + probT w ψ DA DB true false +
      (probT w ψ DA DB false true + probT w ψ DA DB false false) = star ψ ⬝ᵥ ψ := by
  unfold probT expect event
  simp only [← dotProduct_add, ← add_mulVec, ← mul_add]
  rw [onB_add_aux, P_sum, onB_one, mul_one, mul_one, onA_add_aux, P_sum, onA_one,
    Matrix.one_mulVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, jointFold_unitary,
    Matrix.one_mulVec]

/-- **No signalling, as a probability statement.** For typed measurements, `A`'s marginal is
    independent of `B`'s observable. -/
theorem no_signalling_typed (w : List Tok) (ψ : Fin 2 × Fin 2 → ℂ) (DA DB DB' : Dichotomic)
    (a : Bool) :
    probT w ψ DA DB a true + probT w ψ DA DB a false =
      probT w ψ DA DB' a true + probT w ψ DA DB' a false := by
  unfold probT expect event
  simp only [← dotProduct_add, ← add_mulVec, ← mul_add]
  rw [onB_add_aux, onB_add_aux, P_sum, P_sum]

/-! ## §6 Bell factorization relative to a complete state `λ`

Bell's factorization is conditional on a complete state `λ`: `E(x, y | λ) = a_x(λ) · b_y(λ)`,
with `λ` distributed independently of the settings (measurement independence). This section
proves the CHSH bound for every such model with a **finite** space of complete states, and
that no such model reproduces the singlet's operator correlations. So, given measurement
independence, factorization relative to `λ` fails for every choice of `λ`; operationally,
parameter independence holds (`no_signalling_typed`). -/

/-- **Bell–CHSH for factorizable models.** Response functions bounded by `1`, weights a
    probability distribution: the CHSH combination is at most `2` in absolute value. -/
theorem chsh_factorizable_le {Λ : Type} [Fintype Λ] (p : Λ → ℝ) (hp : ∀ l, 0 ≤ p l)
    (hs : ∑ l, p l = 1) (a0 a1 b0 b1 : Λ → ℝ)
    (ha0 : ∀ l, |a0 l| ≤ 1) (ha1 : ∀ l, |a1 l| ≤ 1) (hb0 : ∀ l, |b0 l| ≤ 1)
    (hb1 : ∀ l, |b1 l| ≤ 1) :
    |∑ l, p l * (a0 l * b0 l + a0 l * b1 l + a1 l * b0 l - a1 l * b1 l)| ≤ 2 := by
  have key : ∀ l, |a0 l * b0 l + a0 l * b1 l + a1 l * b0 l - a1 l * b1 l| ≤ 2 := by
    intro l
    have e : a0 l * b0 l + a0 l * b1 l + a1 l * b0 l - a1 l * b1 l =
        a0 l * (b0 l + b1 l) + a1 l * (b0 l - b1 l) := by ring
    rw [e]
    have h1 : |a0 l * (b0 l + b1 l)| ≤ |b0 l + b1 l| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (ha0 l)
    have h2 : |a1 l * (b0 l - b1 l)| ≤ |b0 l - b1 l| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (ha1 l)
    have h3 : |b0 l + b1 l| + |b0 l - b1 l| ≤ 2 := by
      have := hb0 l; have := hb1 l
      rw [abs_le] at *
      rcases abs_cases (b0 l + b1 l) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases (b0 l - b1 l) with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h, h'] <;> linarith
    calc _ ≤ |a0 l * (b0 l + b1 l)| + |a1 l * (b0 l - b1 l)| := abs_add_le _ _
      _ ≤ 2 := by linarith
  calc |∑ l, p l * _| ≤ ∑ l, |p l * (a0 l * b0 l + a0 l * b1 l + a1 l * b0 l - a1 l * b1 l)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, p l * 2 := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_mul, abs_of_nonneg (hp l)]
        exact mul_le_mul_of_nonneg_left (key l) (hp l)
    _ = 2 := by rw [← Finset.sum_mul, hs, one_mul]

open QLF.JointClosure in
/-- The singlet's normalized correlation for observables `X` on `A` and `Y` on `B`. -/
def singletCorr (X Y : M) : ℝ := (expect (onA X * onB Y) s).re / 2

open QLF.JointClosure in
/-- **No factorizable model reproduces the singlet.** There is no finite space of complete
    states `λ`, distributed independently of the settings, with local responses bounded by `1`,
    whose factorized correlations equal the singlet's for `σz`, `σx` on `A` and `b0`, `b1` on
    `B`. -/
theorem no_factorizable_model :
    ¬ ∃ (Λ : Type) (_ : Fintype Λ) (p : Λ → ℝ) (a0 a1 b0' b1' : Λ → ℝ),
      (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1 ∧
      (∀ l, |a0 l| ≤ 1) ∧ (∀ l, |a1 l| ≤ 1) ∧ (∀ l, |b0' l| ≤ 1) ∧ (∀ l, |b1' l| ≤ 1) ∧
      ∑ l, p l * (a0 l * b0' l) = singletCorr σz b0 ∧
      ∑ l, p l * (a0 l * b1' l) = singletCorr σz b1 ∧
      ∑ l, p l * (a1 l * b0' l) = singletCorr σx b0 ∧
      ∑ l, p l * (a1 l * b1' l) = singletCorr σx b1 := by
  rintro ⟨Λ, _, p, a0, a1, b0', b1', hp, hs, ha0, ha1, hb0, hb1, e00, e01, e10, e11⟩
  have hb := chsh_factorizable_le p hp hs a0 a1 b0' b1' ha0 ha1 hb0 hb1
  have hsum : ∑ l, p l * (a0 l * b0' l + a0 l * b1' l + a1 l * b0' l - a1 l * b1' l) =
      singletCorr σz b0 + singletCorr σz b1 + singletCorr σx b0 - singletCorr σx b1 := by
    rw [← e00, ← e01, ← e10, ← e11, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have hq : singletCorr σz b0 + singletCorr σz b1 + singletCorr σx b0 - singletCorr σx b1 =
      2 * Real.sqrt 2 := by
    have h := singlet_saturates
    rw [singlet_norm] at h
    simp only [chsh, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, Complex.add_re,
      Complex.sub_re] at h
    unfold singletCorr expect
    norm_num at h
    linarith
  rw [hsum, hq, abs_of_pos (by positivity)] at hb
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end QLF.PerspectiveLocality
