import QLF_PhaseRule
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_IndexedFactors — many bodies need **indexed copies** of the eight twists, not more twists

The question this settles: does a multi-body inventory need new primitive twist directions —
`^`, `2^`, `3^`, … as distinct letters? **No.** The alphabet stays `Σ₈`; what a second body needs is
a *label*, so that a token is `(factor, twist) ∈ ℕ × Σ₈` — independent **uses** of the same `^`, never
a new kind of `^`. That matches [`eight-twists-sufficiency.md`](../eight-twists-sufficiency.md): higher
dimension comes from parallel composition, not from enlarging the basis.

What indexing changes is the **algebra**, and that is where the real content is.

## Independent factors commute; flat concatenation does not

An operation on body 1 and one on body 2 act as `A ⊗ I` and `I ⊗ B`, which **commute**
(`indexed_factors_commute`). Flattened into one word they land in a single Pauli algebra where
distinct axes **anticommute** — `σy σx = −σx σy` ([`anti_yx`](QLF_BasisIndependence.lean)). So
concatenation is not a faithful model of two independent bodies: `not_all_flat_pairs_commute`
exhibits the failure with `^` and `>`.

## But the flat model is not simply wrong — the two are different sectors

A Kronecker product is a (non-zero) scalar exactly when both factors are, so **a joint closure of
independent factors requires each factor to close on its own**. That is now a theorem,
`kron_scalar_iff` in [`QLF_TensorFromClosure`](QLF_TensorFromClosure.lean), which also derives the
Kronecker form of independent bodies from interleaving invariance. In the flat model a factor may stay *open* and be
balanced by the other — and that is precisely `SharedClosure` ([`ER_EPR_QLF`](ER_EPR_QLF.lean)),
QLF's entanglement. Hence the split:

* **product sector** — both factors close alone: genuinely independent bodies, tensor-valid;
* **coupled sector** — neither closes alone, the pair does: entanglement, and it exists **only** under
  concatenation.

**`shared_closure_not_factorizable`** proves the coupled sector is non-empty in the sharpest way: the
primordial witness `^ | v` is jointly balanced while *neither* side folds to a scalar. So indexing
cannot simply replace concatenation — an interaction binding two bodies is a genuine Pauli **string**
`σ ⊗ σ`, not a product of single-factor operators. Measured in
[`census_inventory.py`](../census_inventory.py)'s factor inventory, the coupled sector is the *majority*
and grows with length: `0.750`, `0.791`, `0.804` of shared closures at lengths 2, 4, 6.

## Where the phase does factorize — and the correction that earned it

For the product sector the phase multiplies: **`fold_scalar_factorizes`**. Note the group is `μ₄`, not
`μ₂`. An open factor is *not* count-balanced, so [`balanced_phase_is_real`](QLF_BalancedPhaseReal.lean)
does not apply to it and its scalar may be `±i`; a `μ₂`-valued rule cannot express that. Asserting the
`μ₂` version is an error the inventory's checker caught — the `μ₂` restriction is a fact about
*closures*, and a **factor** of a closure needs the full group.

No axioms.
-/

namespace QLF.IndexedFactors

open QLF QLF.PhaseRule

/-- **A token is a labelled twist, not a new twist.** The alphabet stays `Σ₈`; the label says which
    independent body the operation acts on. So the many-body alphabet is `ℕ × Σ₈` — indexed copies,
    built from the same eight primitives. -/
abbrev IndexedTwist := ℕ × Twist

/-- The label of a token. -/
def factorOf (it : IndexedTwist) : ℕ := it.1

/-- The underlying twist — always one of the original eight. -/
def twistOf (it : IndexedTwist) : Twist := it.2

/-- **The alphabet does not grow.** Every indexed token's twist is one of the eight; indexing adds a
    label, never a letter. -/
theorem twistOf_mem_alphabet (it : IndexedTwist) :
    twistOf it = Twist.up ∨ twistOf it = Twist.down ∨ twistOf it = Twist.left ∨
    twistOf it = Twist.right ∨ twistOf it = Twist.slash ∨ twistOf it = Twist.backslash ∨
    twistOf it = Twist.plus ∨ twistOf it = Twist.minus := by
  rcases it with ⟨_, t⟩
  cases t
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-- Two tokens act on the same body. -/
def sameFactor (a b : IndexedTwist) : Prop := factorOf a = factorOf b

-- ==========================================
-- Independent factors commute
-- ==========================================

/-- A `2×2` operation placed on the first of two bodies. -/
noncomputable def onFirst (A : M) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) A 1

/-- A `2×2` operation placed on the second of two bodies. -/
noncomputable def onSecond (B : M) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) 1 B

/-- **Independent factors commute** — the algebraic fact that flat concatenation cannot represent.
    Both orders equal `A ⊗ B`, by multiplicativity of the Kronecker product. -/
theorem indexed_factors_commute (A B : M) :
    onFirst A * onSecond B = onSecond B * onFirst A := by
  show Matrix.kroneckerMap (· * ·) A 1 * Matrix.kroneckerMap (· * ·) 1 B
      = Matrix.kroneckerMap (· * ·) 1 B * Matrix.kroneckerMap (· * ·) A 1
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul, one_mul, mul_one]

/-- **Flattening breaks that commutation.** `^` and `>` are single twists; placed on *different*
    bodies they must commute, but concatenated into one word they anticommute. So a flat word is not a
    faithful record of two independent bodies. -/
theorem not_all_flat_pairs_commute :
    Twist.up.toMatrix * Twist.right.toMatrix ≠ Twist.right.toMatrix * Twist.up.toMatrix := by
  show σy * σx ≠ σx * σy
  rw [sigma_yx, sigma_xy]
  intro hcon
  -- read the `(0,0)` entry, where `σz` is `1`; the `(0,1)` entry is `0` on both sides
  have h : (-(Complex.I • σz)) 0 0 = (Complex.I • σz) 0 0 := by rw [hcon]
  have h2 : -Complex.I = Complex.I := by
    simpa [σz, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const] using h
  -- `-I = I` compares imaginary parts as `-1 = 1` in ℝ
  have h3 : (-Complex.I).im = Complex.I.im := congrArg Complex.im h2
  rw [Complex.neg_im, Complex.I_im] at h3
  linarith

-- ==========================================
-- The flat fold splits over a cut — always
-- ==========================================

/-- The ordered fold of a concatenation is the product of the folds. Always true, and it is what makes
    "cut a closure into two bodies" meaningful in the first place. -/
theorem twistMatrixFold_append (a b : List Twist) :
    twistMatrixFold (a ++ b) = twistMatrixFold a * twistMatrixFold b := by
  induction a with
  | nil => show twistMatrixFold b = 1 * twistMatrixFold b; rw [one_mul]
  | cons t a ih =>
      show t.toMatrix * twistMatrixFold (a ++ b) = t.toMatrix * twistMatrixFold a * twistMatrixFold b
      rw [ih, mul_assoc]

/-- **Where the phase factorizes**: if each body's history folds to a scalar, the joint scalar is the
    product of theirs. In `μ₄` — an *open* factor need not be count-balanced, so its scalar may be
    `±i` and the `μ₂` restriction of `balanced_phase_is_real` does not apply to it. -/
theorem fold_scalar_factorizes {a b : List Twist} {ca cb : ℂ}
    (ha : twistMatrixFold a = ca • (1 : M)) (hb : twistMatrixFold b = cb • (1 : M)) :
    twistMatrixFold (a ++ b) = (ca * cb) • (1 : M) := by
  rw [twistMatrixFold_append, ha, hb, smul_mul_smul', mul_one]

/-- Scalar folds commute, so within the product sector the order of two bodies is immaterial —
    the flat model and the indexed model agree exactly there. -/
theorem product_sector_order_free {a b : List Twist} {ca cb : ℂ}
    (ha : twistMatrixFold a = ca • (1 : M)) (hb : twistMatrixFold b = cb • (1 : M)) :
    twistMatrixFold (a ++ b) = twistMatrixFold (b ++ a) := by
  rw [fold_scalar_factorizes ha hb, fold_scalar_factorizes hb ha, mul_comm]

-- ==========================================
-- The coupled sector: entanglement is not of product form
-- ==========================================

/-- `σy` is not a scalar multiple of the identity — the fold of the single twist `^` is an *open*
    strand, not a closure. -/
theorem up_fold_not_scalar : ∀ c : ℂ, twistMatrixFold [Twist.up] ≠ c • (1 : M) := by
  intro c hcon
  have hfold : twistMatrixFold [Twist.up] = σy := by
    show Twist.up.toMatrix * 1 = σy
    rw [mul_one]; rfl
  rw [hfold] at hcon
  have h00 : σy 0 0 = c := by
    have := congrArg (fun N => N 0 0) hcon
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  have h01 : σy 0 1 = 0 := by
    have := congrArg (fun N => N 0 1) hcon
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  simp [σy] at h01

/-- Likewise `v`. -/
theorem down_fold_not_scalar : ∀ c : ℂ, twistMatrixFold [Twist.down] ≠ c • (1 : M) := by
  intro c hcon
  have hfold : twistMatrixFold [Twist.down] = -σy := by
    show Twist.down.toMatrix * 1 = -σy
    rw [mul_one]; rfl
  rw [hfold] at hcon
  have h01 : (-σy) 0 1 = 0 := by
    have := congrArg (fun N => N 0 1) hcon
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  simp [σy, Matrix.neg_apply] at h01

/-- The primordial pair `^ | v` closes jointly. -/
theorem up_down_balanced : countBalanced [Twist.up, Twist.down] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Entanglement is not of product form — the coupled sector is real.** The pair `^ | v` is a joint
    closure (`countBalanced`) in which **neither** body's history folds to a scalar: each is an open
    strand, closed only by the other. Because a Kronecker product is a scalar exactly when both its
    factors are, no assignment of these two histories to independent indexed bodies can reproduce this
    closure — it exists only under concatenation. So indexing the alphabet by body **cannot replace**
    joint closure; binding two bodies takes a genuine Pauli string `σ ⊗ σ`, not a product of
    single-factor operations. -/
theorem shared_closure_not_factorizable :
    countBalanced ([Twist.up] ++ [Twist.down]) ∧
    (∀ c : ℂ, twistMatrixFold [Twist.up] ≠ c • (1 : M)) ∧
    (∀ c : ℂ, twistMatrixFold [Twist.down] ≠ c • (1 : M)) :=
  ⟨up_down_balanced, up_fold_not_scalar, down_fold_not_scalar⟩

/-- The gauge pair, by contrast, **does** live in the product sector: each side folds to a scalar on
    its own, so `+ | −` survives indexing where `^ | v` does not. That is the sharp boundary between
    the two sectors. -/
theorem gauge_pair_is_product_sector :
    twistMatrixFold [Twist.plus] = (1 : ℂ) • (1 : M) ∧
    twistMatrixFold [Twist.minus] = (-1 : ℂ) • (1 : M) := by
  constructor
  · show Twist.plus.toMatrix * 1 = (1 : ℂ) • (1 : M)
    rw [mul_one]; simp [Twist.toMatrix]
  · show Twist.minus.toMatrix * 1 = (-1 : ℂ) • (1 : M)
    rw [mul_one]; simp [Twist.toMatrix, neg_smul, one_smul]

/-- **Established constructively, no axioms.** A many-body inventory does **not** need new primitive
    twists: a token is `(factor, twist) ∈ ℕ × Σ₈` (`IndexedTwist`), an indexed *use* of the same eight
    (`twistOf_mem_alphabet`). What indexing changes is the algebra — independent bodies commute
    (`indexed_factors_commute`) where a flat word puts them in one Pauli algebra and makes them
    anticommute (`not_all_flat_pairs_commute`). The two models are therefore **two sectors, not
    rivals**: where both bodies close on their own the phase simply multiplies in `μ₄`
    (`fold_scalar_factorizes`, `product_sector_order_free`) and the models agree; where neither closes
    alone but the pair does — `SharedClosure`, entanglement — the closure has **no product form at
    all** (`shared_closure_not_factorizable`, the `^ | v` witness), since a Kronecker product is scalar
    only when both factors are. The gauge pair `+ | −` shows the boundary is sharp by falling on the
    other side (`gauge_pair_is_product_sector`). **Consequence:** index the inventory, but do not let
    indexing replace concatenation — the coupled sector is the majority (`0.750`, `0.791`, `0.804` of
    shared closures at lengths 2, 4, 6, from the factor inventory) and it is exactly where entanglement
    lives. -/
theorem indexed_factors_summary : True := trivial

end QLF.IndexedFactors
