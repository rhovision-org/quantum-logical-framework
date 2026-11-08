import QLF_IndexedFactors
import QLF_JointClosure
import QLF_ClosureUnitarity
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_TensorFromClosure — the tensor product, derived from closure composition

[`QLF_EntanglementPrimacy`](QLF_EntanglementPrimacy.lean) left one gap open: the two-body reading
of a pair used the Kronecker product `A ⊗ I`, `I ⊗ B` as given, so *deriving the tensor product
itself stayed open*. This module closes that gap for two bodies. The tensor product is not
assumed anywhere below; it is the output.

## What is assumed

Only what a "body" means in QLF:

* **Each body is a QLF body.** Its histories act through their own fold, so the joint fold sees body
  `A` through an algebra map `ρA : M → J` and body `B` through `ρB : M → J`, for an arbitrary
  `ℂ`-algebra `J` of joint operations. `M` is the `2 × 2` twist algebra. Nothing says what `J` is.
* **The joint fold is multiplicative.** A two-body history is a word of labelled twists
  (`Tok = Bool × Twist`, the [`IndexedFactors`](QLF_IndexedFactors.lean) token with two labels), and
  its fold is the ordered product of its letters (`cfold`), as for one body.
* **Distinct bodies have no relative order.** Swapping two adjacent events of *different* bodies
  (`Step`) does not change the joint fold. This is what makes two bodies two bodies: nothing fixes
  which of two separate events came first.

## What is derived (no axioms)

1. **The composite is the pair (`same_composite_iff`).** Two-body words are interleaving-equivalent
   exactly when they have the same history on each body. The composite history monoid of two
   independent bodies is `H × H`, not the free monoid on both alphabets.
2. **Independence is commutation (`interleaving_invariant_iff`).** The joint fold ignores
   interleaving exactly when every twist on `A` commutes with every twist on `B`. Commutation is
   *derived* from "no relative order", not posited.
3. **The joint fold is a product of the two body folds (`cfold_eq`):**
   `cfold w = ρA (fold w_A) · ρB (fold w_B)`.
4. **The universal property (`composite_is_tensor`).** There is exactly one algebra map
   `Ψ : M ⊗[ℂ] M → J` with `Ψ (X ⊗ 1) = ρA X` and `Ψ (1 ⊗ Y) = ρB Y`, and every joint fold is
   `Ψ (fold w_A ⊗ₜ fold w_B)`. So **every** independent composition of two QLF bodies, in whatever
   joint algebra, factors through the tensor product `M ⊗ M`. That is the characterization of the
   tensor product, and here it is a consequence of closure composition.
5. **The twist realization is the tensor product (`tensorEquiv`).** Realized on four-component
   states (`onA`, `onB`), the factoring map `M ⊗[ℂ] M → Mat₄(ℂ)` is an isomorphism: it is onto
   (every `4 × 4` matrix is a combination of composite elementary moves, `kronLift_surjective`), and
   both sides have dimension `16 = 4 · 4`. The joint algebra of two qubit bodies is exactly
   `M ⊗ M`, no bigger and no smaller. The flat model fails the premise
   (`flat_not_independent`): one undivided word puts both bodies in one Pauli algebra, where `^`
   and `>` anticommute.
6. **Faithful in every joint algebra (`composite_faithful`).** In any non-trivial `J`, the factoring
   map `M ⊗ M → J` is injective: `M ⊗ M ≅ Mat₄(ℂ)` is simple (Mathlib's `IsSimpleRing.matrix`), so a
   ring map out of it has zero kernel. Every independent composite contains an exact copy of the
   tensor product, and its joint fold remembers both bodies (`joint_fold_determines_pair`).
7. **The state space (`state_cyclic`, `two_body_states_irreducible`).** Every non-zero state of
   `ℂ² ⊗ ℂ² = ℂ⁴` is sent to every other by some joint operator, so a subspace invariant under the
   derived composite and holding one non-zero state is everything. The tensor-product state space
   is irreducible for the composite of two independent bodies.
8. **Any number of bodies (`n_interleaving_invariant_iff`, `nstep_proj`, `ncfold_eq`).** With
   labels from any type, interleaving invariance holds exactly when every pair of distinct bodies
   commutes, interleaving preserves each body's history, and the joint fold is the ordered product
   of the bodies' own folds, `∏ᵢ ρᵢ(fold wᵢ)`. Two `N`-body words are interleavings of each other
   exactly when they agree on every body (`n_same_composite_iff`), so the composite history monoid
   of `N` independent bodies is `H^N`.
9. **The `N`-fold tensor object (`nTensorLift`, `nTensorLift_unique`, `n_composite_is_tensor`).**
   For bodies labelled `0, …, N−1`, the ordered product of commuting body actions is an algebra map
   out of Mathlib's `⨂[ℂ] i, M`, it is the only one restricting to each body on its own slot, and
   every joint fold is that map applied to `fold w₀ ⊗ ⋯ ⊗ fold w_{N−1}`.

## The two sectors

* **Product sector (`kron_scalar_iff`, `independent_closure_factors`).** A Kronecker product is a
  non-zero scalar exactly when both factors are scalars. So a joint closure of independent bodies is
  always two separate closures. [`IndexedFactors`](QLF_IndexedFactors.lean) stated this in prose;
  it is now a theorem.
* **Coupled sector (`open_factor_never_closes_jointly`, `shared_closure_not_independent`).** If one
  body's history is open, no history on the other body closes it as an independent factor. The
  primordial shared closure `^ | v` closes as one word and **cannot** close as a product. Shared
  closure is not a property of independent factors.
* **Entanglement lives inside the tensor space (`product_never_joint_closure`,
  `singlet_not_product`, `tensor_space_sectors`).** The state space of the derived composite is
  `ℂ² ⊗ ℂ²`. No non-zero product vector `u ⊗ v` is a joint closure, while the singlet, which is in
  the same space, is one, and it is not a product.

So the right sentence is **not** "tensor products cannot represent entanglement". They do: the singlet
is a vector of the tensor space. The precise claim is: **a product of independently closed factors
cannot produce a shared closure.** Closure composition is primitive; the tensor product is the
representation of its factorized limit, and the entangled vectors are the part of that
representation that no factorization reaches.

## What is still NOT proved

1. **Uniqueness of the state space.** `two_body_states_irreducible` proves `ℂ² ⊗ ℂ² = ℂ⁴` is an
   irreducible module of the derived composite. That every module of `Mat₄(ℂ)` is a sum of copies of
   it (so `ℂ⁴` is the only irreducible one) is classical Wedderburn theory, not formalized here.
2. **The rung-6 reading.** The map from a flat pair `[t, t†]` to the joint action of its axis on two
   sites ([`EntanglementPrimacy`](QLF_EntanglementPrimacy.lean), rung 6) is still a reading. What is
   now derived is the space it lands in.
3. **`N`-body faithfulness and isomorphism.** Point 9 gives the factoring map out of `⨂ᵢ M`. That
   it is injective, and an isomorphism onto `Mat_{2^N}(ℂ)` for the twist realization, is proved
   only for `N = 2` (`composite_faithful`, `tensorEquiv`).

**Credit.** The universal property of the tensor product of algebras is standard (Mathlib's
`Algebra.TensorProduct.lift`). Deriving the composite of independent systems from local structure is
the operational-reconstruction programme: local tomography in Hardy, *Quantum theory from five
reasonable axioms* (arXiv:quant-ph/0101012), and Chiribella, D'Ariano and Perinotti, *Phys. Rev. A*
**84**, 012311 (2011). The step specific to QLF is that commutation of distinct bodies follows from
interleaving invariance of the fold. The trace monoid of commuting letters is Cartier and Foata's
(1969). Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.TensorFromClosure

open QLF QLF.PhaseRule Matrix
open scoped Kronecker TensorProduct

-- ==========================================
-- §1. Two-body histories and their interleavings
-- ==========================================

/-- A two-body token: a twist labelled by its body (`false` = body `A`, `true` = body `B`). -/
abbrev Tok := Bool × Twist

/-- Body `A`'s history inside a two-body word. -/
def projA : List Tok → List Twist
  | [] => []
  | (false, t) :: w => t :: projA w
  | (true, _) :: w => projA w

/-- Body `B`'s history inside a two-body word. -/
def projB : List Tok → List Twist
  | [] => []
  | (false, _) :: w => projB w
  | (true, t) :: w => t :: projB w

@[simp] lemma projA_nil : projA [] = [] := rfl
@[simp] lemma projB_nil : projB [] = [] := rfl
@[simp] lemma projA_consA (t : Twist) (w : List Tok) : projA ((false, t) :: w) = t :: projA w := rfl
@[simp] lemma projA_consB (t : Twist) (w : List Tok) : projA ((true, t) :: w) = projA w := rfl
@[simp] lemma projB_consA (t : Twist) (w : List Tok) : projB ((false, t) :: w) = projB w := rfl
@[simp] lemma projB_consB (t : Twist) (w : List Tok) : projB ((true, t) :: w) = t :: projB w := rfl

/-- **One interleaving move**: swap two adjacent events of *different* bodies, anywhere in the word.
    Nothing fixes which of two separate bodies' events came first. -/
inductive Step : List Tok → List Tok → Prop
  | swap (x y : Tok) (v : List Tok) (h : x.1 ≠ y.1) : Step (x :: y :: v) (y :: x :: v)
  | cons (z : Tok) {w w' : List Tok} : Step w w' → Step (z :: w) (z :: w')

theorem Step.symm {w w' : List Tok} (h : Step w w') : Step w' w := by
  induction h with
  | swap x y v h => exact Step.swap y x v (Ne.symm h)
  | cons z _ ih => exact Step.cons z ih

/-- An interleaving move changes neither body's history. -/
theorem step_proj {w w' : List Tok} (h : Step w w') :
    projA w = projA w' ∧ projB w = projB w' := by
  induction h with
  | swap x y v h =>
      rcases x with ⟨b₁, s⟩
      rcases y with ⟨b₂, t⟩
      cases b₁ <;> cases b₂
      · exact absurd rfl h
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact absurd rfl h
  | cons z _ ih =>
      rcases z with ⟨b, t⟩
      cases b <;> simp [ih.1, ih.2]

/-- Interleaving moves lift under a common first event. -/
theorem rtg_cons (z : Tok) {w w' : List Tok} (h : Relation.ReflTransGen Step w w') :
    Relation.ReflTransGen Step (z :: w) (z :: w') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (Step.cons z hbc)

theorem rtg_symm {w w' : List Tok} (h : Relation.ReflTransGen Step w w') :
    Relation.ReflTransGen Step w' w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (Step.symm hbc) ih

/-- Label a one-body history as body `A`. -/
def tagA (a : List Twist) : List Tok := a.map (fun t => (false, t))
/-- Label a one-body history as body `B`. -/
def tagB (b : List Twist) : List Tok := b.map (fun t => (true, t))

/-- A `B` event passes freely through any run of `A` events. -/
theorem pass (t : Twist) (a : List Twist) (r : List Tok) :
    Relation.ReflTransGen Step ((true, t) :: (tagA a ++ r)) (tagA a ++ (true, t) :: r) := by
  induction a with
  | nil => exact Relation.ReflTransGen.refl
  | cons s a ih =>
      show Relation.ReflTransGen Step ((true, t) :: (false, s) :: (tagA a ++ r))
        ((false, s) :: (tagA a ++ (true, t) :: r))
      exact Relation.ReflTransGen.head (Step.swap _ _ _ (by simp)) (rtg_cons _ ih)

/-- **Normal form**: every two-body word is an interleaving of "all of `A`, then all of `B`". -/
theorem to_normal (w : List Tok) :
    Relation.ReflTransGen Step w (tagA (projA w) ++ tagB (projB w)) := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons x w ih =>
      rcases x with ⟨b, t⟩
      cases b
      · rw [projA_consA, projB_consA]
        exact rtg_cons _ ih
      · rw [projA_consB, projB_consB]
        show Relation.ReflTransGen Step ((true, t) :: w)
          (tagA (projA w) ++ (true, t) :: tagB (projB w))
        exact (rtg_cons _ ih).trans (pass t _ _)

theorem projA_normal (a b : List Twist) : projA (tagA a ++ tagB b) = a := by
  induction a with
  | nil =>
      induction b with
      | nil => rfl
      | cons t b ih => exact ih
  | cons s a ih => exact congrArg (s :: ·) ih

theorem projB_normal (a b : List Twist) : projB (tagA a ++ tagB b) = b := by
  induction a with
  | nil =>
      induction b with
      | nil => rfl
      | cons t b ih => exact congrArg (t :: ·) ih
  | cons s a ih => exact ih

/-- **The composite of two independent bodies is the pair of their histories.** Two two-body words
    are interleavings of each other exactly when they agree on each body. So the composite history
    monoid is `H × H`. -/
theorem same_composite_iff (w w' : List Tok) :
    Relation.ReflTransGen Step w w' ↔ (projA w = projA w' ∧ projB w = projB w') := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨rfl, rfl⟩
    | tail _ hbc ih => exact ⟨ih.1.trans (step_proj hbc).1, ih.2.trans (step_proj hbc).2⟩
  · rintro ⟨hA, hB⟩
    have h1 := to_normal w
    have h2 := rtg_symm (to_normal w')
    rw [hA, hB] at h1
    exact h1.trans h2

-- ==========================================
-- §2. The joint fold, in an arbitrary joint algebra
-- ==========================================

section Abstract

variable {J : Type*} [Ring J] [Algebra ℂ J] (ρA ρB : M →ₐ[ℂ] J)

/-- One event of the joint fold: a twist acts through its own body's map. -/
noncomputable def letter : Tok → J
  | (false, t) => ρA t.toMatrix
  | (true, t) => ρB t.toMatrix

/-- **The joint fold** of a two-body word: the ordered product of its events. -/
noncomputable def cfold : List Tok → J
  | [] => 1
  | x :: w => letter ρA ρB x * cfold w

/-- **Independence is commutation.** The joint fold ignores the interleaving of the two bodies
    exactly when every twist on `A` commutes with every twist on `B`. -/
theorem interleaving_invariant_iff :
    (∀ w w', Step w w' → cfold ρA ρB w = cfold ρA ρB w') ↔
      ∀ s t : Twist, Commute (ρA s.toMatrix) (ρB t.toMatrix) := by
  constructor
  · intro h s t
    have e := h _ _ (Step.swap (false, s) (true, t) [] (by simp))
    show ρA s.toMatrix * ρB t.toMatrix = ρB t.toMatrix * ρA s.toMatrix
    have e' : ρA s.toMatrix * (ρB t.toMatrix * 1) = ρB t.toMatrix * (ρA s.toMatrix * 1) := e
    rwa [mul_one, mul_one] at e'
  · intro hc w w' hs
    induction hs with
    | swap x y v h =>
        rcases x with ⟨b₁, s⟩
        rcases y with ⟨b₂, t⟩
        cases b₁ <;> cases b₂
        · exact absurd rfl h
        · show ρA s.toMatrix * (ρB t.toMatrix * cfold ρA ρB v)
              = ρB t.toMatrix * (ρA s.toMatrix * cfold ρA ρB v)
          rw [← mul_assoc, (hc s t).eq, mul_assoc]
        · show ρB s.toMatrix * (ρA t.toMatrix * cfold ρA ρB v)
              = ρA t.toMatrix * (ρB s.toMatrix * cfold ρA ρB v)
          rw [← mul_assoc, ← (hc t s).eq, mul_assoc]
        · exact absurd rfl h
    | cons z _ ih =>
        show letter ρA ρB z * cfold ρA ρB _ = letter ρA ρB z * cfold ρA ρB _
        rw [ih]

/-- A body-`A` fold commutes with every body-`B` twist, given letter commutation. -/
theorem commute_fold (hc : ∀ s t : Twist, Commute (ρA s.toMatrix) (ρB t.toMatrix))
    (a : List Twist) (t : Twist) : Commute (ρA (twistMatrixFold a)) (ρB t.toMatrix) := by
  induction a with
  | nil =>
      show Commute (ρA 1) (ρB t.toMatrix)
      rw [map_one]; exact Commute.one_left _
  | cons s a ih =>
      show Commute (ρA (s.toMatrix * twistMatrixFold a)) (ρB t.toMatrix)
      rw [map_mul]; exact (hc s t).mul_left ih

/-- **The joint fold is the product of the two body folds.** -/
theorem cfold_eq (hc : ∀ s t : Twist, Commute (ρA s.toMatrix) (ρB t.toMatrix)) (w : List Tok) :
    cfold ρA ρB w = ρA (twistMatrixFold (projA w)) * ρB (twistMatrixFold (projB w)) := by
  induction w with
  | nil =>
      show (1 : J) = ρA 1 * ρB 1
      rw [map_one, map_one, mul_one]
  | cons x w ih =>
      rcases x with ⟨b, t⟩
      cases b
      · show ρA t.toMatrix * cfold ρA ρB w
            = ρA (t.toMatrix * twistMatrixFold (projA w)) * ρB (twistMatrixFold (projB w))
        rw [ih, map_mul, mul_assoc]
      · show ρB t.toMatrix * cfold ρA ρB w
            = ρA (twistMatrixFold (projA w)) * ρB (t.toMatrix * twistMatrixFold (projB w))
        rw [ih, map_mul, ← mul_assoc, ← (commute_fold ρA ρB hc (projA w) t).eq, mul_assoc]

end Abstract

-- ==========================================
-- §3. The twists span the one-body algebra
-- ==========================================

/-- The elementary `2 × 2` matrix with a single `1` at `(i, k)`. -/
def E (i k : Fin 2) : M := Matrix.of fun a c => if a = i ∧ c = k then 1 else 0

/-- Every one-body operator is a combination of the four elementary moves. -/
theorem decomp_E (X : M) :
    X = X 0 0 • E 0 0 + X 0 1 • E 0 1 + X 1 0 • E 1 0 + X 1 1 • E 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E]

theorem E00_twists : E 0 0 = (1 / 2 : ℂ) • Twist.plus.toMatrix + (1 / 2 : ℂ) • Twist.slash.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, Twist.toMatrix, σz]

theorem E11_twists :
    E 1 1 = (1 / 2 : ℂ) • Twist.plus.toMatrix + (-1 / 2 : ℂ) • Twist.slash.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, Twist.toMatrix, σz]

theorem E01_twists :
    E 0 1 = (1 / 2 : ℂ) • Twist.right.toMatrix + (Complex.I / 2) • Twist.up.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, Twist.toMatrix, σx, σy] <;>
    first
    | linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
    | linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I

theorem E10_twists :
    E 1 0 = (1 / 2 : ℂ) • Twist.right.toMatrix + (-Complex.I / 2) • Twist.up.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, Twist.toMatrix, σx, σy] <;>
    first
    | linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
    | linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I

section Extend

variable {J : Type*} [Ring J] [Algebra ℂ J]

private lemma comm_comb_left {u v w : J} (a b : ℂ) (hu : Commute u w) (hv : Commute v w) :
    Commute (a • u + b • v) w :=
  (hu.smul_left a).add_left (hv.smul_left b)

private lemma comm_comb4_left {u₁ u₂ u₃ u₄ w : J} (a b c d : ℂ) (h₁ : Commute u₁ w)
    (h₂ : Commute u₂ w) (h₃ : Commute u₃ w) (h₄ : Commute u₄ w) :
    Commute (a • u₁ + b • u₂ + c • u₃ + d • u₄) w :=
  (((h₁.smul_left a).add_left (h₂.smul_left b)).add_left (h₃.smul_left c)).add_left
    (h₄.smul_left d)

/-- Commutation with every twist extends to commutation with every operator, by linearity. -/
theorem commute_of_twists (ρ : M →ₐ[ℂ] J) (w : J) (h : ∀ t : Twist, Commute (ρ t.toMatrix) w)
    (X : M) : Commute (ρ X) w := by
  have h00 : Commute (ρ (E 0 0)) w := by
    rw [E00_twists, map_add, map_smul, map_smul]; exact comm_comb_left _ _ (h _) (h _)
  have h01 : Commute (ρ (E 0 1)) w := by
    rw [E01_twists, map_add, map_smul, map_smul]; exact comm_comb_left _ _ (h _) (h _)
  have h10 : Commute (ρ (E 1 0)) w := by
    rw [E10_twists, map_add, map_smul, map_smul]; exact comm_comb_left _ _ (h _) (h _)
  have h11 : Commute (ρ (E 1 1)) w := by
    rw [E11_twists, map_add, map_smul, map_smul]; exact comm_comb_left _ _ (h _) (h _)
  rw [decomp_E X, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  exact comm_comb4_left _ _ _ _ h00 h01 h10 h11

/-- **Letter commutation is full commutation**: if every twist on `A` commutes with every twist on
    `B`, the two bodies' whole operator algebras commute. -/
theorem commute_all (ρA ρB : M →ₐ[ℂ] J)
    (hc : ∀ s t : Twist, Commute (ρA s.toMatrix) (ρB t.toMatrix)) (X Y : M) :
    Commute (ρA X) (ρB Y) := by
  have hY : ∀ t : Twist, Commute (ρA X) (ρB t.toMatrix) := fun t =>
    commute_of_twists ρA _ (fun s => hc s t) X
  exact (commute_of_twists ρB (ρA X) (fun t => (hY t).symm) Y).symm

-- ==========================================
-- §4. The universal property: every independent composite factors through M ⊗ M
-- ==========================================

/-- **The tensor product, derived.** Let two QLF bodies act in any joint algebra `J`, with a joint
    fold that ignores interleaving of their events. Then there is an algebra map
    `Ψ : M ⊗[ℂ] M → J` through which every joint fold factors,
    `cfold w = Ψ (fold w_A ⊗ₜ fold w_B)`, and it is the **only** algebra map extending the two
    bodies' own maps. -/
theorem composite_is_tensor (ρA ρB : M →ₐ[ℂ] J)
    (hinv : ∀ w w', Step w w' → cfold ρA ρB w = cfold ρA ρB w') :
    ∃ Ψ : M ⊗[ℂ] M →ₐ[ℂ] J,
      (∀ w, cfold ρA ρB w = Ψ (twistMatrixFold (projA w) ⊗ₜ twistMatrixFold (projB w))) ∧
      (∀ X, Ψ (X ⊗ₜ 1) = ρA X) ∧ (∀ Y, Ψ (1 ⊗ₜ Y) = ρB Y) ∧
      ∀ Ψ' : M ⊗[ℂ] M →ₐ[ℂ] J, (∀ X, Ψ' (X ⊗ₜ 1) = ρA X) → (∀ Y, Ψ' (1 ⊗ₜ Y) = ρB Y) →
        Ψ' = Ψ := by
  have hc := (interleaving_invariant_iff ρA ρB).1 hinv
  refine ⟨Algebra.TensorProduct.lift ρA ρB (commute_all ρA ρB hc), ?_, ?_, ?_, ?_⟩
  · intro w
    rw [Algebra.TensorProduct.lift_tmul, cfold_eq ρA ρB hc]
  · intro X
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · intro Y
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  · intro Ψ' hA hB
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul X Y =>
        have hsplit : X ⊗ₜ[ℂ] Y = (X ⊗ₜ[ℂ] (1 : M)) * ((1 : M) ⊗ₜ[ℂ] Y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hsplit, map_mul, hA, hB, map_mul, Algebra.TensorProduct.lift_tmul,
          Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end Extend

-- ==========================================
-- §5. The twist realization: M ⊗ M ≅ Mat₄(ℂ)
-- ==========================================

open QLF.Tsirelson in
/-- Body `A` acting on four-component states. -/
noncomputable def embA : M →ₐ[ℂ] Q where
  toFun := onA
  map_one' := onA_one
  map_mul' X Y := (onA_mul X Y).symm
  map_zero' := by simp [onA]
  map_add' X Y := by simp [onA, Matrix.add_kronecker]
  commutes' c := by
    simp [onA, Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker]

open QLF.Tsirelson in
/-- Body `B` acting on four-component states. -/
noncomputable def embB : M →ₐ[ℂ] Q where
  toFun := onB
  map_one' := onB_one
  map_mul' X Y := (onB_mul X Y).symm
  map_zero' := by simp [onB]
  map_add' X Y := by simp [onB, Matrix.kronecker_add]
  commutes' c := by
    simp [onB, Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul]

lemma embA_apply (X : M) : embA X = QLF.Tsirelson.onA X := rfl
lemma embB_apply (Y : M) : embB Y = QLF.Tsirelson.onB Y := rfl

/-- The two embedded bodies commute (`indexed_factors_commute`'s content). -/
theorem emb_commute (X Y : M) : Commute (embA X) (embB Y) := QLF.Tsirelson.onA_onB X Y

lemma onA_mul_onB (X Y : M) : QLF.Tsirelson.onA X * QLF.Tsirelson.onB Y = X ⊗ₖ Y := by
  rw [QLF.Tsirelson.onA, QLF.Tsirelson.onB, ← Matrix.mul_kronecker_mul, mul_one, one_mul]

/-- The factoring map of the twist realization. -/
noncomputable def kronLift : M ⊗[ℂ] M →ₐ[ℂ] QLF.Tsirelson.Q :=
  Algebra.TensorProduct.lift embA embB emb_commute

theorem kronLift_tmul (X Y : M) : kronLift (X ⊗ₜ Y) = X ⊗ₖ Y := by
  rw [kronLift, Algebra.TensorProduct.lift_tmul, embA_apply, embB_apply, onA_mul_onB]

/-- **Onto**: every `4 × 4` operator is a combination of composite elementary moves. -/
theorem kronLift_surjective : Function.Surjective kronLift := by
  intro X
  refine ⟨∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
    X (i, j) (k, l) • (E i k ⊗ₜ[ℂ] E j l), ?_⟩
  simp only [map_sum, map_smul, kronLift_tmul]
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, E, Fin.sum_univ_two]

/-- **The joint algebra of two twist bodies is exactly the tensor product.** The factoring map
    `M ⊗[ℂ] M → Mat₄(ℂ)` is bijective: onto by `kronLift_surjective`, and both sides have dimension
    `16 = 4 · 4`. -/
theorem kronLift_bijective : Function.Bijective kronLift := by
  have h1 : Module.finrank ℂ (M ⊗[ℂ] M) = 16 := by
    simp [Module.finrank_tensorProduct, Module.finrank_matrix]
  have h2 : Module.finrank ℂ QLF.Tsirelson.Q = 16 := by
    simp [Module.finrank_matrix]
  have hs : Function.Surjective kronLift.toLinearMap := kronLift_surjective
  have hi : Function.Injective kronLift.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h1.trans h2.symm)).2 hs
  exact ⟨hi, kronLift_surjective⟩

/-- `M ⊗[ℂ] M ≃ Mat₄(ℂ)`, as algebras. -/
noncomputable def tensorEquiv : M ⊗[ℂ] M ≃ₐ[ℂ] QLF.Tsirelson.Q :=
  AlgEquiv.ofBijective kronLift kronLift_bijective

/-- In the twist realization the joint fold is the Kronecker product of the body folds. -/
theorem twist_cfold (w : List Tok) :
    cfold embA embB w = twistMatrixFold (projA w) ⊗ₖ twistMatrixFold (projB w) := by
  rw [cfold_eq embA embB (fun s t => emb_commute _ _), embA_apply, embB_apply, onA_mul_onB]

/-- **The flat model is not a composite of independent bodies.** Reading both bodies in one Pauli
    algebra (`ρA = ρB = id`), `^` and `>` do not commute, so the flat fold depends on the
    interleaving. That is where shared closures live (§6). -/
theorem flat_not_independent :
    ¬ ∀ s t : Twist, Commute ((AlgHom.id ℂ M) s.toMatrix) ((AlgHom.id ℂ M) t.toMatrix) := by
  intro h
  exact QLF.IndexedFactors.not_all_flat_pairs_commute (h Twist.up Twist.right)

-- ==========================================
-- §5b. Faithfulness in every joint algebra
-- ==========================================

section Faithful

variable {J : Type*} [Ring J] [Algebra ℂ J] [Nontrivial J]

/-- **Every independent composite is faithful.** In any non-trivial joint algebra `J`, the unique
    factoring map `Ψ : M ⊗[ℂ] M → J` of `composite_is_tensor` is injective. Reason: `M ⊗ M ≅ Mat₄(ℂ)`
    (`tensorEquiv`), a matrix ring over a field is simple, and a ring map out of a simple ring into a
    non-trivial ring has zero kernel. So no independent composition of two QLF bodies loses
    information: its joint algebra contains an exact copy of the tensor product. -/
theorem composite_faithful (ρA ρB : M →ₐ[ℂ] J)
    (hc : ∀ s t : Twist, Commute (ρA s.toMatrix) (ρB t.toMatrix)) :
    Function.Injective (Algebra.TensorProduct.lift ρA ρB (commute_all ρA ρB hc)) := by
  set Ψ := Algebra.TensorProduct.lift ρA ρB (commute_all ρA ρB hc)
  let Ψ' : QLF.Tsirelson.Q →ₐ[ℂ] J := Ψ.comp (tensorEquiv.symm : QLF.Tsirelson.Q →ₐ[ℂ] M ⊗[ℂ] M)
  have hφ : Function.Injective (Ψ'.toRingHom) := RingHom.injective _
  have key : ∀ z, Ψ' (tensorEquiv z) = Ψ z := fun z => by
    simp [Ψ', AlgHom.comp_apply]
  intro x y hxy
  apply tensorEquiv.injective
  apply hφ
  show Ψ' (tensorEquiv x) = Ψ' (tensorEquiv y)
  rw [key, key]
  exact hxy

/-- **The joint fold remembers both bodies.** In any non-trivial joint algebra, two two-body words
    with the same joint fold have the same pair of body folds in `M ⊗ M`. -/
theorem joint_fold_determines_pair (ρA ρB : M →ₐ[ℂ] J)
    (hinv : ∀ w w', Step w w' → cfold ρA ρB w = cfold ρA ρB w') (w w' : List Tok)
    (h : cfold ρA ρB w = cfold ρA ρB w') :
    twistMatrixFold (projA w) ⊗ₜ[ℂ] twistMatrixFold (projB w) =
      twistMatrixFold (projA w') ⊗ₜ[ℂ] twistMatrixFold (projB w') := by
  have hc := (interleaving_invariant_iff ρA ρB).1 hinv
  apply composite_faithful ρA ρB hc
  rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, ← cfold_eq ρA ρB hc,
    ← cfold_eq ρA ρB hc]
  exact h

end Faithful

-- ==========================================
-- §5c. States: ℂ² ⊗ ℂ² is irreducible for the derived composite
-- ==========================================

/-- **Every non-zero two-body state is cyclic.** For any non-zero `v ∈ ℂ⁴` and any target `u`,
    some joint operator sends `v` to `u`. -/
theorem state_cyclic (v u : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0) :
    ∃ X : QLF.Tsirelson.Q, X *ᵥ v = u := by
  obtain ⟨q, hq⟩ : ∃ q, v q ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  refine ⟨Matrix.of fun a b => if b = q then u a / v q else 0, ?_⟩
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  rw [Fintype.sum_eq_single q (fun b hb => by simp [hb]), if_pos rfl]
  exact div_mul_cancel₀ _ hq

/-- **The two-body state space is irreducible.** A subspace of `ℂ² ⊗ ℂ² = ℂ⁴` that every joint
    operator maps into itself, and that holds one non-zero state, is the whole space. Every joint
    operator is the image of the derived tensor product (`kronLift_surjective`), so no smaller state
    space carries the composite of two independent bodies. -/
theorem two_body_states_irreducible (W : Submodule ℂ (Fin 2 × Fin 2 → ℂ))
    (hW : ∀ t : M ⊗[ℂ] M, ∀ v ∈ W, kronLift t *ᵥ v ∈ W) (hne : ∃ v ∈ W, v ≠ 0) : W = ⊤ := by
  obtain ⟨v, hvW, hv0⟩ := hne
  rw [Submodule.eq_top_iff']
  intro u
  obtain ⟨X, hX⟩ := state_cyclic v u hv0
  obtain ⟨t, rfl⟩ := kronLift_surjective X
  rw [← hX]
  exact hW t v hvW

-- ==========================================
-- §5d. Any number of bodies
-- ==========================================

section NBody

variable {ι : Type*} [DecidableEq ι] {J : Type*} [Ring J] [Algebra ℂ J]

/-- **One interleaving move among `N` bodies**: swap two adjacent events carried by different
    labels. -/
inductive NStep : List (ι × Twist) → List (ι × Twist) → Prop
  | swap (x y : ι × Twist) (v : List (ι × Twist)) (h : x.1 ≠ y.1) : NStep (x :: y :: v) (y :: x :: v)
  | cons (z : ι × Twist) {w w' : List (ι × Twist)} : NStep w w' → NStep (z :: w) (z :: w')

/-- Body `i`'s history inside an `N`-body word. -/
def nproj (i : ι) : List (ι × Twist) → List Twist
  | [] => []
  | x :: w => if x.1 = i then x.2 :: nproj i w else nproj i w

lemma nproj_cons_self (i : ι) (t : Twist) (w : List (ι × Twist)) :
    nproj i ((i, t) :: w) = t :: nproj i w := by simp [nproj]

lemma nproj_cons_ne {i j : ι} (h : i ≠ j) (t : Twist) (w : List (ι × Twist)) :
    nproj j ((i, t) :: w) = nproj j w := by simp [nproj, h]

/-- An interleaving move changes no body's history. -/
theorem nstep_proj {w w' : List (ι × Twist)} (h : NStep w w') (i : ι) : nproj i w = nproj i w' := by
  induction h with
  | swap x y v h =>
      by_cases hx : x.1 = i
      · have hy : y.1 ≠ i := fun hy => h (hx.trans hy.symm)
        simp [nproj, hx, hy]
      · by_cases hy : y.1 = i
        · simp [nproj, hx, hy]
        · simp [nproj, hx, hy]
  | cons z _ ih => simp [nproj, ih]

theorem n_rtg_cons (z : ι × Twist) {w w' : List (ι × Twist)} (h : Relation.ReflTransGen NStep w w') :
    Relation.ReflTransGen NStep (z :: w) (z :: w') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (NStep.cons z hbc)

/-- Pull the first body-`i` event to the front of a word, past events of other bodies. -/
theorem extract (i : ι) (t : Twist) (l : List Twist) :
    ∀ w : List (ι × Twist), nproj i w = t :: l →
      ∃ r, Relation.ReflTransGen NStep w ((i, t) :: r) ∧ nproj i r = l ∧
        ∀ j, j ≠ i → nproj j r = nproj j w
  | [], h => by simp [nproj] at h
  | y :: w, h => by
      by_cases hy : y.1 = i
      · rcases y with ⟨a, s⟩
        simp only at hy
        subst hy
        rw [nproj_cons_self] at h
        obtain ⟨rfl, rfl⟩ := List.cons.inj h
        refine ⟨w, Relation.ReflTransGen.refl, rfl, fun j hj => ?_⟩
        rw [nproj_cons_ne (Ne.symm hj)]
      · have h' : nproj i w = t :: l := by simpa [nproj, hy] using h
        obtain ⟨r, hr, hri, hrj⟩ := extract i t l w h'
        refine ⟨y :: r, ?_, ?_, fun j hj => ?_⟩
        · exact (n_rtg_cons y hr).tail (NStep.swap y (i, t) r hy)
        · simp [nproj, hy, hri]
        · simp [nproj, hrj j hj]

/-- **The `N`-body composite is the tuple of body histories.** Two `N`-body words are interleavings
    of each other exactly when they agree on every body. -/
theorem n_same_composite_iff :
    ∀ w w' : List (ι × Twist),
      Relation.ReflTransGen NStep w w' ↔ ∀ i, nproj i w = nproj i w' := by
  intro w w'
  constructor
  · intro h i
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (nstep_proj hbc i)
  · intro h
    induction w' generalizing w with
    | nil =>
        cases w with
        | nil => exact Relation.ReflTransGen.refl
        | cons y w =>
            have := h y.1
            simp [nproj] at this
    | cons x v ih =>
        rcases x with ⟨i, t⟩
        have hx : nproj i w = t :: nproj i v := by rw [h i, nproj_cons_self]
        obtain ⟨r, hr, hri, hrj⟩ := extract i t (nproj i v) w hx
        have hrv : ∀ j, nproj j r = nproj j v := by
          intro j
          by_cases hj : j = i
          · rw [hj, hri]
          · rw [hrj j hj, h j, nproj_cons_ne (Ne.symm hj)]
        exact hr.trans (n_rtg_cons _ (ih r hrv))

variable (ρ : ι → M →ₐ[ℂ] J)

/-- The joint fold of an `N`-body word: each event acts through its own body's map. -/
noncomputable def ncfold : List (ι × Twist) → J
  | [] => 1
  | x :: w => ρ x.1 x.2.toMatrix * ncfold w

/-- **Independence of `N` bodies is pairwise commutation.** The joint fold ignores interleaving
    exactly when every twist on one body commutes with every twist on every other body. -/
theorem n_interleaving_invariant_iff :
    (∀ w w', NStep w w' → ncfold ρ w = ncfold ρ w') ↔
      ∀ i j : ι, i ≠ j → ∀ s t : Twist, Commute (ρ i s.toMatrix) (ρ j t.toMatrix) := by
  constructor
  · intro h i j hij s t
    have e := h _ _ (NStep.swap (i, s) (j, t) [] hij)
    have e' : ρ i s.toMatrix * (ρ j t.toMatrix * 1) = ρ j t.toMatrix * (ρ i s.toMatrix * 1) := e
    show ρ i s.toMatrix * ρ j t.toMatrix = ρ j t.toMatrix * ρ i s.toMatrix
    rwa [mul_one, mul_one] at e'
  · intro hc w w' hs
    induction hs with
    | swap x y v h =>
        show ρ x.1 x.2.toMatrix * (ρ y.1 y.2.toMatrix * ncfold ρ v)
            = ρ y.1 y.2.toMatrix * (ρ x.1 x.2.toMatrix * ncfold ρ v)
        rw [← mul_assoc, (hc x.1 y.1 h x.2 y.2).eq, mul_assoc]
    | cons z _ ih =>
        show ρ z.1 z.2.toMatrix * ncfold ρ _ = ρ z.1 z.2.toMatrix * ncfold ρ _
        rw [ih]

/-- Slot an operator into an ordered product past factors it commutes with. -/
theorem insert_prod (X : J) (g : ι → J) (i : ι) :
    ∀ L : List ι, L.Nodup → i ∈ L → (∀ j ∈ L, j ≠ i → Commute X (g j)) →
      X * (L.map g).prod = (L.map (fun j => if j = i then X * g j else g j)).prod
  | [], _, hi, _ => by simp at hi
  | j :: L, hnd, hi, hc => by
      rw [List.nodup_cons] at hnd
      by_cases hji : j = i
      · have hiL' : i ∉ L := hji ▸ hnd.1
        have hrest : L.map (fun k => if k = i then X * g k else g k) = L.map g := by
          apply List.map_congr_left
          intro k hk
          have hki : k ≠ i := fun h => hiL' (h ▸ hk)
          simp [hki]
        rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hrest, if_pos hji,
          mul_assoc]
      · have hiL : i ∈ L := by
          rcases List.mem_cons.1 hi with h | h
          · exact absurd h.symm hji
          · exact h
        have ih := insert_prod X g i L hnd.2 hiL (fun k hk hki => hc k (by simp [hk]) hki)
        rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, if_neg hji, ← mul_assoc,
          (hc j (by simp) hji).eq, mul_assoc, ih]

/-- **The `N`-body joint fold factors body by body.** For any duplicate-free list `L` of the bodies
    a word uses, and pairwise-commuting bodies, the joint fold is the ordered product of each body's
    own fold: `ncfold w = ∏_{i ∈ L} ρ i (fold w_i)`. This is the `N`-fold tensor product's universal
    map evaluated on `⊗ᵢ fold w_i`. -/
theorem ncfold_eq (hc : ∀ i j : ι, i ≠ j → ∀ s t : Twist, Commute (ρ i s.toMatrix) (ρ j t.toMatrix))
    (L : List ι) (hL : L.Nodup) :
    ∀ w : List (ι × Twist), (∀ x ∈ w, x.1 ∈ L) →
      ncfold ρ w = (L.map fun i => ρ i (twistMatrixFold (nproj i w))).prod
  | [], _ => by
      show (1 : J) = (L.map fun i => ρ i (twistMatrixFold [])).prod
      have h1 : ∀ i, ρ i (twistMatrixFold []) = 1 := fun i => map_one (ρ i)
      simp [h1]
  | (i, t) :: w, hw => by
      have hi : i ∈ L := hw (i, t) (by simp)
      have ih := ncfold_eq hc L hL w (fun x hx => hw x (by simp [hx]))
      show ρ i t.toMatrix * ncfold ρ w = _
      rw [ih, insert_prod (ρ i t.toMatrix) (fun j => ρ j (twistMatrixFold (nproj j w))) i L hL hi
        (fun j _ hji =>
        (commute_fold (ρ j) (ρ i) (fun s u => hc j i hji s u) (nproj j w) t).symm)]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hji : j = i
      · rw [if_pos hji, hji, nproj_cons_self, ← map_mul]
        rfl
      · rw [if_neg hji, nproj_cons_ne (Ne.symm hji)]

end NBody

-- ==========================================
-- §5e. The N-fold tensor object
-- ==========================================

section NTensor

variable {J : Type*} [Ring J] [Algebra ℂ J]

/-- An ordered product of entries that are all `1` is `1`. -/
theorem ofFn_prod_ones {n : ℕ} (g : Fin n → J) (h : ∀ j, g j = 1) : (List.ofFn g).prod = 1 := by
  rw [show g = fun _ => 1 from funext h]
  simp

/-- An ordered product whose entries are `1` away from position `i` is its `i`-th entry. -/
theorem ofFn_single_prod : ∀ {n : ℕ} (i : Fin n) (g : Fin n → J), (∀ j, j ≠ i → g j = 1) →
    (List.ofFn g).prod = g i
  | 0, i, _, _ => i.elim0
  | n + 1, i, g, h => by
      rw [List.ofFn_succ, List.prod_cons]
      cases i using Fin.cases with
      | zero =>
          rw [ofFn_prod_ones (fun j => g j.succ) (fun j => h _ (Fin.succ_ne_zero j)), mul_one]
      | succ k =>
          rw [h 0 (Fin.succ_ne_zero k).symm, one_mul]
          exact ofFn_single_prod k (fun j => g j.succ)
            (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e)))

/-- **Ordered products split when later factors of one kind commute past earlier ones of the
other.** `∏ (aᵢ bᵢ) = (∏ aᵢ)(∏ bᵢ)` once every `bᵢ` commutes with every `aⱼ`, `j ≠ i`. -/
theorem ofFn_prod_mul : ∀ {n : ℕ} (a b : Fin n → J), (∀ i j, i ≠ j → Commute (b i) (a j)) →
    (List.ofFn fun i => a i * b i).prod = (List.ofFn a).prod * (List.ofFn b).prod
  | 0, _, _, _ => by simp
  | n + 1, a, b, h => by
      simp only [List.ofFn_succ, List.prod_cons]
      rw [ofFn_prod_mul (fun i => a i.succ) (fun i => b i.succ)
        (fun i j hij => h _ _ (fun e => hij (Fin.succ_injective _ e)))]
      have hc : Commute (b 0) (List.ofFn fun i => a i.succ).prod := by
        apply Commute.list_prod_right
        intro c hcm
        simp only [List.mem_ofFn] at hcm
        obtain ⟨j, rfl⟩ := hcm
        exact h 0 j.succ (Fin.succ_ne_zero j).symm
      simp only [mul_assoc]
      rw [← mul_assoc (b 0), hc.eq]
      simp only [mul_assoc]

variable {n : ℕ} (ρ : Fin n → M →ₐ[ℂ] J)

/-- The ordered product `(Xᵢ)ᵢ ↦ ρ₀ X₀ · ρ₁ X₁ ⋯`, multilinear in the bodies' operators. -/
noncomputable def nMulti : MultilinearMap ℂ (fun _ : Fin n => M) J :=
  (MultilinearMap.mkPiAlgebraFin ℂ n J).compLinearMap (fun i => (ρ i).toLinearMap)

theorem nMulti_apply (x : Fin n → M) : nMulti ρ x = (List.ofFn fun i => ρ i (x i)).prod := by
  simp [nMulti, MultilinearMap.mkPiAlgebraFin_apply]

variable (hc : ∀ i j : Fin n, i ≠ j → ∀ X Y : M, Commute (ρ i X) (ρ j Y))

/-- **The factoring map out of the `N`-fold tensor product `⨂ᵢ M`.** When distinct bodies commute
(which interleaving invariance forces, `n_interleaving_invariant_iff`), the ordered product of the
bodies' actions is an algebra map out of `⨂[ℂ] i, M`. -/
noncomputable def nTensorLift : (⨂[ℂ] _ : Fin n, M) →ₐ[ℂ] J :=
  PiTensorProduct.liftAlgHom (nMulti ρ) (by rw [nMulti_apply]; simp) (fun x y => by
    rw [nMulti_apply, nMulti_apply, nMulti_apply]
    simp only [Pi.mul_apply, map_mul]
    exact ofFn_prod_mul _ _ (fun i j hij => hc i j hij _ _))

theorem nTensorLift_tprod (x : Fin n → M) :
    nTensorLift ρ hc (PiTensorProduct.tprod ℂ x) = (List.ofFn fun i => ρ i (x i)).prod := by
  simp [nTensorLift, nMulti_apply]

/-- On `1 ⊗ ⋯ ⊗ X ⊗ ⋯ ⊗ 1` (`X` in slot `i`) the factoring map is body `i`'s own action. -/
theorem nTensorLift_single (i : Fin n) (X : M) :
    nTensorLift ρ hc (PiTensorProduct.singleAlgHom i X) = ρ i X := by
  simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply, nTensorLift_tprod]
  rw [ofFn_single_prod i _ (fun j hj => by simp [Pi.mulSingle_eq_of_ne hj])]
  simp

/-- **Uniqueness: the universal property of `⨂ᵢ M`.** Any algebra map out of `⨂ᵢ M` that restricts
to each body's action on its own slot is `nTensorLift`. -/
theorem nTensorLift_unique (Φ : (⨂[ℂ] _ : Fin n, M) →ₐ[ℂ] J)
    (h : ∀ i X, Φ (PiTensorProduct.singleAlgHom i X) = ρ i X) : Φ = nTensorLift ρ hc :=
  PiTensorProduct.algHom_ext fun i => AlgHom.ext fun X => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h, nTensorLift_single]

/-- **Every `N`-body joint fold factors through `⨂ᵢ M`.** If distinct bodies' twists commute, the
joint fold of any word is the factoring map applied to `fold w₀ ⊗ fold w₁ ⊗ ⋯`. This is the
`N`-body form of `composite_is_tensor`. -/
theorem n_composite_is_tensor
    (ht : ∀ i j : Fin n, i ≠ j → ∀ s t : Twist, Commute (ρ i s.toMatrix) (ρ j t.toMatrix))
    (w : List (Fin n × Twist)) :
    ncfold ρ w = nTensorLift ρ (fun i j hij => commute_all (ρ i) (ρ j) (ht i j hij))
      (PiTensorProduct.tprod ℂ fun i => twistMatrixFold (nproj i w)) := by
  rw [nTensorLift_tprod, ncfold_eq ρ ht (List.finRange n) (by first | exact List.nodup_finRange n | exact List.nodup_finRange) w
    (fun x _ => by simp), List.ofFn_eq_map]

end NTensor

-- ==========================================
-- §6. The two sectors
-- ==========================================

/-- **A Kronecker product is a non-zero scalar exactly when both factors are scalars.** -/
theorem kron_scalar_iff (A B : M) {c : ℂ} (hc : c ≠ 0) :
    A ⊗ₖ B = c • (1 : QLF.Tsirelson.Q) ↔ ∃ a b : ℂ, A = a • (1 : M) ∧ B = b • (1 : M) ∧ a * b = c := by
  constructor
  · intro h
    have ent : ∀ i j k l : Fin 2,
        A i k * B j l = (c • (1 : QLF.Tsirelson.Q)) (i, j) (k, l) := fun i j k l =>
      congrFun (congrFun h (i, j)) (k, l)
    have e1 : A 0 0 * B 0 0 = c := by simpa using ent 0 0 0 0
    have e2 : A 1 1 * B 0 0 = c := by simpa using ent 1 0 1 0
    have e3 : A 0 0 * B 1 1 = c := by simpa using ent 0 1 0 1
    have z1 : A 0 1 * B 0 0 = 0 := by simpa using ent 0 0 1 0
    have z2 : A 1 0 * B 0 0 = 0 := by simpa using ent 1 0 0 0
    have z3 : A 0 0 * B 0 1 = 0 := by simpa using ent 0 0 0 1
    have z4 : A 0 0 * B 1 0 = 0 := by simpa using ent 0 1 0 0
    have hB : B 0 0 ≠ 0 := fun h0 => hc (by rw [← e1, h0, mul_zero])
    have hA : A 0 0 ≠ 0 := fun h0 => hc (by rw [← e1, h0, zero_mul])
    have a01 : A 0 1 = 0 := (mul_eq_zero.1 z1).resolve_right hB
    have a10 : A 1 0 = 0 := (mul_eq_zero.1 z2).resolve_right hB
    have b01 : B 0 1 = 0 := (mul_eq_zero.1 z3).resolve_left hA
    have b10 : B 1 0 = 0 := (mul_eq_zero.1 z4).resolve_left hA
    have a11 : A 1 1 = A 0 0 := mul_right_cancel₀ hB (e2.trans e1.symm)
    have b11 : B 1 1 = B 0 0 := mul_left_cancel₀ hA (e3.trans e1.symm)
    refine ⟨A 0 0, B 0 0, ?_, ?_, e1⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [a01, a10, a11]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [b01, b10, b11]
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]

/-- Every twist fold is invertible: the reversed history undoes it. -/
theorem fold_mul_reverse (a : List Twist) : twistMatrixFold a * twistMatrixFold a.reverse = 1 := by
  induction a with
  | nil => show (1 : M) * 1 = 1; rw [mul_one]
  | cons t a ih =>
      rw [List.reverse_cons, QLF.IndexedFactors.twistMatrixFold_append]
      show t.toMatrix * twistMatrixFold a * (twistMatrixFold a.reverse * (t.toMatrix * 1)) = 1
      rw [mul_one, mul_assoc, ← mul_assoc (twistMatrixFold a), ih, one_mul,
        QLF.ClosureUnitarity.twist_sq]

/-- **Product sector: a joint closure of independent bodies is two separate closures.** If the
    composite fold `fold a ⊗ fold b` is a scalar, each body's own fold is a scalar. -/
theorem independent_closure_factors (a b : List Twist) {c : ℂ}
    (h : twistMatrixFold a ⊗ₖ twistMatrixFold b = c • (1 : QLF.Tsirelson.Q)) :
    (∃ x : ℂ, twistMatrixFold a = x • (1 : M)) ∧ (∃ y : ℂ, twistMatrixFold b = y • (1 : M)) := by
  have hc : c ≠ 0 := by
    rintro rfl
    have hinv : (twistMatrixFold a ⊗ₖ twistMatrixFold b) *
        (twistMatrixFold a.reverse ⊗ₖ twistMatrixFold b.reverse) = 1 := by
      rw [← Matrix.mul_kronecker_mul, fold_mul_reverse, fold_mul_reverse,
        Matrix.one_kronecker_one]
    rw [h, zero_smul, zero_mul] at hinv
    exact zero_ne_one hinv
  obtain ⟨x, y, hx, hy, _⟩ := (kron_scalar_iff _ _ hc).1 h
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

/-- **Coupled sector: an open body is never closed by an independent partner.** If body `A`'s
    history is open (its fold is no scalar), then for every history on body `B` the composite
    fold is no scalar either. -/
theorem open_factor_never_closes_jointly (a : List Twist)
    (hopen : ∀ x : ℂ, twistMatrixFold a ≠ x • (1 : M)) (b : List Twist) (c : ℂ) :
    twistMatrixFold a ⊗ₖ twistMatrixFold b ≠ c • (1 : QLF.Tsirelson.Q) := by
  intro h
  obtain ⟨⟨x, hx⟩, _⟩ := independent_closure_factors a b h
  exact hopen x hx

/-- **A product of independent factors cannot produce a shared closure.** The primordial pair
    `^ | v` closes as one word (`countBalanced`), but placed on two independent bodies its
    composite fold is no scalar for any phase. -/
theorem shared_closure_not_independent :
    countBalanced ([Twist.up] ++ [Twist.down]) ∧
    ∀ c : ℂ, twistMatrixFold [Twist.up] ⊗ₖ twistMatrixFold [Twist.down] ≠
      c • (1 : QLF.Tsirelson.Q) :=
  ⟨QLF.IndexedFactors.up_down_balanced,
   open_factor_never_closes_jointly _ QLF.IndexedFactors.up_fold_not_scalar _⟩

-- ==========================================
-- §7. States: entanglement lives inside the tensor space
-- ==========================================

/-- A product state `u ⊗ v` of the derived two-body space. -/
def prodVec (u v : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun ij => u ij.1 * v ij.2

lemma s_00 : QLF.JointClosure.s (0, 0) = 0 := by simp [QLF.JointClosure.s]
lemma s_11 : QLF.JointClosure.s (1, 1) = 0 := by simp [QLF.JointClosure.s]
lemma s_10 : QLF.JointClosure.s (1, 0) = -1 := by simp [QLF.JointClosure.s]
lemma s_01 : QLF.JointClosure.s (0, 1) = 1 := by simp [QLF.JointClosure.s]

/-- **No product state is a joint closure.** A product vector on which the two bodies' actions
    cancel on the `x` and `z` axes is zero. -/
theorem product_never_joint_closure (u v : Fin 2 → ℂ)
    (hx : QLF.JointClosure.joint σx *ᵥ prodVec u v = 0)
    (hz : QLF.JointClosure.joint σz *ᵥ prodVec u v = 0) : prodVec u v = 0 := by
  have h := (QLF.JointClosure.closed_iff_singlet _).1 ⟨hx, hz⟩
  have e00 : u 0 * v 0 = u 0 * v 1 * 0 := by
    have := congrFun h (0, 0)
    rw [Pi.smul_apply, s_00, smul_eq_mul] at this
    exact this
  have e10 : u 1 * v 0 = u 0 * v 1 * -1 := by
    have := congrFun h (1, 0)
    rw [Pi.smul_apply, s_10, smul_eq_mul] at this
    exact this
  have hsq : (u 0 * v 1) * (u 0 * v 1) = 0 := by
    linear_combination (u 0 * v 1) * e10 - (u 1 * v 1) * e00
  have hc : prodVec u v (0, 1) = 0 := mul_self_eq_zero.1 hsq
  rw [h, hc, zero_smul]

/-- **The singlet is not a product state.** -/
theorem singlet_not_product : ¬ ∃ u v : Fin 2 → ℂ, QLF.JointClosure.s = prodVec u v := by
  rintro ⟨u, v, huv⟩
  have h0 : prodVec u v = 0 :=
    product_never_joint_closure u v (huv ▸ QLF.JointClosure.closed_x)
      (huv ▸ QLF.JointClosure.closed_z)
  have h1 := congrFun (huv.trans h0) (0, 1)
  rw [s_01] at h1
  exact one_ne_zero h1

/-- **Both sectors live in the derived tensor space.** It holds a non-zero joint closure, the
    singlet, which is not a product; and no non-zero product vector is a joint closure. So tensor
    products do represent entanglement. What no product of independent factors produces is a
    shared closure. -/
theorem tensor_space_sectors :
    (QLF.JointClosure.s ≠ 0 ∧ QLF.JointClosure.joint σx *ᵥ QLF.JointClosure.s = 0 ∧
      QLF.JointClosure.joint σz *ᵥ QLF.JointClosure.s = 0 ∧
      ¬ ∃ u v : Fin 2 → ℂ, QLF.JointClosure.s = prodVec u v) ∧
    (∀ u v : Fin 2 → ℂ, QLF.JointClosure.joint σx *ᵥ prodVec u v = 0 →
      QLF.JointClosure.joint σz *ᵥ prodVec u v = 0 → prodVec u v = 0) := by
  refine ⟨⟨?_, QLF.JointClosure.closed_x, QLF.JointClosure.closed_z, singlet_not_product⟩,
    product_never_joint_closure⟩
  intro h
  have := congrFun h (0, 1)
  rw [s_01] at this
  exact one_ne_zero this

end QLF.TensorFromClosure
