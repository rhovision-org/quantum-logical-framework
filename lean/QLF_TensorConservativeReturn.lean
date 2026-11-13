import QLF_TensorFromClosure
import QLF_ConservativeReturn
import Mathlib

/-!
# QLF_TensorConservativeReturn — the quotient return for the tensor representation

`QLF_TensorFromClosure` derives the tensor product for independent two-body
composition. This file supplies the missing return **on physical equivalence
classes**, in the quotient shape of
`QLF.ConservativeReturn.QuotientStrangeLoopTrigger`.

The finite side is the quotient of two-body histories by equality of the tensor
image

```
w ~ w'  iff  fold(projA w) ⊗ fold(projB w) = fold(projA w') ⊗ fold(projB w').
```

The forward map is that tensor image. The return map reads a class back from a
tensor image. `R ∘ F = id` is proved on classes, not on raw words. This is
required: `pair_scalar_ambiguity` shows that a tensor element does not remember
how a common scalar was split between the factors.

Scope: this proves the quotient return is coherent and machine-checked. It does
**not** prove that the chosen equivalence is the physically selected closure
equivalence, that the entangled sector returns a shared closure, or that the
tensor bridge is empirically closed. The actual bridge records remain `B-OPEN`.
-/

noncomputable section

open QLF QLF.TensorFromClosure QLF.ConservativeReturn
open scoped TensorProduct

namespace QLF.TensorConservativeReturn

/-- A two-body history. -/
abbrev PairHistory := List Tok

/-- The tensor image of a two-body history. -/
def foldPair (w : PairHistory) : M ⊗[ℂ] M :=
  twistMatrixFold (projA w) ⊗ₜ twistMatrixFold (projB w)

/-- Physical equivalence on two-body histories: same tensor image. -/
def PairEquiv (w w' : PairHistory) : Prop :=
  foldPair w = foldPair w'

/-- The finite closure class of a two-body history, quotiented by its tensor image. -/
def ClosureClass : Type :=
  Quot PairEquiv

/-- The forward map from a closure class to its tensor image. -/
def F (c : ClosureClass) : M ⊗[ℂ] M :=
  Quot.lift foldPair (by
    intro a b h
    exact h) c

/-- The tensor side of the return: a tensor element together with a proof that it
    is in the image of `F`. -/
abbrev TensorImage :=
  {x : M ⊗[ℂ] M // ∃ c : ClosureClass, F c = x}

/-- The forward map into the image subtype. -/
def forwardImage (c : ClosureClass) : TensorImage :=
  ⟨F c, ⟨c, rfl⟩⟩

/-- The return map: choose a closure class whose image is the given tensor. -/
def R (x : TensorImage) : ClosureClass :=
  Classical.choose x.property

/-- The tensor image map is injective on closure classes. -/
theorem F_injective : Function.Injective F := by
  intro c d h
  induction c using Quot.ind with
  | mk a =>
    induction d using Quot.ind with
    | mk b =>
      apply Quot.sound
      simpa [F, PairEquiv] using h

/-- **The quotient conservative return:** the class read back from the tensor
    image is the original class. -/
theorem R_forward (c : ClosureClass) : R (forwardImage c) = c := by
  unfold R
  have h := Classical.choose_spec (forwardImage c).2
  exact F_injective (by simpa [forwardImage] using h)

/-- Interleaving moves preserve the tensor image. -/
theorem step_foldPair {w w' : PairHistory} (h : Step w w') :
    foldPair w = foldPair w' := by
  obtain ⟨hA, hB⟩ := step_proj h
  simp [foldPair, hA, hB]

/-- Interleaving-equivalent histories have the same closure class. -/
theorem class_of_step {w w' : PairHistory} (h : Step w w') :
    Quot.mk PairEquiv w = Quot.mk PairEquiv w' :=
  Quot.sound (step_foldPair h)

/-- The quotient trigger instantiated with the actual tensor algebra. -/
def tensorTrigger : QuotientStrangeLoopTrigger where
  Core := ClosureClass
  Tensor := TensorImage
  coreEquiv := Eq
  equiv_refl := fun _ => rfl
  equiv_symm := fun h => h.symm
  equiv_trans := fun h₁ h₂ => h₁.trans h₂
  forward := forwardImage
  ret := R
  forward_respects := by
    intro c c' h
    rw [h]
  composite_id_on_quotient := R_forward

/-- The tensor quotient return exists. -/
theorem tensorTrigger_exists :
    Nonempty QuotientStrangeLoopTrigger :=
  ⟨tensorTrigger⟩

/-- The composite identity, exposed in the notation of the target theorem. -/
theorem tensor_conservative_return (c : ClosureClass) :
    R (forwardImage c) = c :=
  R_forward c

end QLF.TensorConservativeReturn
