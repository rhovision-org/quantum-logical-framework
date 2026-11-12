/-!
# QLF_StrangeLoop — a toy conservative-return interface

This file is the first Lean step of the strange-loop proof programme described in
`Strange_Loops.md` §6. It proves the **shape** of a conservative return on a toy
two-element ortholattice:

* `Formal` and `Physical` are two copies of the two-element lattice;
* `F : Formal -> Physical` and `R : Physical -> Formal`;
* `R (F a) = a` and `F (R b) = b`;
* `F` preserves order, join, meet and complement, and `R` preserves order.

It is deliberately **not** the optical bridge: no polarizer geometry, detector map,
probability rule or ZFA-history interpretation is formalized. It is a machine-checked
toy witness that the interface is coherent, not evidence that the three-polarizer
`1/8` is derived. The operational map remains `B-OPEN`.

No axioms, no Mathlib.
-/
namespace QLF.StrangeLoop

/-- Formal side of the toy interface: the two-element lattice. -/
inductive Formal | bot | top
  deriving DecidableEq, Repr

/-- Physical side of the toy interface: the same two-element lattice, kept as a distinct type. -/
inductive Physical | bot | top
  deriving DecidableEq, Repr

namespace Formal

/-- Toy order: `bot` is below everything; everything is below `top`. -/
def le (a b : Formal) : Bool :=
  match a, b with
  | .bot, _ => true
  | _, .top => true
  | _, _ => false

/-- Toy join. -/
def sup (a b : Formal) : Formal :=
  match a, b with
  | .bot, x => x
  | x, .bot => x
  | _, _ => .top

/-- Toy meet. -/
def inf (a b : Formal) : Formal :=
  match a, b with
  | .top, x => x
  | x, .top => x
  | _, _ => .bot

/-- Toy orthocomplement. -/
def compl : Formal -> Formal
  | .bot => .top
  | .top => .bot

end Formal

namespace Physical

/-- Physical order, mirroring the formal order. -/
def le (a b : Physical) : Bool :=
  match a, b with
  | .bot, _ => true
  | _, .top => true
  | _, _ => false

/-- Physical join. -/
def sup (a b : Physical) : Physical :=
  match a, b with
  | .bot, x => x
  | x, .bot => x
  | _, _ => .top

/-- Physical meet. -/
def inf (a b : Physical) : Physical :=
  match a, b with
  | .top, x => x
  | x, .top => x
  | _, _ => .bot

/-- Physical orthocomplement. -/
def compl : Physical -> Physical
  | .bot => .top
  | .top => .bot

end Physical

/-- Forward map: the toy formal object is realized as the corresponding physical object. -/
def F : Formal -> Physical
  | .bot => .bot
  | .top => .top

/-- Return map: read the finite formal record back from its physical image. -/
def R : Physical -> Formal
  | .bot => .bot
  | .top => .top

/-- The composite `R ∘ F` is the identity on the formal toy. -/
theorem conservative_return (a : Formal) : R (F a) = a := by
  cases a <;> rfl

/-- The other composite is the identity on the physical toy. -/
theorem return_forward (b : Physical) : F (R b) = b := by
  cases b <;> rfl

/-- `F` preserves the order. -/
theorem F_preserves_le (a b : Formal) (h : Formal.le a b = true) :
    Physical.le (F a) (F b) = true := by
  cases a <;> cases b <;> simp [Formal.le, Physical.le, F] at h ⊢

/-- `R` preserves the physical order. -/
theorem R_preserves_le (a b : Physical) (h : Physical.le a b = true) :
    Formal.le (R a) (R b) = true := by
  cases a <;> cases b <;> simp [Physical.le, Formal.le, R] at h ⊢

/-- `F` preserves join. -/
theorem F_preserves_sup (a b : Formal) :
    F (Formal.sup a b) = Physical.sup (F a) (F b) := by
  cases a <;> cases b <;> rfl

/-- `F` preserves meet. -/
theorem F_preserves_inf (a b : Formal) :
    F (Formal.inf a b) = Physical.inf (F a) (F b) := by
  cases a <;> cases b <;> rfl

/-- `F` preserves complement. -/
theorem F_preserves_compl (a : Formal) :
    F (Formal.compl a) = Physical.compl (F a) := by
  cases a <;> rfl

end QLF.StrangeLoop
