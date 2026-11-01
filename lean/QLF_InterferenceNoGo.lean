import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# QLF_InterferenceNoGo — what an interfering event weight must be

Pre-registered in [`Interference_NoGo.md`](../Interference_NoGo.md) §2 (statements N1–N5). This
commit carries the definitions only; the theorems follow in a later commit.
-/

namespace QLF.InterferenceNoGo

open Finset

variable {ι : Type} [DecidableEq ι]

/-- The pairwise interference term of an event weight. -/
def I₂ (μ : Finset ι → ℝ) (A B : Finset ι) : ℝ := μ (A ∪ B) - μ A - μ B

/-- Sorkin's third-order interference term. -/
def I₃ (μ : Finset ι → ℝ) (A B C : Finset ι) : ℝ :=
  μ (A ∪ B ∪ C) - μ (A ∪ B) - μ (A ∪ C) - μ (B ∪ C) + μ A + μ B + μ C

/-- The additive tally of an event. -/
def tally {V : Type} [AddCommMonoid V] (v : ι → V) (E : Finset ι) : V := ∑ h ∈ E, v h

/-- A tally readout: the event weight `Φ(T(E))`. -/
def readout {V : Type} [AddCommMonoid V] (Φ : V → ℝ) (v : ι → V) (E : Finset ι) : ℝ :=
  Φ (tally v E)

end QLF.InterferenceNoGo
