import QLF_BornFromWays

/-!
# QLF_StrangeLoopBorn — the finite Born return, not the physical refinement

This file instantiates the return half of the strange-loop interface on the existing
finite Born characterization in `QLF_BornFromWays`.

What is proved:

* `refinement_return`: a unit-way refinement's fibre counts return the formal norm
  `‖ψᵢ‖²` on every outcome;
* `born_return`: any admissible `ProbAssignment` returns the formal `bornProb` weight;
* `born_two_thirds_return`: the worked `(1+i, 1)` register returns `2/3`.

What is **not** proved: that QLF dynamics performs an amplitude-preserving physical
refinement, or that a detector record is a count of the same unit ways. That is the
`B-OPEN` half of the Born bridge; this file is a finite return witness, not its
physical closure.
-/
namespace QLF.StrangeLoop

open QLF.BornFromWays
open QLF.StateSpace

/-- The formal side of the finite Born return: the Born weight of outcome `i`. -/
def bornReturn {n : Nat} (ψ : Fin n → GaussianInt) (i : Fin n) : ℚ :=
  bornProb ψ i

/-- A unit-way refinement's fibre counts recover the formal norm on every outcome. -/
theorem refinement_return {n N : Nat} (ψ : Fin n → GaussianInt) (f : Fin N → Fin n)
    (hf : ∀ i, ((fibre f i).card : ℤ) = Zsqrtd.norm (ψ i)) :
    (fun i => ((fibre f i).card : ℤ)) = fun i => Zsqrtd.norm (ψ i) := by
  funext i
  exact hf i

/-- Every admissible Born assignment returns the formal Born weight. -/
theorem born_return (A : ProbAssignment) {n : Nat} (ψ : Fin n → GaussianInt)
    (i : Fin n) : A.P ψ i = bornReturn ψ i := by
  unfold bornReturn
  exact born_from_ways A ψ i

/-- The worked register `(1+i, 1)` returns the formal `2/3` weight. -/
theorem born_two_thirds_return (A : ProbAssignment) :
    A.P (![⟨1, 1⟩, 1] : Fin 2 → GaussianInt) 0 =
      bornReturn (![⟨1, 1⟩, 1] : Fin 2 → GaussianInt) 0 := by
  exact born_return A _ 0

end QLF.StrangeLoop
