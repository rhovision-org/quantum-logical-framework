import QLF_KraftMeasure

/-!
# QLF_UniformMeasure — **the uniform twist measure is forced by symmetry**

Part of obligation O5 of [`Framing.md`](../Framing.md) §6: replace a structural choice by a necessity
proof where one exists. The cylinder measure `8^{−|h|}` (`twist_kraft`) was listed as a choice. Here it
is derived from two weaker statements:

1. **No twist is preferred a priori**: the per-step weight `p` is invariant under every relabelling of
   the alphabet. This is the absence of an assumption: nothing but ZFA distinguishes histories, and ZFA
   treats every axis and every sign alike.
2. **Normalization**: the weights of the eight continuations of a history sum to `1`.

Then `p t = 1/8` for every twist (`uniform_forced`), and a history of length `L` built step by step
weighs `8^{−L}` (`word_weight_uniform`).

**What stays a choice.** The product form: that a history's weight is the product of its steps'
weights (independent steps). That is the remaining structural content of the measure, and the
identification of the measure with physical probability is still the bridge B09.

No axioms beyond Lean's.
-/

namespace QLF.UniformMeasure

open QLF

/-- **Symmetry and normalization force the uniform step weight.** -/
theorem uniform_forced (p : Twist → ℝ) (hsym : ∀ s t, p s = p t) (hsum : ∑ t, p t = 1) :
    ∀ t, p t = 1 / 8 := by
  intro t
  have h : ∑ s : Twist, p s = ∑ _s : Twist, p t := Finset.sum_congr rfl fun s _ => hsym s t
  rw [h, Finset.sum_const, Finset.card_univ, card_twist, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

/-- Invariance under relabelling of the alphabet gives the symmetry hypothesis. -/
theorem symm_of_perm_invariant (p : Twist → ℝ) (hinv : ∀ σ : Equiv.Perm Twist, ∀ t, p (σ t) = p t) :
    ∀ s t, p s = p t := by
  intro s t
  have := hinv (Equiv.swap t s) t
  rwa [Equiv.swap_apply_left] at this

/-- **The cylinder measure follows**: with independent steps, a history of length `L` weighs `8^{−L}`. -/
theorem word_weight_uniform (p : Twist → ℝ) (hinv : ∀ σ : Equiv.Perm Twist, ∀ t, p (σ t) = p t)
    (hsum : ∑ t, p t = 1) (h : List Twist) : (h.map p).prod = (1 / 8 : ℝ) ^ h.length := by
  have hu := uniform_forced p (symm_of_perm_invariant p hinv) hsum
  induction h with
  | nil => simp
  | cons t rest ih => rw [List.map_cons, List.prod_cons, ih, hu t, List.length_cons, pow_succ']

end QLF.UniformMeasure
