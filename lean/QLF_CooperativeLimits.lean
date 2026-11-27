import Mathlib
import QLF_FreeEnergy
import QLF_LawOfExceptions
import QLF_CooperativeClosure

/-!
# QLF_CooperativeLimits — gates CC5 and CC8

Write-up: [`Cooperative_Intelligence.md`](../Cooperative_Intelligence.md) §5. Part of
[Quantum Logical Framework (QLF)](../README.md).

## CC5: QLF's `log 2` against variational free energy

QLF's per-closure quantum is the constant `log 2` (`QLF_FreeEnergy`). Friston's variational free
energy of a belief `q` against a model is `KL(q ‖ posterior) − log evidence`, a function of `q`. The
proposal asked whether they are the same quantity. They are not, and the overlap is exactly located:

* **`kl_delta_prior`**: fully resolving a binary question with prior `p` gains `−log p`.
* **`quantum_matches_iff_uniform`**: that gain equals `log 2` **iff the prior is uniform**.
* **`partial_belief_below_quantum`**: a belief that does not fully resolve the bit gains strictly less.
* **`vfe_not_constant`**, **`no_constant_identity`**: free energy varies with the belief, so no
  identity with a constant per-closure quantum holds.

So the `log 2` is one variational free-energy change: a complete resolution of one bit from a uniform
prior. That match is **derived on that domain** and nowhere else. Calling QLF's closure quantum
"Friston free energy" in general is false; CC5 stays an open bridge for any other model.

## CC8: hierarchy, and the Law of Exceptions

* **`hierarchical_parity`**: a two-level hierarchy (blocks report their parity, the top adds the
  reports) computes the flat parity. **`reports_irreducible`**: the top needs every block's report,
  and **`block_irreducible`**: each report needs every member of its block. A hierarchy factors an
  irreducible question and never lets a level skip a member.
* **`budget_failure_undetermined`**: a listener of capacity `R` that does not hear a closure returns
  *undetermined*, and the closure is real at `R + 1` (`QLF_LawOfExceptions`). Failing within a budget
  is not impossibility.
* **`pooled_capacity`**: pooling two capacity-bounded listeners hears exactly what the larger hears.
* **`group_of_listeners_misses`**: any finite group of capacity-bounded listeners misses a real
  closure. No finite committee is final.

**Kinds.** Derived throughout. The capacity results are corollaries of the Law of Exceptions. That a
human or AI participant *is* a capacity-bounded listener is a reading. No axiom.
-/

set_option linter.unusedSectionVars false

namespace QLF.CooperativeLimits

open QLF QLF.HorizonClosure QLF.LawOfExceptions QLF.CooperativeClosure

/-! ## CC5 -/

/-- Fully resolving a binary question with prior `p` gains `−log p`. -/
theorem kl_delta_prior (p : ℝ) : binary_kl 1 p = - Real.log p := by
  unfold binary_kl
  simp [one_div, Real.log_inv]

/-- The other full resolution of a uniform bit also gains `log 2`. -/
theorem kl_delta_zero_uniform : binary_kl 0 (1/2) = Real.log 2 := by
  unfold binary_kl
  norm_num

/-- **The per-closure quantum is a full resolution gain iff the prior is uniform.** -/
theorem quantum_matches_iff_uniform {p : ℝ} (hp : 0 < p) :
    binary_kl 1 p = Real.log 2 ↔ p = 1/2 := by
  rw [kl_delta_prior]
  constructor
  · intro h
    have hl : Real.log p⁻¹ = Real.log 2 := by rw [Real.log_inv]; linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (inv_pos.mpr hp)) (Set.mem_Ioi.mpr two_pos) hl
    rw [← inv_inv p, this]
    norm_num
  · rintro rfl
    rw [one_div, Real.log_inv, neg_neg]

/-- A belief that does not fully resolve a uniform bit gains strictly less than the quantum. -/
theorem partial_belief_below_quantum {q : ℝ} (hq1 : 0 < q) (hq2 : q < 1) :
    binary_kl q (1/2) < Real.log 2 :=
  binary_kl_uniform_lt_log_two hq1 hq2

/-- Variational free energy of a binary belief `q` against posterior `p` and evidence `ev`. -/
noncomputable def vfe (q p ev : ℝ) : ℝ := binary_kl q p - Real.log ev

/-- **Free energy depends on the belief.** -/
theorem vfe_not_constant (ev : ℝ) : vfe (1/2) (1/2) ev ≠ vfe 1 (1/2) ev := by
  unfold vfe
  have := partial_belief_below_quantum (q := 1/2) (by norm_num) (by norm_num)
  rw [binary_kl_delta_uniform]
  intro h
  linarith

/-- **No identity with a constant per-closure quantum.** No constant equals the free energy of every
belief on a uniform bit. -/
theorem no_constant_identity (ev : ℝ) : ¬ ∃ c : ℝ, ∀ q ∈ Set.Icc (0 : ℝ) 1, vfe q (1/2) ev = c := by
  rintro ⟨c, hc⟩
  have h1 := hc (1/2) ⟨by norm_num, by norm_num⟩
  have h2 := hc 1 ⟨by norm_num, by norm_num⟩
  exact vfe_not_constant ev (h1.trans h2.symm)

/-! ## CC8: hierarchy -/

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **A two-level hierarchy computes the flat parity.** -/
theorem hierarchical_parity (x : A × B → ZMod 2) :
    parity x = parity (fun a => parity (fun b => x (a, b))) := by
  unfold parity
  exact Fintype.sum_prod_type x

/-- **The top needs every block's report.** -/
theorem reports_irreducible :
    Irreducible (Finset.univ : Finset A) (parity : (A → ZMod 2) → ZMod 2) :=
  parity_irreducible

/-- **Each report needs every member of its block.** -/
theorem block_irreducible :
    Irreducible (Finset.univ : Finset B) (parity : (B → ZMod 2) → ZMod 2) :=
  parity_irreducible

/-- **No level skips a member.** Any coalition of leaves missing one member cannot resolve the top. -/
theorem missing_leaf_blind {S : Finset (A × B)} (hS : S ≠ Finset.univ) : ¬ Resolves S parity :=
  fun h => hS ((parity_resolves_iff S).mp h)

/-! ## CC8: the Law of Exceptions for listeners -/

/-- What a capacity-bounded listener can say about a history. -/
inductive BudgetVerdict
  | possible
  | undetermined
  deriving DecidableEq, Repr

open Classical in
/-- A capacity-`R` listener says *possible* when it hears the closure and *undetermined* otherwise.
It never says *impossible*. -/
noncomputable def budgetVerdict (R : ℕ) (s : TopoString) : BudgetVerdict :=
  if closedAtHorizon R s then BudgetVerdict.possible else BudgetVerdict.undetermined

/-- **Failing within a budget is not impossibility.** The capacity-`R` listener returns undetermined
on a history that closes at `R + 1`. -/
theorem budget_failure_undetermined (R : ℕ) :
    budgetVerdict R (exceptionTo R) = BudgetVerdict.undetermined ∧
      closedAtHorizon (R + 1) (exceptionTo R) := by
  refine ⟨?_, exceptionTo_is_real R⟩
  unfold budgetVerdict
  simp [exceptionTo_not_closed R]

/-- **Pooling two listeners hears what the larger hears.** -/
theorem pooled_capacity (R₁ R₂ : ℕ) (s : TopoString) :
    (closedAtHorizon R₁ s ∨ closedAtHorizon R₂ s) ↔ closedAtHorizon (max R₁ R₂) s := by
  constructor
  · rintro (h | h)
    · exact closedAtHorizon_mono h (le_max_left _ _)
    · exact closedAtHorizon_mono h (le_max_right _ _)
  · intro h
    rcases le_total R₁ R₂ with hle | hle
    · right; rwa [max_eq_right hle] at h
    · left; rwa [max_eq_left hle] at h

/-- **Any finite group of capacity-bounded listeners misses a real closure.** -/
theorem group_of_listeners_misses (Rs : List ℕ) :
    ∃ s : TopoString, (∃ R', closedAtHorizon R' s) ∧ ∀ R ∈ Rs, ¬ closedAtHorizon R s := by
  refine ⟨exceptionTo Rs.sum, ⟨_, exceptionTo_is_real Rs.sum⟩, fun R hR hc => ?_⟩
  exact exceptionTo_not_closed Rs.sum (closedAtHorizon_mono hc (List.le_sum_of_mem hR))

end QLF.CooperativeLimits
