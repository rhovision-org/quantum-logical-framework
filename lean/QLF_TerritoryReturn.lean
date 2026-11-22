import QLF_PerspectiveHolography

/-!
# QLF_TerritoryReturn — the closure record does not return ZFA

Issue #213 ("the map is the territory") needs a conservative return from physical records back to
the territory's own events. The test is pre-registered in
[`Map_Is_Territory.md`](../Map_Is_Territory.md) §3a and run by
[`territory_return.py`](../territory_return.py).

The strongest record in hand is the observational one. Two two-body histories are equivalent when
no appended context separates them by joint closure and phase
([`QLF_ObservationalEquivalence`](QLF_ObservationalEquivalence.lean)). That record is the joint
fold, and every fold-built (tensor/Hilbert) observable factors through it. Its closure, though, is
*fold* closure: the joint fold is a scalar. The territory's event is ZFA, which is count balance.

## What is proved

* **`gaugeStep_obsEquiv_nil`.** The single gauge twist `+` on body `A` folds to `I`, so it is
  observationally equivalent to the empty history.
* **`zfa_not_class_function`, `zfa_not_reconstructible`, `zfa_not_from_fold`.** The empty history is
  ZFA and `+` is not. So ZFA is not a function of the observational class: no record built from
  joint closure tests with phase, or from the joint fold, returns the territory's events (M1 fails).
* **`ledger_returns_zfa`, `joint_record_with_ledger_returns_zfa`.** The integer ledger (each body's
  twist counts) does return ZFA, alone or together with the closure record (M3, structural).

So the fold-based map keeps the ledger only through its parity classes (M2, numerical). A
conservative return for #213 must include an apparatus that reads the integer ledger.

No axioms.
-/

noncomputable section

namespace QLF.TerritoryReturn

open QLF QLF.TensorFromClosure QLF.TensorConservativeReturn QLF.ObservationalEquivalence
open QLF.PerspectiveHolography QLF.ClosureUnitarity
open scoped TensorProduct

/-- **ZFA for a two-body history:** each body's projection is count-balanced. -/
def TerritoryZFA (w : PairHistory) : Prop :=
  countBalanced (projA w) ∧ countBalanced (projB w)

/-- The gauge twist `+` on body `A`. -/
def gaugeStep : PairHistory := [(false, Twist.plus)]

theorem foldPair_gaugeStep : foldPair gaugeStep = foldPair [] := by
  have hm : twistMatrixFold [Twist.plus] = (1 : M) := by
    rw [fold_singleton]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Twist.toMatrix]
  show twistMatrixFold [Twist.plus] ⊗ₜ[ℂ] twistMatrixFold [] =
    twistMatrixFold [] ⊗ₜ[ℂ] twistMatrixFold []
  rw [hm]
  rfl

/-- `+` is observationally equivalent to the empty history. -/
theorem gaugeStep_obsEquiv_nil : ObsEquiv gaugeStep [] :=
  (obsEquiv_iff_pairEquiv _ _).2 foldPair_gaugeStep

theorem nil_zfa : TerritoryZFA [] := by
  unfold TerritoryZFA countBalanced
  simp

theorem gaugeStep_not_zfa : ¬ TerritoryZFA gaugeStep := by
  rintro ⟨h, -⟩
  unfold countBalanced at h
  exact absurd h.2.2.2 (by decide)

/-- **ZFA is not a function of the observational class.** -/
theorem zfa_not_class_function :
    ∃ w w' : PairHistory, ObsEquiv w w' ∧ TerritoryZFA w' ∧ ¬ TerritoryZFA w :=
  ⟨gaugeStep, [], gaugeStep_obsEquiv_nil, nil_zfa, gaugeStep_not_zfa⟩

/-- **No record of joint closure tests with phase returns ZFA.** -/
theorem zfa_not_reconstructible : ¬ Reconstructs closureTests TerritoryZFA := by
  rw [not_reconstructs_iff]
  refine ⟨gaugeStep, [], (closureTests_eq_iff _ _).2 gaugeStep_obsEquiv_nil, fun h => ?_⟩
  exact gaugeStep_not_zfa (by rw [h]; exact nil_zfa)

/-- **Nor does the joint fold.** -/
theorem zfa_not_from_fold : ¬ Reconstructs foldPair TerritoryZFA := by
  rw [not_reconstructs_iff]
  refine ⟨gaugeStep, [], foldPair_gaugeStep, fun h => ?_⟩
  exact gaugeStep_not_zfa (by rw [h]; exact nil_zfa)

/-- The integer ledger: each body's count of each twist. -/
def ledger (w : PairHistory) : Twist → ℕ × ℕ :=
  fun t => ((projA w).count t, (projB w).count t)

/-- **The ledger returns ZFA.** -/
theorem ledger_returns_zfa : Reconstructs ledger TerritoryZFA :=
  ⟨fun L => ((L Twist.up).1 = (L Twist.down).1 ∧ (L Twist.left).1 = (L Twist.right).1 ∧
      (L Twist.slash).1 = (L Twist.backslash).1 ∧ (L Twist.plus).1 = (L Twist.minus).1) ∧
      ((L Twist.up).2 = (L Twist.down).2 ∧ (L Twist.left).2 = (L Twist.right).2 ∧
      (L Twist.slash).2 = (L Twist.backslash).2 ∧ (L Twist.plus).2 = (L Twist.minus).2),
    fun _ => rfl⟩

/-- **The closure record plus the ledger returns ZFA.** -/
theorem joint_record_with_ledger_returns_zfa :
    Reconstructs (fun w => (closureTests w, ledger w)) TerritoryZFA := by
  obtain ⟨R, hR⟩ := ledger_returns_zfa
  exact ⟨fun p => R p.2, hR⟩

end QLF.TerritoryReturn
