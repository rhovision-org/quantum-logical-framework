import QLF_QuarkStructure

/-!
# QLF_DiversityEmergence — three-colour emergence

First quark test case for the diversity program (#290).

The theorem has two halves:

* any history missing one colour axis has `junctionBaryon = 0` — the existing
  Borromean necessity (`baryon_zero_of_missing`), applied to the junction;
* a ZFA-closed three-axis witness with nonzero `junctionBaryon` exists — the
  proton word `>^/<\\v`, checked directly.

This establishes a structural invariant accessible only to the three-axis
system. It does **not** establish prevalence, continuation advantage,
persistence, QCD confinement, or that every three-axis history is a baryon.
-/

namespace QLF.DiversityEmergence

open QLF QLF.BaryonWinding QLF.QuarkStructure

/-- The proton word `>^/<\\v`: the minimal three-axis closure. -/
def protonWord : List Twist :=
  [Twist.right, Twist.up, Twist.slash, Twist.left, Twist.backslash, Twist.down]

/-- The gauge-invariant junction baryon number vanishes when any colour axis is
missing. This applies `baryon_zero_of_missing` to the spatial projection. -/
theorem junctionBaryon_zero_of_missing (a : Ax) (ts : List Twist)
    (h : ∀ t ∈ ts, axOf t ≠ some a) : junctionBaryon ts = 0 := by
  unfold junctionBaryon
  apply baryon_zero_of_missing a
  intro t ht
  exact h t (List.mem_of_mem_filter ht)

/-- The proton word is ZFA-closed. -/
theorem protonWord_closed : countBalanced protonWord := by
  unfold countBalanced
  decide

/-- The proton word carries junction baryon number `+1`. -/
theorem protonWord_baryon : junctionBaryon protonWord = 1 := by
  decide

/-- **Three-colour emergence, necessity + existence.**

No history missing any colour axis carries nonzero junction baryon number;
nevertheless a closed three-axis witness with nonzero junction baryon number
exists. Both halves use the same gauge-invariant invariant.

No new axiom and no QCD/selection claim. -/
theorem three_colour_emergence :
    (∀ ts : List Twist,
      (∃ a : Ax, ∀ t ∈ ts, axOf t ≠ some a) →
      junctionBaryon ts = 0) ∧
    (∃ ts : List Twist,
      countBalanced ts ∧ junctionBaryon ts ≠ 0) := by
  constructor
  · rintro ts ⟨a, ha⟩
    exact junctionBaryon_zero_of_missing a ts ha
  · refine ⟨protonWord, protonWord_closed, ?_⟩
    rw [protonWord_baryon]
    norm_num

/-- The explicit witness has the first three twists on the three colour axes. -/
theorem three_colour_witness :
    protonWord.take 3 = [Twist.right, Twist.up, Twist.slash] ∧
    countBalanced protonWord ∧ junctionBaryon protonWord = 1 := by
  exact ⟨rfl, protonWord_closed, protonWord_baryon⟩

end QLF.DiversityEmergence
