import QLF_QuarkStructure
import QLF_Manifestation

/-!
# QLF_DiversityEmergence — three-colour emergence

First quark test case for the diversity program (#290), gate D8b/D8a-adjacent.

The theorem has two halves:

* any history missing one colour axis has `baryonNumber = 0` — the existing
  Borromean necessity (`baryon_zero_of_missing`);
* a ZFA-closed three-axis witness with nonzero `junctionBaryon` exists — the
  existing proton closure (`proton_simplest_isolated_imbalance`).

This establishes a structural invariant accessible only to the three-axis
system. It does **not** establish that the three-axis structure is more
prevalent, more persistent, or physically realized as QCD confinement.
-/

namespace QLF.DiversityEmergence

open QLF QLF.BaryonWinding QLF.QuarkStructure QLF.Manifestation

/-- The gauge-invariant junction baryon number vanishes when any colour axis is
missing. This applies `baryon_zero_of_missing` to the spatial projection. -/
theorem junctionBaryon_zero_of_missing (a : Ax) (ts : List Twist)
    (h : ∀ t ∈ ts, axOf t ≠ some a) : junctionBaryon ts = 0 := by
  unfold junctionBaryon
  apply baryon_zero_of_missing a
  intro t ht
  exact h t (List.mem_of_mem_filter ht)

/-- **Three-colour emergence, necessity + existence.**

No history missing any colour axis carries nonzero junction baryon number;
nevertheless a closed three-axis witness with nonzero junction baryon number
exists.

Both halves use the gauge-invariant `junctionBaryon`. No new axiom and no
QCD/selection claim. -/
theorem three_colour_emergence :
    (∀ ts : List Twist,
      (∃ a : Ax, ∀ t ∈ ts, axOf t ≠ some a) →
      junctionBaryon ts = 0) ∧
    (∃ ts : List Twist,
      countBalanced ts ∧ junctionBaryon ts ≠ 0) := by
  constructor
  · rintro ts ⟨a, ha⟩
    exact junctionBaryon_zero_of_missing a ts ha
  · refine ⟨protonClosure, proton_simplest_isolated_imbalance.2.1, ?_⟩
    rw [proton_simplest_isolated_imbalance.2.2.2.1]
    norm_num

/-- The witness is the explicit proton closure, with the first three twists on
the three colour axes. -/
theorem three_colour_witness :
    protonClosure.take 3 = [Twist.right, Twist.up, Twist.slash] ∧
    countBalanced protonClosure ∧
    junctionBaryon protonClosure = 1 := by
  exact ⟨proton_simplest_isolated_imbalance.1,
    proton_simplest_isolated_imbalance.2.1,
    proton_simplest_isolated_imbalance.2.2.2.1⟩

end QLF.DiversityEmergence
