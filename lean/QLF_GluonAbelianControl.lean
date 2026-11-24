import QLF_ColourFlux

/-!
# QLF_GluonAbelianControl — what the non-Abelian vertex does to singlet distance (#286)

Issue #286 asks what a gluon interaction does to the distance `d_G` to colour-singlet closure.
PR #289's move relation has two channels on multisets of nonzero `F₃²` labels, gated by
non-collinearity `symp q r ≠ 0`: **create** adds `p = −(q + r)`, **glue** replaces `q, r` by `p`.
The test is pre-registered in [`Gluon_Abelian_Control.md`](../Gluon_Abelian_Control.md) §1 and run
by [`gluon_abelian_control.py`](../gluon_abelian_control.py), which compares the gated relation with
the same channels ungated.

* **`first_singlet_move_reduces`.** For any distance that vanishes exactly on singlets, a move from
  a non-singlet into a singlet reduces it. So "every first-singlet move reduces `d_G`" holds for
  every move relation and cannot fail.
* **`create_total`, `glue_total`.** Create shifts the total colour by `−(q + r)` and glue by
  `q + r`. So one create closes exactly when `q + r = T`, one glue exactly when `q + r = −T`.
* **`same_label_blocked_gated`, `same_label_closes_ungated`.** A pair of equal labels has no
  non-collinear pair, so the gated relation cannot move it, while one ungated create closes it.
* **`gate_lengthens_witness`.** On `{(0,1), (0,1), (1,0), (2,0)}` no gated pair closes in one
  move, while the collinear pair `(0,1), (0,1)` closes in one ungated create.

The gate only removes moves, so it can only lengthen `d_G`; the census measures by how much.

No QLF axioms.
-/

namespace QLF.GluonAbelianControl

open QLF.ColourFlux

/-- **The first-singlet result is bookkeeping.** -/
theorem first_singlet_move_reduces {S : Type*} (singlet : S → Prop) (d : S → ℕ)
    (hd : ∀ s, d s = 0 ↔ singlet s) {s t : S} (hs : ¬ singlet s) (ht : singlet t) :
    d t < d s := by
  have h0 : d t = 0 := (hd t).2 ht
  have h1 : d s ≠ 0 := fun h => hs ((hd s).1 h)
  omega

/-- The third vertex leg. -/
def leg (q r : V) : V := -(q + r)

/-- **Create shifts the total by `−(q + r)`.** -/
theorem create_total (T q r : V) : T + leg q r = T - (q + r) := by
  simp [leg, sub_eq_add_neg]

/-- **Glue shifts the total by `q + r`.** The pair leaves and `−(q + r)` arrives, and
    `−2 = 1` in `F₃`. -/
theorem glue_total : ∀ T q r : V, T - (q + r) + leg q r = T + (q + r) := by
  unfold leg; decide

theorem glue_closes_iff : ∀ T q r : V, T - (q + r) + leg q r = 0 ↔ q + r = -T := by
  unfold leg; decide

theorem create_closes_iff (T q r : V) : T + leg q r = 0 ↔ q + r = T := by
  rw [create_total, sub_eq_zero, eq_comm]

/-- **Equal labels are blocked by the gate.** -/
theorem same_label_blocked_gated : ∀ q : V, symp q q = 0 := by decide

/-- **One ungated create closes a pair of equal nonzero labels.** -/
theorem same_label_closes_ungated :
    ∀ q : V, q ≠ 0 → q + q ≠ 0 ∧ q + q + leg q q = 0 := by decide

/-- The state `{(0,1), (0,1), (1,0), (2,0)}`. -/
def witness : List V := [(0, 1), (0, 1), (1, 0), (2, 0)]

/-- **The gate lengthens distance on the witness.** No non-collinear pair closes in one create or
    one glue; the collinear pair `(0,1), (0,1)` closes in one ungated create. -/
theorem gate_lengthens_witness :
    (∀ i j : Fin 4, i < j → symp (witness.get ⟨i, by simp [witness]⟩) (witness.get ⟨j, by simp [witness]⟩) ≠ 0 →
      (witness.get ⟨i, by simp [witness]⟩ + witness.get ⟨j, by simp [witness]⟩ ≠ witness.sum ∧
       witness.get ⟨i, by simp [witness]⟩ + witness.get ⟨j, by simp [witness]⟩ ≠ -witness.sum)) ∧
    symp ((0, 1) : V) (0, 1) = 0 ∧ ((0, 1) : V) + (0, 1) = witness.sum := by
  decide

end QLF.GluonAbelianControl
