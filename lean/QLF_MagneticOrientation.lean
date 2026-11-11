import QLF_PlaquetteArea
import QLF_HandedLoops

set_option linter.unusedVariables false

/-!
# QLF_MagneticOrientation — **events create space with an orientation**

Jim, 2026-11-11: *"its simple, events create space with an orientation"*, and asked how that
orientation shows up as magnetic attraction and repulsion, and as space being synthesized or
annihilated.

[`QLF_PlaquetteArea`](QLF_PlaquetteArea.lean) gives every history three shadows, its signed projected
areas on the `XY`, `XZ` and `YZ` planes (`projArea`), and shows the closure's phase is their parity.
The sign of a shadow is the loop's **orientation**, counter-clockwise or clockwise. The three signed
shadows together are the loop's oriented area vector, which in the continuum is its magnetic moment
(`m = ½ ∮ r × dr`). This module proves how oriented area combines.

* **`projArea_append`** — the shadows of closures **add**: a closure followed by any history has the
  sum of their signed areas on every plane. Area made by an event is kept by the next one.
* **`projArea_mirror`** — the mirror (Hermitian adjoint, `QLF_HandedLoops.mirror`: reverse the order,
  flip every handedness bit) of a closure has **the opposite orientation** on every plane.
* **`annihilation`** — a history followed by its mirror retraces its own path: it returns, it is a
  ZFA closure, its shadows on all three planes are zero and its holonomy is trivial. Oriented area and
  its opposite **annihilate**, and leave nothing.
* **`synthesis`** — a closure repeated `k` times encloses `k` times its area on every plane. Same
  orientation **synthesizes** space.
* **`joint_cost_pos_iff`** / **`joint_release_iff`** — for two closures with areas `A` and `B` on a
  plane, `(A+B)² − (A² + B²) = 2AB`. Joining two same-oriented events increases the square of the area,
  and joining opposite-oriented events decreases it.

**The magnetic reading (imported, labelled).** If magnetic action is quadratic in the enclosed flux,
as the Maxwell action is in `B`, then with flux quantized (each plaquette is one π quantum,
`QLF_EdgeSign`) the joint-cost identity is the fluxoid rule of type-II superconductors: two
same-sense flux quanta cost more action merged than apart, so they **repel**; opposite-sense quanta
cost less merged, so they **attract**, and merged completely they **annihilate** (`annihilation`).
This is the fixed-flux case, and matches vortex–vortex repulsion and vortex–antivortex annihilation.
The quadratic action is an input here, not derived, and the head-to-tail attraction of bar magnets
(fixed moment, stacked along the normal) is a different geometry that this module does not cover.

**Honest scope (method rule 4).** These are identities about how oriented area composes. None of them
changes a count of ways. What would: counting how many closures of length `L` have a given signed
area, and showing the joint census of two events favours the opposite-orientation pairing.

No axioms.
-/

namespace QLF.MagneticOrientation

open QLF QLF.PhaseRule QLF.EdgeSign QLF.PlaquetteArea QLF.HandedLoops

-- ==========================================
-- §1  Walks compose
-- ==========================================

/-- A history **returns** when its walk ends where it began on every axis. -/
def Returns (ts : List Twist) : Prop := ∀ a : Axis, position ts a = 0

theorem positionFrom_append (u v : List Twist) : ∀ x : Axis → ℤ,
    positionFrom x (u ++ v) = positionFrom (positionFrom x u) v := by
  induction u with
  | nil => intro x; rfl
  | cons t ts ih => intro x; exact ih (stepPos x t)

theorem lineInt_append (a b : Axis) (u v : List Twist) : ∀ x : Axis → ℤ,
    lineInt a b x (u ++ v) = lineInt a b x u + lineInt a b (positionFrom x u) v := by
  induction u with
  | nil => intro x; simp [lineInt, positionFrom]
  | cons t ts ih =>
      intro x
      simp only [List.cons_append, lineInt, positionFrom]
      rw [ih (stepPos x t)]
      ring

theorem position_zero_of_returns {u : List Twist} (hu : Returns u) :
    positionFrom (fun _ => 0) u = fun _ => 0 := by
  funext a
  exact hu a

/-- **Oriented area adds.** After a closure, the next history's shadows add to the closure's own, on
    every plane. -/
theorem projArea_append (a b : Axis) {u : List Twist} (hu : Returns u) (v : List Twist) :
    projArea a b (u ++ v) = projArea a b u + projArea a b v := by
  unfold projArea
  rw [lineInt_append, position_zero_of_returns hu]
  ring

theorem returns_append {u v : List Twist} (hu : Returns u) (hv : Returns v) :
    Returns (u ++ v) := by
  intro a
  unfold position
  rw [positionFrom_append, position_zero_of_returns hu]
  exact hv a

-- ==========================================
-- §2  The mirror retraces
-- ==========================================

theorem axisOf_conj (t : Twist) : axisOf t.conj = axisOf t := by
  cases t <;> rfl

theorem twistStep_conj (t : Twist) : twistStep t.conj = -twistStep t := by
  cases t <;> simp [twistStep, isNegTwist, Twist.conj]

/-- A step followed by its conjugate puts the walker back. -/
theorem stepPos_conj (x : Axis → ℤ) (t : Twist) : stepPos (stepPos x t) t.conj = x := by
  funext c
  unfold stepPos
  rw [axisOf_conj, twistStep_conj]
  split_ifs <;> ring

theorem mirror_cons (t : Twist) (ts : List Twist) : mirror (t :: ts) = mirror ts ++ [t.conj] := by
  simp [mirror]

/-- A history followed by its mirror returns to where it started, from any point. -/
theorem retrace_position (u : List Twist) : ∀ x : Axis → ℤ,
    positionFrom x (u ++ mirror u) = x := by
  induction u with
  | nil => intro x; rfl
  | cons t ts ih =>
      intro x
      rw [mirror_cons, ← List.append_assoc, List.cons_append, List.cons_append, positionFrom, positionFrom_append,
        ih (stepPos x t)]
      exact stepPos_conj x t

/-- A history followed by its mirror sweeps no area on any plane: every step is undone by its
    conjugate at the same place. -/
theorem retrace_lineInt {a b : Axis} (hab : a ≠ b) (u : List Twist) : ∀ x : Axis → ℤ,
    lineInt a b x (u ++ mirror u) = 0 := by
  induction u with
  | nil => intro x; rfl
  | cons t ts ih =>
      intro x
      rw [mirror_cons, ← List.append_assoc, List.cons_append, List.cons_append, lineInt, lineInt_append,
        ih (stepPos x t), retrace_position ts (stepPos x t)]
      simp only [lineInt, axisOf_conj, twistStep_conj]
      by_cases ha : axisOf t = a
      · rw [if_pos ha, if_pos ha, stepPos_of_ne x t (ha ▸ hab)]
        ring
      · rw [if_neg ha, if_neg ha]
        ring

theorem returns_retrace (u : List Twist) : Returns (u ++ mirror u) := by
  intro a
  unfold position
  rw [retrace_position]

/-- **Annihilation.** A history followed by its mirror returns, is a ZFA closure, has zero shadow
    on all three spatial planes, and has trivial holonomy. -/
theorem annihilation (u : List Twist) :
    Returns (u ++ mirror u) ∧ countBalanced (u ++ mirror u) ∧
      projArea Axis.X Axis.Y (u ++ mirror u) = 0 ∧
      projArea Axis.X Axis.Z (u ++ mirror u) = 0 ∧
      projArea Axis.Y Axis.Z (u ++ mirror u) = 0 ∧
      holonomy (u ++ mirror u) = 0 := by
  have hxy : projArea Axis.X Axis.Y (u ++ mirror u) = 0 := by
    unfold projArea; rw [retrace_lineInt (by decide)]; rfl
  have hxz : projArea Axis.X Axis.Z (u ++ mirror u) = 0 := by
    unfold projArea; rw [retrace_lineInt (by decide)]; rfl
  have hyz : projArea Axis.Y Axis.Z (u ++ mirror u) = 0 := by
    unfold projArea; rw [retrace_lineInt (by decide)]; rfl
  refine ⟨returns_retrace u, equal_and_opposite_balances u, hxy, hxz, hyz, ?_⟩
  rw [holonomy_eq_projected_areas, hxy, hxz, hyz]
  simp

/-- **The mirror reverses orientation.** A closure's mirror has the opposite signed area on every
    plane. -/
theorem projArea_mirror {a b : Axis} (hab : a ≠ b) {u : List Twist} (hu : Returns u) :
    projArea a b (mirror u) = -projArea a b u := by
  have h0 : projArea a b (u ++ mirror u) = 0 := by
    unfold projArea; rw [retrace_lineInt hab]; rfl
  rw [projArea_append a b hu] at h0
  linarith

theorem returns_mirror {u : List Twist} (hu : Returns u) : Returns (mirror u) := by
  intro a
  have h := returns_retrace u a
  unfold position at h ⊢
  rw [positionFrom_append, position_zero_of_returns hu] at h
  exact h

-- ==========================================
-- §3  Same orientation synthesizes
-- ==========================================

theorem returns_loopTrain {u : List Twist} (hu : Returns u) : ∀ k, Returns (loopTrain u k)
  | 0 => fun a => rfl
  | k + 1 => by rw [loopTrain_succ]; exact returns_append (returns_loopTrain hu k) hu

/-- **Synthesis.** A closure repeated `k` times encloses `k` times its oriented area on every plane. -/
theorem synthesis (a b : Axis) {u : List Twist} (hu : Returns u) :
    ∀ k : ℕ, projArea a b (loopTrain u k) = (k : ℤ) * projArea a b u
  | 0 => by simp [loopTrain, projArea, lineInt]
  | k + 1 => by
      rw [loopTrain_succ, projArea_append a b (returns_loopTrain hu k), synthesis a b hu k]
      push_cast
      ring

-- ==========================================
-- §4  Joining two oriented events
-- ==========================================

/-- The cross term of joining two oriented areas. -/
theorem joint_square (A B : ℤ) : (A + B) ^ 2 - (A ^ 2 + B ^ 2) = 2 * (A * B) := by ring

/-- Joining raises the squared area exactly when the two orientations agree. -/
theorem joint_cost_pos_iff (A B : ℤ) : A ^ 2 + B ^ 2 < (A + B) ^ 2 ↔ 0 < A * B := by
  constructor <;> intro h <;> nlinarith [joint_square A B]

/-- Joining lowers the squared area exactly when the two orientations are opposite. -/
theorem joint_release_iff (A B : ℤ) : (A + B) ^ 2 < A ^ 2 + B ^ 2 ↔ A * B < 0 := by
  constructor <;> intro h <;> nlinarith [joint_square A B]

/-- **Two oriented events on a plane.** For closures `u`, `v`, the joint history `u ++ v` carries the
    summed area, and its square exceeds the separate squares iff the orientations agree. -/
theorem joint_events (a b : Axis) {u : List Twist} (hu : Returns u) (v : List Twist) :
    projArea a b (u ++ v) = projArea a b u + projArea a b v ∧
      (projArea a b u ^ 2 + projArea a b v ^ 2 < projArea a b (u ++ v) ^ 2 ↔
        0 < projArea a b u * projArea a b v) ∧
      (projArea a b (u ++ v) ^ 2 < projArea a b u ^ 2 + projArea a b v ^ 2 ↔
        projArea a b u * projArea a b v < 0) := by
  rw [projArea_append a b hu]
  exact ⟨rfl, joint_cost_pos_iff _ _, joint_release_iff _ _⟩

/-- **An event and its mirror are opposite-oriented, and joined they annihilate.** For a closure with
    nonzero area on a plane, its mirror has the opposite sign there (so joining releases), and the
    joint area is zero. -/
theorem mirror_pair_annihilates {a b : Axis} (hab : a ≠ b) {u : List Twist} (hu : Returns u)
    (hA : projArea a b u ≠ 0) :
    projArea a b u * projArea a b (mirror u) < 0 ∧ projArea a b (u ++ mirror u) = 0 := by
  rw [projArea_mirror hab hu, projArea_append a b hu, projArea_mirror hab hu]
  refine ⟨?_, by ring⟩
  have : 0 < projArea a b u * projArea a b u := mul_self_pos.mpr hA
  linarith

-- ==========================================
-- §5  Worked cases
-- ==========================================

/-- The clockwise unit square `^>v<` returns and encloses `−1` on the `XY` plane. -/
theorem square_returns : Returns [Twist.up, Twist.right, Twist.down, Twist.left] := by
  intro a; cases a <;> decide

theorem square_area : projArea Axis.X Axis.Y [Twist.up, Twist.right, Twist.down, Twist.left] = -1 := by
  decide

/-- Its mirror is the counter-clockwise square, area `+1`. -/
theorem square_mirror_area :
    projArea Axis.X Axis.Y (mirror [Twist.up, Twist.right, Twist.down, Twist.left]) = 1 := by
  decide

/-- Two same-sense squares synthesize area `−2`; a square and its mirror annihilate to `0`. -/
theorem square_pair :
    projArea Axis.X Axis.Y (loopTrain [Twist.up, Twist.right, Twist.down, Twist.left] 2) = -2 ∧
    projArea Axis.X Axis.Y ([Twist.up, Twist.right, Twist.down, Twist.left] ++
      mirror [Twist.up, Twist.right, Twist.down, Twist.left]) = 0 := by
  constructor <;> decide

end QLF.MagneticOrientation
