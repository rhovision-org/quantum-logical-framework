import QLF_EdgeSign
import Mathlib.Tactic.Linarith
-- Narrow imports, as in QLF_EdgeSign: this module stays off `import Mathlib`.

set_option linter.unusedVariables false

/-!
# QLF_PlaquetteArea — **in a plane, the closure phase counts the enclosed area**

[`QLF_EdgeSign`](QLF_EdgeSign.lean) puts the phase of a history on the edges of its walk: a ℤ₂
connection on `ℤ⁴` with π flux through every mixed spatial plaquette, the phase being the holonomy.
That module decides individual squares (`^>v<` is `−1`, `^><v` is `+1`). This one says what the
holonomy of a planar loop *is*: **one bit per unit of enclosed area**. It is the lattice form of
Stokes' (Green's) theorem for a connection of constant flux.

The physical reading (Jim, 2026-11-09: *does one up/down entanglement team with a left/right
entanglement to make a closure?*). An up/down pair alone closes on its own axis and encloses
nothing; so does a left/right pair. Interleaved, the two pairs bound an area, and the closure's sign
is the parity of that area. A closure's phase is therefore not a property of its pairs one at a
time, but of how they are woven together — the pairs *team*, and the team carries a quantity
neither pair has.

* **`xDy_add_yDx`** — the discrete product rule: `∮x dy + ∮y dx = Δ(xy)`, exactly, for every walk
  (the lattice has no second-order term because every step moves one axis).
* **`shoelace_eq_two_area`** — for a walk that returns in `X`, the shoelace sum `∮x dy − ∮y dx` is
  twice `enclosedArea`, so the shoelace area of a lattice loop is an integer.
* **`holonomy_eq_area_parity`** — for any history with no `Z` twist (the `XY` plane, gauge steps
  allowed), the holonomy is `enclosedArea` mod 2.
* **`connectionPhase_planar`** / **`fold_eq_area_phase`** — so the phase is
  `(−1)^{#neg} · (−1)^{area}`, and for a balanced planar history that scalar *is* the Pauli fold.
* **`area_zero_of_no_X`** — a loop with no left/right twist encloses nothing: a single-axis
  closure carries no area bit.

`closure_walk.py`'s data agree: 0 mismatches over the 68,844 planar closures of length `≤ 10`.

No axioms.
-/

namespace QLF.PlaquetteArea

open QLF QLF.PhaseRule QLF.EdgeSign

-- ==========================================
-- The two line integrals
-- ==========================================

/-- `∮ y dx` along a walk from `x`: each `X` step contributes the current `y` times its sign. -/
def yDxAux (x : Axis → ℤ) : List Twist → ℤ
  | [] => 0
  | t :: ts => (if axisOf t = Axis.X then x Axis.Y * twistStep t else 0) + yDxAux (stepPos x t) ts

/-- `∮ x dy` along a walk from `x`: each `Y` step contributes the current `x` times its sign. -/
def xDyAux (x : Axis → ℤ) : List Twist → ℤ
  | [] => 0
  | t :: ts => (if axisOf t = Axis.Y then x Axis.X * twistStep t else 0) + xDyAux (stepPos x t) ts

/-- **The enclosed (signed) area** of a history's walk in the `XY` plane: `−∮ y dx` from the
    origin. Counter-clockwise loops are positive. -/
def enclosedArea (ts : List Twist) : ℤ := -yDxAux (fun _ => 0) ts

/-- The shoelace sum `∮ x dy − ∮ y dx` — twice the area, by the usual formula. -/
def shoelace (ts : List Twist) : ℤ := xDyAux (fun _ => 0) ts - yDxAux (fun _ => 0) ts

-- ==========================================
-- Green's theorem on the lattice
-- ==========================================

/-- One step of the product rule: the two increments add up to the change in `x·y`. -/
theorem xy_step (x : Axis → ℤ) (t : Twist) :
    (if axisOf t = Axis.Y then x Axis.X * twistStep t else 0)
      + (if axisOf t = Axis.X then x Axis.Y * twistStep t else 0)
      = stepPos x t Axis.X * stepPos x t Axis.Y - x Axis.X * x Axis.Y := by
  cases t <;> simp [axisOf, stepPos] <;> ring

/-- **The discrete product rule**: `∮x dy + ∮y dx = Δ(xy)`, exactly, for every walk. -/
theorem xDy_add_yDx (ts : List Twist) : ∀ x : Axis → ℤ,
    xDyAux x ts + yDxAux x ts
      = positionFrom x ts Axis.X * positionFrom x ts Axis.Y - x Axis.X * x Axis.Y := by
  induction ts with
  | nil => intro x; simp [xDyAux, yDxAux, positionFrom]
  | cons t ts ih =>
      intro x
      have h1 := ih (stepPos x t)
      have h2 := xy_step x t
      simp only [xDyAux, yDxAux, positionFrom]
      linarith

/-- **The shoelace area of a lattice loop is twice an integer.** Once the walk is back on the
    `Y` axis (`X` returns to `0`), `∮x dy = −∮y dx`, so `shoelace = 2 · enclosedArea`. -/
theorem shoelace_eq_two_area (ts : List Twist) (h : position ts Axis.X = 0) :
    shoelace ts = 2 * enclosedArea ts := by
  have hp := xDy_add_yDx ts (fun _ => 0)
  simp only [mul_zero, sub_zero] at hp
  unfold position at h
  rw [h, zero_mul] at hp
  unfold shoelace enclosedArea
  linarith

-- ==========================================
-- The holonomy of a planar walk
-- ==========================================

/-- A step off axis `b` leaves coordinate `b` alone. -/
theorem stepPos_of_ne (x : Axis → ℤ) (t : Twist) {b : Axis} (h : axisOf t ≠ b) :
    stepPos x t b = x b := by
  simp [stepPos, h]

/-- In the plane `x_Z = 0`, the connection increment is the `∮ y dx` increment mod 2. -/
theorem step_parity (x : Axis → ℤ) (t : Twist) (ht : axisOf t ≠ Axis.Z) (hz : x Axis.Z = 0) :
    edgeParity (posMod x) (axisOf t)
      = (((if axisOf t = Axis.X then x Axis.Y * twistStep t else 0 : ℤ)) : ZMod 2) := by
  cases t <;> simp [axisOf] at ht ⊢ <;> simp [edgeParity, posMod, hz, twistStep_cast]

/-- The walk's holonomy from any point of the plane is `∮ y dx` mod 2, as long as it stays there. -/
theorem holAux_planar (ts : List Twist) : ∀ x : Axis → ℤ,
    (∀ t ∈ ts, axisOf t ≠ Axis.Z) → x Axis.Z = 0 → holAux x ts = ((yDxAux x ts : ℤ) : ZMod 2) := by
  induction ts with
  | nil => intro x _ _; simp [holAux, yDxAux]
  | cons t ts ih =>
      intro x hp hz
      have ht : axisOf t ≠ Axis.Z := hp t (by simp)
      have hz' : stepPos x t Axis.Z = 0 := by rw [stepPos_of_ne x t ht, hz]
      have hp' : ∀ u ∈ ts, axisOf u ≠ Axis.Z := fun u hu => hp u (by simp [hu])
      simp only [holAux, yDxAux]
      rw [Int.cast_add, step_parity x t ht hz, ih (stepPos x t) hp' hz']

/-- Negation is the identity mod 2. -/
theorem zmod2_neg (a : ZMod 2) : -a = a := by
  revert a; decide

/-- **The holonomy is the area parity.** For any history with no `Z` twist, the ℤ₂ holonomy of its
    walk is its enclosed area mod 2: one π flux quantum per unit cell enclosed. -/
theorem holonomy_eq_area_parity (ts : List Twist) (hp : ∀ t ∈ ts, axisOf t ≠ Axis.Z) :
    holonomy ts = ((enclosedArea ts : ℤ) : ZMod 2) := by
  unfold holonomy enclosedArea
  rw [holAux_planar ts (fun _ => 0) hp rfl, Int.cast_neg, zmod2_neg]

/-- **The planar phase**: `(−1)^{#neg} · (−1)^{area}` — the sign content times one bit per enclosed
    cell. -/
theorem connectionPhase_planar (ts : List Twist) (hp : ∀ t ∈ ts, axisOf t ≠ Axis.Z) :
    connectionPhase ts = (-1 : ℤ) ^ negCount ts * sgn ((enclosedArea ts : ℤ) : ZMod 2) := by
  have h := holonomy_eq_area_parity ts hp
  unfold holonomy at h
  unfold connectionPhase
  rw [connAux_eq, h]

/-- **The fold of a balanced planar closure is its area phase.** The `2×2` Pauli product equals
    `(−1)^{#neg} · (−1)^{area}` times the identity. -/
theorem fold_eq_area_phase {ts : List Twist} (h : countBalanced ts)
    (hp : ∀ t ∈ ts, axisOf t ≠ Axis.Z) :
    twistMatrixFold ts
      = ((((-1 : ℤ) ^ negCount ts * sgn ((enclosedArea ts : ℤ) : ZMod 2) : ℤ)) : ℂ) • (1 : M) := by
  rw [fold_eq_connectionPhase h, connectionPhase_planar ts hp]

/-- **A single-axis loop encloses nothing.** With no `X` (left/right) twist there is no `∮ y dx`,
    so an up/down closure alone carries no area bit — the area needs both pairs. -/
theorem yDxAux_eq_zero_of_no_X (ts : List Twist) : ∀ x : Axis → ℤ,
    (∀ t ∈ ts, axisOf t ≠ Axis.X) → yDxAux x ts = 0 := by
  induction ts with
  | nil => intro x _; simp [yDxAux]
  | cons t ts ih =>
      intro x hp
      have ht : axisOf t ≠ Axis.X := hp t (by simp)
      have hp' : ∀ u ∈ ts, axisOf u ≠ Axis.X := fun u hu => hp u (by simp [hu])
      simp only [yDxAux]
      rw [if_neg ht, ih (stepPos x t) hp', add_zero]

theorem area_zero_of_no_X (ts : List Twist) (hp : ∀ t ∈ ts, axisOf t ≠ Axis.X) :
    enclosedArea ts = 0 := by
  unfold enclosedArea
  rw [yDxAux_eq_zero_of_no_X ts (fun _ => 0) hp, neg_zero]

-- ==========================================
-- The squares, decided
-- ==========================================

/-- `^>v<` goes round one cell clockwise: area `−1`, hence the π flux of `plaquette_yx`. -/
theorem area_yx : enclosedArea [Twist.up, Twist.right, Twist.down, Twist.left] = -1 := by decide

/-- `^<v>` goes round it counter-clockwise: area `+1`. -/
theorem area_yx_ccw : enclosedArea [Twist.up, Twist.left, Twist.down, Twist.right] = 1 := by decide

/-- `^><v` uses the same four twists but folds back on itself: area `0`, hence the `+1` of
    `plaquette_yx_other_order`. The order changes the sign *because* it changes the area. -/
theorem area_yx_other_order :
    enclosedArea [Twist.up, Twist.right, Twist.left, Twist.down] = 0 := by decide

/-- Twice round: area `−2`, even, hence the `+1` of `plaquette_twice`. -/
theorem area_twice :
    enclosedArea [Twist.up, Twist.right, Twist.down, Twist.left,
                  Twist.up, Twist.right, Twist.down, Twist.left] = -2 := by decide

/-- A `2×1` rectangle `^^>vv<`: area `−2`, so two cells' flux cancel. -/
theorem area_rectangle :
    enclosedArea [Twist.up, Twist.up, Twist.right, Twist.down, Twist.down, Twist.left] = -2 := by
  decide

end QLF.PlaquetteArea
