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
* **`fixed_distance_iff`** — reading the space between two poles as the running sum of those cross
  terms, **a fixed distance has equal space orientation**: like and opposite pairings equal in number.
  **`like_poles_expand`**, **`opposite_poles_destroy`**: like poles make `2n` units, opposite poles
  remove `2n`. **`fixed_distance_is_balanced`**: a fixed distance is a balanced (ZFA) string of
  relative orientations.

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

-- ==========================================
-- §6  A fixed distance has equal space orientation
-- ==========================================

/-! Jim, 2026-11-11: *"prove a fixed distance has equal space orientation, like poles expand space,
opposite poles destroy space."*

Two poles exchange events. Each event pairs one unit of oriented space from each pole, up or down
(`true` / `false`), and §4 says what joining them does: the squared area changes by the cross term
`2AB`. With unit orientations that is `+2` when the poles agree and `−2` when they are opposite. The
space between the poles is the running sum of those cross terms, so it holds still exactly when like
and opposite pairings come in equal numbers. -/

/-- The signed unit area of an orientation: up `+1`, down `−1`. -/
def unitArea (b : Bool) : ℤ := if b then 1 else -1

/-- **The space one joint event makes**: the cross term `(A+B)² − (A² + B²)` for two unit areas. -/
def jointSpace (p q : Bool) : ℤ := (unitArea p + unitArea q) ^ 2 - (unitArea p ^ 2 + unitArea q ^ 2)

/-- Like orientations make two units of space; opposite orientations destroy two. -/
theorem jointSpace_eq (p q : Bool) : jointSpace p q = if p = q then 2 else -2 := by
  cases p <;> cases q <;> decide

/-- The space made between two poles over a run of joint events. -/
def netSpace : List (Bool × Bool) → ℤ
  | [] => 0
  | e :: es => jointSpace e.1 e.2 + netSpace es

/-- Joint events whose poles agree. -/
def likeCount (es : List (Bool × Bool)) : ℕ := es.countP (fun e => e.1 == e.2)

/-- Joint events whose poles are opposite. -/
def oppositeCount (es : List (Bool × Bool)) : ℕ := es.countP (fun e => !(e.1 == e.2))

theorem netSpace_eq (es : List (Bool × Bool)) :
    netSpace es = 2 * ((likeCount es : ℤ) - (oppositeCount es : ℤ)) := by
  induction es with
  | nil => simp [netSpace, likeCount, oppositeCount]
  | cons e es ih =>
      obtain ⟨p, q⟩ := e
      simp only [netSpace, likeCount, oppositeCount, List.countP_cons] at ih ⊢
      rw [ih, jointSpace_eq]
      cases p <;> cases q <;> simp <;> ring

/-- **A fixed distance has equal space orientation.** The space between two poles is unchanged by a
    run of joint events exactly when as many of them pair like orientations as pair opposite ones. -/
theorem fixed_distance_iff (es : List (Bool × Bool)) :
    netSpace es = 0 ↔ likeCount es = oppositeCount es := by
  rw [netSpace_eq]
  constructor
  · intro h; omega
  · intro h; rw [h]; ring

/-- **Like poles expand space.** If every joint event pairs like orientations, `n` events make `2n`
    units of space. -/
theorem like_poles_expand (es : List (Bool × Bool)) (h : ∀ e ∈ es, e.1 = e.2) :
    netSpace es = 2 * es.length := by
  induction es with
  | nil => simp [netSpace]
  | cons e es ih =>
      simp only [netSpace, List.length_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), jointSpace_eq,
        if_pos (h e (List.mem_cons_self))]
      push_cast; ring

/-- **Opposite poles destroy space.** If every joint event pairs opposite orientations, `n` events
    remove `2n` units. -/
theorem opposite_poles_destroy (es : List (Bool × Bool)) (h : ∀ e ∈ es, e.1 ≠ e.2) :
    netSpace es = -(2 * es.length) := by
  induction es with
  | nil => simp [netSpace]
  | cons e es ih =>
      simp only [netSpace, List.length_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), jointSpace_eq,
        if_neg (h e (List.mem_cons_self))]
      push_cast; ring

/-- **The relative orientation is a ZFA string.** Read each joint event by its relative orientation,
    like (`+`) or opposite (`−`). A fixed distance is exactly a balanced string: equal and opposite
    relative orientation, the ZFA condition on the one axis that separates the poles. -/
theorem fixed_distance_is_balanced (es : List (Bool × Bool)) :
    netSpace es = 0 ↔
      (es.map (fun e => e.1 == e.2)).count true = (es.map (fun e => e.1 == e.2)).count false := by
  rw [fixed_distance_iff, likeCount, oppositeCount, List.count_eq_countP, List.count_eq_countP,
    List.countP_map, List.countP_map]
  have h1 : ((fun x => x == true) ∘ fun e : Bool × Bool => e.1 == e.2) = fun e => e.1 == e.2 := by
    funext e; obtain ⟨a, b⟩ := e; cases a <;> cases b <;> rfl
  have h2 : ((fun x => x == false) ∘ fun e : Bool × Bool => e.1 == e.2) =
      fun e => !(e.1 == e.2) := by
    funext e; obtain ⟨a, b⟩ := e; cases a <;> cases b <;> rfl
  rw [h1, h2]

-- ==========================================
-- §7  Every pairing of two bodies: moments for orientation, counts for the rest
-- ==========================================

/-! Two bodies, each a list of oriented units (up `true`, down `false`). Let every unit of one pair
with every unit of the other. The number of pairings is the product of the sizes, blind to
orientation. The space they make is the product of the bodies' net orientations (their moments). So
a body with as many ups as downs holds every distance under the orientation term, whatever it is
paired with: what is left between neutral bodies is only the orientation-blind count. -/

/-- Every unit of `A` paired with every unit of `B`. -/
def allPairings (A B : List Bool) : List (Bool × Bool) := A.flatMap (fun p => B.map (fun q => (p, q)))

/-- The net orientation of a body: ups minus downs, its moment. -/
def moment : List Bool → ℤ
  | [] => 0
  | p :: ps => unitArea p + moment ps

theorem jointSpace_eq_mul (p q : Bool) : jointSpace p q = 2 * (unitArea p * unitArea q) := by
  cases p <;> cases q <;> decide

theorem netSpace_append (l m : List (Bool × Bool)) : netSpace (l ++ m) = netSpace l + netSpace m := by
  induction l with
  | nil => simp [netSpace]
  | cons e es ih => simp only [List.cons_append, netSpace, ih]; ring

theorem netSpace_row (p : Bool) (B : List Bool) :
    netSpace (B.map (fun q => (p, q))) = 2 * (unitArea p * moment B) := by
  induction B with
  | nil => simp [netSpace, moment]
  | cons q qs ih => simp only [List.map_cons, netSpace, moment, ih, jointSpace_eq_mul]; ring

/-- **The space two bodies make is the product of their moments.** -/
theorem netSpace_allPairings (A B : List Bool) :
    netSpace (allPairings A B) = 2 * (moment A * moment B) := by
  induction A with
  | nil => simp [allPairings, netSpace, moment]
  | cons p ps ih =>
      have h : allPairings (p :: ps) B = B.map (fun q => (p, q)) ++ allPairings ps B := by
        simp [allPairings, List.flatMap_cons]
      rw [h, netSpace_append, netSpace_row, ih, moment]
      ring

/-- **The number of pairings is the product of the sizes**, whatever the orientations. -/
theorem allPairings_length (A B : List Bool) : (allPairings A B).length = A.length * B.length := by
  induction A with
  | nil => simp [allPairings]
  | cons p ps ih =>
      have h : allPairings (p :: ps) B = B.map (fun q => (p, q)) ++ allPairings ps B := by
        simp [allPairings, List.flatMap_cons]
      rw [h, List.length_append, List.length_map, ih, List.length_cons]
      ring

/-- **Neutral bodies hold every distance under the orientation term.** If one body has zero moment,
    the space made by all pairings with any other body is zero, while the number of pairings is still
    the product of the sizes. -/
theorem neutral_holds_distance (A B : List Bool) (hA : moment A = 0) :
    netSpace (allPairings A B) = 0 ∧ (allPairings A B).length = A.length * B.length := by
  refine ⟨?_, allPairings_length A B⟩
  rw [netSpace_allPairings, hA]
  ring

/-- **Like poles expand, opposite poles destroy, for whole bodies.** Space is made iff the moments
    agree in sign, destroyed iff they are opposite. -/
theorem bodies_expand_iff (A B : List Bool) :
    0 < netSpace (allPairings A B) ↔ 0 < moment A * moment B := by
  rw [netSpace_allPairings]; constructor <;> intro h <;> linarith

theorem bodies_destroy_iff (A B : List Bool) :
    netSpace (allPairings A B) < 0 ↔ moment A * moment B < 0 := by
  rw [netSpace_allPairings]; constructor <;> intro h <;> linarith

end QLF.MagneticOrientation
