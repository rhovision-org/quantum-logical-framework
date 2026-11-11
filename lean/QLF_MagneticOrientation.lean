import QLF_PlaquetteArea
import QLF_HandedLoops
import QLF_KraftMeasure
import QLF_HolographicBoundary

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

**The one count (§9).** `closure_area_symmetric`: at every length, as many closures enclose signed
area `A` on a plane as `−A`, because the mirror is an involution on closures that negates area; so
`vacuum_net_orientation_zero`, the vacuum's total oriented area is zero at every length.

**Honest scope (method rule 4).** Apart from §9 these are identities about how oriented area composes. None of them
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

-- ==========================================
-- §8  Bending preserves balance
-- ==========================================

/-! Jim, 2026-11-11: *"the orientation bends with curvature"*. Carried round a loop, an orientation
comes back flipped exactly when the loop's holonomy is odd (`holonomy_eq_projected_areas`). A body
carried round one loop is flipped as a whole: every unit by the same holonomy bit. -/

/-- Carry every unit of a body round a loop of holonomy bit `h`: flip all of them iff `h`. -/
def transport (h : Bool) (A : List Bool) : List Bool := A.map (fun p => xor h p)

theorem unitArea_xor (h p : Bool) : unitArea (xor h p) = (if h then -1 else 1) * unitArea p := by
  cases h <;> cases p <;> decide

/-- Transport multiplies the moment by the holonomy sign. -/
theorem moment_transport (h : Bool) (A : List Bool) :
    moment (transport h A) = (if h then -1 else 1) * moment A := by
  induction A with
  | nil => simp [transport, moment]
  | cons p ps ih =>
      simp only [transport, List.map_cons, moment] at ih ⊢
      rw [ih, unitArea_xor]; ring

theorem transport_length (h : Bool) (A : List Bool) : (transport h A).length = A.length := by
  simp [transport]

/-- **Bending preserves balance.** Carried round any loop, a balanced body stays balanced, it keeps
    its size, and so its pairing count with any other body is unchanged while the space it makes stays
    zero. Gravity, read as the orientation-blind count, is the same in curved and flat regions. -/
theorem bending_preserves_balance (h : Bool) (A B : List Bool) (hA : moment A = 0) :
    moment (transport h A) = 0 ∧
      netSpace (allPairings (transport h A) B) = 0 ∧
      (allPairings (transport h A) B).length = A.length * B.length := by
  have hm : moment (transport h A) = 0 := by rw [moment_transport, hA]; ring
  refine ⟨hm, (neutral_holds_distance _ B hm).1, ?_⟩
  rw [allPairings_length, transport_length]

/-- Two bodies carried round loops with bits `h`, `k`: the space they make is multiplied by the
    product of the two holonomy signs, and the pairing count does not change. -/
theorem transport_pair (h k : Bool) (A B : List Bool) :
    netSpace (allPairings (transport h A) (transport k B)) =
        (if h then -1 else 1) * (if k then -1 else 1) * netSpace (allPairings A B) ∧
      (allPairings (transport h A) (transport k B)).length = (allPairings A B).length := by
  refine ⟨?_, ?_⟩
  · rw [netSpace_allPairings, netSpace_allPairings, moment_transport, moment_transport]; ring
  · rw [allPairings_length, allPairings_length, transport_length, transport_length]

-- ==========================================
-- §9  The vacuum is balanced in orientation
-- ==========================================

/-! The census reason gravity sees balance. Among all closures of a given length, the mirror pairs
each one with another of the same length whose oriented area is the opposite on every plane. So the
census of closures by signed area is exactly symmetric: as many ways enclose `+A` as `−A`, and the
vacuum's total oriented area is zero at every length. This is a statement about counts of ways. -/

private instance decCB : DecidablePred countBalanced := fun ts => by
  unfold countBalanced; infer_instance

/-- All closures of length `L`: the count-balanced twist histories. -/
def closures (L : ℕ) : Finset (List Twist) :=
  (words Twist L).filter (fun ts => decide (countBalanced ts))

theorem conj_conj (t : Twist) : t.conj.conj = t := by cases t <;> rfl

theorem mirror_mirror (u : List Twist) : mirror (mirror u) = u := by
  simp [mirror, List.map_reverse, Function.comp_def, conj_conj]

theorem countBalanced_mirror {u : List Twist} (hu : countBalanced u) : countBalanced (mirror u) := by
  rw [zfa_iff_handedness_balanced] at hu ⊢
  intro a
  rw [handednessOn_mirror, hu a]
  simp

theorem returns_of_balanced {u : List Twist} (hu : countBalanced u) : Returns u := by
  intro a
  have h := (QLF.HolographicBoundary.position_eq_zero_iff u).mpr hu
  exact congrFun h a

theorem mirror_mem_closures {L : ℕ} {u : List Twist} (hu : u ∈ closures L) :
    mirror u ∈ closures L := by
  simp only [closures, Finset.mem_filter, mem_words, decide_eq_true_eq] at hu ⊢
  exact ⟨by rw [mirror_length]; exact hu.1, countBalanced_mirror hu.2⟩

/-- **The orientation census is symmetric.** At every length, as many closures enclose signed area
    `A` on a plane as enclose `−A`. -/
theorem closure_area_symmetric {a b : Axis} (hab : a ≠ b) (L : ℕ) (A : ℤ) :
    ((closures L).filter (fun u => projArea a b u = A)).card =
      ((closures L).filter (fun u => projArea a b u = -A)).card := by
  apply Finset.card_bij' (fun u _ => mirror u) (fun u _ => mirror u)
  · intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    refine ⟨mirror_mem_closures hu.1, ?_⟩
    have hb : countBalanced u := by
      simp only [closures, Finset.mem_filter, decide_eq_true_eq] at hu; exact hu.1.2
    rw [projArea_mirror hab (returns_of_balanced hb), hu.2]
  · intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    refine ⟨mirror_mem_closures hu.1, ?_⟩
    have hb : countBalanced u := by
      simp only [closures, Finset.mem_filter, decide_eq_true_eq] at hu; exact hu.1.2
    rw [projArea_mirror hab (returns_of_balanced hb), hu.2, neg_neg]
  · intro u _; exact mirror_mirror u
  · intro u _; exact mirror_mirror u

/-- **The vacuum carries zero net orientation.** Summed over every closure of length `L`, the signed
    area on any plane is zero. -/
theorem vacuum_net_orientation_zero {a b : Axis} (hab : a ≠ b) (L : ℕ) :
    ∑ u ∈ closures L, projArea a b u = 0 := by
  have h : ∑ u ∈ closures L, projArea a b u = ∑ u ∈ closures L, projArea a b (mirror u) := by
    apply Finset.sum_nbij' mirror mirror
    · intro u hu; exact mirror_mem_closures hu
    · intro u hu; exact mirror_mem_closures hu
    · intro u _; exact mirror_mirror u
    · intro u _; exact mirror_mirror u
    · intro u _; rw [mirror_mirror]
  have h2 : ∑ u ∈ closures L, projArea a b (mirror u) = -∑ u ∈ closures L, projArea a b u := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have hb : countBalanced u := by
      simp only [closures, Finset.mem_filter, decide_eq_true_eq] at hu; exact hu.2
    exact projArea_mirror hab (returns_of_balanced hb)
  linarith

-- ==========================================
-- §10  The census is axis-blind: γ = 1
-- ==========================================

/-! Jim, 2026-11-11: *"distance equals delay."* Every step runs at `c`, so a step on the gauge axis
is delay in time and a step on a spatial axis is delay in space. In the weak field, light passing a
mass is late by `(1 + γ)` times the Newtonian amount: `1` from slowed clocks (the time part) and `γ`
from stretched space. GR has `γ = 1`; Cassini measured `γ − 1 = (2.1 ± 2.3) × 10⁻⁵`.

What the census gives: swapping the gauge axis with any spatial axis is a bijection on closures of
each length (count balance treats the four axes alike), so summed over all closures of length `L`,
every axis receives exactly the same number of steps. If the delay that balance adds to each axis is
proportional to that axis's share of the census (the reading, labelled below), the time part and the
part along each spatial axis are equal, which is `γ = 1`. -/

private instance lawfulBEqTwist : LawfulBEq Twist where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

/-- Swap two axes in the frame, keeping every twist's sign. -/
def axSwap (a b c : Axis) : Axis := if c = a then b else if c = b then a else c

/-- The twist with its axis relabelled by `axSwap a b` and its handedness kept. -/
def swapTw (a b : Axis) (t : Twist) : Twist :=
  if isNegTwist t then leftTwist (axSwap a b (axisOf t)) else rightTwist (axSwap a b (axisOf t))

theorem axSwap_invol (a b c : Axis) : axSwap a b (axSwap a b c) = c := by
  cases a <;> cases b <;> cases c <;> decide

theorem swapTw_invol (a b : Axis) (t : Twist) : swapTw a b (swapTw a b t) = t := by
  cases a <;> cases b <;> cases t <;> decide

theorem swapTw_right (a b c : Axis) : swapTw a b (rightTwist c) = rightTwist (axSwap a b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem swapTw_left (a b c : Axis) : swapTw a b (leftTwist c) = leftTwist (axSwap a b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem axisOf_swapTw (a b : Axis) (t : Twist) : axisOf (swapTw a b t) = axSwap a b (axisOf t) := by
  cases a <;> cases b <;> cases t <;> decide

theorem swapTw_injective (a b : Axis) : Function.Injective (swapTw a b) := by
  intro x y h
  have := congrArg (swapTw a b) h
  rwa [swapTw_invol, swapTw_invol] at this

theorem count_map_swap (a b : Axis) (u : List Twist) (t : Twist) :
    (u.map (swapTw a b)).count t = u.count (swapTw a b t) := by
  conv_lhs => rw [← swapTw_invol a b t]
  exact List.count_map_of_injective u (swapTw a b) (swapTw_injective a b) _

theorem handednessOn_swap (a b c : Axis) (u : List Twist) :
    handednessOn c (u.map (swapTw a b)) = handednessOn (axSwap a b c) u := by
  unfold handednessOn
  rw [count_map_swap, count_map_swap, swapTw_right, swapTw_left]

theorem countBalanced_swap (a b : Axis) (u : List Twist) :
    countBalanced (u.map (swapTw a b)) ↔ countBalanced u := by
  rw [zfa_iff_handedness_balanced, zfa_iff_handedness_balanced]
  constructor
  · intro h c
    have := h (axSwap a b c)
    rwa [handednessOn_swap, axSwap_invol] at this
  · intro h c
    rw [handednessOn_swap]
    exact h _

/-- Steps a history spends on axis `a`. -/
def stepsOn (a : Axis) (u : List Twist) : ℕ := u.countP (fun t => decide (axisOf t = a))

theorem stepsOn_swap (a b c : Axis) (u : List Twist) :
    stepsOn c (u.map (swapTw a b)) = stepsOn (axSwap a b c) u := by
  unfold stepsOn
  rw [List.countP_map]
  congr 1
  funext t
  simp only [Function.comp_apply, axisOf_swapTw]
  apply decide_eq_decide.mpr
  constructor
  · intro h; rw [← h, axSwap_invol]
  · intro h; rw [h, axSwap_invol]

theorem swap_mem_closures (a b : Axis) {L : ℕ} {u : List Twist} (hu : u ∈ closures L) :
    u.map (swapTw a b) ∈ closures L := by
  simp only [closures, Finset.mem_filter, mem_words, decide_eq_true_eq] at hu ⊢
  exact ⟨by rw [List.length_map]; exact hu.1, (countBalanced_swap a b u).mpr hu.2⟩

theorem axSwap_right (a b : Axis) : axSwap a b b = a := by
  cases a <;> cases b <;> decide

/-- **The census is axis-blind.** Summed over all closures of length `L`, every axis receives the
    same number of steps; in particular the gauge (time) axis gets exactly what each spatial axis
    gets. -/
theorem census_axis_blind (a b : Axis) (L : ℕ) :
    ∑ u ∈ closures L, stepsOn a u = ∑ u ∈ closures L, stepsOn b u := by
  apply Finset.sum_nbij' (fun u => u.map (swapTw a b)) (fun u => u.map (swapTw a b))
  · intro u hu; exact swap_mem_closures a b hu
  · intro u hu; exact swap_mem_closures a b hu
  · intro u _; simp [List.map_map, Function.comp_def, swapTw_invol]
  · intro u _; simp [List.map_map, Function.comp_def, swapTw_invol]
  · intro u _; rw [stepsOn_swap, axSwap_right]

/-- **`γ = 1` from the census.** Read the PPN `γ` as the delay weight of a spatial axis over that of
    the time axis, each weight being the axis's share of the closure census. At every length where
    the census is nonempty the ratio is exactly `1`, and the Shapiro factor `1 + γ` is `2`, GR's
    value. The reading (delay per axis ∝ census share) is the step this theorem does not prove. -/
noncomputable def censusGamma (L : ℕ) (s : Axis) : ℚ :=
  ((∑ u ∈ closures L, stepsOn s u : ℕ) : ℚ) / ((∑ u ∈ closures L, stepsOn Axis.I u : ℕ) : ℚ)

theorem censusGamma_eq_one (L : ℕ) (s : Axis) (h : ∑ u ∈ closures L, stepsOn Axis.I u ≠ 0) :
    censusGamma L s = 1 ∧ 1 + censusGamma L s = 2 := by
  have he : censusGamma L s = 1 := by
    unfold censusGamma
    rw [census_axis_blind s Axis.I L]
    exact div_self (by exact_mod_cast h)
  exact ⟨he, by rw [he]; norm_num⟩

/-- The census is nonempty on the gauge axis at every even length: `+^k −^k` is a closure. -/
theorem gauge_steps_pos (k : ℕ) : ∑ u ∈ closures (2 * (k + 1)), stepsOn Axis.I u ≠ 0 := by
  have hmem : List.replicate (k + 1) Twist.plus ++ List.replicate (k + 1) Twist.minus ∈
      closures (2 * (k + 1)) := by
    simp only [closures, Finset.mem_filter, mem_words, decide_eq_true_eq]
    refine ⟨by simp; ring, ?_⟩
    unfold countBalanced
    simp [List.count_replicate]
  have hpos : 0 < stepsOn Axis.I (List.replicate (k + 1) Twist.plus ++
      List.replicate (k + 1) Twist.minus) := by
    unfold stepsOn
    simp [List.countP_replicate, axisOf]
  have hle := Finset.single_le_sum (f := fun u => stepsOn Axis.I u)
    (fun _ _ => Nat.zero_le _) hmem
  omega

-- ==========================================
-- §11  Classes of magnetism
-- ==========================================

/-! Jim, 2026-11-11: *"should we consider classes of magnetism effects, anti, ferro, ferri?"* A body
is a list of oriented units; its size `n` and moment `m` (ups minus downs) are the two numbers the
pairing split reads. The classes separate by `m/n` and by how neighbours pair, and the count of ways
puts them in order: the unordered (paramagnetic) moment is the mode, the fully ordered ones are the
fewest ways. -/

/-- The moment is twice the number of ups minus the size. -/
theorem moment_eq (A : List Bool) : moment A = 2 * (A.count true : ℤ) - A.length := by
  induction A with
  | nil => simp [moment]
  | cons p ps ih =>
      rw [moment, ih, List.count_cons, List.length_cons]
      cases p <;> simp [unitArea] <;> ring

theorem count_true_le (A : List Bool) : A.count true ≤ A.length := List.count_le_length

/-- **The moment never exceeds the size.** -/
theorem abs_moment_le (A : List Bool) : |moment A| ≤ A.length := by
  rw [moment_eq, abs_le]
  have := count_true_le A
  constructor <;> omega

/-- **Ferromagnet: the moment is the full size exactly when every unit is up.** -/
theorem moment_eq_length_iff (A : List Bool) : moment A = A.length ↔ ∀ p ∈ A, p = true := by
  rw [moment_eq]
  constructor
  · intro h p hp
    have hc : A.count true = A.length := by omega
    have := List.count_eq_length.mp hc p hp
    simpa using this.symm
  · intro h
    have hc : A.count true = A.length := List.count_eq_length.mpr (fun p hp => by rw [h p hp])
    rw [hc]; ring

/-- An alternating chain: up, down, up, … starting from `b`. -/
def alt : Bool → ℕ → List Bool
  | _, 0 => []
  | b, n + 1 => b :: alt (!b) n

/-- **Antiferromagnet: every neighbour pair in an alternating chain is opposite.** -/
theorem alt_neighbours_opposite (b : Bool) (n : ℕ) : List.IsChain (· ≠ ·) (alt b n) := by
  induction n generalizing b with
  | zero => exact List.IsChain.nil
  | succ n ih =>
      cases n with
      | zero => exact List.IsChain.singleton b
      | succ n =>
          have h := ih (!b)
          simp only [alt] at h ⊢
          exact List.IsChain.cons_cons (by cases b <;> simp) h

/-- **Antiferromagnet: an even alternating chain has zero moment, an odd one a single unit.** -/
theorem moment_alt (b : Bool) (k : ℕ) :
    moment (alt b (2 * k)) = 0 ∧ moment (alt b (2 * k + 1)) = unitArea b := by
  induction k generalizing b with
  | zero => simp [alt, moment]
  | succ k ih =>
      have h1 : alt b (2 * (k + 1)) = b :: (!b) :: alt b (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; simp [alt]
      have h2 : alt b (2 * (k + 1) + 1) = b :: (!b) :: alt b (2 * k + 1) := by
        rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring]; simp [alt]
      rw [h1, h2]
      simp only [moment, (ih b).1, (ih b).2]
      cases b <;> simp [unitArea]

theorem moment_append (A B : List Bool) : moment (A ++ B) = moment A + moment B := by
  induction A with
  | nil => simp [moment]
  | cons p ps ih => simp only [List.cons_append, moment, ih]; ring

theorem moment_replicate (b : Bool) (n : ℕ) : moment (List.replicate n b) = n * unitArea b := by
  induction n with
  | zero => simp [moment]
  | succ n ih => rw [List.replicate_succ, moment, ih]; push_cast; ring

/-- **Ferrimagnet: two opposite sublattices of sizes `n₁`, `n₂` leave moment `n₁ − n₂`.** -/
theorem moment_ferri (n₁ n₂ : ℕ) :
    moment (List.replicate n₁ true ++ List.replicate n₂ false) = (n₁ : ℤ) - n₂ := by
  rw [moment_append, moment_replicate, moment_replicate]
  simp [unitArea]; ring

/-- Every body of size `n`, each once. -/
def bodies : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bodies n).map (true :: ·) ++ (bodies n).map (false :: ·)

theorem mem_bodies (n : ℕ) (A : List Bool) : A ∈ bodies n ↔ A.length = n := by
  induction n generalizing A with
  | zero => cases A <;> simp [bodies]
  | succ n ih =>
      cases A with
      | nil => simp [bodies]
      | cons p ps => cases p <;> simp [bodies, ih]

theorem bodies_nodup (n : ℕ) : (bodies n).Nodup := by
  induction n with
  | zero => simp [bodies]
  | succ n ih =>
      rw [bodies, List.nodup_append]
      refine ⟨ih.map (fun _ _ h => by simpa using h), ih.map (fun _ _ h => by simpa using h), ?_⟩
      intro x hx y hy
      simp only [List.mem_map] at hx hy
      obtain ⟨_, _, rfl⟩ := hx
      obtain ⟨_, _, rfl⟩ := hy
      simp

/-- How many bodies of size `n` have exactly `k` ups. -/
def waysWithUps (n k : ℕ) : ℕ := (bodies n).countP (fun A => A.count true == k)

/-- **The number of bodies of size `n` with `k` ups is `C(n, k)`.** -/
theorem waysWithUps_eq_choose (n k : ℕ) : waysWithUps n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp [waysWithUps, bodies]
  | succ n ih =>
      unfold waysWithUps at ih ⊢
      rw [bodies, List.countP_append, List.countP_map, List.countP_map]
      cases k with
      | zero =>
          have h1 : (bodies n).countP ((fun A => A.count true == 0) ∘ (true :: ·)) = 0 := by
            rw [List.countP_eq_zero]; intro A _; simp
          have h2 : (bodies n).countP ((fun A => A.count true == 0) ∘ (false :: ·)) =
              (bodies n).countP (fun A => A.count true == 0) := by
            rfl
          rw [h1, h2, ih]; simp
      | succ k =>
          have h1 : (bodies n).countP ((fun A => A.count true == k + 1) ∘ (true :: ·)) =
              (bodies n).countP (fun A => A.count true == k) := by
            congr 1; funext A; simp
          have h2 : (bodies n).countP ((fun A => A.count true == k + 1) ∘ (false :: ·)) =
              (bodies n).countP (fun A => A.count true == k + 1) := by
            rfl
          rw [h1, h2, ih, ih, Nat.choose_succ_succ]

/-- **Paramagnet is the mode.** No moment class has more ways than the one closest to zero
    (`k = n/2` ups). -/
theorem paramagnet_most_ways (n k : ℕ) : waysWithUps n k ≤ waysWithUps n (n / 2) := by
  rw [waysWithUps_eq_choose, waysWithUps_eq_choose]
  exact Nat.choose_le_middle k n

/-- **Ferromagnet is the fewest.** Fully aligned up is one way (and fully down is one more). -/
theorem ferromagnet_one_way (n : ℕ) : waysWithUps n n = 1 ∧ waysWithUps n 0 = 1 := by
  rw [waysWithUps_eq_choose, waysWithUps_eq_choose]
  exact ⟨Nat.choose_self n, Nat.choose_zero_right n⟩

end QLF.MagneticOrientation
