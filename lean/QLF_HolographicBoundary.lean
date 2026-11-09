import QLF_EdgeSign
import QLF_GravityFromDelay
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
-- Narrow imports, as in QLF_EdgeSign: the whole chain stays off `import Mathlib`.

set_option linter.unusedVariables false

/-!
# QLF_HolographicBoundary — what "the boundary determines the bulk" proves, and what it does not

The holography audit ([`Holography_Audit.md`](../Holography_Audit.md)) found that the repo's
holographic content had **no bulk–boundary theorem**: the area law is a definition
(`holographic_event_count R := 4πR²`, `QLF_GravityFromDelay`), and the sentence "the entire bulk is
mathematically identical to the sum of its boundary states" (`Holographic.md`, `CLAUDE.md`) cited
Lean files that contain nothing about a bulk or a boundary. This module proves the three precise
statements that sentence can be given, and says what each one does and does not carry.

**1. The boundary-flux theorem (discrete Gauss law).** For *any* walk and *any* region `S`, the net
number of times the walk leaves `S` equals `[start ∈ S] − [end ∈ S]` (`outFlux_eq`). So a closure
sends zero net flux through **every** boundary (`closed_zero_flux`), and conversely zero flux through
the one-cell boundary around the start already forces closure (`closed_iff_zero_flux_everywhere`):
**closure, a property of the whole history, is decided by boundary data alone.** For twist histories
this is count balance (`position_eq_zero_iff`, `closure_iff_boundary_silent`). *Status:* the identity
holds for every walk — it is telescoping, so it is bookkeeping by method rule 4. The ZFA content is
only the endpoint condition.

**2. Bulk from boundary, at the level of the generator tree.** Every prefix extends to a closure —
append its conjugate (`every_prefix_closes`). So the bulk (prefixes) is exactly the prefix closure of
the boundary (closures): the boundary determines the bulk, but **because the bulk is all of
possibility** (`bulk_eq_prefixes_of_boundary`). No finite prefix is pruned. Where selection *does*
have teeth is in measure, not in existence: a uniformly random continuation never closes with
probability `≥ 1/4` (`QLF_FirstReturn`), Pólya's `1 − p₄ ≈ 0.807` numerically.

**3. The area law follows from locality, not from closure.** Put one shared pair (one bit, `log 2`)
on each pair of sites that close jointly. The bits a region `A` shares with its outside are the pairs
cut by its boundary. If every pair joins **adjacent** sites, the cut pairs are a subset of the edge
boundary, so `S_A ≤ |∂A| · log 2` (`area_law_of_local_pairs`, `cutEntropy_le_area`) — an area law,
derived. Drop locality and it fails: three nonlocal pairs cross a cut with two boundary edges
(`nonlocal_pairs_break_area_law`). So the area law needs a premise QLF has not yet derived — that
shared closures are local — and that premise, not ZFA, is where holography's content lives. Reading
`cutPairs · log 2` as von Neumann entropy is the standard singlet count (each cut singlet is one
`log 2`), cited, not proved here.

No axioms.
-/

namespace QLF.HolographicBoundary

open QLF QLF.PhaseRule QLF.EdgeSign

-- ==========================================
-- 1. The boundary-flux theorem, for any walk
-- ==========================================

section Flux

variable {P α : Type*}

/-- Walk from `x`, one `move` per letter. -/
def walkFrom (move : P → α → P) : P → List α → P
  | x, [] => x
  | x, t :: ts => walkFrom move (move x t) ts

/-- The indicator of a region, as an integer. -/
def ind (S : P → Prop) [DecidablePred S] (x : P) : ℤ := if S x then 1 else 0

/-- One step's crossing of the boundary of `S`: `+1` out, `−1` in, `0` if it stays on one side. -/
def crossing (S : P → Prop) [DecidablePred S] (x y : P) : ℤ :=
  if S x ∧ ¬ S y then 1 else if ¬ S x ∧ S y then -1 else 0

/-- **Net outward flux** of a walk through the boundary of `S`: the crossings summed. -/
def outFlux (move : P → α → P) (S : P → Prop) [DecidablePred S] : P → List α → ℤ
  | _, [] => 0
  | x, t :: ts => crossing S x (move x t) + outFlux move S (move x t) ts

/-- A crossing is the drop in the indicator. -/
theorem crossing_eq (S : P → Prop) [DecidablePred S] (x y : P) :
    crossing S x y = ind S x - ind S y := by
  unfold crossing ind
  by_cases hx : S x <;> by_cases hy : S y <;> simp [hx, hy]

/-- **The boundary-flux theorem.** For every walk and every region, net outward flux through the
    boundary is `[start ∈ S] − [end ∈ S]`. The bulk's net source is read off the boundary. -/
theorem outFlux_eq (move : P → α → P) (S : P → Prop) [DecidablePred S] (x : P) (ts : List α) :
    outFlux move S x ts = ind S x - ind S (walkFrom move x ts) := by
  induction ts generalizing x with
  | nil => simp [outFlux, walkFrom]
  | cons t ts ih =>
    simp only [outFlux, walkFrom]
    rw [crossing_eq, ih]
    ring

/-- **A closed walk is silent on every boundary**: zero net flux through the boundary of any region. -/
theorem closed_zero_flux (move : P → α → P) {x : P} {ts : List α}
    (h : walkFrom move x ts = x) (S : P → Prop) [DecidablePred S] :
    outFlux move S x ts = 0 := by
  rw [outFlux_eq, h, sub_self]

/-- **One cell suffices**: zero net flux through the boundary of the single cell `{x}` around the
    start already forces the walk to close. -/
theorem closed_of_cell_flux [DecidableEq P] (move : P → α → P) {x : P} {ts : List α}
    (h : outFlux move (fun y => y = x) x ts = 0) : walkFrom move x ts = x := by
  rw [outFlux_eq] at h
  unfold ind at h
  by_contra hne
  simp [hne] at h

/-- **Closure is a boundary property.** A walk closes iff every boundary sees zero net flux. -/
theorem closed_iff_zero_flux_everywhere [DecidableEq P] (move : P → α → P) (x : P) (ts : List α) :
    walkFrom move x ts = x ↔ ∀ (S : P → Prop) [DecidablePred S], outFlux move S x ts = 0 := by
  constructor
  · intro h S _
    exact closed_zero_flux move h S
  · intro h
    exact closed_of_cell_flux move (h (fun y => y = x))

end Flux

-- ==========================================
-- 1b. The twist walk on ℤ⁴: closure = count balance = boundary silence
-- ==========================================

/-- The twist walk is the `walkFrom` of `stepPos` (`QLF_EdgeSign`). -/
theorem walkFrom_stepPos (ts : List Twist) : ∀ x : Axis → ℤ,
    walkFrom stepPos x ts = positionFrom x ts := by
  induction ts with
  | nil => intro x; rfl
  | cons t ts ih => intro x; simp only [walkFrom, positionFrom]; exact ih _

/-- Walking from `x` is walking from the origin, shifted by `x`. -/
theorem positionFrom_shift (ts : List Twist) : ∀ (x : Axis → ℤ) (b : Axis),
    positionFrom x ts b = x b + positionFrom (fun _ => 0) ts b := by
  induction ts with
  | nil => intro x b; simp [positionFrom]
  | cons t ts ih =>
    intro x b
    simp only [positionFrom]
    rw [ih (stepPos x t) b, ih (stepPos (fun _ => 0) t) b]
    simp only [stepPos]
    split_ifs <;> ring

theorem position_cons (t : Twist) (ts : List Twist) (b : Axis) :
    position (t :: ts) b = stepPos (fun _ => 0) t b + position ts b := by
  unfold position
  simp only [positionFrom]
  exact positionFrom_shift ts _ b

theorem position_Y (ts : List Twist) :
    position ts Axis.Y = (ts.count Twist.up : ℤ) - ts.count Twist.down := by
  induction ts with
  | nil => simp [position, positionFrom]
  | cons t ts ih =>
    rw [position_cons, ih]
    simp only [List.count_cons]
    cases t <;> simp +decide [stepPos, axisOf, twistStep, isNegTwist] <;> omega

theorem position_X (ts : List Twist) :
    position ts Axis.X = (ts.count Twist.right : ℤ) - ts.count Twist.left := by
  induction ts with
  | nil => simp [position, positionFrom]
  | cons t ts ih =>
    rw [position_cons, ih]
    simp only [List.count_cons]
    cases t <;> simp +decide [stepPos, axisOf, twistStep, isNegTwist] <;> omega

theorem position_Z (ts : List Twist) :
    position ts Axis.Z = (ts.count Twist.slash : ℤ) - ts.count Twist.backslash := by
  induction ts with
  | nil => simp [position, positionFrom]
  | cons t ts ih =>
    rw [position_cons, ih]
    simp only [List.count_cons]
    cases t <;> simp +decide [stepPos, axisOf, twistStep, isNegTwist] <;> omega

theorem position_I (ts : List Twist) :
    position ts Axis.I = (ts.count Twist.plus : ℤ) - ts.count Twist.minus := by
  induction ts with
  | nil => simp [position, positionFrom]
  | cons t ts ih =>
    rw [position_cons, ih]
    simp only [List.count_cons]
    cases t <;> simp +decide [stepPos, axisOf, twistStep, isNegTwist] <;> omega

/-- **A twist history closes on `ℤ⁴` exactly when it is count-balanced.** -/
theorem position_eq_zero_iff (ts : List Twist) :
    position ts = (fun _ => 0) ↔ countBalanced ts := by
  unfold countBalanced
  constructor
  · intro h
    have hY : position ts Axis.Y = 0 := congrFun h Axis.Y
    have hX : position ts Axis.X = 0 := congrFun h Axis.X
    have hZ : position ts Axis.Z = 0 := congrFun h Axis.Z
    have hI : position ts Axis.I = 0 := congrFun h Axis.I
    rw [position_Y] at hY
    rw [position_X] at hX
    rw [position_Z] at hZ
    rw [position_I] at hI
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro ⟨hUD, hLR, hSB, hPM⟩
    funext b
    show position ts b = 0
    cases b
    · rw [position_I]; omega
    · rw [position_X]; omega
    · rw [position_Y]; omega
    · rw [position_Z]; omega

/-- **ZFA closure is boundary silence.** A twist history is count-balanced iff its walk on `ℤ⁴` sends
    zero net flux through the boundary of every region — and by `count_balanced_pauli_closed` that is
    full ZFA, both conjuncts. -/
theorem closure_iff_boundary_silent (ts : List Twist) :
    countBalanced ts ↔
      ∀ (S : (Axis → ℤ) → Prop) [DecidablePred S], outFlux stepPos S (fun _ => 0) ts = 0 := by
  classical
  have key := closed_iff_zero_flux_everywhere stepPos (fun _ : Axis => (0 : ℤ)) ts
  rw [walkFrom_stepPos] at key
  rw [← position_eq_zero_iff]
  exact key

-- ==========================================
-- 2. Bulk from boundary on the generator tree
-- ==========================================

/-- Conjugating every letter swaps each count with its conjugate's. -/
theorem count_map_conj (p : List Twist) (a : Twist) :
    (p.map Twist.conj).count a = p.count a.conj := by
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.count_cons, ih]
    cases t <;> cases a <;> simp +decide [Twist.conj]

/-- **Every bulk path reaches the boundary.** Any prefix closes by appending its conjugate. -/
theorem every_prefix_closes (p : List Twist) : countBalanced (p ++ p.map Twist.conj) := by
  unfold countBalanced
  have h := fun a => count_map_conj p a
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [List.count_append, h, Twist.conj] <;> omega

/-- **The bulk is the prefix closure of the boundary — and it is everything.** A history is a prefix
    of some closure, for every history. The boundary determines the bulk, but it constrains no
    finite path: selection acts on measure (`QLF_FirstReturn`), not on which prefixes exist. -/
theorem bulk_eq_prefixes_of_boundary (p : List Twist) :
    ∃ q : List Twist, countBalanced (p ++ q) :=
  ⟨p.map Twist.conj, every_prefix_closes p⟩

-- ==========================================
-- 3. The area law follows from locality of shared pairs
-- ==========================================

section AreaLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An ordered pair of sites straddles the cut `A | Aᶜ`. -/
def Crosses (A : Finset V) (e : V × V) : Prop :=
  (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A)

instance (A : Finset V) : DecidablePred (Crosses A) := fun e => by
  unfold Crosses; infer_instance

/-- The **edge boundary** of `A` for an adjacency relation: the adjacent pairs that straddle the cut.
    This is the region's area in lattice units. -/
def edgeBoundary (adj : V → V → Prop) [DecidableRel adj] (A : Finset V) : Finset (V × V) :=
  (Finset.univ.filter (fun e : V × V => adj e.1 e.2)).filter (Crosses A)

/-- The shared pairs (joint closures, one bit each) that the cut separates. -/
def cutPairs (P : Finset (V × V)) (A : Finset V) : Finset (V × V) := P.filter (Crosses A)

/-- **Area law from locality.** If every shared pair joins adjacent sites, the pairs a region shares
    with its outside are at most its edge boundary — area, not volume. -/
theorem area_law_of_local_pairs (adj : V → V → Prop) [DecidableRel adj]
    (P : Finset (V × V)) (A : Finset V) (hloc : ∀ e ∈ P, adj e.1 e.2) :
    (cutPairs P A).card ≤ (edgeBoundary adj A).card := by
  apply Finset.card_le_card
  intro e he
  simp only [cutPairs, edgeBoundary, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨hloc e he.1, he.2⟩

/-- The entropy a region shares with its outside: `log 2` per cut pair, the per-event quantum
    `per_event_entropy` of `QLF_GravityFromDelay`. (Reading this as von Neumann entropy is the
    standard count for a product of singlets — cited, not proved here.) -/
noncomputable def cutEntropy (P : Finset (V × V)) (A : Finset V) : ℝ :=
  ((cutPairs P A).card : ℝ) * per_event_entropy

/-- **The holographic bound, derived from locality**: `S_A ≤ |∂A| · log 2`. -/
theorem cutEntropy_le_area (adj : V → V → Prop) [DecidableRel adj]
    (P : Finset (V × V)) (A : Finset V) (hloc : ∀ e ∈ P, adj e.1 e.2) :
    cutEntropy P A ≤ ((edgeBoundary adj A).card : ℝ) * per_event_entropy := by
  unfold cutEntropy
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast area_law_of_local_pairs adj P A hloc
  · unfold per_event_entropy
    exact Real.log_nonneg (by norm_num)

end AreaLaw

/-- Six sites on a line. -/
def lineAdj (i j : Fin 6) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

instance : DecidableRel lineAdj := fun i j => by unfold lineAdj; infer_instance

/-- **Locality is necessary.** On a line of six sites cut in half, the boundary has two (ordered)
    edges, but three nonlocal pairs `0–3, 1–4, 2–5` all cross it: a volume law. So closure alone does
    not give the area law; the locality of shared closures is the premise that does. -/
theorem nonlocal_pairs_break_area_law :
    (edgeBoundary lineAdj ({0, 1, 2} : Finset (Fin 6))).card = 2 ∧
      (cutPairs ({(0, 3), (1, 4), (2, 5)} : Finset (Fin 6 × Fin 6))
        ({0, 1, 2} : Finset (Fin 6))).card = 3 := by
  decide

end QLF.HolographicBoundary
