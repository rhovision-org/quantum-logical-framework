import QLF_GluonVertex
import QLF_Manifestation
import QLF_LightCone

set_option linter.unusedVariables false

/-!
# QLF_ColourClosure — three-axis closures, their connectors, and what the delay can and cannot carry

Part of the [Quantum Logical Framework (QLF)](../README.md). **ZFA** (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF. Companion doc:
[`Colour_Closure.md`](../Colour_Closure.md); census: [`borromean_census.py`](../borromean_census.py).

Everything here stays on the eight-twist alphabet: colour is the `F₃²` label `colVec` of a twist
([`QLF_ColourFlux`](QLF_ColourFlux.lean)), baryon number is the junction winding
([`QLF_BaryonWinding`](QLF_BaryonWinding.lean)), closure is count balance (Pauli closure follows by
`count_balanced_pauli_closed`), and delay is `distance` ([`QLF_Manifestation`](QLF_Manifestation.lean)).
No continuum, no spatial embedding beyond the three axes themselves.

## §1 Every closure is a colour singlet (native)

* `colourTotal` — the sum of the colour labels of a history.
* `closure_is_colour_singlet` — every count-balanced history has total colour `0`.
  `QLF_Confinement.singlet_closure` proved this for the binary charge weight and read colour as an
  instance; this is the statement on the actual `F₃²` colour labels.
* `colour_charged_not_closed` — contrapositive: a history with net colour is never a closure.
* `colour_singlet_not_closure` — the converse fails: `>^/` is a colour singlet and is not a closure.
  Colour neutrality is strictly weaker than closure.

## §2 The connectors: spatial three-gluon vertices are exactly the Borromean triples

* `spatial_vertex_iff_borromean` — for three spatial twists, the three-gluon colour vertex of
  [`QLF_GluonVertex`](QLF_GluonVertex.lean) is nonzero **iff** the twists lie on the three distinct
  axes with one common orientation (`>^/` and `<v\` in any order).
* `borromean_baryon` — every such triple carries baryon number `±1`.
* `spatial_singlet_triple` — a spatial triple is a colour singlet iff it is Borromean or one twist
  repeated three times (`>>>`).
* `non_borromean_no_vertex` — a spatial triple that misses an axis has no vertex: it is either
  colour-charged (so it cannot close, §1) or collinear.
* `borromean_count` — 12 ordered spatial Borromean triples.

## §3 What the delay carries (GL7 / GL8)

* `colour_distance_le_one` — every history reaches a colour singlet by appending at most one
  twist; `spatial_colour_distance_le_two` — at most two spatial twists, and two can be needed
  (`spatial_bound_attained`). Colour distance is bounded, whatever the separation.
* `distance_eq_delay` (already proved) — the delay to closure is the `ℓ¹` separation, exactly.
* `colour_singlet_line` — `>^{3k}` is a colour singlet at every `k` with delay `3k`: the delay grows
  linearly while the colour distance stays `0`.
* `delay_colour_blind` — three histories with the same delay `3` carry different colour and baryon
  number.

So a linear delay exists and is exact, but it is the delay of **every** open history, coloured or
not: it is not a colour-specific string tension, and the bounded colour distance cannot supply one.

## §4 The binary pruning is blind to colour

* `binary_projection_blind` — `>\` carries net colour and is not a closure, yet its pos/neg
  projection achieves ZFA under `full_zeno_prune`. Colour pruning is done by the eight-twist count
  balance, not by the binary projection.

## §5 Baryon winding is read from a starting point

* `winding_not_rotation_invariant` — `>^</v\` (`B = −2`) and its rotation `^</v\>` (`B = −1`) are
  both first closures.
* `winding_not_additive` — two closures with `B = 0` concatenate to one with `B = 1`.

## §6 Minimal three-axis closures

* `minimal_diverse_closures_wound_majority` — of the 720 orderings of one conjugate pair per axis,
  576 are wound; of the 480 first closures among them, 384 are.

## §7 Shortest completions and their phases

* `shortest_completion_perm` — every shortest completion is a rearrangement of the canonical one, so
  their number is the multinomial of the per-axis imbalances.
* `diverse_completions_cancel` — the 6 orderings of `^ < /` (the most diverse delay-3 completion) sum
  to `0` (`cone_amplitude`), while `^^^` (1 way) and `^^<` (3 ways) do not
  (`diverse_completion_counts`). More unsigned ways do not survive the phases here.

No axioms.
-/

namespace QLF.ColourClosure

open QLF QLF.BaryonWinding QLF.ColourFlux QLF.GluonVertex QLF.Manifestation QLF.Discoveries2026

-- ============================================================================
-- §1  Every closure is a colour singlet
-- ============================================================================

/-- The total colour label of a history. -/
def colourTotal (ts : List Twist) : V := (ts.map colVec).sum

theorem colourTotal_nil : colourTotal [] = 0 := rfl

theorem colourTotal_cons (t : Twist) (ts : List Twist) :
    colourTotal (t :: ts) = colVec t + colourTotal ts := by
  simp [colourTotal]

theorem colourTotal_append (a b : List Twist) :
    colourTotal (a ++ b) = colourTotal a + colourTotal b := by
  simp [colourTotal]

/-- The total colour is the count-weighted sum of the eight labels. -/
theorem colourTotal_eq_counts (ts : List Twist) : colourTotal ts =
    ts.count Twist.up • colVec Twist.up + ts.count Twist.down • colVec Twist.down +
    ts.count Twist.left • colVec Twist.left + ts.count Twist.right • colVec Twist.right +
    ts.count Twist.slash • colVec Twist.slash +
    ts.count Twist.backslash • colVec Twist.backslash +
    ts.count Twist.plus • colVec Twist.plus + ts.count Twist.minus • colVec Twist.minus := by
  induction ts with
  | nil => simp [colourTotal]
  | cons t ts ih =>
    rw [colourTotal_cons, ih]
    cases t <;> simp (config := { decide := true }) [List.count_cons, add_smul] <;> abel

/-- **Every closure is a colour singlet.** A count-balanced history has total colour label `0`:
    each twist's label is the negative of its conjugate's (`colVec_rev`), and balance pairs them. -/
theorem closure_is_colour_singlet {ts : List Twist} (h : countBalanced ts) :
    colourTotal ts = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : colVec Twist.down = -colVec Twist.up := by decide
  have e2 : colVec Twist.left = -colVec Twist.right := by decide
  have e3 : colVec Twist.backslash = -colVec Twist.slash := by decide
  have e4 : colVec Twist.minus = -colVec Twist.plus := by decide
  rw [colourTotal_eq_counts, h1, h2, h3, h4, e1, e2, e3, e4]
  simp only [smul_neg]
  abel

/-- **Net colour forbids closure.** -/
theorem colour_charged_not_closed {ts : List Twist} (h : colourTotal ts ≠ 0) :
    ¬ countBalanced ts :=
  fun hb => h (closure_is_colour_singlet hb)

/-- **Colour neutrality is strictly weaker than closure.** The Borromean word `>^/` is a colour
    singlet and is not a closure: it is an open walk to `(1, 1, 1)`. -/
theorem colour_singlet_not_closure :
    colourTotal [Twist.right, Twist.up, Twist.slash] = 0 ∧
    ¬ countBalanced [Twist.right, Twist.up, Twist.slash] := by
  unfold countBalanced
  decide

-- ============================================================================
-- §2  The connectors: spatial vertices are the Borromean triples
-- ============================================================================

/-- Positive orientation of a twist (`>`, `^`, `/`, `+`). -/
def positive : Twist → Bool
  | Twist.right | Twist.up | Twist.slash | Twist.plus => true
  | _ => false

/-- A **Borromean triple**: three spatial twists on three distinct axes with one orientation. -/
def borromean (t u v : Twist) : Prop :=
  axOf t ≠ none ∧ axOf u ≠ none ∧ axOf v ≠ none ∧
  axOf t ≠ axOf u ∧ axOf t ≠ axOf v ∧ axOf u ≠ axOf v ∧
  positive t = positive u ∧ positive u = positive v

instance (t u v : Twist) : Decidable (borromean t u v) := by unfold borromean; infer_instance

/-- **The spatial three-gluon vertex is the Borromean triple.** For three spatial twists the colour
    vertex is nonzero exactly when they lie on the three axes with a common orientation. -/
theorem spatial_vertex_iff_borromean (t u v : Twist)
    (ht : axOf t ≠ none) (hu : axOf u ≠ none) (hv : axOf v ≠ none) :
    gluonVertex t u v ≠ 0 ↔ borromean t u v := by
  rw [gluon_vertex_iff]
  unfold borromean
  revert ht hu hv
  cases t <;> cases u <;> cases v <;> decide

/-- Every Borromean triple carries baryon number `±1`. -/
theorem borromean_baryon (t u v : Twist) (h : borromean t u v) :
    baryonNumber [t, u, v] = 1 ∨ baryonNumber [t, u, v] = -1 := by
  revert h
  unfold borromean
  cases t <;> cases u <;> cases v <;> decide

/-- **Spatial colour singlets of three twists**: Borromean, or one twist repeated three times. -/
theorem spatial_singlet_triple (t u v : Twist)
    (ht : axOf t ≠ none) (hu : axOf u ≠ none) (hv : axOf v ≠ none) :
    colVec t + colVec u + colVec v = 0 ↔ (t = u ∧ u = v) ∨ borromean t u v := by
  unfold borromean
  revert ht hu hv
  cases t <;> cases u <;> cases v <;> decide

/-- **A triple that misses an axis is no connector.** If two of three spatial twists share an axis,
    the vertex vanishes, and the triple is colour-charged (so it cannot close) unless it is one
    twist repeated. -/
theorem non_borromean_no_vertex (t u v : Twist)
    (ht : axOf t ≠ none) (hu : axOf u ≠ none) (hv : axOf v ≠ none)
    (hmiss : axOf t = axOf u ∨ axOf t = axOf v ∨ axOf u = axOf v) :
    gluonVertex t u v = 0 ∧ (colVec t + colVec u + colVec v ≠ 0 ∨ (t = u ∧ u = v)) := by
  have hnb : ¬ borromean t u v := by
    unfold borromean; rcases hmiss with h | h | h <;> simp [h]
  refine ⟨?_, ?_⟩
  · by_contra hne
    exact hnb ((spatial_vertex_iff_borromean t u v ht hu hv).1 hne)
  · by_cases hs : colVec t + colVec u + colVec v = 0
    · rcases (spatial_singlet_triple t u v ht hu hv).1 hs with h | h
      · exact Or.inr h
      · exact absurd h hnb
    · exact Or.inl hs

/-- **Twelve ordered Borromean triples**: six orderings of the axes, two orientations. -/
theorem borromean_count :
    ((allTwists.toFinset ×ˢ allTwists.toFinset ×ˢ allTwists.toFinset).filter
      (fun x => borromean x.1 x.2.1 x.2.2)).card = 12 := by
  decide

-- ============================================================================
-- §3  What the delay carries
-- ============================================================================

/-- **Colour distance is at most one twist.** Every history reaches a colour singlet by appending a
    single twist (the twist carrying the negative label, `colVec_surjective`), or none. -/
theorem colour_distance_le_one (h : List Twist) :
    ∃ c : List Twist, c.length ≤ 1 ∧ colourTotal (h ++ c) = 0 := by
  by_cases hz : colourTotal h = 0
  · exact ⟨[], by simp, by simpa using hz⟩
  · obtain ⟨t, -, ht⟩ := List.mem_map.1 (colVec_surjective (-colourTotal h) (neg_ne_zero.mpr hz))
    refine ⟨[t], by simp, ?_⟩
    rw [colourTotal_append, colourTotal_cons, colourTotal_nil, ht]
    simp

/-- Spatial words of length at most two. -/
def spatialShort : List (List Twist) :=
  let s := [Twist.right, Twist.left, Twist.up, Twist.down, Twist.slash, Twist.backslash]
  [] :: (s.map fun a => [a]) ++ (s.flatMap fun a => s.map fun b => [a, b])

theorem spatialShort_spatial :
    ∀ c ∈ spatialShort, c.length ≤ 2 ∧ ∀ t ∈ c, axOf t ≠ none := by
  decide

theorem spatialShort_reaches : ∀ v : V, ∃ c ∈ spatialShort, v + colourTotal c = 0 := by
  decide

/-- **Inside the three axes, colour distance is at most two twists.** -/
theorem spatial_colour_distance_le_two (h : List Twist) :
    ∃ c : List Twist, c.length ≤ 2 ∧ (∀ t ∈ c, axOf t ≠ none) ∧ colourTotal (h ++ c) = 0 := by
  obtain ⟨c, hc, hv⟩ := spatialShort_reaches (colourTotal h)
  obtain ⟨hl, hs⟩ := spatialShort_spatial c hc
  exact ⟨c, hl, hs, by rw [colourTotal_append]; exact hv⟩

/-- Two spatial twists can be needed: `^\` (colour `(1, 0)`, the gauge line) is neutralised by no
    single spatial twist. -/
theorem spatial_bound_attained (t : Twist) (ht : axOf t ≠ none) :
    colourTotal ([Twist.up, Twist.backslash] ++ [t]) ≠ 0 := by
  revert ht
  cases t <;> decide

theorem colourTotal_replicate (n : ℕ) (t : Twist) :
    colourTotal (List.replicate n t) = n • colVec t := by
  simp [colourTotal, List.map_replicate, List.sum_replicate]

theorem three_smul_zero : ∀ v : V, (3 : ℕ) • v = 0 := by decide

theorem nsmul_three_mul (v : V) : ∀ k : ℕ, (3 * k) • v = 0
  | 0 => by simp
  | k + 1 => by
    rw [show 3 * (k + 1) = 3 * k + 3 by ring, add_nsmul, nsmul_three_mul v k, three_smul_zero,
      add_zero]

theorem distance_replicate_right (n : ℕ) : distance (List.replicate n Twist.right) = n := by
  simp [distance, net, count_rep]

/-- **The delay grows linearly while colour distance stays zero.** The single-axis line `>^{3k}` is a
    colour singlet for every `k` and closes after exactly `3k` further events. -/
theorem colour_singlet_line (k : ℕ) :
    colourTotal (List.replicate (3 * k) Twist.right) = 0 ∧
    distance (List.replicate (3 * k) Twist.right) = 3 * k := by
  refine ⟨?_, distance_replicate_right _⟩
  rw [colourTotal_replicate]
  exact nsmul_three_mul _ k

/-- **The delay is colour-blind.** `>>>`, `>^/` and `>>^` all close after exactly three more events;
    the first two are colour singlets (baryon number `0` and `1`), the third is colour-charged. -/
theorem delay_colour_blind :
    distance [Twist.right, Twist.right, Twist.right] = 3 ∧
    distance [Twist.right, Twist.up, Twist.slash] = 3 ∧
    distance [Twist.right, Twist.right, Twist.up] = 3 ∧
    colourTotal [Twist.right, Twist.right, Twist.right] = 0 ∧
    colourTotal [Twist.right, Twist.up, Twist.slash] = 0 ∧
    colourTotal [Twist.right, Twist.right, Twist.up] ≠ 0 ∧
    baryonNumber [Twist.right, Twist.right, Twist.right] = 0 ∧
    baryonNumber [Twist.right, Twist.up, Twist.slash] = 1 := by
  decide

-- ============================================================================
-- §4  The binary pruning is blind to colour
-- ============================================================================

/-- The pos/neg projection of a twist (`twistToTopoElement` of `ZFAEventDynamics`). -/
def topoOf : Twist → TopoElement
  | Twist.right | Twist.up | Twist.slash | Twist.plus => TopoElement.phase LogicPhase.pos
  | _ => TopoElement.phase LogicPhase.neg

/-- **`full_zeno_prune` on the binary projection does not see colour.** `>\` carries net colour and
    is not a closure, yet its projection `[pos, neg]` achieves ZFA. The eight-twist count balance
    is what prunes colour. -/
theorem binary_projection_blind :
    colourTotal [Twist.right, Twist.backslash] ≠ 0 ∧
    ¬ countBalanced [Twist.right, Twist.backslash] ∧
    achieves_ZFA ([Twist.right, Twist.backslash].map topoOf) := by
  refine ⟨by decide, by unfold countBalanced; decide, ?_⟩
  show achieves_ZFA [TopoElement.phase LogicPhase.pos, TopoElement.phase LogicPhase.neg]
  unfold achieves_ZFA
  rw [full_zeno_prune]
  simp [zeno_prune]
  rw [full_zeno_prune]
  simp

-- ============================================================================
-- §5  Baryon winding is read from a starting point
-- ============================================================================

/-- **Winding depends on where the loop is read from.** `>^</v\` and its rotation `^</v\>` are both
    closures (indeed first closures), yet their junction baryon numbers are `−2` and `−1`. So the
    windowed winding is not an invariant of the cyclic loop; it is an invariant of the word read from
    its first event. Which reading is physical is open. -/
theorem winding_not_rotation_invariant :
    countBalanced [Twist.right, Twist.up, Twist.left, Twist.slash, Twist.down, Twist.backslash] ∧
    countBalanced [Twist.up, Twist.left, Twist.slash, Twist.down, Twist.backslash, Twist.right] ∧
    junctionBaryon [Twist.right, Twist.up, Twist.left, Twist.slash, Twist.down, Twist.backslash] = -2 ∧
    junctionBaryon [Twist.up, Twist.left, Twist.slash, Twist.down, Twist.backslash, Twist.right] = -1 := by
  unfold countBalanced
  decide

/-- **Winding is not additive.** `>^<v` and `/\` are closures with baryon number `0`; their
    concatenation is a closure with baryon number `1`, from the window across the boundary. -/
theorem winding_not_additive :
    countBalanced [Twist.right, Twist.up, Twist.left, Twist.down] ∧
    countBalanced [Twist.slash, Twist.backslash] ∧
    junctionBaryon [Twist.right, Twist.up, Twist.left, Twist.down] = 0 ∧
    junctionBaryon [Twist.slash, Twist.backslash] = 0 ∧
    junctionBaryon ([Twist.right, Twist.up, Twist.left, Twist.down] ++ [Twist.slash, Twist.backslash])
      = 1 := by
  unfold countBalanced
  decide

-- ============================================================================
-- §6  Minimal three-axis closures: the 720 orderings of one pair per axis
-- ============================================================================

/-- Count balance as a Boolean. -/
def balB (w : List Twist) : Bool :=
  w.count Twist.up == w.count Twist.down && w.count Twist.left == w.count Twist.right &&
  w.count Twist.slash == w.count Twist.backslash && w.count Twist.plus == w.count Twist.minus

/-- A first closure: balanced, and no proper nonempty prefix is balanced. -/
def firstB (w : List Twist) : Bool :=
  balB w && (List.range w.length).all (fun k => k == 0 || !balB (w.take k))

/-- Insert `a` at every position of a list. -/
def insAll (a : Twist) : List Twist → List (List Twist)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insAll a l).map (b :: ·)

/-- All orderings of a list (structural, so the kernel can evaluate it). -/
def orderings : List Twist → List (List Twist)
  | [] => [[]]
  | a :: l => (orderings l).flatMap (insAll a)

/-- The 720 orderings of one conjugate pair per spatial axis. -/
def minimalOrderings : List (List Twist) := orderings protonClosure

theorem minimalOrderings_perm : ∀ w ∈ minimalOrderings, w.Perm protonClosure := by
  decide +kernel

theorem minimalOrderings_nodup : minimalOrderings.Nodup := by
  decide +kernel

/-- **Once all three pairs are present, winding is the majority.** Of the 720 orderings of
    `> < ^ v / \`, 576 carry nonzero baryon number; of the 480 that are first closures, 384 do. -/
theorem minimal_diverse_closures_wound_majority :
    minimalOrderings.length = 720 ∧
    (minimalOrderings.filter (fun w => junctionBaryon w != 0)).length = 576 ∧
    (minimalOrderings.filter firstB).length = 480 ∧
    (minimalOrderings.filter (fun w => firstB w && junctionBaryon w != 0)).length = 384 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

-- ============================================================================
-- §7  Shortest completions: unsigned ways and their phases
-- ============================================================================

/-- `Twist` derives `BEq` alongside `DecidableEq`; the derived `==` agrees with `=`. -/
instance : LawfulBEq Twist where
  eq_of_beq {a b} h := by revert h; cases a <;> cases b <;> decide
  rfl {a} := by cases a <;> decide

/-- **Every shortest completion is a rearrangement of the canonical one.** A continuation that closes
    `h` in exactly `distance h` events uses each needed conjugate twist exactly as often as the net
    action demands and nothing else. So the shortest completions of `h` are the orderings of one fixed
    multiset, and their number is the multinomial of the per-axis imbalances. -/
theorem shortest_completion_perm {h c : List Twist} (hc : countBalanced (h ++ c))
    (hl : c.length = distance h) : c.Perm (shortestCompletion h) := by
  have e := (countBalanced_append_iff h c).1 hc
  have L := length_eq_sum_counts c
  simp only [distance, net] at hl e
  rw [List.perm_iff_count]
  intro t
  cases t <;>
    simp only [shortestCompletion, fill, net, List.count_append, count_rep] <;>
    simp +decide <;> omega

open QLF.ClosureChannels in
theorem coneAmp_ne_zero {a b c : ℕ} (hp : a % 2 + b % 2 + c % 2 ≤ 1) : coneAmp a b c ≠ 0 := by
  rw [cone_amplitude]
  simp only [hp, ↓reduceIte]
  have hN : (coneCount (a / 2) (b / 2) (c / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (coneCount_pos _ _ _).ne'
  have hs : coneSpin a b c ≠ 0 := by
    intro hz
    have := coneSpin_sq a b c hp
    rw [hz, zero_mul] at this
    exact zero_ne_one this
  exact smul_ne_zero hN hs

open QLF.ClosureChannels in
/-- **The phase gate on diversity.** Spread over three axes, a unit imbalance on each has the most
    shortest completions (the `3! = 6` orderings of `^ < /`), and their signed sum is exactly `0`
    (`cone_amplitude`: three odd axes). Concentrated on one axis (`^^^`, one way) or split `2 + 1`
    (three ways), the signed sum is nonzero. More unsigned ways do not survive the phases here. -/
theorem diverse_completions_cancel :
    coneAmp 1 1 1 = 0 ∧ coneAmp 3 0 0 ≠ 0 ∧ coneAmp 2 1 0 ≠ 0 := by
  refine ⟨?_, coneAmp_ne_zero (by decide), coneAmp_ne_zero (by decide)⟩
  rw [cone_amplitude]
  simp

open QLF.ClosureChannels in
/-- The unsigned counts behind `diverse_completions_cancel`: `6`, `1` and `3` orderings. -/
theorem diverse_completion_counts :
    (coneCount 1 1 1 : ℂ) = 6 ∧ (coneCount 3 0 0 : ℂ) = 1 ∧ (coneCount 2 1 0 : ℂ) = 3 := by
  have c0 : (coneCount 0 0 0 : ℂ) = 1 := by exact_mod_cast coneCount_zero
  have s := fun a b c (h : 0 < a + b + c) => coneCount_succ a b c h
  have c100 : (coneCount 1 0 0 : ℂ) = 1 := by rw [s 1 0 0 (by norm_num)]; simp [c0]
  have c010 : (coneCount 0 1 0 : ℂ) = 1 := by rw [s 0 1 0 (by norm_num)]; simp [c0]
  have c001 : (coneCount 0 0 1 : ℂ) = 1 := by rw [s 0 0 1 (by norm_num)]; simp [c0]
  have c110 : (coneCount 1 1 0 : ℂ) = 2 := by rw [s 1 1 0 (by norm_num)]; simp [c100, c010]; norm_num
  have c101 : (coneCount 1 0 1 : ℂ) = 2 := by rw [s 1 0 1 (by norm_num)]; simp [c100, c001]; norm_num
  have c011 : (coneCount 0 1 1 : ℂ) = 2 := by rw [s 0 1 1 (by norm_num)]; simp [c010, c001]; norm_num
  have c200 : (coneCount 2 0 0 : ℂ) = 1 := by rw [s 2 0 0 (by norm_num)]; simp [c100]
  have c300 : (coneCount 3 0 0 : ℂ) = 1 := by rw [s 3 0 0 (by norm_num)]; simp [c200]
  have c210 : (coneCount 2 1 0 : ℂ) = 3 := by rw [s 2 1 0 (by norm_num)]; simp [c110, c200]; norm_num
  have c111 : (coneCount 1 1 1 : ℂ) = 6 := by
    rw [s 1 1 1 (by norm_num)]; simp [c011, c101, c110]; norm_num
  exact ⟨c111, c300, c210⟩

end QLF.ColourClosure
