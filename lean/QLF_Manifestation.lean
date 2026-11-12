import QLF_KraftMeasure
import QLF_Discoveries2026
import QLF_ClosureKernel
import QLF_ClosureRenewal
import QLF_FirstReturn
import QLF_BaryonWinding

/-!
# QLF_Manifestation — unbounded manifestation from a priori orientation and isolation

Jim's thesis (2026-11-11):

> *The magic of possibilistic quantum logical manifestation is that it manifests unbounded in
> complexity, every possible world and our world, because there exist a priori solutions for
> orientation and isolation, and the promise of quantum computing.*

Most of the supporting facts are already proved elsewhere and are **cited, not re-proved**:

| Claim | Existing theorem |
|---|---|
| every history completes to a closure by its own dagger | `ClosureUnitarity.countBalanced_append_dagger`, `Discoveries2026.mirror_closes` |
| closures compose | `ClosureKernel.balanced_append` |
| after a closure, what closes is what closed before, up to one sign | `ClosureRenewal.closure_renewal` |
| an open part cannot be hidden by a shared closure | `Discoveries2026.forced_sharing` |
| a reversible gate preserves closure | `ClosureUnitarity.countBalanced_perm`, `Fredkin.fredkin_preserves_zfa` |
| the exact closure count | `ProductWalk.card_balanced_twist` |

This module adds only what was missing. No axiom.

* **§1 Orientation: the requirement is fixed, the way is not.** Every completion of a history must
  supply the same signed action (`completion_net_determined`), yet the same history has more than
  one completion (`completion_not_unique`).
* **§2 Isolation IS closure.** A part is invisible to the closure of every environment exactly when
  it is closed (`isolated_iff_closed`); this survives any interleaving of its events with the rest
  (`isolation_interleaved`); and at the amplitude level a closed part inserted *anywhere*, not only
  at the front, changes the rest by one global Pauli phase (`closed_insertion_is_phase`).
* **§3 Complexity is unbounded.** At least `8ⁿ` closures of length `2n`
  (`closures_at_least_eight_pow`, `closures_unbounded`), and a *prime* closure of every even length
  (`prime_closure_every_length`): single irreducible events are unbounded too.
* **§4 Distance equals delay.** A history closes after exactly `distance h` further events, the `ℓ¹`
  norm of its signed action vector, and never sooner (`delay_ge_distance`, `distance_eq_delay`).
  The a priori orientation solution can always be taken shortest.

* **§5 Selection.** A niche admits two variants alike exactly when they carry the same net action
  (`same_niches_iff_sameNet`): selection is a filter on the net and nothing else, so rearrangements
  are neutral (`rearrangement_neutral`) and no aim enters. Read with `isolated_iff_closed`, fixation is
  isolation: a lineage is independent of the niche it meets exactly when it is closed.

* **§6 The proton: the simplest isolated imbalance.** A closure is isolated, so it can carry an
  imbalance only in a quantity counting cannot see. The first such quantity is the three-axis
  winding (baryon number): every closure shorter than six has none (`short_closures_unwound`), and
  at six the proton word `>^/` closes as a prime closure with winding `+1`
  (`proton_simplest_isolated_imbalance`). Possibility makes it stable: at length `6 + 2n` at least
  `2ⁿ` closures carry winding `+1` (`proton_ways_unbounded`), so the proton is a class of ways
  whose multiplicity grows without bound, not one fragile configuration.

**Scope.** These are theorems about the possibility space, not about which world is ours. That
selection is the first closure (`QLF_ClosureDepth`, `/solve`); the physics readings (magnetism from
orientation, gravity from balance, expansion from delay) are mapped with their status in the
companion document.
-/

namespace QLF.Manifestation

open QLF QLF.Discoveries2026 QLF.Majorana

-- ============================================================================
-- §1  Orientation: the requirement is fixed, the way is not
-- ============================================================================

/-- **What a completion must supply is fixed by the history.** Any two completions of `h` carry the
    same signed action on every axis: the opposite of `h`'s. -/
theorem completion_net_determined {h c c' : List Twist}
    (hc : countBalanced (h ++ c)) (hc' : countBalanced (h ++ c')) :
    net c Twist.up Twist.down = net c' Twist.up Twist.down ∧
    net c Twist.left Twist.right = net c' Twist.left Twist.right ∧
    net c Twist.slash Twist.backslash = net c' Twist.slash Twist.backslash ∧
    net c Twist.plus Twist.minus = net c' Twist.plus Twist.minus := by
  have e := (countBalanced_append_iff h c).1 hc
  have e' := (countBalanced_append_iff h c').1 hc'
  omega

/-- **How it is supplied is not fixed.** The open word `^>` closes with its mirror `<v` and also
    with the unreversed conjugate `v<`: two completions of the same length. A construction exhibits
    *a* way, never *the* way (`Philosophy.md` §3a, rule 1). -/
theorem completion_not_unique :
    let h := [Twist.up, Twist.right]
    countBalanced (h ++ antiparticle h) ∧ countBalanced (h ++ h.map Twist.conj) ∧
      antiparticle h ≠ h.map Twist.conj ∧ ¬ countBalanced h := by
  refine ⟨mirror_closes _, ?_, ?_, ?_⟩
  · unfold countBalanced; decide
  · decide
  · unfold countBalanced; decide

-- ============================================================================
-- §2  Isolation IS closure
-- ============================================================================

/-- **Isolation IS closure.** A part is invisible to the closure of every environment exactly when it
    is closed. The Markov blanket is not extra structure: it is the closure itself. -/
theorem isolated_iff_closed (a : List Twist) :
    (∀ b : List Twist, countBalanced (a ++ b) ↔ countBalanced b) ↔ countBalanced a := by
  constructor
  · intro h
    have := (h []).2 (by unfold countBalanced; decide)
    simpa using this
  · intro ha b
    exact ClosureRenewal.countBalanced_append_iff ha b

/-- **Isolation survives interleaving.** However a closed part's events are woven among the rest's,
    the whole closes exactly when the rest does. -/
theorem isolation_interleaved {a b l : List Twist} (ha : countBalanced a) (p : l.Perm (a ++ b)) :
    countBalanced l ↔ countBalanced b :=
  ⟨fun hl => (ClosureRenewal.countBalanced_append_iff ha b).1
      (ClosureUnitarity.countBalanced_perm p.symm hl),
   fun hb => ClosureUnitarity.countBalanced_perm p
      ((ClosureRenewal.countBalanced_append_iff ha b).2 hb)⟩

/-- **Isolation at the amplitude level, anywhere.** A closed part inserted at any point of a history
    changes the fold of the rest by one global Pauli phase from `{±I, ±iI}`, the same phase wherever
    it sits. (`ClosureRenewal.closure_renewal` is the case of insertion at the front.) -/
theorem closed_insertion_is_phase {a : List Twist} (ha : countBalanced a) :
    ∃ p : PauliScalar, ∀ b c : List Twist,
      twistMatrixFold (b ++ a ++ c) = pauliScalarToMatrix p * twistMatrixFold (b ++ c) := by
  obtain ⟨p, hp⟩ := count_balanced_pauli_closed ha
  refine ⟨p, fun b c => ?_⟩
  simp only [ClosureUnitarity.fold_append]
  rw [hp, psm_comm, mul_assoc]

-- ============================================================================
-- §3  Complexity is unbounded
-- ============================================================================

/-- Each twist followed by its conjugate: a word of `n` free choices becomes a closure of length
    `2n`. -/
def pairWord (w : List Twist) : List Twist := w.flatMap (fun t => [t, t.conj])

theorem pairWord_nil : pairWord [] = [] := rfl

theorem pairWord_cons (t : Twist) (w : List Twist) :
    pairWord (t :: w) = t :: t.conj :: pairWord w := rfl

theorem pairWord_length (w : List Twist) : (pairWord w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons t w ih => rw [pairWord_cons, List.length_cons, List.length_cons, ih, List.length_cons]; ring

theorem pairWord_balanced (w : List Twist) : countBalanced (pairWord w) := by
  induction w with
  | nil => unfold countBalanced; decide
  | cons t w ih =>
    rw [pairWord_cons]
    have hp : countBalanced [t, t.conj] := by cases t <;> (unfold countBalanced; decide)
    have := ClosureKernel.balanced_append hp ih
    simpa using this

theorem pairWord_injective : Function.Injective pairWord := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons t y => simp [pairWord_nil, pairWord_cons] at h
  | cons s x ih =>
    intro y h
    cases y with
    | nil => simp [pairWord_nil, pairWord_cons] at h
    | cons t y =>
      rw [pairWord_cons, pairWord_cons] at h
      simp only [List.cons.injEq] at h
      rw [h.1, ih h.2.2]

/-- **At least `8ⁿ` closures of length `2n`.** Each of `n` positions takes any of the eight twists
    freely; the conjugate that follows closes it. Information content grows by at least three bits
    per pair. -/
theorem closures_at_least_eight_pow (n : ℕ) :
    8 ^ n ≤ ((words Twist (2 * n)).filter (fun ts => decide (countBalanced ts))).card := by
  have hcard : (words Twist n).card = 8 ^ n := by rw [card_words, card_twist]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn pairWord
  · intro w hw
    simp only [Finset.mem_coe, mem_words] at hw
    simp only [Finset.mem_coe, Finset.mem_filter, mem_words, decide_eq_true_eq]
    exact ⟨by rw [pairWord_length, hw], pairWord_balanced w⟩
  · intro x _ y _ h
    exact pairWord_injective h

/-- **Complexity is unbounded.** For every bound there is a length with more closures than it. -/
theorem closures_unbounded (N : ℕ) :
    ∃ L, N < ((words Twist L).filter (fun ts => decide (countBalanced ts))).card := by
  refine ⟨2 * N, lt_of_lt_of_le ?_ (closures_at_least_eight_pow N)⟩
  calc N < 2 ^ N := Nat.lt_two_pow_self
    _ ≤ 8 ^ N := Nat.pow_le_pow_left (by norm_num) N

/-- `n` up-twists followed by `n` down-twists. -/
def ladder (n : ℕ) : List Twist := List.replicate n Twist.up ++ List.replicate n Twist.down

theorem count_replicate_up (k : ℕ) (t : Twist) :
    (List.replicate k Twist.up).count t = if t = Twist.up then k else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    cases t <;> simp +decide

theorem count_replicate_down (k : ℕ) (t : Twist) :
    (List.replicate k Twist.down).count t = if t = Twist.down then k else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    cases t <;> simp +decide

/-- **Irreducible events of every size.** For every `n ≥ 1` the ladder `^ⁿvⁿ` is a prime closure
    (`FirstReturn.IsPrime`: no proper nonempty closed prefix) of length `2n`. Elementary events, not
    only their composites, are unbounded in complexity. -/
theorem prime_closure_every_length (n : ℕ) (hn : 1 ≤ n) :
    (ladder n).length = 2 * n ∧ FirstReturn.IsPrime (ladder n) := by
  have hlen : (ladder n).length = 2 * n := by simp [ladder]; ring
  refine ⟨hlen, by omega, ?_, ?_⟩
  · simp only [countBalanced, ladder, List.count_append, count_replicate_up, count_replicate_down]
    simp
  · intro k hk hk0
    rw [hlen] at hk
    simp only [countBalanced, ladder, List.take_append, List.take_replicate, List.length_replicate,
      List.count_append, count_replicate_up, count_replicate_down]
    simp
    omega

-- ============================================================================
-- §4  Distance equals delay
-- ============================================================================

open Twist in
/-- A history's length is the sum of its eight twist counts. -/
theorem length_eq_sum_counts (l : List Twist) :
    l.length = l.count up + l.count down + l.count left + l.count right +
      l.count slash + l.count backslash + l.count plus + l.count minus := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [List.length_cons, List.count_cons, ih]
    cases t <;> simp +decide <;> omega

/-- **Distance from closure**: the `ℓ¹` norm of a history's signed action vector, i.e. how far its
    walk on `ℤ⁴` stands from the origin (`Closure_Walk.md`). -/
def distance (h : List Twist) : ℕ :=
  (net h Twist.up Twist.down).natAbs + (net h Twist.left Twist.right).natAbs +
    (net h Twist.slash Twist.backslash).natAbs + (net h Twist.plus Twist.minus).natAbs

/-- **No closure comes sooner than the distance.** Every completion of `h` has at least
    `distance h` events: each unit of unmatched action needs one event to cancel it. -/
theorem delay_ge_distance {h c : List Twist} (hc : countBalanced (h ++ c)) :
    distance h ≤ c.length := by
  have e := (countBalanced_append_iff h c).1 hc
  have hl := length_eq_sum_counts c
  simp only [distance, net] at e ⊢
  omega

/-- `n` copies of `b` when `n ≥ 0`, else `-n` copies of `a`: the events that cancel a net `n` of
    `a` over `b`. -/
def fill (n : ℤ) (a b : Twist) : List Twist :=
  List.replicate n.toNat b ++ List.replicate (-n).toNat a

theorem count_rep (k : ℕ) (a t : Twist) :
    (List.replicate k a).count t = if a = t then k else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    cases a <;> cases t <;> simp +decide

/-- The shortest completion: cancel each axis's net action directly. -/
def shortestCompletion (h : List Twist) : List Twist :=
  fill (net h Twist.up Twist.down) Twist.up Twist.down ++
    fill (net h Twist.left Twist.right) Twist.left Twist.right ++
    fill (net h Twist.slash Twist.backslash) Twist.slash Twist.backslash ++
    fill (net h Twist.plus Twist.minus) Twist.plus Twist.minus

/-- **Distance equals delay.** Every history closes after exactly `distance h` further events, and
    no sooner (`delay_ge_distance`): the shortest closing delay of a history *is* its distance from
    closure. The a priori orientation solution is also the fastest one. -/
theorem distance_eq_delay (h : List Twist) :
    countBalanced (h ++ shortestCompletion h) ∧ (shortestCompletion h).length = distance h ∧
      ∀ c, countBalanced (h ++ c) → (shortestCompletion h).length ≤ c.length := by
  have hb : countBalanced (h ++ shortestCompletion h) := by
    simp only [countBalanced, net, shortestCompletion, fill, List.count_append,
      count_rep, reduceCtorEq, ↓reduceIte]
    omega
  have hlen : (shortestCompletion h).length = distance h := by
    simp only [shortestCompletion, fill, distance, net, List.length_append, List.length_replicate]
    omega
  exact ⟨hb, hlen, fun c hc => hlen ▸ delay_ge_distance hc⟩

-- ============================================================================
-- §5  Selection: a niche sees only the net
-- ============================================================================

/-- Two variants carry the same signed action on every axis. -/
def SameNet (a a' : List Twist) : Prop :=
  net a Twist.up Twist.down = net a' Twist.up Twist.down ∧
  net a Twist.left Twist.right = net a' Twist.left Twist.right ∧
  net a Twist.slash Twist.backslash = net a' Twist.slash Twist.backslash ∧
  net a Twist.plus Twist.minus = net a' Twist.plus Twist.minus

/-- **A niche sees only the net.** Two variants are admitted by exactly the same niches (environments
    `e` in which `variant ++ e` closes) if and only if they carry the same signed action. Selection is
    a filter on the net action and on nothing else: not the order of events, not their number, and
    not any aim. Everything else about a variant is selectively neutral. -/
theorem same_niches_iff_sameNet (a a' : List Twist) :
    (∀ e : List Twist, countBalanced (a ++ e) ↔ countBalanced (a' ++ e)) ↔ SameNet a a' := by
  constructor
  · intro h
    have hc := mirror_closes a
    have hc' := (h (antiparticle a)).1 hc
    have e1 := (countBalanced_append_iff a (antiparticle a)).1 hc
    have e2 := (countBalanced_append_iff a' (antiparticle a)).1 hc'
    unfold SameNet
    omega
  · intro hs e
    unfold SameNet at hs
    rw [countBalanced_append_iff, countBalanced_append_iff]
    omega

/-- **Rearrangement is neutral.** A variant whose events are a rearrangement of another's (an
    inversion, a transposition) is admitted by exactly the same niches. -/
theorem rearrangement_neutral {a a' : List Twist} (p : a.Perm a') (e : List Twist) :
    countBalanced (a ++ e) ↔ countBalanced (a' ++ e) :=
  ⟨fun h => ClosureUnitarity.countBalanced_perm (p.symm.append_right e) h,
   fun h => ClosureUnitarity.countBalanced_perm (p.append_right e) h⟩

-- ============================================================================
-- §6  The proton: the simplest isolated imbalance
-- ============================================================================

section Proton

open QLF.BaryonWinding

theorem signTriple_ne_zero_axes : ∀ p q r : Option Ax, signTriple p q r ≠ 0 →
    (p = some Ax.x ∨ q = some Ax.x ∨ r = some Ax.x) ∧
    (p = some Ax.y ∨ q = some Ax.y ∨ r = some Ax.y) ∧
    (p = some Ax.z ∨ q = some Ax.z ∨ r = some Ax.z) := by
  decide

/-- **A winding needs all three spatial axes.** A history with nonzero baryon winding contains a
    twist on each of `x`, `y`, `z`. -/
theorem winding_needs_three_axes : ∀ w : List Twist, baryonNumber w ≠ 0 →
    (∃ t ∈ w, axOf t = some Ax.x) ∧ (∃ t ∈ w, axOf t = some Ax.y) ∧ (∃ t ∈ w, axOf t = some Ax.z)
  | [], h => (h rfl).elim
  | [_], h => (h rfl).elim
  | [_, _], h => (h rfl).elim
  | a :: b :: c :: rest, h => by
    by_cases hs : signTriple (axOf a) (axOf b) (axOf c) = 0
    · have h' : baryonNumber (b :: c :: rest) ≠ 0 := by
        intro h0; apply h; simp only [baryonNumber, hs, h0]; rfl
      obtain ⟨⟨t1, m1, e1⟩, ⟨t2, m2, e2⟩, ⟨t3, m3, e3⟩⟩ := winding_needs_three_axes _ h'
      exact ⟨⟨t1, List.mem_cons_of_mem _ m1, e1⟩, ⟨t2, List.mem_cons_of_mem _ m2, e2⟩,
        ⟨t3, List.mem_cons_of_mem _ m3, e3⟩⟩
    · have mem : a ∈ a :: b :: c :: rest ∧ b ∈ a :: b :: c :: rest ∧ c ∈ a :: b :: c :: rest := by
        simp
      obtain ⟨hx, hy, hz⟩ := signTriple_ne_zero_axes _ _ _ hs
      refine ⟨?_, ?_, ?_⟩
      · rcases hx with e | e | e
        exacts [⟨a, mem.1, e⟩, ⟨b, mem.2.1, e⟩, ⟨c, mem.2.2, e⟩]
      · rcases hy with e | e | e
        exacts [⟨a, mem.1, e⟩, ⟨b, mem.2.1, e⟩, ⟨c, mem.2.2, e⟩]
      · rcases hz with e | e | e
        exacts [⟨a, mem.1, e⟩, ⟨b, mem.2.1, e⟩, ⟨c, mem.2.2, e⟩]

theorem count_pos_of_mem {t : Twist} : ∀ {w : List Twist}, t ∈ w → 0 < w.count t
  | _ :: _, List.Mem.head _ => by
    have : (t == t) = true := by cases t <;> rfl
    simp [List.count_cons, this]
  | _ :: _, List.Mem.tail _ h => by
    have := count_pos_of_mem h
    rw [List.count_cons]
    omega

theorem axis_count_pos {w : List Twist} {a : Ax} (h : ∃ t ∈ w, axOf t = some a) :
    (a = Ax.x → 0 < w.count Twist.left + w.count Twist.right) ∧
    (a = Ax.y → 0 < w.count Twist.up + w.count Twist.down) ∧
    (a = Ax.z → 0 < w.count Twist.slash + w.count Twist.backslash) := by
  obtain ⟨t, m, e⟩ := h
  have := count_pos_of_mem m
  cases t <;> simp only [axOf, Option.some.injEq, reduceCtorEq] at e
  all_goals
    subst e
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;> (try cases h') <;> omega

/-- **Short closures carry no winding.** Every closure of length below six has baryon number zero:
    a winding needs all three spatial axes, and a closure pays two events per axis. -/
theorem short_closures_unwound {w : List Twist} (hb : countBalanced w) (hl : w.length < 6) :
    baryonNumber w = 0 := by
  by_contra h
  obtain ⟨hx, hy, hz⟩ := winding_needs_three_axes w h
  have cx := (axis_count_pos hx).1 rfl
  have cy := (axis_count_pos hy).2.1 rfl
  have cz := (axis_count_pos hz).2.2 rfl
  have hlen := length_eq_sum_counts w
  unfold countBalanced at hb
  omega

/-- The proton word `>^/` closed by `<\v`. -/
def protonClosure : List Twist :=
  [Twist.right, Twist.up, Twist.slash, Twist.left, Twist.backslash, Twist.down]

/-- **The proton is the simplest isolated imbalance.** A closure is isolated (`isolated_iff_closed`),
    so it can hide an imbalance only in a quantity that counting cannot see. The first such quantity
    is the three-axis winding: no closure shorter than six carries it (`short_closures_unwound`),
    and at six the proton word `>^/` (`baryon_proton`) closes into a prime closure with winding
    exactly `+1`. -/
theorem proton_simplest_isolated_imbalance :
    protonClosure.take 3 = [Twist.right, Twist.up, Twist.slash] ∧
    countBalanced protonClosure ∧ FirstReturn.IsPrime protonClosure ∧
    baryonNumber protonClosure = 1 ∧ protonClosure.length = 6 ∧
    ∀ w : List Twist, countBalanced w → w.length < 6 → baryonNumber w = 0 := by
  refine ⟨rfl, ?_, ?_, by decide, rfl, fun w hb hl => short_closures_unwound hb hl⟩
  · unfold countBalanced; decide
  · decide

theorem signTriple_none_left (q r : Option Ax) : signTriple none q r = 0 := by
  cases q <;> cases r <;> rfl

theorem signTriple_none_mid (p r : Option Ax) : signTriple p none r = 0 := by
  rcases p with _ | ⟨_ | _ | _⟩ <;> rfl

theorem signTriple_none_right (p q : Option Ax) : signTriple p q none = 0 := by
  rcases p with _ | ⟨_ | _ | _⟩ <;> rcases q with _ | ⟨_ | _ | _⟩ <;> rfl

/-- A history of gauge twists only carries no winding. -/
theorem baryon_all_gauge : ∀ w : List Twist, (∀ t ∈ w, axOf t = none) → baryonNumber w = 0
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | a :: b :: c :: rest, h => by
    have ha : axOf a = none := h a (by simp)
    have ih := baryon_all_gauge (b :: c :: rest) (fun t ht => h t (List.mem_cons_of_mem _ ht))
    show signTriple (axOf a) (axOf b) (axOf c) + baryonNumber (b :: c :: rest) = 0
    rw [ha, signTriple_none_left, ih]; rfl

theorem baryon_gauge_tail (a : Twist) (w : List Twist) (h : ∀ t ∈ w, axOf t = none) :
    baryonNumber (a :: w) = 0 := by
  match w, h with
  | [], _ => rfl
  | [_], _ => rfl
  | g₁ :: g₂ :: r, h =>
    have h1 : axOf g₁ = none := h g₁ (by simp)
    show signTriple (axOf a) (axOf g₁) (axOf g₂) + baryonNumber (g₁ :: g₂ :: r) = 0
    rw [h1, signTriple_none_mid, baryon_all_gauge _ h]; rfl

/-- **Gauge padding leaves the winding unchanged.** Appending gauge twists to any history adds no
    winding: every window that reaches the padding contains an axis-free twist. -/
theorem baryon_append_gauge : ∀ (l w : List Twist), (∀ t ∈ w, axOf t = none) →
    baryonNumber (l ++ w) = baryonNumber l
  | [], w, h => baryon_all_gauge w h
  | [a], w, h => by rw [List.singleton_append, baryon_gauge_tail a w h]; rfl
  | [a, b], w, h => by
    match w, h with
    | [], _ => rfl
    | g :: r, h =>
      have hg : axOf g = none := h g (by simp)
      show signTriple (axOf a) (axOf b) (axOf g) + baryonNumber (b :: g :: r) = baryonNumber [a, b]
      rw [hg, signTriple_none_right, baryon_gauge_tail b (g :: r) h]; rfl
  | a :: b :: c :: rest, w, h => by
    have ih := baryon_append_gauge (b :: c :: rest) w h
    show signTriple (axOf a) (axOf b) (axOf c) + baryonNumber ((b :: c :: rest) ++ w) =
      signTriple (axOf a) (axOf b) (axOf c) + baryonNumber (b :: c :: rest)
    rw [ih]

/-- A balanced gauge word from a word of bits: each bit chooses `+-` or `-+`. -/
def gaugeWord (bs : List Bool) : List Twist :=
  bs.flatMap (fun b => if b then [Twist.plus, Twist.minus] else [Twist.minus, Twist.plus])

theorem gaugeWord_cons (b : Bool) (bs : List Bool) :
    gaugeWord (b :: bs) =
      (if b then [Twist.plus, Twist.minus] else [Twist.minus, Twist.plus]) ++ gaugeWord bs := rfl

theorem gaugeWord_length (bs : List Bool) : (gaugeWord bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [gaugeWord_cons, List.length_append, ih]; cases b <;> simp <;> ring

theorem gaugeWord_gauge (bs : List Bool) : ∀ t ∈ gaugeWord bs, axOf t = none := by
  induction bs with
  | nil => simp [gaugeWord]
  | cons b bs ih =>
    intro t ht
    rw [gaugeWord_cons, List.mem_append] at ht
    rcases ht with ht | ht
    · cases b <;> simp at ht <;> rcases ht with rfl | rfl <;> rfl
    · exact ih t ht

theorem gaugeWord_balanced (bs : List Bool) : countBalanced (gaugeWord bs) := by
  induction bs with
  | nil => unfold countBalanced; decide
  | cons b bs ih =>
    rw [gaugeWord_cons]
    apply ClosureKernel.balanced_append _ ih
    cases b <;> (unfold countBalanced; decide)

theorem gaugeWord_injective : Function.Injective gaugeWord := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons b y => cases b <;> simp [gaugeWord] at h
  | cons a x ih =>
    intro y h
    cases y with
    | nil => cases a <;> simp [gaugeWord] at h
    | cons b y =>
      rw [gaugeWord_cons, gaugeWord_cons] at h
      cases a <;> cases b <;> simp at h
      all_goals rw [ih h]

/-- **Possibility makes the proton stable: its ways are unbounded.** At length `6 + 2n` there are at
    least `2ⁿ` closures carrying baryon winding exactly `+1`, all admitted by the same niches as the
    proton closure padded to that length. The proton is not one fragile configuration but a class
    whose multiplicity grows without bound. (Census: 192 at length 6, 15 552 at length 8.) -/
theorem proton_ways_unbounded (n : ℕ) :
    2 ^ n ≤ ((words Twist (6 + 2 * n)).filter
      (fun w => decide (countBalanced w ∧ baryonNumber w = 1))).card := by
  have hcard : (words Bool n).card = 2 ^ n := by rw [card_words]; simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun bs => protonClosure ++ gaugeWord bs)
  · intro bs hbs
    simp only [Finset.mem_coe, mem_words] at hbs
    simp only [Finset.mem_coe, Finset.mem_filter, mem_words, decide_eq_true_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, gaugeWord_length, hbs]; rfl
    · exact ClosureKernel.balanced_append (by unfold countBalanced; decide) (gaugeWord_balanced bs)
    · rw [baryon_append_gauge _ _ (gaugeWord_gauge bs)]; decide
  · intro x _ y _ h
    exact gaugeWord_injective (List.append_cancel_left h)

end Proton

end QLF.Manifestation
