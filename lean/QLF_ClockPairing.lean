import QLF_ClockDomains
import QLF_ClosureUnitarity
import QLF_Majorana
import QLF_QuarkSignature

/-!
# Paired local clocks and the map `J`

Companion: Time_Reversed_Clock_Domains.md (section "Next stage"), issue #236.

The second finite stage of the clock-domain program. On paired histories
`h = (p, q)` it studies the candidate map `J (p, q) = (dagger q, dagger p)`:
swap the two domains and conjugate-reverse each word.

What is proved, and how each statement may be read:

* `J` is an involution preserving admissibility (structural).
* Its fixed points are exactly the canonical dagger completions `q = dagger p`,
  and there are `8 ^ n` of them at word length `n`. So `J` does not pair every
  history with a distinct counterpart: it does not double the census.
* The same class `q = dagger p` is the stricter class on which the counterpart
  is reconstructible; the non-identifiability witnesses of `QLF_ClockDomains`
  lie outside it.
* The record fiber is counted, not merely witnessed: `([up], 3)` has 21
  admissible counterparts.
* The charge label flips under `dagger` because of the conjugation, not the
  reversal. Opposite total label on the two sides holds for every admissible
  history, so it is forced by closure and is no evidence for a reversed
  counterpart.
* Local ticks: `J` reverses event order and preserves every duration, so order
  reversal alone yields no factor between the two ages (a no-go).

No physical time reversal, antimatter identification, horizon, no-signalling
law, tick normalization or age map is derived. No axiom is added.
-/

namespace QLF.ClockPairing

open QLF QLF.ClockDomains QLF.ClosureUnitarity QLF.QuarkSignature

-- ==========================================
-- §1  The candidate map and its two neighbours
-- ==========================================

/-- Swap the domains and conjugate-reverse each word. -/
def J (h : History) : History := (dagger h.2, dagger h.1)

/-- Swap the domains and reverse each word, without conjugating. -/
def reversal (h : History) : History := (h.2.reverse, h.1.reverse)

/-- Swap the domains only. -/
def swap (h : History) : History := (h.2, h.1)

theorem dagger_dagger (ts : List Twist) : dagger (dagger ts) = ts :=
  QLF.Majorana.antiparticle_involutive ts

theorem dagger_length (ts : List Twist) : (dagger ts).length = ts.length := by
  simp [dagger]

/-- `J` is an involution. -/
theorem J_involutive (h : History) : J (J h) = h := by
  obtain ⟨p, q⟩ := h
  simp only [J, dagger_dagger]

/-- `J` preserves joint count balance. -/
theorem J_admissible (h : History) (hh : admissible h) : admissible (J h) := by
  obtain ⟨p, q⟩ := h
  unfold admissible at hh ⊢
  unfold countBalanced at hh ⊢
  simp only [J, List.count_append, count_dagger, Twist.conj] at hh ⊢
  omega

/-- `J` exchanges the two word lengths. -/
theorem J_lengths (h : History) :
    (J h).1.length = h.2.length ∧ (J h).2.length = h.1.length :=
  ⟨dagger_length _, dagger_length _⟩

-- ==========================================
-- §2  Fixed points: `J` does not double the census
-- ==========================================

/-- The stricter pairing class: the counterpart is the dagger of the local word. -/
def strict (h : History) : Prop := h.2 = dagger h.1

/-- **The fixed points of `J` are exactly the canonical dagger completions.** -/
theorem J_fixed_iff (h : History) : J h = h ↔ strict h := by
  obtain ⟨p, q⟩ := h
  unfold strict
  simp only [J, Prod.mk.injEq]
  constructor
  · rintro ⟨_, h2⟩
    exact h2.symm
  · intro hq
    subst hq
    exact ⟨dagger_dagger p, rfl⟩

/-- Every member of the strict class is admissible. -/
theorem strict_admissible (h : History) (hs : strict h) : admissible h := by
  obtain ⟨p, q⟩ := h
  have hq : q = dagger p := hs
  subst hq
  exact countBalanced_append_dagger p

/-- The canonical history `([up], [down])` is its own `J`-counterpart. -/
theorem canonical_fixed : J canonical = canonical := by decide

/-- **`J` is not fixed-point free** on admissible histories, so an involution
    alone does not give every history a distinct counterpart. -/
theorem J_not_fixed_point_free : ∃ h : History, admissible h ∧ J h = h :=
  ⟨canonical, canonical_admissible, canonical_fixed⟩

/-- Histories with unequal word lengths are never fixed. -/
theorem J_fixed_lengths (h : History) (hf : J h = h) : h.1.length = h.2.length := by
  have hs := (J_fixed_iff h).mp hf
  unfold strict at hs
  rw [hs, dagger_length]

/-- The fixed points with local word length `n`, listed. -/
def fixedOfLength (n : ℕ) : List History := (words n).map (fun p => (p, dagger p))

theorem mem_fixedOfLength (n : ℕ) (h : History) :
    h ∈ fixedOfLength n ↔ J h = h ∧ h.1.length = n := by
  obtain ⟨p, q⟩ := h
  rw [J_fixed_iff]
  unfold strict fixedOfLength
  simp only [List.mem_map, mem_words, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨hq, hp⟩
    exact ⟨p, hp, rfl, hq.symm⟩

theorem words_length (n : ℕ) : (words n).length = 8 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [words, allTwists, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_map, List.length_nil, ih]
    rw [pow_succ]
    omega

/-- **The fixed points are counted**: `8 ^ n` at local word length `n`. -/
theorem fixedOfLength_length (n : ℕ) : (fixedOfLength n).length = 8 ^ n := by
  simp [fixedOfLength, words_length]

/-- All admissible histories with word lengths `(m, n)`, listed. -/
def admissiblePairs (m n : ℕ) : List History :=
  (words m).flatMap (fun p =>
    ((words n).filter (fun q => decide (countBalanced (p ++ q)))).map (fun q => (p, q)))

/-- At lengths `(1, 1)` every admissible history is fixed: 8 of 8. -/
theorem census_one_one :
    (admissiblePairs 1 1).length = 8 ∧
      ((admissiblePairs 1 1).filter (fun h => decide (J h = h))).length = 8 := by
  decide

set_option maxRecDepth 200000 in
/-- At lengths `(2, 2)`: 168 admissible histories, 64 of them fixed. The 104
    others pair off, so `J` has `64 + 52 = 116` orbits, not `84`. -/
theorem census_two_two :
    (admissiblePairs 2 2).length = 168 ∧
      ((admissiblePairs 2 2).filter (fun h => decide (J h = h))).length = 64 := by
  decide

theorem words_nodup : ∀ n : ℕ, (words n).Nodup
  | 0 => by simp [words]
  | n + 1 => by
    have ih := words_nodup n
    unfold words
    rw [List.nodup_flatMap]
    refine ⟨fun t _ => ih.map (fun a b hab => List.tail_eq_of_cons_eq hab), ?_⟩
    have hd : ∀ a b : Twist, a ≠ b →
        List.Disjoint ((words n).map (List.cons a)) ((words n).map (List.cons b)) := by
      intro a b hab x hx hy
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
      exact hab (List.head_eq_of_cons_eq hv).symm
    exact (by decide : allTwists.Pairwise (· ≠ ·)).imp (fun h => hd _ _ h)

/-- The listed fixed points are pairwise distinct, so `8 ^ n` counts histories. -/
theorem fixedOfLength_nodup (n : ℕ) : (fixedOfLength n).Nodup :=
  (words_nodup n).map (fun _ _ hab => congrArg Prod.fst hab)

-- ==========================================
-- §3  The strict class removes the witnesses
-- ==========================================

theorem extendedLeft_not_strict : ¬ strict extendedLeft := by
  unfold strict; decide

theorem extendedRight_not_strict : ¬ strict extendedRight := by
  unfold strict; decide

theorem canonical_strict : strict canonical := by
  unfold strict; decide

/-- In the strict class the local word determines the whole history. -/
theorem strict_unique (h k : History) (hh : strict h) (hk : strict k)
    (hp : h.1 = k.1) : h = k := by
  obtain ⟨p, q⟩ := h
  obtain ⟨p', q'⟩ := k
  unfold strict at hh hk
  simp only at hh hk hp
  subst hp
  rw [hh, hk]

/-- So no two strict histories share a record while differing in counterpart:
    the collision that blocks reconstruction cannot occur in this class. -/
theorem strict_no_collision (h k : History) (hh : strict h) (hk : strict k)
    (hsame : accessible h = accessible k) : h.2 = k.2 := by
  have hp : (accessible h).1 = (accessible k).1 := congrArg Prod.fst hsame
  exact congrArg Prod.snd (strict_unique h k hh hk hp)

-- ==========================================
-- §4  The record fiber, counted
-- ==========================================

/-- The admissible counterparts of length `n` for a local word `p`. -/
def fiber (p : List Twist) (n : ℕ) : List (List Twist) :=
  (words n).filter (fun q => decide (countBalanced (p ++ q)))

theorem mem_fiber (p : List Twist) (n : ℕ) (q : List Twist) :
    q ∈ fiber p n ↔ admissible (p, q) ∧ accessible (p, q) = (p, n) := by
  unfold fiber admissible accessible
  simp only [List.mem_filter, mem_words, decide_eq_true_eq, Prod.mk.injEq, true_and]
  exact And.comm

/-- The record `([up], 1)` has exactly one admissible counterpart. -/
theorem fiber_up_one : (fiber [Twist.up] 1).length = 1 := by decide

/-- **The record `([up], 3)` has exactly 21 admissible counterparts.** The two
    witnesses of `QLF_ClockDomains` are two of these 21. -/
theorem fiber_up_three : (fiber [Twist.up] 3).length = 21 := by decide

theorem extendedLeft_in_fiber : extendedLeft.2 ∈ fiber [Twist.up] 3 :=
  (mem_fiber _ _ _).mpr ⟨extendedLeft_admissible, rfl⟩

theorem extendedRight_in_fiber : extendedRight.2 ∈ fiber [Twist.up] 3 :=
  (mem_fiber _ _ _).mpr ⟨extendedRight_admissible, rfl⟩

-- ==========================================
-- §5  Label versus order
-- ==========================================

theorem charge3_conj (t : Twist) : charge3 t.conj = - charge3 t := by
  cases t <;> rfl

theorem charge3W_append (a b : List Twist) :
    charge3W (a ++ b) = charge3W a + charge3W b := by
  simp [charge3W]

/-- **Pure reversal leaves the label alone.** -/
theorem charge3W_reverse (w : List Twist) : charge3W w.reverse = charge3W w := by
  simp [charge3W]

theorem charge3W_map_conj (w : List Twist) :
    charge3W (w.map Twist.conj) = - charge3W w := by
  induction w with
  | nil => rfl
  | cons t rest ih =>
    have hc : charge3W (t :: rest) = charge3 t + charge3W rest := by simp [charge3W]
    have hm : charge3W ((t :: rest).map Twist.conj)
        = charge3 t.conj + charge3W (rest.map Twist.conj) := by simp [charge3W]
    rw [hm, hc, ih, charge3_conj]
    omega

/-- **The dagger flips the label**, and by `charge3W_reverse` the flip comes
    from the conjugation, not from reversing the order. -/
theorem charge3W_dagger (w : List Twist) : charge3W (dagger w) = - charge3W w := by
  unfold dagger
  rw [charge3W_reverse, charge3W_map_conj]

/-- The label as a signed count. -/
theorem charge3W_counts (w : List Twist) :
    charge3W w = 2 * ((w.count Twist.up : ℤ) - w.count Twist.down)
      + 2 * ((w.count Twist.right : ℤ) - w.count Twist.left)
      + 2 * ((w.count Twist.slash : ℤ) - w.count Twist.backslash)
      - 3 * ((w.count Twist.plus : ℤ) - w.count Twist.minus) := by
  induction w with
  | nil => rfl
  | cons t rest ih =>
    have hc : charge3W (t :: rest) = charge3 t + charge3W rest := by simp [charge3W]
    rw [hc, ih]
    cases t <;> simp (config := { decide := true }) only [charge3, List.count_cons, ite_true, ite_false,
      Nat.cast_add, Nat.cast_one, add_zero] <;> omega

/-- A count-balanced word carries zero label. -/
theorem charge3W_balanced (w : List Twist) (hw : countBalanced w) : charge3W w = 0 := by
  rw [charge3W_counts]
  unfold countBalanced at hw
  omega

/-- **Opposite label on the two sides is forced by closure alone.** It holds
    for every admissible history, whatever the completion, so it is no evidence
    for a reversed counterpart. -/
theorem admissible_label_opposite (h : History) (hh : admissible h) :
    charge3W h.1 + charge3W h.2 = 0 := by
  rw [← charge3W_append]
  exact charge3W_balanced _ hh

/-- `J` carries the label of each side to minus the label of the other. -/
theorem J_label (h : History) :
    charge3W (J h).1 = - charge3W h.2 ∧ charge3W (J h).2 = - charge3W h.1 :=
  ⟨charge3W_dagger _, charge3W_dagger _⟩

/-- The pure reversal carries the label across unchanged. -/
theorem reversal_label (h : History) :
    charge3W (reversal h).1 = charge3W h.2 ∧ charge3W (reversal h).2 = charge3W h.1 :=
  ⟨charge3W_reverse _, charge3W_reverse _⟩

-- ==========================================
-- §6  Local ticks: order reversed, duration preserved
-- ==========================================

/-- **The event at tick `i` of a word sits, conjugated, at tick `n − 1 − i` of its
    dagger.** Each word is still read `0, 1, …, n − 1` in its own domain. -/
theorem dagger_tick (w : List Twist) (i : ℕ) (hi : i < w.length) :
    (dagger w)[i]? = (w[w.length - 1 - i]?).map Twist.conj := by
  unfold dagger
  rw [List.getElem?_reverse (by simpa using hi)]
  simp

/-- Cross-domain order is reversed: an earlier tick lands on a later one. -/
theorem tick_order_reversed (n i j : ℕ) (hij : i < j) (hj : j < n) :
    n - 1 - j < n - 1 - i := by omega

/-- **No-go: `J` preserves total duration and merely exchanges the two.** Order
    reversal alone therefore gives no factor between the two elapsed counts. -/
theorem J_duration (h : History) :
    (J h).1.length + (J h).2.length = h.1.length + h.2.length := by
  obtain ⟨hl, hr⟩ := J_lengths h
  omega

/-- A history with equal durations keeps equal durations under `J`. -/
theorem J_equal_durations (h : History) (he : h.1.length = h.2.length) :
    (J h).1.length = (J h).2.length := by
  obtain ⟨hl, hr⟩ := J_lengths h
  omega

/-- The same holds for the pure reversal and for the bare swap. -/
theorem reversal_duration (h : History) :
    (reversal h).1.length + (reversal h).2.length = h.1.length + h.2.length := by
  simp only [reversal, List.length_reverse]
  omega

theorem swap_duration (h : History) :
    (swap h).1.length + (swap h).2.length = h.1.length + h.2.length := by
  simp only [swap]
  omega

end QLF.ClockPairing
