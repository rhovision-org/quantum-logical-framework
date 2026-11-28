import Mathlib
import QLF_TwistAlphabet

/-!
# QLF_ClosureSelection — **a constraint class computed by closure, with its cost**

Obligation O4 of [`Framing.md`](../Framing.md) §6: which problems can be posed as closure obligations,
and at what cost. `closing_cost_exact` solves *free completion* (append anything): the shortest closing
continuation has length exactly the imbalance. The next class is **closure selection**: an obligation
`o` and a list of offered words `ws`; choose some of the offers, in order, so that `o` followed by the
chosen words closes. This is the form of composition, scheduling and resource matching: each offer
carries signed distinctions, and a solution is a selection that leaves none unresolved.

**Results** (no axioms):

* `charge` — the four signed counts of a history; `balanced_iff_charge_zero`: closure is
  `charge = 0`, and `charge_append` makes it additive.
* `mem_reachable` — the **reachable charges** `reachable ws`, built by one sweep over the offers, are
  exactly the total charges of the selections.
* `selection_closes_iff` — **a selection closes iff `−charge o` is reachable**, so `closable` decides
  closure selection (`closable_iff`).
* `reachable_card_le` — **the cost**: the sweep never holds more than `(2L + 1)⁴` charges, `L` the total
  written length of the offers. Each of the `k` steps touches at most that many, so closure selection
  is decided in time polynomial in the written length.
* `subset_sum_embeds` — Subset Sum is closure selection: weights become runs of `^`, the target a run of
  `v`. Since a charge is written as a count, the weights are in unary, so this is consistent with the
  polynomial bound and transfers no NP-hardness: a closure encoding pays for every unit it resolves.

So the class is **conservation of written counts**: problems whose constraints say that signed
quantities, written out, cancel. Those closure computes in polynomial time. Problems whose hardness lives
in a compact (binary) description of large quantities are not in it, which is the closure-side form of
the warning in [`P_vs_NP_QLF.md`](../P_vs_NP_QLF.md) that an encoding can carry the hardness.
-/

namespace QLF.ClosureSelection

open QLF
open scoped List

/-- The four signed counts: `#^ − #v`, `#> − #<`, `#/ − #\`, `#+ − #−`. -/
def charge (h : List Twist) : ℤ × ℤ × ℤ × ℤ :=
  ((h.count Twist.up : ℤ) - h.count Twist.down, (h.count Twist.right : ℤ) - h.count Twist.left,
    (h.count Twist.slash : ℤ) - h.count Twist.backslash, (h.count Twist.plus : ℤ) - h.count Twist.minus)

theorem balanced_iff_charge_zero (h : List Twist) : countBalanced h ↔ charge h = 0 := by
  unfold countBalanced charge
  simp only [Prod.mk_eq_zero, sub_eq_zero, Nat.cast_inj]
  constructor
  · rintro ⟨a, b, c, d⟩; exact ⟨a, b.symm, c, d⟩
  · rintro ⟨a, b, c, d⟩; exact ⟨a, b.symm, c, d⟩

theorem charge_append (h k : List Twist) : charge (h ++ k) = charge h + charge k := by
  simp only [charge, List.count_append, Prod.mk_add_mk]
  push_cast
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp <;> ring

theorem charge_nil : charge [] = 0 := by simp [charge]

theorem charge_flatten (ws : List (List Twist)) : charge ws.flatten = (ws.map charge).sum := by
  induction ws with
  | nil => simp [charge_nil]
  | cons w ws ih => rw [List.flatten_cons, charge_append, ih, List.map_cons, List.sum_cons]

/-! ## The sweep -/

/-- **Reachable charges**: one sweep over the offers, each either skipped or taken. -/
def reachable : List (List Twist) → Finset (ℤ × ℤ × ℤ × ℤ)
  | [] => {0}
  | w :: ws => reachable ws ∪ (reachable ws).image (fun c => charge w + c)

/-- The reachable charges are exactly the total charges of selections. -/
theorem mem_reachable (ws : List (List Twist)) (c : ℤ × ℤ × ℤ × ℤ) :
    c ∈ reachable ws ↔ ∃ sel, sel <+ ws ∧ (sel.map charge).sum = c := by
  induction ws generalizing c with
  | nil =>
    simp only [reachable, Finset.mem_singleton, List.sublist_nil]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl⟩
    · rintro ⟨sel, rfl, rfl⟩; rfl
  | cons w ws ih =>
    simp only [reachable, Finset.mem_union, Finset.mem_image, ih, List.sublist_cons_iff]
    constructor
    · rintro (⟨sel, hs, rfl⟩ | ⟨_, ⟨sel, hs, rfl⟩, rfl⟩)
      · exact ⟨sel, Or.inl hs, rfl⟩
      · exact ⟨w :: sel, Or.inr ⟨sel, rfl, hs⟩, by simp⟩
    · rintro ⟨sel, (hs | ⟨r, rfl, hr⟩), rfl⟩
      · exact Or.inl ⟨sel, hs, rfl⟩
      · exact Or.inr ⟨_, ⟨r, hr, rfl⟩, by simp⟩

/-- **A selection closes iff the obligation's opposite charge is reachable.** -/
theorem selection_closes_iff (o : List Twist) (ws : List (List Twist)) :
    (∃ sel, sel <+ ws ∧ countBalanced (o ++ sel.flatten)) ↔ -charge o ∈ reachable ws := by
  rw [mem_reachable]
  refine exists_congr fun sel => and_congr Iff.rfl ?_
  rw [balanced_iff_charge_zero, charge_append, charge_flatten, add_comm, add_eq_zero_iff_eq_neg]

/-- The decision procedure. -/
def closable (o : List Twist) (ws : List (List Twist)) : Bool := decide (-charge o ∈ reachable ws)

theorem closable_iff (o : List Twist) (ws : List (List Twist)) :
    closable o ws = true ↔ ∃ sel, sel <+ ws ∧ countBalanced (o ++ sel.flatten) := by
  rw [selection_closes_iff, closable, decide_eq_true_iff]

/-! ## The cost -/

theorem count_add_count_le (a b : Twist) (hab : a ≠ b) (h : List Twist) :
    h.count a + h.count b ≤ h.length := by
  induction h with
  | nil => simp
  | cons t h ih =>
    rw [List.count_cons, List.count_cons, List.length_cons]
    have : (if (t == a) = true then 1 else 0) + (if (t == b) = true then 1 else 0) ≤ 1 := by
      cases t <;> cases a <;> cases b <;> simp_all (config := { decide := true })
    omega

/-- The box of charges with every coordinate in `[−L, L]`. -/
noncomputable def box (L : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  Finset.Icc (-(L : ℤ)) L ×ˢ (Finset.Icc (-(L : ℤ)) L ×ˢ (Finset.Icc (-(L : ℤ)) L ×ˢ
    Finset.Icc (-(L : ℤ)) L))

theorem box_card (L : ℕ) : (box L).card = (2 * L + 1) ^ 4 := by
  simp only [box, Finset.card_product, Int.card_Icc]
  have : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  rw [this]; ring

theorem charge_mem_box (h : List Twist) : charge h ∈ box h.length := by
  have h1 := count_add_count_le Twist.up Twist.down (by decide) h
  have h2 := count_add_count_le Twist.right Twist.left (by decide) h
  have h3 := count_add_count_le Twist.slash Twist.backslash (by decide) h
  have h4 := count_add_count_le Twist.plus Twist.minus (by decide) h
  simp only [box, charge, Finset.mem_product, Finset.mem_Icc]
  omega

theorem box_add {L L' : ℕ} {c c' : ℤ × ℤ × ℤ × ℤ} (hc : c ∈ box L) (hc' : c' ∈ box L') :
    c + c' ∈ box (L + L') := by
  obtain ⟨a, b, d, e⟩ := c
  obtain ⟨a', b', d', e'⟩ := c'
  simp only [box, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk] at hc hc' ⊢
  push_cast
  omega

theorem box_mono {L L' : ℕ} (h : L ≤ L') {c : ℤ × ℤ × ℤ × ℤ} (hc : c ∈ box L) : c ∈ box L' := by
  obtain ⟨a, b, d, e⟩ := c
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hc ⊢
  have : (L : ℤ) ≤ L' := by exact_mod_cast h
  omega

/-- The total written length of the offers. -/
def totalLength (ws : List (List Twist)) : ℕ := (ws.map List.length).sum

theorem reachable_subset_box (ws : List (List Twist)) : reachable ws ⊆ box (totalLength ws) := by
  induction ws with
  | nil =>
    intro c hc
    simp only [reachable, Finset.mem_singleton] at hc
    subst hc
    have := charge_mem_box []
    rw [charge_nil] at this
    simpa [totalLength] using this
  | cons w ws ih =>
    intro c hc
    simp only [reachable, Finset.mem_union, Finset.mem_image] at hc
    have hlen : totalLength (w :: ws) = w.length + totalLength ws := by
      simp [totalLength]
    rw [hlen]
    rcases hc with hc | ⟨c', hc', rfl⟩
    · exact box_mono (Nat.le_add_left _ _) (ih hc)
    · exact box_add (charge_mem_box w) (ih hc')

/-- **The cost of closure selection**: the sweep holds at most `(2L + 1)⁴` charges. -/
theorem reachable_card_le (ws : List (List Twist)) :
    (reachable ws).card ≤ (2 * totalLength ws + 1) ^ 4 := by
  rw [← box_card]; exact Finset.card_le_card (reachable_subset_box ws)

/-! ## Subset Sum is closure selection, in unary -/

theorem count_rep (a b : Twist) (k : ℕ) :
    (List.replicate k b).count a = if a = b then k else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    cases a <;> cases b <;> simp (config := { decide := true })

theorem charge_up (k : ℕ) : charge (List.replicate k Twist.up) = ((k : ℤ), 0, 0, 0) := by
  simp (config := { decide := true }) [charge, count_rep]

theorem charge_down (k : ℕ) : charge (List.replicate k Twist.down) = (-(k : ℤ), 0, 0, 0) := by
  simp (config := { decide := true }) [charge, count_rep]

theorem sum_charge_up (sel : List ℕ) :
    ((sel.map fun x => List.replicate x Twist.up).map charge).sum = ((sel.sum : ℤ), 0, 0, 0) := by
  induction sel with
  | nil => simp [Prod.ext_iff]
  | cons x sel ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, charge_up, List.sum_cons]
    simp

/-- **Subset Sum embeds**: a sub-list of the weights sums to the target iff a selection of the
    corresponding `^` runs closes the obligation `v^T`. -/
theorem subset_sum_embeds (a : List ℕ) (T : ℕ) :
    (∃ sel, sel <+ a ∧ sel.sum = T) ↔
      ∃ sel, sel <+ a.map (fun x => List.replicate x Twist.up) ∧
        countBalanced (List.replicate T Twist.down ++ sel.flatten) := by
  constructor
  · rintro ⟨sel, hs, hsum⟩
    refine ⟨sel.map fun x => List.replicate x Twist.up, hs.map _, ?_⟩
    rw [balanced_iff_charge_zero, charge_append, charge_flatten, sum_charge_up, charge_down, hsum]
    simp
  · rintro ⟨sel, hs, hb⟩
    obtain ⟨l', hl', rfl⟩ := List.sublist_map_iff.mp hs
    refine ⟨l', hl', ?_⟩
    rw [balanced_iff_charge_zero, charge_append, charge_flatten, sum_charge_up, charge_down] at hb
    simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero] at hb
    exact_mod_cast (by linarith [hb.1] : (l'.sum : ℤ) = T)

end QLF.ClosureSelection
