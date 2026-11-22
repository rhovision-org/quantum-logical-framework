import QLF_ClosureChannels
import QLF_ClosureBinding

set_option linter.unusedVariables false

/-!
# QLF_Morphogenesis — compatibility, conserved demotion, and the residue that differentiates

The first rungs of the morphogenesis ladder of [`Morphogenesis.md`](../Morphogenesis.md). The
question is what local closure can and cannot do to a diverse population of histories, before any
lattice or simulation enters. Everything here is about counts on the 8-twist alphabet; Pauli closure
comes free by `count_balanced_pauli_closed`. No axioms.

## §1  Compatibility: trivial on closures, an opposite-charge rule on open strands

A natural first guess for a morphogen rule is a compatibility graph `K(i, j) = 1` iff the joint history
of `i` and `j` is ZFA. On closures that graph is **complete**:

* **`closures_always_compatible`** — two closures always bind. So no differentiation can come from
  closure–closure compatibility; a rule that differentiates must act on something that is not yet
  closed.
* **`bind_iff_opposite`** — two histories bind iff their boundary states are opposite,
  `disp A + disp B = 0` in `ℤ⁴`. On open strands this is a charge rule: each open strand binds only
  with strands carrying the opposite boundary state.
* **`identical_open_blocked`** — an open strand never binds with a copy of itself (the count-level
  analogue of `identical_channel_blocked`).

## §2  Promotion and demotion conserve the ledger

A **region** is a list of histories. Its **ledger** is the sum of their boundary states. The local
events are: promote (join two histories), demote (split one), emit (a closure leaves as a receipt),
reorder. None of them is defined by any target pattern.

* **`event_conserves_ledger`** / **`events_conserve_ledger`** — every local event, and every finite
  sequence of them, leaves the ledger unchanged.
* **`demotion_leaves_closures`** — demoting a closure along a closed prefix leaves two closures: no
  receipt is lost by unbinding.

## §3  What local closure can erase, exactly

* **`region_closes_iff`** — a region can be closed away completely by local events **iff its ledger is
  zero**.
* **`imbalance_persists`** — a region with non-zero ledger keeps at least one open strand under every
  sequence of local events.
* **`excess_species_persists`** — sharper, per projection: if any additive reading of the ledger (for
  instance the `up − down` count) is positive, some surviving strand carries a positive value of it.
  The locally excess species cannot be removed by closure; only transport moves it.
* **`hop_flux`** — moving one history between regions changes their ledgers by exactly its boundary
  state and conserves the total: the continuity equation `Δ ledger = −flux`.

These are the substrate statement of the mechanism behind diffusion-limited `A + B → 0` segregation
(Ovchinnikov–Zeldovich 1978; Toussaint–Wilczek 1983): local closure removes the balanced part, the
conserved residue is the initial fluctuation of the ledger, and that residue is what is left to form
domains. Whether it does on a lattice is a numerical question, tested in
[`morphogenesis_census.py`](../morphogenesis_census.py) (`Morphogenesis.md` §4).

## Scope

Bookkeeping in the method's sense: conservation and its consequences, proved exactly. These theorems
do not say a pattern forms, that it persists, or that it has a preferred wavelength. They say what any
morphogen rule built from closure alone must conserve, and so what it can leave behind.
-/

namespace QLF.Morphogenesis

open QLF QLF.ClosureChannels

local notation "Bind" => QLF.ClosureBinding.Bind

/-- A boundary state / ledger value in `ℤ⁴`. -/
abbrev Ledger := ℤ × ℤ × ℤ × ℤ

-- ==========================================
-- §1  Compatibility
-- ==========================================

/-- **Closures are always compatible.** The closure–closure compatibility graph is complete, so it
    cannot differentiate anything. -/
theorem closures_always_compatible {A B : List Twist} (hA : countBalanced A)
    (hB : countBalanced B) : Bind A B :=
  ClosureKernel.balanced_append hA hB

/-- **Two histories bind iff their boundary states are opposite.** -/
theorem bind_iff_opposite (A B : List Twist) : Bind A B ↔ disp A + disp B = 0 := by
  unfold QLF.ClosureBinding.Bind
  rw [balanced_iff_disp, disp_append]

/-- With a closure, binding is decided by the partner alone. -/
theorem bind_closure_iff {A B : List Twist} (hA : countBalanced A) :
    Bind A B ↔ countBalanced B := by
  rw [bind_iff_opposite, (balanced_iff_disp A).1 hA, zero_add, balanced_iff_disp]

/-- **An open strand never binds with a copy of itself.** -/
theorem identical_open_blocked {A : List Twist} (hA : ¬ countBalanced A) : ¬ Bind A A := by
  rw [bind_iff_opposite]
  rw [balanced_iff_disp] at hA
  intro h
  apply hA
  rcases hd : disp A with ⟨a, b, c, d⟩
  rw [hd] at h
  simp only [Prod.mk_add_mk, Prod.mk_eq_zero] at h ⊢
  omega

/-- Worked instances: `^` binds `v`, and `^` does not bind `<`. -/
theorem up_binds_down : Bind [Twist.up] [Twist.down] := by
  unfold QLF.ClosureBinding.Bind countBalanced; decide

theorem up_not_binds_left : ¬ Bind [Twist.up] [Twist.left] := by
  unfold QLF.ClosureBinding.Bind countBalanced; decide

-- ==========================================
-- §2  Regions, events, the ledger
-- ==========================================

/-- The **ledger** of a region: the sum of its histories' boundary states. -/
def ledger (S : List (List Twist)) : Ledger := (S.map disp).sum

theorem ledger_nil : ledger [] = 0 := rfl

theorem ledger_cons (A : List Twist) (S : List (List Twist)) :
    ledger (A :: S) = disp A + ledger S := by
  simp [ledger]

/-- The **local events** on a region. Promotion joins two histories, demotion splits one, emission
    releases a closure as a receipt, and reordering changes nothing physical. -/
inductive Event : List (List Twist) → List (List Twist) → Prop
  | promote (A B : List Twist) (S : List (List Twist)) : Event (A :: B :: S) ((A ++ B) :: S)
  | demote (A B : List Twist) (S : List (List Twist)) : Event ((A ++ B) :: S) (A :: B :: S)
  | emit (C : List Twist) (S : List (List Twist)) (hC : countBalanced C) : Event (C :: S) S
  | reorder {S T : List (List Twist)} (h : S.Perm T) : Event S T

/-- **Every local event conserves the ledger.** -/
theorem event_conserves_ledger {S T : List (List Twist)} (h : Event S T) :
    ledger S = ledger T := by
  cases h with
  | promote A B S =>
    simp only [ledger_cons, disp_append]
    abel
  | demote A B S =>
    simp only [ledger_cons, disp_append]
    abel
  | emit C S hC =>
    rw [ledger_cons, (balanced_iff_disp C).1 hC, zero_add]
  | reorder h =>
    exact (h.map disp).sum_eq

/-- **Every finite sequence of local events conserves the ledger.** -/
theorem events_conserve_ledger {S T : List (List Twist)}
    (h : Relation.ReflTransGen Event S T) : ledger S = ledger T := by
  induction h with
  | refl => rfl
  | tail _ hst ih => exact ih.trans (event_conserves_ledger hst)

/-- **Demotion loses no receipt**: splitting a closure along a closed prefix leaves two closures. -/
theorem demotion_leaves_closures {A B : List Twist} (hAB : countBalanced (A ++ B))
    (hA : countBalanced A) : countBalanced A ∧ countBalanced B :=
  ⟨hA, ClosureKernel.balanced_of_append hA hAB⟩

-- ==========================================
-- §3  What local closure can erase
-- ==========================================

theorem ledger_eq_disp_flatten : ∀ S : List (List Twist), ledger S = disp S.flatten
  | [] => by simp [ledger, disp]; rfl
  | A :: S => by
    rw [ledger_cons, List.flatten_cons, disp_append, ledger_eq_disp_flatten S]

/-- Promotion can always gather a non-empty region into one history. -/
theorem joins_to_flatten : ∀ (A : List Twist) (S : List (List Twist)),
    Relation.ReflTransGen Event (A :: S) [A ++ S.flatten]
  | A, [] => by
    simp only [List.flatten_nil, List.append_nil]
    exact Relation.ReflTransGen.refl
  | A, B :: S => by
    have h2 := joins_to_flatten (A ++ B) S
    rw [List.append_assoc, ← List.flatten_cons] at h2
    exact Relation.ReflTransGen.head (Event.promote A B S) h2

/-- **A region can be closed away completely iff its ledger is zero.** -/
theorem region_closes_iff (S : List (List Twist)) :
    Relation.ReflTransGen Event S [] ↔ ledger S = 0 := by
  constructor
  · intro h
    rw [events_conserve_ledger h]
    rfl
  · intro h
    cases S with
    | nil => exact Relation.ReflTransGen.refl
    | cons A S =>
      have hb : countBalanced (A ++ S.flatten) := by
        rw [balanced_iff_disp, ← List.flatten_cons, ← ledger_eq_disp_flatten]
        exact h
      exact (joins_to_flatten A S).tail (Event.emit _ [] hb)

theorem ledger_zero_of_all_balanced :
    ∀ T : List (List Twist), (∀ A ∈ T, countBalanced A) → ledger T = 0
  | [], _ => rfl
  | A :: T, h => by
    rw [ledger_cons, (balanced_iff_disp A).1 (h A List.mem_cons_self), zero_add]
    exact ledger_zero_of_all_balanced T (fun B hB => h B (List.mem_cons_of_mem A hB))

/-- **An imbalance persists**: a region with non-zero ledger keeps an open strand under every
    sequence of local events. -/
theorem imbalance_persists {S T : List (List Twist)} (h : Relation.ReflTransGen Event S T)
    (hS : ledger S ≠ 0) : ∃ A ∈ T, ¬ countBalanced A := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  exact hS ((events_conserve_ledger h).trans (ledger_zero_of_all_balanced T hc))

theorem reading_nonpos (f : Ledger →+ ℤ) :
    ∀ T : List (List Twist), (∀ A ∈ T, f (disp A) ≤ 0) → f (ledger T) ≤ 0
  | [], _ => by simp [ledger]
  | A :: T, h => by
    rw [ledger_cons, map_add]
    have h1 := h A List.mem_cons_self
    have h2 := reading_nonpos f T (fun B hB => h B (List.mem_cons_of_mem A hB))
    omega

/-- **The excess species persists.** For any additive reading `f` of the ledger (for instance the
    `up − down` count), a positive regional excess leaves a surviving strand with a positive reading,
    whatever local events occur. -/
theorem excess_species_persists (f : Ledger →+ ℤ) {S T : List (List Twist)}
    (h : Relation.ReflTransGen Event S T) (hpos : 0 < f (ledger S)) :
    ∃ A ∈ T, 0 < f (disp A) := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  have := reading_nonpos f T hc
  rw [← events_conserve_ledger h] at this
  omega

/-- **Transport is the only flux.** Moving `A` from region `x` to region `y` lowers `x`'s ledger by
    `disp A`, raises `y`'s by the same, and conserves the total. -/
theorem hop_flux (A : List Twist) (Sx Sy : List (List Twist)) :
    ledger Sx = ledger (A :: Sx) - disp A ∧
    ledger (A :: Sy) = ledger Sy + disp A ∧
    ledger (A :: Sx) + ledger Sy = ledger Sx + ledger (A :: Sy) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ledger_cons] <;> abel

end QLF.Morphogenesis
