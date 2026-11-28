/-
# QLF_CooperativeClosure

The first gates of the cooperative-closure program (`Cooperative_Intelligence.md`): what can be
proved about cooperative synthesis *before* any semantic bridge to ZFA is assumed.

* **CC0 — the consensus fallacy.**  Agreement among any number of participants, all internally
  consistent, can be false (`consensus_fallacy`).  When no report originates in an observation,
  consensus is the *same* in every world (`unobserved_consensus_world_free`), so it carries no
  information about the world at all.  One observation in the record is what makes accepted
  consensus sound (`observed_consensus_sound`).
* **CC3 — provenance conservation.**  Provenance is the set of originating sources.  Repetition,
  duplication, replay and copying leave it unchanged (`origins_replicate`, `duplicate_suppression`,
  `replay_invariance`, `compose_same_origin`), and so leave independent observational support
  unchanged (`support_replicate_le`, `copy_adds_no_support`).  Separate provenance is not
  statistical independence (`separate_not_independent`).
* **CC2/CC6 — irreducible synthesis.**  A coalition *resolves* a question when what its members
  hold determines the answer.  For parity, a coalition resolves the question **iff** it holds every
  variable (`parity_resolves_iff`); every smaller coalition, whatever it sees, leaves both answers
  open (`parity_coalition_blind`).  So parity is an irreducible synthesis (`parity_irreducible`),
  with XOR as the two-party case (`xor_synthesis`); a dictator question is the ordinary contrast
  (`dictator_not_irreducible`).  Resolution depends only on the set of variables held, never on how
  many members hold them (`coalitionResolves_iff`), so an echo chamber resolves nothing a single
  member could not (`echo_chamber_blind`).  Limits: irrelevant members add nothing
  (`irrelevant_member`), and a variable nobody holds blocks every coalition (`missing_variable`).
* **Substrate witness.**  On the twist alphabet, `n` parties holding `^` and one holding `v^n` close
  jointly (`star_closes`), and no nonempty proper sub-coalition closes (`star_irreducible`).  The
  `n = 1` case is the primordial `^ | v`, the `StrongCoIncides` witness of `Coincidence_QLF.md`.

What this module does **not** do: it does not connect semantic resolution to ZFA closure.  The two
irreducibility results (information-theoretic and substrate) are separate theorems; the encoding
that would make one the other is the open bridge CC4.

No axioms.  Part of [Quantum Logical Framework (QLF)](../README.md).
-/

import Mathlib
import QLF_TwistAlphabet

namespace QLF.CooperativeClosure

open QLF

/-! ## CC0 — the consensus fallacy -/

/-- An originating source.  An observation reads the world; an assertion states a fixed claim
whatever the world is.  Each carries an identity, so two sources can be told apart. -/
inductive Source
  | observe (id : ℕ)
  | assert (id : ℕ) (claim : Bool)
  deriving DecidableEq

/-- What a source reports in world `w` (the truth value of the proposition `p := w`). -/
def Source.reading (w : Bool) : Source → Bool
  | .observe _ => w
  | .assert _ c => c

/-- Whether a source is an observation. -/
def Source.isObs : Source → Bool
  | .observe _ => true
  | .assert _ _ => false

/-- Every participant in the record accepts `p`.  A record lists, per participant, the source
that participant relays. -/
def Consensus (w : Bool) (r : List Source) : Prop := ∀ s ∈ r, s.reading w = true

/-- The record is internally consistent: no two participants disagree. -/
def Consistent (w : Bool) (r : List Source) : Prop :=
  ∀ s ∈ r, ∀ t ∈ r, s.reading w = t.reading w

/-- **CC0.**  For every number of participants there is a record in which all accept `p`, the
record is consistent, all reports share one origin, and `p` is false. -/
theorem consensus_fallacy (n : ℕ) :
    ∃ r : List Source, r.length = n ∧ Consensus false r ∧ Consistent false r ∧
      r.toFinset.card ≤ 1 := by
  refine ⟨List.replicate n (.assert 0 true), by simp, ?_, ?_, ?_⟩
  · intro s hs
    rw [List.eq_of_mem_replicate hs]; rfl
  · intro s hs t ht
    rw [List.eq_of_mem_replicate hs, List.eq_of_mem_replicate ht]
  · rcases n with _ | n
    · simp
    · simp [List.toFinset_replicate_of_ne_zero]

/-- With no observation in the record, consensus is the same in both worlds: it carries no
information about which world holds. -/
theorem unobserved_consensus_world_free (r : List Source)
    (h : ∀ s ∈ r, s.isObs = false) : Consensus true r ↔ Consensus false r := by
  unfold Consensus
  constructor <;> intro hc s hs <;> have := hc s hs <;> have ho := h s hs <;>
    cases s <;> simp_all [Source.reading, Source.isObs]

/-- One observation in an accepting record makes the consensus true. -/
theorem observed_consensus_sound (w : Bool) (r : List Source)
    (hobs : ∃ s ∈ r, s.isObs = true) (hc : Consensus w r) : w = true := by
  obtain ⟨s, hs, ho⟩ := hobs
  have := hc s hs
  cases s <;> simp_all [Source.reading, Source.isObs]

/-! ## CC3 — provenance conservation -/

/-- Independent observational support: the number of distinct observation sources. -/
def support (r : List Source) : ℕ := (r.toFinset.filter (fun s => s.isObs = true)).card

/-- A thousand repeats of one source have exactly one origin. -/
theorem origins_replicate {n : ℕ} (hn : n ≠ 0) (s : Source) :
    (List.replicate n s).toFinset = {s} :=
  List.toFinset_replicate_of_ne_zero hn

/-- Repetition never raises support above one. -/
theorem support_replicate_le (n : ℕ) (s : Source) : support (List.replicate n s) ≤ 1 := by
  unfold support
  rcases n with _ | n
  · simp
  · rw [List.toFinset_replicate_of_ne_zero (Nat.succ_ne_zero n)]
    exact (Finset.card_filter_le _ _).trans (by simp)

/-- Duplicate suppression: re-transmitting a source already present changes no origin. -/
theorem duplicate_suppression {s : Source} {r : List Source} (h : s ∈ r) :
    (s :: r).toFinset = r.toFinset := by
  rw [List.toFinset_cons]
  exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)

/-- Replay invariance: reordering the record changes no origin. -/
theorem replay_invariance {r r' : List Source} (h : r.Perm r') : r.toFinset = r'.toFinset :=
  List.toFinset_eq_of_perm _ _ h

/-- Composition carries the union of origins (traceability of derived claims). -/
theorem origins_append (a b : List Source) : (a ++ b).toFinset = a.toFinset ∪ b.toFinset :=
  List.toFinset_append

/-- Composing two contributions of the same origin set yields that origin set. -/
theorem compose_same_origin {a b : List Source} (h : a.toFinset = b.toFinset) :
    (a ++ b).toFinset = a.toFinset := by
  rw [List.toFinset_append, h, Finset.union_self]

/-- Support is subadditive under composition. -/
theorem support_append_le (a b : List Source) : support (a ++ b) ≤ support a + support b := by
  unfold support
  rw [List.toFinset_append, Finset.filter_union]
  exact Finset.card_union_le _ _

/-- Copying sources already held adds no independent support. -/
theorem copy_adds_no_support {a b : List Source} (h : ∀ s ∈ b, s ∈ a) :
    support (a ++ b) = support a := by
  unfold support
  congr 2
  rw [List.toFinset_append]
  apply Finset.union_eq_left.mpr
  intro s hs
  exact List.mem_toFinset.mpr (h s (List.mem_toFinset.mp hs))

/-- Separate provenance is not statistical independence: two distinct observations of one
proposition agree in every world. -/
theorem separate_not_independent :
    Source.observe 0 ≠ Source.observe 1 ∧
      ∀ w, (Source.observe 0).reading w = (Source.observe 1).reading w :=
  ⟨by decide, fun _ => rfl⟩

/-! ## CC2/CC6 — irreducible synthesis -/

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set `S` of variables resolves the question `Q` when agreement on `S` forces agreement on
the answer: the values in `S` determine `Q`. -/
def Resolves (S : Finset V) (Q : (V → ZMod 2) → ZMod 2) : Prop :=
  ∀ x y : V → ZMod 2, (∀ v ∈ S, x v = y v) → Q x = Q y

/-- The parity of all variables (XOR for two). -/
def parity (x : V → ZMod 2) : ZMod 2 := ∑ v, x v

/-- Flipping one variable flips the parity. -/
theorem parity_flip (x : V → ZMod 2) (v : V) :
    parity (Function.update x v (x v + 1)) = parity x + 1 := by
  unfold parity
  rw [Finset.sum_update_of_mem (Finset.mem_univ v),
    Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase Finset.univ x (Finset.mem_univ v)]
  ring

/-- Resolution is monotone: holding more variables never loses a resolution. -/
theorem resolves_mono {S T : Finset V} {Q : (V → ZMod 2) → ZMod 2} (hST : S ⊆ T)
    (h : Resolves S Q) : Resolves T Q :=
  fun x y hxy => h x y (fun v hv => hxy v (hST hv))

private theorem zmod2_ne (a b : ZMod 2) (h : a ≠ b) : b = a + 1 := by
  revert a b; decide

/-- **Blindness of every proper coalition.**  A set missing any variable, whatever values it
sees, is compatible with both parities. -/
theorem parity_coalition_blind {S : Finset V} (hS : S ≠ Finset.univ) (x : V → ZMod 2)
    (c : ZMod 2) : ∃ y : V → ZMod 2, (∀ v ∈ S, y v = x v) ∧ parity y = c := by
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra h
    push_neg at h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  by_cases hc : parity x = c
  · exact ⟨x, fun _ _ => rfl, hc⟩
  · refine ⟨Function.update x v (x v + 1), ?_, ?_⟩
    · intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      exact Function.update_of_ne hwv _ _
    · rw [parity_flip, zmod2_ne _ _ hc]

/-- **Parity is resolved exactly by the whole collective.** -/
theorem parity_resolves_iff (S : Finset V) : Resolves S parity ↔ S = Finset.univ := by
  constructor
  · intro h
    by_contra hS
    obtain ⟨y, hy, hpy⟩ := parity_coalition_blind hS (0 : V → ZMod 2) (parity (0 : V → ZMod 2) + 1)
    have := h y 0 hy
    rw [hpy] at this
    have h10 : (1 : ZMod 2) = 0 := by linear_combination this
    exact absurd h10 (by decide)
  · rintro rfl x y hxy
    have : x = y := funext fun v => hxy v (Finset.mem_univ v)
    rw [this]

/-- Irreducible synthesis: `S` resolves `Q` and no proper subset does. -/
def Irreducible (S : Finset V) (Q : (V → ZMod 2) → ZMod 2) : Prop :=
  Resolves S Q ∧ ∀ T, T ⊂ S → ¬ Resolves T Q

/-- **CC2/CC6, `n` participants.**  Parity of all variables is an irreducible synthesis. -/
theorem parity_irreducible : Irreducible (Finset.univ : Finset V) parity := by
  refine ⟨(parity_resolves_iff _).mpr rfl, fun T hT hres => ?_⟩
  exact hT.ne ((parity_resolves_iff T).mp hres)

/-- **CC2, two participants (XOR).**  Together the two bits determine `x ⊕ y`; neither alone does. -/
theorem xor_synthesis :
    Resolves (Finset.univ : Finset (Fin 2)) parity ∧
      ¬ Resolves ({0} : Finset (Fin 2)) parity ∧ ¬ Resolves ({1} : Finset (Fin 2)) parity := by
  refine ⟨(parity_resolves_iff _).mpr rfl, ?_, ?_⟩ <;> rw [parity_resolves_iff] <;> decide

/-- The ordinary contrast: a question one variable decides is resolved by the whole collective
but is not an irreducible synthesis of it. -/
theorem dictator_not_irreducible (v₀ v₁ : V) (hne : v₀ ≠ v₁) :
    Resolves (Finset.univ : Finset V) (fun x => x v₀) ∧
      ¬ Irreducible (Finset.univ : Finset V) (fun x => x v₀) := by
  have hres : Resolves ({v₀} : Finset V) (fun x => x v₀) :=
    fun x y h => h v₀ (Finset.mem_singleton_self v₀)
  refine ⟨resolves_mono (Finset.subset_univ _) hres, fun ⟨_, hirr⟩ => hirr {v₀} ?_ hres⟩
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun h => ?_⟩
  have : v₁ ∈ ({v₀} : Finset V) := h ▸ Finset.mem_univ v₁
  exact hne (Finset.mem_singleton.mp this).symm

/-- **Limit: irrelevant diversity.**  A member whose variable the question ignores adds nothing. -/
theorem irrelevant_member {S : Finset V} {Q : (V → ZMod 2) → ZMod 2} (j : V)
    (hj : ∀ x b, Q (Function.update x j b) = Q x) (h : Resolves (insert j S) Q) :
    Resolves S Q := by
  intro x y hxy
  have h1 := h x (Function.update y j (x j)) (by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · by_cases hvj : v = j
      · subst hvj; simp
      · rw [Function.update_of_ne hvj]; exact hxy v hv)
  rw [h1, hj]

/-! ### Participants, holders and echo chambers -/

/-- A coalition `S` of participants, each holding one variable, resolves `Q` when what its
members hold determines the answer. -/
def CoalitionResolves {P : Type*} (holder : P → V) (S : Finset P)
    (Q : (V → ZMod 2) → ZMod 2) : Prop :=
  ∀ x y : V → ZMod 2, (∀ i ∈ S, x (holder i) = y (holder i)) → Q x = Q y

/-- **Resolution depends only on which variables are held, never on how many members hold
them.** -/
theorem coalitionResolves_iff {P : Type*} [DecidableEq P] (holder : P → V) (S : Finset P)
    (Q : (V → ZMod 2) → ZMod 2) :
    CoalitionResolves holder S Q ↔ Resolves (S.image holder) Q := by
  constructor
  · intro h x y hxy
    exact h x y (fun i hi => hxy _ (Finset.mem_image_of_mem _ hi))
  · intro h x y hxy
    apply h x y
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact hxy i hi

/-- A coalition resolves parity iff its members together hold every variable. -/
theorem coalition_parity_iff {P : Type*} [DecidableEq P] (holder : P → V) (S : Finset P) :
    CoalitionResolves holder S parity ↔ S.image holder = Finset.univ := by
  rw [coalitionResolves_iff, parity_resolves_iff]

/-- **Echo chamber.**  However many members there are, if they all hold the same variable and
another exists, the coalition does not resolve parity. -/
theorem echo_chamber_blind {P : Type*} [DecidableEq P] (holder : P → V) (S : Finset P) (v₀ : V)
    (hecho : ∀ i ∈ S, holder i = v₀) (hother : ∃ v, v ≠ v₀) :
    ¬ CoalitionResolves holder S parity := by
  rw [coalition_parity_iff]
  intro h
  obtain ⟨v, hv⟩ := hother
  have : v ∈ S.image holder := h ▸ Finset.mem_univ v
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp this
  exact hv (hecho i hi)

/-- **Limit: a missing observation.**  If no participant holds `v`, no coalition resolves
parity. -/
theorem missing_variable {P : Type*} [DecidableEq P] (holder : P → V) (v : V)
    (hv : ∀ i, holder i ≠ v) (S : Finset P) : ¬ CoalitionResolves holder S parity := by
  rw [coalition_parity_iff]
  intro h
  have : v ∈ S.image holder := h ▸ Finset.mem_univ v
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this
  exact hv i hi

/-! ## Substrate witness: an irreducible joint closure of `n + 1` parties -/

/-- `n` parties contribute `^`; one party contributes `v^n`. -/
def starParties (n : ℕ) : List (List Twist) :=
  List.replicate n [Twist.up] ++ [List.replicate n Twist.down]

private theorem cnt (n : ℕ) (s t : Twist) :
    (List.replicate n s).count t = if s = t then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    cases s <;> cases t <;> simp (config := { decide := true })

/-- All `n + 1` parties together close. -/
theorem star_closes (n : ℕ) : countBalanced (starParties n).flatten := by
  unfold starParties countBalanced
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.flatten_replicate_singleton, List.count_append, cnt]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true })

/-- **No nonempty proper sub-coalition closes.**  Any order-preserving selection of the parties
that closes is either nobody or everybody. -/
theorem star_irreducible {n : ℕ} (C : List (List Twist))
    (hC : C.Sublist (starParties n)) (hb : countBalanced C.flatten) :
    C = [] ∨ C = starParties n := by
  unfold starParties at hC
  obtain ⟨C₁, C₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hC
  obtain ⟨k, rfl, hk⟩ : ∃ k, C₁ = List.replicate k [Twist.up] ∧ k ≤ n := by
    rw [List.sublist_replicate_iff] at h₁
    obtain ⟨k, hk, rfl⟩ := h₁
    exact ⟨k, rfl, hk⟩
  have hup := hb.1
  rcases List.sublist_singleton.mp h₂ with rfl | rfl
  · simp only [List.append_nil, List.flatten_replicate_singleton, cnt] at hup
    simp (config := { decide := true }) at hup
    subst hup
    left; simp
  · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.flatten_replicate_singleton, List.count_append, cnt] at hup
    simp (config := { decide := true }) at hup
    right
    unfold starParties
    rw [show k = n by omega]

/-- The two-party case is the primordial `^ | v`: each side open, the pair closed. -/
theorem star_one_is_primordial :
    starParties 1 = [[Twist.up], [Twist.down]] ∧
      ¬ countBalanced [Twist.up] ∧ ¬ countBalanced [Twist.down] ∧
      countBalanced (starParties 1).flatten := by
  refine ⟨rfl, ?_, ?_, star_closes 1⟩ <;> (unfold countBalanced; decide)

end QLF.CooperativeClosure
