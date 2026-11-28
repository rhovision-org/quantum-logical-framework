import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sets
import QLF_ProductWalk
import QLF_PvsNP

/-!
# QLF_PossibilityGrowth — possibilities grow exponentially, and blind search pays for it

Two things are proved here, and one thing is deliberately not.

**1. Growth.** Over the eight-twist alphabet there are `8^L` histories of length `L`
(`possibilities_card`), and the closures among them (the count-balanced histories, which are
Pauli-closed by `count_balanced_pauli_closed`) number `walkCount L` (`closures_card`, via the
bridge `card_balanced_twist`). The closures alone grow exponentially:
`16^n ≤ (2n+1)² · #closures(2n)` (`closures_exponential`). The one-axis realized set of
`QLF_PvsNP` grows the same way: `4^n ≤ (2n+1) · C(2n,n)` (`realized_exponential`).

**2. Blind search pays for every possibility.** A *decision tree* over a finite candidate set
queries "does candidate `a` have property `X`?" one candidate at a time and branches on the
answer. Any tree that correctly answers "does some candidate have property `X`?" for **every**
property `X` must, on the instance where no candidate has it, query every candidate
(`search_must_query_all`). A tree with a smaller budget is necessarily approximate: if it says
"no" when nothing has the property, then among the single-witness instances it detects at most
as many as it queries (`bounded_search_detects_few`) and misses the rest
(`bounded_search_misses`). Instantiated on the closures, any exact blind search for a closure
with an arbitrary property needs at least `16^n/(2n+1)²` queries at length `2n`
(`closure_search_lower_bound`).

**What this is not.** It is a *black-box* (query, relativized) lower bound: the property `X` is
seen only through queries. Baker–Gill–Solovay (1975) showed that results of this kind cannot
settle P vs NP, because there are oracles relative to which P = NP. A polynomial algorithm for a
concrete property reads its structure rather than querying it blindly. And the count itself does
not make anything hard: `walkCount L` is a sum of `L + 1` closed-form terms, so *counting*
closures is easy even though *finding one with an arbitrary property* is not. So this module
formalizes "possibilities grow exponentially, so blind search over them can only be exact at
exponential cost, and is otherwise approximate". It does not touch `qlf_cost_model`, and it adds
no axiom.

See `Possibility_Growth.md` and `P_vs_NP_QLF.md`.
-/

namespace QLF.PossibilityGrowth

open Finset QLF QLF.PolyaTransience QLF.ProductWalk

/-! ## 1. Growth -/

/-- **The possibility space at length `L` is `8^L`.** -/
theorem possibilities_card (L : ℕ) : (words Twist L).card = 8 ^ L := by
  rw [card_words, card_twist]

/-- The closures at length `L`: the count-balanced twist histories. By
    `count_balanced_pauli_closed` each is also Pauli-closed, so these are the full ZFA closures. -/
def closureSet (L : ℕ) : Finset (List Twist) :=
  (words Twist L).filter (fun ts => decide (countBalanced ts))

/-- **The closures are counted by `walkCount`** (the bridge `card_balanced_twist`). -/
theorem closures_card (L : ℕ) : (closureSet L).card = walkCount L :=
  card_balanced_twist L

/-- The `k = 0` term of `walkCount (2n)` alone is `C(2n,n)²`: all the steps on one plane. -/
theorem centralBinom_sq_le_walkCount (n : ℕ) :
    (Nat.centralBinom n) ^ 2 ≤ walkCount (2 * n) := by
  have h : (2 * n).choose 0 * w₂ 0 * w₂ (2 * n - 0) ≤ walkCount (2 * n) := by
    unfold walkCount
    exact Finset.single_le_sum (f := fun k => (2 * n).choose k * w₂ k * w₂ (2 * n - k))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have h0 : w₂ 0 = 1 := by unfold w₂; simp
  have h2 : w₂ (2 * n) = (Nat.centralBinom n) ^ 2 := by
    have he : (2 * n) % 2 = 0 := by omega
    unfold w₂
    simp only [he, ↓reduceIte, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]
  rw [Nat.sub_zero, Nat.choose_zero_right, h0, h2] at h
  simpa using h

/-- **The closures grow exponentially: `16^n ≤ (2n+1)² · #closures(2n)`.** Closure is a
    vanishing fraction of the `64^n` possibilities, but in absolute terms it is still an
    exponential set. The bound is deliberately weak: it keeps only the one-plane term
    `C(2n,n)²` of `walkCount (2n)`, so the base `16` and the factor `(2n+1)²` are artifacts of
    that choice. Numerically `walkCount (2n) ≈ (2/π²)·64^n/n²` (`Closure_Walk.md`, not proved
    here); any exponential lower bound suffices for the query bound below. -/
theorem closures_exponential (n : ℕ) :
    16 ^ n ≤ (2 * n + 1) ^ 2 * (closureSet (2 * n)).card := by
  rw [closures_card]
  have hc := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have hsq : (4 ^ n) ^ 2 ≤ ((2 * n + 1) * Nat.centralBinom n) ^ 2 := Nat.pow_le_pow_left hc 2
  calc 16 ^ n = (4 ^ n) ^ 2 := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
    _ ≤ ((2 * n + 1) * Nat.centralBinom n) ^ 2 := hsq
    _ = (2 * n + 1) ^ 2 * (Nat.centralBinom n) ^ 2 := by ring
    _ ≤ (2 * n + 1) ^ 2 * walkCount (2 * n) :=
        Nat.mul_le_mul_left _ (centralBinom_sq_le_walkCount n)

/-- **The one-axis realized set grows exponentially: `4^n ≤ (2n+1) · |realizedSet n|`.** -/
theorem realized_exponential (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * (realizedSet n).length := by
  rw [realized_count_eq_central_binomial, ← Nat.centralBinom_eq_two_mul_choose]
  exact Nat.four_pow_le_two_mul_add_one_mul_central_binom n

/-! ## 2. Blind search: decision trees over a finite candidate set -/

/-- A deterministic query procedure: at a `query a yes no` node it asks whether candidate `a`
    has the property and continues with `yes` or `no`; a `leaf` gives the answer. Every
    deterministic algorithm that sees the property only through such queries is one of these. -/
inductive DTree (α : Type) where
  | leaf (b : Bool)
  | query (a : α) (yes no : DTree α)

namespace DTree

variable {α : Type}

/-- The answer the tree gives on property `f`. -/
def eval : DTree α → (α → Bool) → Bool
  | leaf b, _ => b
  | query a yes no, f => if f a then yes.eval f else no.eval f

/-- The candidates the tree actually queries on property `f`, in order. Its length is the
    number of queries the run costs. -/
def path : DTree α → (α → Bool) → List α
  | leaf _, _ => []
  | query a yes no, f => a :: (if f a then yes.path f else no.path f)

/-- **A run sees only what it queries.** Two properties that agree on every candidate the run
    queries give the same answer and the same run. -/
theorem agree (T : DTree α) (f g : α → Bool) (h : ∀ a ∈ T.path f, f a = g a) :
    T.eval f = T.eval g ∧ T.path f = T.path g := by
  induction T with
  | leaf b => simp [eval, path]
  | query a yes no ihy ihn =>
    have ha : f a = g a := h a (by simp [path])
    cases hfa : f a with
    | true =>
      have hga : g a = true := by rw [← ha]; exact hfa
      have hrest : ∀ x ∈ yes.path f, f x = g x := fun x hx => h x (by simp [path, hfa, hx])
      obtain ⟨h1, h2⟩ := ihy hrest
      simp [eval, path, hfa, hga, h1, h2]
    | false =>
      have hga : g a = false := by rw [← ha]; exact hfa
      have hrest : ∀ x ∈ no.path f, f x = g x := fun x hx => h x (by simp [path, hfa, hx])
      obtain ⟨h1, h2⟩ := ihn hrest
      simp [eval, path, hfa, hga, h1, h2]

/-- **An unqueried candidate is invisible.** If the run on the empty property never queries
    `a`, the tree cannot tell the empty property from "only `a` has it". -/
theorem unqueried_invisible [DecidableEq α] (T : DTree α) (a : α)
    (ha : a ∉ T.path (fun _ => false)) :
    T.eval (fun x => decide (x = a)) = T.eval (fun _ => false) := by
  have hag : ∀ x ∈ T.path (fun _ => false), (fun _ => false) x = decide (x = a) := by
    intro x hx
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    simp [hxa]
  exact (agree T (fun _ => false) (fun x => decide (x = a)) hag).1.symm

/-- **Exact blind search queries every candidate.** A tree that answers "does some candidate
    have the property?" correctly for every property must, on the empty property, query all
    `card α` candidates. -/
theorem search_must_query_all [Fintype α] [DecidableEq α] (T : DTree α)
    (hT : ∀ f : α → Bool, T.eval f = decide (∃ a, f a = true)) :
    Fintype.card α ≤ (T.path (fun _ => false)).length := by
  have hall : ∀ a, a ∈ T.path (fun _ => false) := by
    intro a
    by_contra ha
    have h1 := unqueried_invisible T a ha
    rw [hT, hT] at h1
    simp at h1
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
    _ ≤ (T.path (fun _ => false)).toFinset.card :=
        Finset.card_le_card (fun a _ => List.mem_toFinset.mpr (hall a))
    _ ≤ (T.path (fun _ => false)).length := List.toFinset_card_le _

/-- **Bounded blind search is approximate.** A tree that correctly says "no" on the empty
    property detects at most as many single-witness instances as it makes queries there. -/
theorem bounded_search_detects_few [Fintype α] [DecidableEq α] (T : DTree α)
    (hnone : T.eval (fun _ => false) = false) :
    (Finset.univ.filter (fun a => T.eval (fun x => decide (x = a)) = true)).card
      ≤ (T.path (fun _ => false)).length := by
  calc (Finset.univ.filter (fun a => T.eval (fun x => decide (x = a)) = true)).card
      ≤ (T.path (fun _ => false)).toFinset.card := by
        apply Finset.card_le_card
        intro a ha
        rw [Finset.mem_filter] at ha
        rw [List.mem_toFinset]
        by_contra hna
        have h := unqueried_invisible T a hna
        rw [h, hnone] at ha
        exact Bool.false_ne_true ha.2
    _ ≤ (T.path (fun _ => false)).length := List.toFinset_card_le _

/-- **And it misses the rest.** With a budget of `k` queries on the empty property, a tree that
    says "no" there answers wrongly on at least `card α − k` of the single-witness instances. -/
theorem bounded_search_misses [Fintype α] [DecidableEq α] (T : DTree α) (k : ℕ)
    (hnone : T.eval (fun _ => false) = false)
    (hk : (T.path (fun _ => false)).length ≤ k) :
    Fintype.card α - k ≤
      (Finset.univ.filter (fun a => ¬ T.eval (fun x => decide (x = a)) = true)).card := by
  have h1 := bounded_search_detects_few T hnone
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α)) (fun a => T.eval (fun x => decide (x = a)) = true)
  rw [Finset.card_univ] at h2
  omega

end DTree

/-! ## 3. Blind search over the closures -/

/-- **Exact blind search for a closure with an arbitrary property costs `16^n/(2n+1)²`
    queries.** Any decision tree over the length-`2n` closures that decides, for every property,
    whether some closure has it, makes at least that many queries on the empty property. -/
theorem closure_search_lower_bound (n : ℕ) (T : DTree {ts // ts ∈ closureSet (2 * n)})
    (hT : ∀ f : {ts // ts ∈ closureSet (2 * n)} → Bool, T.eval f = decide (∃ a, f a = true)) :
    16 ^ n ≤ (2 * n + 1) ^ 2 * (T.path (fun _ => false)).length := by
  have h := DTree.search_must_query_all T hT
  rw [Fintype.card_coe] at h
  calc 16 ^ n ≤ (2 * n + 1) ^ 2 * (closureSet (2 * n)).card := closures_exponential n
    _ ≤ (2 * n + 1) ^ 2 * (T.path (fun _ => false)).length := Nat.mul_le_mul_left _ h

/-- **And a polynomial budget is approximate.** A tree over the length-`2n` closures that says
    "no" on the empty property and makes at most `k` queries there detects at most `k` of the
    `walkCount (2n)` single-witness instances. -/
theorem closure_search_detects_few (n : ℕ) (T : DTree {ts // ts ∈ closureSet (2 * n)})
    (hnone : T.eval (fun _ => false) = false) (k : ℕ)
    (hk : (T.path (fun _ => false)).length ≤ k) :
    ((Finset.univ : Finset {ts // ts ∈ closureSet (2 * n)}).filter
      (fun a => T.eval (fun x => decide (x = a)) = true)).card ≤ k :=
  (DTree.bounded_search_detects_few T hnone).trans hk

end QLF.PossibilityGrowth
