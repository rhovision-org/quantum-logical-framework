import QLF_LinkAction

/-!
# QLF_LinkClosure — the link action sourced by a history is stationary only if the history closes

Issue #303 §3.2 asks whether the genuine variational equation of
[`QLF_LinkAction`](QLF_LinkAction.lean) — stationarity of the finite link action is the static
Ampère law `curl F = J` — can be tied to ZFA closure by a proved map, without building closure into
the admissible variations. This module gives one such map and proves its forward direction.

**The map.** A history is a list of signed axis steps `(i, ±)`, the twist alphabet's signed axis
frame. Started at a site `p`, it traverses links; its **current** `walkCurrent e p w` counts each
traversal with its sign (`+1` along `e i`, `−1` against). Nothing about the action enters the map.

**The theorems.**

* `sum_walkCurrent` — the total current on axis `k` is the history's net count on that axis,
  `#(k,+) − #(k,−)`.
* `div_walkCurrent` — the divergence of the current is `δ_start − δ_end`.
* `sum_ampere_zero` — `curl F` has zero total on every axis (translation invariance of the sum).
* **`stationary_forces_count_balance`** — if some link configuration makes the action stationary
  under every link variation with this current, then the history is **count-balanced on every
  axis**. Count balance is ZFA's count condition, and with `count_balanced_pauli_closed` it is full
  ZFA closure.
* `stationary_forces_return` — and it returns to its starting site (`div J = 0`).
* `open_history_no_stationary` — the kill condition: a history unbalanced on any axis admits **no**
  stationary configuration at all; the single step is the minimal witness (`single_step_no_stationary`).
* `closed_history_gauge_invariant` — a history that returns makes the coupling gauge invariant
  (Noether, via `gauge_invariant_iff_conserved`).

**Noncircularity.** Closure is a property of the history (a count); stationarity is a property of a
field (the Euler–Lagrange equation of a fixed quadratic action under every single-link variation).
The admissible variations are all link bumps, not those that preserve closure.

**Open.** The converse — every count-balanced history admits a stationary configuration — is the
statement that `J` orthogonal to gradients (`div J = 0`) and to the constant fields (zero net flux)
lies in the range of `curl curl`, a finite Hodge decomposition on the torus. It is checked exactly
for small tori by [`link_closure.py`](../link_closure.py) but not proved here. This is the link
sector at fixed time; it identifies no physical action with the census cost of
[`QLF_CensusActionLimit`](QLF_CensusActionLimit.lean). No axioms.
-/

namespace QLF.LinkClosure

open QLF.LinkAction

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {n : ℕ}

/-- One signed step: an axis and a sign (`true` = along `e i`). -/
abbrev Step (n : ℕ) := Fin n × Bool

/-- Where a history started at `p` ends. -/
def endpoint (e : Fin n → S) : S → List (Step n) → S
  | p, [] => p
  | p, (i, b) :: w => endpoint e (if b then p + e i else p - e i) w

/-- The signed current of one step from `p`: `+1` on link `(i, p)` going up, `−1` on link
    `(i, p − e i)` going down. -/
def stepCurrent (e : Fin n → S) (p : S) (i : Fin n) (b : Bool) : Fin n → S → ℝ :=
  fun k x => if k = i ∧ x = (if b then p else p - e i) then (if b then 1 else -1) else 0

/-- The signed link current of a history started at `p`. -/
def walkCurrent (e : Fin n → S) : S → List (Step n) → Fin n → S → ℝ
  | _, [] => fun _ _ => 0
  | p, (i, b) :: w => fun k x =>
      stepCurrent e p i b k x + walkCurrent e (if b then p + e i else p - e i) w k x

/-- The net count of a history on axis `k`: up-steps minus down-steps. -/
def netCount : List (Step n) → Fin n → ℤ
  | [], _ => 0
  | (i, b) :: w, k => (if i = k then (if b then 1 else -1) else 0) + netCount w k

lemma sum_stepCurrent (e : Fin n → S) (p : S) (i : Fin n) (b : Bool) (k : Fin n) :
    ∑ x, stepCurrent e p i b k x = if i = k then (if b then 1 else -1) else 0 := by
  unfold stepCurrent
  by_cases h : k = i
  · subst h
    simp only [true_and, ite_true]
    rw [Finset.sum_ite_eq' Finset.univ]
    simp
  · have h' : ¬ i = k := fun hh => h hh.symm
    simp [h, h']

/-- **The total current on an axis is the net count on that axis.** -/
theorem sum_walkCurrent (e : Fin n → S) (p : S) (w : List (Step n)) (k : Fin n) :
    ∑ x, walkCurrent e p w k x = (netCount w k : ℝ) := by
  induction w generalizing p with
  | nil => simp [walkCurrent, netCount]
  | cons s w ih =>
    obtain ⟨i, b⟩ := s
    simp only [walkCurrent, netCount, Finset.sum_add_distrib, sum_stepCurrent, ih]
    push_cast
    split_ifs <;> simp

omit [Fintype S] [DecidableEq S] in
lemma div_add (e : Fin n → S) (A B : Fin n → S → ℝ) (x : S) :
    Maxwell.div e (fun k z => A k z + B k z) x = Maxwell.div e A x + Maxwell.div e B x := by
  simp only [Maxwell.div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

omit [Fintype S] in
lemma div_stepCurrent (e : Fin n → S) (p : S) (i : Fin n) (b : Bool) (x : S) :
    Maxwell.div e (stepCurrent e p i b) x =
      (if x = p then 1 else 0) - (if x = (if b then p + e i else p - e i) then 1 else 0) := by
  unfold Maxwell.div stepCurrent
  rw [Finset.sum_sub_distrib]
  have h1 : ∀ y : S, (∑ k : Fin n, if k = i ∧ y = (if b then p else p - e i)
      then (if b then (1 : ℝ) else -1) else 0) =
      if y = (if b then p else p - e i) then (if b then 1 else -1) else 0 := by
    intro y
    have : ∀ k : Fin n, (if k = i ∧ y = (if b then p else p - e i)
        then (if b then (1 : ℝ) else -1) else 0) =
        if k = i then (if y = (if b then p else p - e i) then (if b then 1 else -1) else 0)
        else 0 := by
      intro k; by_cases hk : k = i <;> simp [hk]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h2 : (∑ k : Fin n, if k = i ∧ x - e k = (if b then p else p - e i)
      then (if b then (1 : ℝ) else -1) else 0) =
      if x - e i = (if b then p else p - e i) then (if b then 1 else -1) else 0 := by
    have : ∀ k : Fin n, (if k = i ∧ x - e k = (if b then p else p - e i)
        then (if b then (1 : ℝ) else -1) else 0) =
        if k = i then (if x - e i = (if b then p else p - e i) then (if b then 1 else -1) else 0)
        else 0 := by
      intro k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h1 x, h2]
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    have e1 : (x - e i = p - e i) ↔ (x = p) := sub_left_inj
    by_cases hx : x = p
    · subst hx
      have hne : ¬ (x = x - e i) ∨ e i = 0 := by
        by_cases h0 : e i = 0
        · exact Or.inr h0
        · left; intro h; apply h0; have := congrArg (fun z => x - z) h; simp at this; exact this.symm
      rcases hne with hne | h0
      · simp [hne]
      · simp [h0]
    · simp only [e1, hx, ite_false]
      split_ifs <;> simp
  · simp only [ite_true]
    have e1 : (x - e i = p) ↔ (x = p + e i) := sub_eq_iff_eq_add
    simp only [e1]

omit [Fintype S] in
/-- **The divergence of a history's current is `δ_start − δ_end`.** -/
theorem div_walkCurrent (e : Fin n → S) (p : S) (w : List (Step n)) (x : S) :
    Maxwell.div e (walkCurrent e p w) x =
      (if x = p then 1 else 0) - (if x = endpoint e p w then 1 else 0) := by
  induction w generalizing p with
  | nil =>
    rw [show endpoint e p [] = p from rfl, sub_self]
    simp [walkCurrent, Maxwell.div]
  | cons s w ih =>
    obtain ⟨i, b⟩ := s
    have : walkCurrent e p ((i, b) :: w) = fun k z =>
        stepCurrent e p i b k z + walkCurrent e (if b then p + e i else p - e i) w k z := rfl
    rw [this, div_add, div_stepCurrent, ih, sub_add_sub_cancel]
    rfl

omit [DecidableEq S] in
/-- **`curl F` has zero total on every axis.** -/
theorem sum_ampere_zero (e : Fin n → S) (a : Fin n → S → ℝ) (k : Fin n) :
    ∑ y, ampere e a k y = 0 := by
  unfold ampere
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact (Fintype.sum_equiv (Equiv.subRight (e j)) _ _ (fun y => rfl)).symm

/-- Stationarity of the link action with the history's current, as `QLF_LinkAction` states it. -/
def Stationary (e : Fin n → S) (p : S) (w : List (Step n)) (a : Fin n → S → ℝ) : Prop :=
  ∀ k y, action e (walkCurrent e p w) (fun l z => a l z + bump k y l z) =
    action e (walkCurrent e p w) (fun l z => a l z + (-1) * bump k y l z)

/-- **Stationarity forces count balance.** If any link configuration makes the action stationary
    under every single-link variation, the history sourcing it is count-balanced on every axis. -/
theorem stationary_forces_count_balance (e : Fin n → S) (p : S) (w : List (Step n))
    (a : Fin n → S → ℝ) (h : Stationary e p w a) (k : Fin n) : netCount w k = 0 := by
  have hA := (stationary_iff_ampere e _ a).1 h
  have hsum : (netCount w k : ℝ) = 0 := by
    rw [← sum_walkCurrent e p w k, ← sum_ampere_zero e a k]
    exact Finset.sum_congr rfl (fun y _ => (hA k y).symm)
  exact_mod_cast hsum

/-- **Stationarity forces return:** the history ends where it started. -/
theorem stationary_forces_return (e : Fin n → S) (p : S) (w : List (Step n))
    (a : Fin n → S → ℝ) (h : Stationary e p w a) : endpoint e p w = p := by
  have hA := (stationary_iff_ampere e _ a).1 h
  have hd := stationary_conserves_current e _ a hA p
  rw [div_walkCurrent] at hd
  by_contra hne
  have : ¬ p = endpoint e p w := fun hh => hne hh.symm
  simp [this] at hd

/-- **The kill condition.** A history unbalanced on some axis admits no stationary configuration. -/
theorem open_history_no_stationary (e : Fin n → S) (p : S) (w : List (Step n)) (k : Fin n)
    (hk : netCount w k ≠ 0) : ¬ ∃ a, Stationary e p w a := by
  rintro ⟨a, ha⟩
  exact hk (stationary_forces_count_balance e p w a ha k)

/-- The minimal witness: one step has no stationary configuration. -/
theorem single_step_no_stationary (e : Fin n → S) (p : S) (k : Fin n) (b : Bool) :
    ¬ ∃ a, Stationary e p [(k, b)] a := by
  apply open_history_no_stationary e p _ k
  cases b <;> simp [netCount]

/-- **A history that returns makes the coupling gauge invariant** (Noether). -/
theorem closed_history_gauge_invariant (e : Fin n → S) (p : S) (w : List (Step n))
    (hw : endpoint e p w = p) (a : Fin n → S → ℝ) (θ : S → ℝ) :
    action e (walkCurrent e p w) (gaugeShift e θ a) = action e (walkCurrent e p w) a := by
  refine (gauge_invariant_iff_conserved e _ a).2 (fun x => ?_) θ
  rw [div_walkCurrent, hw, sub_self]

/-- **Summary.** Stationarity of the link action sourced by a history forces the history to be
    count-balanced and to return; an unbalanced history has no stationary configuration. -/
theorem link_stationarity_forces_closure (e : Fin n → S) (p : S) (w : List (Step n)) :
    (∀ a, Stationary e p w a → (∀ k, netCount w k = 0) ∧ endpoint e p w = p) ∧
    (∀ k, netCount w k ≠ 0 → ¬ ∃ a, Stationary e p w a) :=
  ⟨fun a h => ⟨stationary_forces_count_balance e p w a h, stationary_forces_return e p w a h⟩,
    fun k hk => open_history_no_stationary e p w k hk⟩

end QLF.LinkClosure
