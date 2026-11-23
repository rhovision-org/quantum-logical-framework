import QLF_TwistAlphabet
import QLF_ReachableEvent
import QLF_Minkowski

/-!
# QLF_LocalityDefinitions — what "local" means, and which meanings imply which

Gates L0 and L1 of issue #315. Part of the [Quantum Logical Framework (QLF)](../README.md);
the write-up is [`Locality.md`](../Locality.md).

The repository uses "local" in several inequivalent senses. This module puts them side by side
on one model and records, for each implication between them, a proof or a counterexample.

## The vocabulary

* **Shared closure** — `SharedClosure a b := countBalanced (a ++ b)`: the two words close
  together (the twist form of `ER_EPR_QLF.SharedClosure`).
* **Prefix reachability** — `reachable a b := a <+: b` (`QLF_ReachableEvent`), the substrate
  causal order. `PrefixSpacelike` is incomparability in it, the predicate `ER_EPR_QLF` calls
  `Spacelike`.
* **Tick displacement** — `tick h = (|h|, x, y, z)`. Time is the number of steps, which is the
  repository's own reading of time as an event count (`QLF_CausalInterval.intervalVolume`, the
  Kitada local clock, and the time axis of `QLF_LightCone`). Space is the net spatial
  displacement on the three Pauli axes (`right − left`, `up − down`, `slash − backslash`).
  Gauge twists take a tick and move nowhere. That the tick reading is the operational spacetime
  separation is the **L2 bridge** and is not proved here. Every statement below is about the
  reading, not about nature.
* **Interval** — `interval v = t² − x² − y² − z²`, which equals `Form.interval`
  (`tickForm_interval`) and hence the determinant of the Hermitian state
  (`det_toMatrix_eq_interval`).

## Results

* **`tick_causal`** (P1): every history's tick displacement lies in the closed future cone:
  `Δt ≥ 0` and interval `≥ 0`. One step per tick is a speed limit of one axis unit per tick.
* **`closure_timelike`** (P2): a nonempty ZFA closure is **strictly timelike**. Count balance
  makes the spatial displacement zero while the clock has advanced. A closure is a rest mass,
  as in `QLF_Inertia`.
* **`straight_run_null`** (P3, Test A): a nonempty straight spatial run is null, with
  `Δt > 0` and nonzero spatial displacement. Null is not zero distance or zero time.
* **`null_not_closed`**: a nonempty null history never closes. So under the tick reading,
  "radiative ∧ ZFA ⇒ null" (the draft Gate 2 target) has **no nonempty instance**. Light is
  the open part of a history, and closure is what makes a history massive.
* **`pair_shared_closure`, `pair_endpoints_spacelike`, `no_history_connects`** (P4, Test C):
  halves born at one event, `a` walking `ts` and `b` walking `ts.map conj`, always close
  together. Their endpoints are separated by `(0, 2x)`, which is spacelike whenever `x ≠ 0`, and
  no history has that displacement. So a shared closure can join events that no history joins.
* **`reachable_causal`** (P5): prefix reachability implies the tick separation is causal.
  **`causal_not_reachable`**: the converse fails. **`prefixSpacelike_not_spacelike`**: the
  primordial pair `[plus]`, `[minus]` is prefix-incomparable, yet its tick endpoints coincide.
  So `ER_EPR_QLF.Spacelike` is an order relation and does not mean Minkowski-spacelike.
* **`zero_displacement_degenerate`**: the signed reading, in which the gauge axis is a signed
  coordinate (`QLF_EdgeSign.position`), sends every closure to the zero vector, so "ZFA ⇒ null"
  is true there only because the interval of `0` is `0`. That reading cannot serve as the L2
  map. The tick reading is non-degenerate (`tick_reading_nondegenerate`).
* **L1, `null_lorentz_invariant`**: nullity of a Hermitian state is preserved by every
  `SL(2,ℂ)` congruence (from `lorentz_preserves_interval`). **`null_not_zero_time`** and
  **`null_not_zero_space`**: a null `Form` need not have zero time or zero space.
* **`census_postselection_signals`** (P6): uniform counting over joint closures, conditioned
  on the set of words Bob may use (his setting), **signals**. With one twist each, Alice's
  count for `slash` is `1` under Bob's `z` setting and `0` under his `x` setting, while both
  settings admit the same total of `2` joint closures. So the closure census, used as a global
  post-selection filter, is not a locality-respecting probability. The operator-layer
  statistics of [`QLF_PerspectiveLocality`](QLF_PerspectiveLocality.lean) do not signal. The
  joint verdict on which the census conditions is not available to either body alone
  (`QLF_SharedReality.zfa_not_from_one_body`).

No axioms.
-/

namespace QLF.LocalityDefinitions

open QLF QLF.ReachableEvent
open scoped Matrix

instance instDecCountBalanced : DecidablePred countBalanced := fun ts => by
  unfold countBalanced; infer_instance

/-! ## §1 Vocabulary -/

/-- Two twist words **close together**. -/
def SharedClosure (a b : List Twist) : Prop := countBalanced (a ++ b)

/-- Incomparable in the prefix order: the predicate `ER_EPR_QLF` calls `Spacelike`. -/
def PrefixSpacelike (a b : List Twist) : Prop := ¬ reachable a b ∧ ¬ reachable b a

/-- A spacetime displacement on the integer lattice: `(t, x, y, z)`. -/
abbrev Disp := ℤ × ℤ × ℤ × ℤ

/-- The tick displacement of one twist: one tick, plus a unit move on its spatial axis. -/
def stepDisp : Twist → Disp
  | .right     => (1, 1, 0, 0)
  | .left      => (1, -1, 0, 0)
  | .up        => (1, 0, 1, 0)
  | .down      => (1, 0, -1, 0)
  | .slash     => (1, 0, 0, 1)
  | .backslash => (1, 0, 0, -1)
  | .plus      => (1, 0, 0, 0)
  | .minus     => (1, 0, 0, 0)

/-- The **tick displacement** of a history: the sum of its steps. -/
def tick (h : List Twist) : Disp := (h.map stepDisp).sum

/-- The Minkowski interval of a lattice displacement, signature `(+,−,−,−)`. -/
def interval (v : Disp) : ℤ := v.1 ^ 2 - v.2.1 ^ 2 - v.2.2.1 ^ 2 - v.2.2.2 ^ 2

def IsNull (v : Disp) : Prop := interval v = 0
def IsTimelike (v : Disp) : Prop := 0 < interval v
def IsSpacelike (v : Disp) : Prop := interval v < 0

/-- The displacement as a `Form` (time on the identity, space on the Paulis). -/
noncomputable def tickForm (v : Disp) : Form := ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩

theorem tickForm_interval (v : Disp) :
    Minkowski.Form.interval (tickForm v) = (interval v : ℝ) := by
  simp [Minkowski.Form.interval, tickForm, interval]

/-! ## §2 The tick displacement in counts -/

@[simp] lemma tick_nil : tick [] = 0 := rfl

lemma tick_cons (t : Twist) (h : List Twist) : tick (t :: h) = stepDisp t + tick h := by
  simp [tick]

lemma tick_append (a b : List Twist) : tick (a ++ b) = tick a + tick b := by
  simp [tick]

/-- The four components of `tick` as twist counts. -/
lemma tick_eq (h : List Twist) :
    tick h = ((h.length : ℤ),
      (h.count .right : ℤ) - h.count .left,
      (h.count .up : ℤ) - h.count .down,
      (h.count .slash : ℤ) - h.count .backslash) := by
  induction h with
  | nil => rfl
  | cons t h ih =>
    rw [tick_cons, ih]
    cases t <;>
      simp (config := { decide := true }) only [stepDisp, List.length_cons, List.count_cons,
        ite_true, ite_false, Prod.mk_add_mk, Nat.cast_add,
        Nat.cast_one, add_zero, Prod.mk.injEq] <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

lemma length_eq_counts' (w : List Twist) :
    w.length = w.count .up + w.count .down + w.count .left + w.count .right
      + w.count .slash + w.count .backslash + w.count .plus + w.count .minus := by
  induction w with
  | nil => rfl
  | cons t rest ih =>
    cases t <;>
      simp (config := { decide := true }) only [List.length_cons, List.count_cons,
        ite_true, ite_false] <;>
      omega

/-! ## §3 P1–P3: the tick reading is causal, closures are timelike, runs are null -/

/-- **P1. Every history is causal.** Its tick displacement has `Δt ≥ 0` and interval `≥ 0`. -/
theorem tick_causal (h : List Twist) : 0 ≤ (tick h).1 ∧ 0 ≤ interval (tick h) := by
  rw [tick_eq]
  refine ⟨by positivity, ?_⟩
  simp only [interval]
  rw [length_eq_counts' h]
  push_cast
  set a := (h.count .up : ℤ); set b := (h.count .down : ℤ)
  set c := (h.count .left : ℤ); set d := (h.count .right : ℤ)
  set e := (h.count .slash : ℤ); set f := (h.count .backslash : ℤ)
  set g := (h.count .plus : ℤ); set k := (h.count .minus : ℤ)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have hd : 0 ≤ d := by positivity
  have he : 0 ≤ e := by positivity
  have hf : 0 ≤ f := by positivity
  have hg : 0 ≤ g := by positivity
  have hk : 0 ≤ k := by positivity
  nlinarith [mul_nonneg ha hb, mul_nonneg hc hd, mul_nonneg he hf,
    mul_nonneg (add_nonneg ha hb) (add_nonneg hc hd),
    mul_nonneg (add_nonneg ha hb) (add_nonneg he hf),
    mul_nonneg (add_nonneg hc hd) (add_nonneg he hf),
    mul_nonneg (add_nonneg (add_nonneg ha hb) (add_nonneg (add_nonneg hc hd) (add_nonneg he hf)))
      (add_nonneg hg hk),
    mul_nonneg (add_nonneg hg hk) (add_nonneg hg hk)]

/-- **No history has a spacelike displacement.** -/
theorem tick_not_spacelike (h : List Twist) : ¬ IsSpacelike (tick h) := by
  unfold IsSpacelike; have := (tick_causal h).2; omega

/-- **P2. A nonempty closure is strictly timelike.** -/
theorem closure_timelike (h : List Twist) (hb : countBalanced h) (hne : h ≠ []) :
    IsTimelike (tick h) := by
  obtain ⟨h1, h2, h3, _⟩ := hb
  have hl : 0 < h.length := List.length_pos_iff.mpr hne
  unfold IsTimelike interval
  rw [tick_eq]
  simp only
  rw [h1, h2, h3]
  simp only [sub_self]
  have : (0 : ℤ) < h.length := by exact_mod_cast hl
  nlinarith

lemma tick_replicate_right (n : ℕ) :
    tick (List.replicate n Twist.right) = ((n : ℤ), (n : ℤ), 0, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, tick_cons, ih]
    simp [stepDisp] <;> ring

/-- **P3 (Test A). A straight spatial run is null**, with time and space both nonzero. -/
theorem straight_run_null (n : ℕ) (hn : 0 < n) :
    IsNull (tick (List.replicate n Twist.right)) ∧
      0 < (tick (List.replicate n Twist.right)).1 ∧
      (tick (List.replicate n Twist.right)).2.1 ≠ 0 := by
  rw [tick_replicate_right]
  refine ⟨by simp [IsNull, interval], by simp; omega, by simp; omega⟩

/-- **A nonempty null history never closes**, so "radiative ∧ ZFA ⇒ null" has no nonempty
    instance in the tick reading. -/
theorem null_not_closed (h : List Twist) (hne : h ≠ []) (hn : IsNull (tick h)) :
    ¬ countBalanced h := by
  intro hb
  have := closure_timelike h hb hne
  unfold IsNull at hn; unfold IsTimelike at this; omega

/-- **The tick reading is non-degenerate**: null, timelike and closed-timelike histories exist,
    and distinct closures can have distinct displacements. -/
theorem tick_reading_nondegenerate :
    IsNull (tick [Twist.right]) ∧ IsTimelike (tick [Twist.plus]) ∧
      tick [Twist.right, Twist.left] ≠ tick [Twist.right, Twist.left, Twist.up, Twist.down] := by
  refine ⟨by unfold IsNull; decide, by unfold IsTimelike; decide, by decide⟩

/-- **The signed reading is degenerate.** Reading the gauge axis as a signed coordinate (as
    `QLF_EdgeSign.position` does), a count-balanced history has displacement zero, so every
    closure is sent to the origin and "ZFA ⇒ null" holds only because `interval 0 = 0`. -/
def signedDisp (h : List Twist) : Disp :=
  ((h.count .plus : ℤ) - h.count .minus, (tick h).2)

theorem zero_displacement_degenerate (h : List Twist) (hb : countBalanced h) :
    signedDisp h = 0 ∧ IsNull (signedDisp h) := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  have e : signedDisp h = 0 := by
    unfold signedDisp
    rw [tick_eq]
    simp only [h1, h2, h3, h4, sub_self]
    rfl
  exact ⟨e, by rw [e]; rfl⟩

/-! ## §4 P4 (Test C): shared closure across spacelike endpoints -/

lemma count_map_conj (ts : List Twist) (t : Twist) :
    (ts.map Twist.conj).count t = ts.count t.conj := by
  induction ts with
  | nil => rfl
  | cons s ts ih =>
    cases s <;> cases t <;> simp [List.count_cons, Twist.conj, ih] <;> decide

/-- **Pair-born halves close together.** -/
theorem pair_shared_closure (ts : List Twist) : SharedClosure ts (ts.map Twist.conj) := by
  unfold SharedClosure countBalanced
  simp only [List.count_append, count_map_conj, Twist.conj]
  omega

/-- The conjugate half moves the opposite way in space and takes the same time. -/
lemma tick_map_conj (ts : List Twist) :
    tick (ts.map Twist.conj) = ((tick ts).1, -(tick ts).2.1, -(tick ts).2.2.1, -(tick ts).2.2.2) := by
  rw [tick_eq, tick_eq]
  simp only [List.length_map, count_map_conj, Twist.conj]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp

/-- **The endpoints of a pair are spacelike** whenever the half has moved. -/
theorem pair_endpoints_spacelike (ts : List Twist) (hx : (tick ts).2 ≠ (0, 0, 0)) :
    IsSpacelike (tick (ts.map Twist.conj) - tick ts) := by
  rw [tick_map_conj]
  generalize tick ts = v at hx ⊢
  obtain ⟨t, x, y, z⟩ := v
  simp only [ne_eq, Prod.mk.injEq, not_and] at hx
  unfold IsSpacelike interval
  simp only [Prod.fst_sub, Prod.snd_sub, sub_self]
  by_cases h1 : x = 0
  · by_cases h2 : y = 0
    · have h3 : z ≠ 0 := hx h1 h2
      have : 0 < z ^ 2 := by positivity
      subst h1 h2; nlinarith
    · have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg x, sq_nonneg z]
  · have : 0 < x ^ 2 := by positivity
    nlinarith [sq_nonneg y, sq_nonneg z]

/-- **No history connects the two endpoints of a moved pair.** The shared closure joins events
    that no causal history joins. -/
theorem no_history_connects (ts : List Twist) (hx : (tick ts).2 ≠ (0, 0, 0)) (h : List Twist) :
    tick ts + tick h ≠ tick (ts.map Twist.conj) := by
  intro he
  have hs := pair_endpoints_spacelike ts hx
  rw [← he, add_sub_cancel_left] at hs
  exact tick_not_spacelike h hs

/-- The canonical witness: one step each way. -/
theorem up_down_pair :
    SharedClosure [Twist.up] [Twist.down] ∧
      IsSpacelike (tick [Twist.down] - tick [Twist.up]) ∧ PrefixSpacelike [Twist.up] [Twist.down] :=
  ⟨by unfold SharedClosure; decide, by unfold IsSpacelike; decide,
    by unfold PrefixSpacelike reachable; decide⟩

/-! ## §5 P5: the prefix order against the tick reading -/

/-- **Prefix reachability is causal in the tick reading.** -/
theorem reachable_causal {a b : List Twist} (h : reachable a b) :
    0 ≤ (tick b - tick a).1 ∧ 0 ≤ interval (tick b - tick a) := by
  obtain ⟨c, rfl⟩ := h
  rw [tick_append, add_sub_cancel_left]
  exact tick_causal c

/-- **Causal does not imply reachable.** `[up]` and `[plus, up]` are timelike-separated, yet
    neither is a prefix of the other: the history order is a tree, finer than the cone. -/
theorem causal_not_reachable :
    IsTimelike (tick [Twist.plus, Twist.up] - tick [Twist.up]) ∧
      PrefixSpacelike [Twist.up] [Twist.plus, Twist.up] :=
  ⟨by unfold IsTimelike; decide, by unfold PrefixSpacelike reachable; decide⟩

/-- **Prefix-incomparable does not mean spacelike.** The primordial pair `[plus]`, `[minus]`
    (`ER_EPR_QLF.primordial_wormhole`, in twist form) closes together and is prefix-incomparable,
    yet both halves land on the same tick event. -/
theorem prefixSpacelike_not_spacelike :
    SharedClosure [Twist.plus] [Twist.minus] ∧ PrefixSpacelike [Twist.plus] [Twist.minus] ∧
      tick [Twist.plus] = tick [Twist.minus] :=
  ⟨by unfold SharedClosure; decide, by unfold PrefixSpacelike reachable; decide, rfl⟩

/-- **Shared closure does not imply reachability**, and **reachability does not imply shared
    closure**. -/
theorem shared_closure_vs_reachable :
    (SharedClosure [Twist.up] [Twist.down] ∧ ¬ reachable [Twist.up] [Twist.down]) ∧
      (reachable [Twist.up] [Twist.up, Twist.up] ∧ ¬ SharedClosure [Twist.up] [Twist.up, Twist.up]) :=
  ⟨⟨by unfold SharedClosure; decide, by unfold reachable; decide⟩,
    ⟨by unfold reachable; decide, by unfold SharedClosure; decide⟩⟩

/-! ## §6 L1: nullity is Lorentz invariant, and null is not zero time or zero space -/

/-- **Nullity is preserved by every `SL(2,ℂ)` congruence.** -/
theorem null_lorentz_invariant (A X : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (A * X * Aᴴ).det = 0 ↔ X.det = 0 := by
  rw [Minkowski.lorentz_preserves_interval A X hA]

/-- A `Form` is null exactly when its Hermitian matrix is singular. -/
theorem form_null_iff_singular (f : Form) :
    Minkowski.Form.interval f = 0 ↔ (Form.toMatrix f).det = 0 := by
  rw [Minkowski.det_toMatrix_eq_interval]; exact_mod_cast Iff.rfl

/-- **Null is not zero time.** -/
theorem null_not_zero_time :
    Minkowski.Form.interval ⟨1, 1, 0, 0⟩ = 0 ∧ (⟨1, 1, 0, 0⟩ : Form).t ≠ 0 := by
  norm_num [Minkowski.Form.interval]

/-- **Null is not zero space.** -/
theorem null_not_zero_space :
    Minkowski.Form.interval ⟨1, 1, 0, 0⟩ = 0 ∧ (⟨1, 1, 0, 0⟩ : Form).x ≠ 0 := by
  norm_num [Minkowski.Form.interval]

/-! ## §7 P6: the closure census as a post-selection filter signals -/

/-- Bob's setting `z`: he may use `slash` or `backslash`. -/
def settingZ : List Twist := [.slash, .backslash]
/-- Bob's setting `x`: he may use `left` or `right`. -/
def settingX : List Twist := [.left, .right]

/-- Alice's count: how many of Bob's admissible words close jointly with Alice's word `a`. -/
def aliceCount (setting : List Twist) (a : Twist) : ℕ :=
  (setting.filter (fun b => decide (countBalanced [a, b]))).length

/-- Total joint closures under a setting, over Alice's eight one-twist words. -/
def totalCount (setting : List Twist) : ℕ :=
  ([Twist.up, .down, .left, .right, .slash, .backslash, .plus, .minus].map
    (aliceCount setting)).sum

/-- **P6. The census, conditioned on Bob's setting, signals.** Both settings admit the same
    number of joint closures, but Alice's count for `slash` is `1` under `z` and `0` under `x`.
    Her conditional distribution therefore depends on Bob's choice. -/
theorem census_postselection_signals :
    totalCount settingZ = 2 ∧ totalCount settingX = 2 ∧
      aliceCount settingZ .slash = 1 ∧ aliceCount settingX .slash = 0 := by
  decide

end QLF.LocalityDefinitions
