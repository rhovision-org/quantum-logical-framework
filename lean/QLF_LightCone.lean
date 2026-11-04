import QLF_ChannelZeros

set_option linter.unusedVariables false

/-!
# QLF_LightCone — **the boundary amplitude on the light cone**

Continues [`QLF_ChannelZeros`](QLF_ChannelZeros.lean) (issue #207). See
[`Closure_Unitarity.md`](../Closure_Unitarity.md) §11.

## The light-cone shell

Take a fixed time `L` and the three spatial axes. A boundary state `v = (a, b, c, 0)` with
`a + b + c = L` lies **on the light cone**: every step of every history reaching it moved outward,
so those histories are exactly the orderings of `a` ups, `b` lefts and `c` slashes (`chanAmp_cone`).
The channel's classical multiplicity is the multinomial `L! / (a! b! c!)` (`coneCount`).

## Interference on the cone

The three spatial twists square to `1` and pairwise anticommute (a Clifford algebra), so two
adjacent different steps cancel against their swap and two adjacent equal steps fold to `1`
(`cone_two_step`). The amplitude is therefore the count of **paired walks** at half resolution:

> **`cone_amplitude`** — `G_L(a, b, c, 0) = N(⌊a/2⌋, ⌊b/2⌋, ⌊c/2⌋) · σ` when at most one of
> `a, b, c` is odd, and `0` otherwise,

where `N` is the multinomial count and `σ` is the leftover single twist (or `1`). In particular

> **`cone_zero_iff`** — on the light cone the channel vanishes **exactly** when it is mixed.

`mixed_channel_zero` gave one direction at every length; on the cone it is the only source of zeros.

No continuum is used: everything is a finite sum over histories. No axioms.
-/

namespace QLF.ClosureChannels

open Finset QLF QLF.FirstReturn QLF.ClosureLeakage

-- ==========================================
-- §1  Cone words and weighted cone sums
-- ==========================================

/-- The light-cone words: `a` ups, `b` lefts and `c` slashes, in every order. -/
def coneSet (a b c : ℕ) : Finset (List Twist) :=
  (words Twist (a + b + c)).filter
    (fun w => w.count Twist.up = a ∧ w.count Twist.left = b ∧ w.count Twist.slash = c)

/-- A cone sum with an arbitrary weight per twist. -/
def coneSum {R : Type} [Ring R] (f : Twist → R) (a b c : ℕ) : R :=
  ∑ w ∈ coneSet a b c, (w.map f).prod

theorem sum_words_succ {β : Type} [AddCommMonoid β] (m : ℕ) (g : List Twist → β) :
    ∑ w ∈ words Twist (m + 1), g w = ∑ t : Twist, ∑ w ∈ words Twist m, g (t :: w) := by
  rw [words, sum_biUnion]
  · apply sum_congr rfl
    intro t _
    rw [sum_image (fun _ _ _ _ h => by simpa using h)]
  · intro t₁ _ t₂ _ hne
    apply Finset.disjoint_left.mpr
    intro h h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨w₁, -, rfl⟩ := h1
    obtain ⟨w₂, -, he⟩ := h2
    exact hne (List.cons.inj he).1.symm

theorem count_three_le (w : List Twist) :
    w.count Twist.up + w.count Twist.left + w.count Twist.slash ≤ w.length := by
  induction w with
  | nil => simp
  | cons t w ih => cases t <;> simp +decide [List.count_cons] <;> omega

theorem coneSum_eq {R : Type} [Ring R] (f : Twist → R) (a b c : ℕ) :
    coneSum f a b c = ∑ w ∈ words Twist (a + b + c),
      if w.count Twist.up = a ∧ w.count Twist.left = b ∧ w.count Twist.slash = c
      then (w.map f).prod else 0 := by
  unfold coneSum coneSet
  rw [sum_filter]

/-- **The first-step recursion on the cone.** -/
theorem coneSum_succ {R : Type} [Ring R] (f : Twist → R) (a b c : ℕ) (h : 0 < a + b + c) :
    coneSum f a b c =
      (if 0 < a then f Twist.up * coneSum f (a - 1) b c else 0) +
      (if 0 < b then f Twist.left * coneSum f a (b - 1) c else 0) +
      (if 0 < c then f Twist.slash * coneSum f a b (c - 1) else 0) := by
  obtain ⟨m, hm⟩ : ∃ m, a + b + c = m + 1 := ⟨a + b + c - 1, by omega⟩
  rw [coneSum_eq, hm, sum_words_succ]
  have key : ∀ t : Twist, ∀ w ∈ words Twist m,
      (if (t :: w).count Twist.up = a ∧ (t :: w).count Twist.left = b ∧
          (t :: w).count Twist.slash = c then ((t :: w).map f).prod else 0) =
      (if t = Twist.up ∧ 0 < a ∧ w.count Twist.up = a - 1 ∧ w.count Twist.left = b ∧
          w.count Twist.slash = c then f Twist.up * (w.map f).prod else 0) +
      (if t = Twist.left ∧ 0 < b ∧ w.count Twist.up = a ∧ w.count Twist.left = b - 1 ∧
          w.count Twist.slash = c then f Twist.left * (w.map f).prod else 0) +
      (if t = Twist.slash ∧ 0 < c ∧ w.count Twist.up = a ∧ w.count Twist.left = b ∧
          w.count Twist.slash = c - 1 then f Twist.slash * (w.map f).prod else 0) := by
    intro t w hw
    rw [mem_words] at hw
    have hle := count_three_le w
    cases t <;> simp +decide only [List.count_cons, List.map_cons, List.prod_cons] <;>
      (try simp only [ite_true, ite_false, true_and, false_and, add_zero]) <;>
      split_ifs <;> first | (simp only [add_zero, zero_add]; done) | rfl | omega
  rw [sum_congr rfl (fun t _ => sum_congr rfl (key t))]
  simp only [sum_add_distrib]
  congr 1
  congr 1
  all_goals
    rw [Finset.sum_comm]
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    split_ifs with ha
    · rw [coneSum_eq, show (_ : ℕ) + _ + _ = m by omega, Finset.mul_sum]
      apply sum_congr rfl
      intro w _
      split_ifs <;> simp_all
    · simp

-- ==========================================
-- §2  The Clifford relations of the three spatial twists
-- ==========================================

/-- The light-cone amplitude: the folds of every cone word, summed. -/
noncomputable def coneAmp (a b c : ℕ) : M := coneSum Twist.toMatrix a b c

/-- The classical multiplicity of the cone channel: how many histories reach it. -/
def coneCount (a b c : ℕ) : ℕ := (coneSet a b c).card

theorem coneSum_one (a b c : ℕ) : coneSum (fun _ => (1 : ℤ)) a b c = coneCount a b c := by
  unfold coneSum coneCount
  simp

theorem up_up (X : M) : Twist.up.toMatrix * (Twist.up.toMatrix * X) = X := by
  rw [← mul_assoc]; show σy * σy * X = X; rw [sigma_y_sq, one_mul]

theorem left_left (X : M) : Twist.left.toMatrix * (Twist.left.toMatrix * X) = X := by
  rw [← mul_assoc]; show (-σx) * (-σx) * X = X; rw [neg_mul_neg, sigma_x_sq, one_mul]

theorem slash_slash (X : M) : Twist.slash.toMatrix * (Twist.slash.toMatrix * X) = X := by
  rw [← mul_assoc]; show σz * σz * X = X; rw [sigma_z_sq, one_mul]

theorem left_up (X : M) : Twist.left.toMatrix * (Twist.up.toMatrix * X) =
    -(Twist.up.toMatrix * (Twist.left.toMatrix * X)) := by
  rw [← mul_assoc, ← mul_assoc, twist_mul_comm]; simp [anti, axisOf]

theorem slash_up (X : M) : Twist.slash.toMatrix * (Twist.up.toMatrix * X) =
    -(Twist.up.toMatrix * (Twist.slash.toMatrix * X)) := by
  rw [← mul_assoc, ← mul_assoc, twist_mul_comm]; simp [anti, axisOf]

theorem slash_left (X : M) : Twist.slash.toMatrix * (Twist.left.toMatrix * X) =
    -(Twist.left.toMatrix * (Twist.slash.toMatrix * X)) := by
  rw [← mul_assoc, ← mul_assoc, twist_mul_comm]; simp [anti, axisOf]

/-- **Two steps at a time.** Adjacent equal steps fold to `1`; adjacent different steps cancel
against their swap. -/
theorem cone_two_step (a b c : ℕ) (h : 2 ≤ a + b + c) :
    coneAmp a b c =
      (if 2 ≤ a then coneAmp (a - 2) b c else 0) +
      (if 2 ≤ b then coneAmp a (b - 2) c else 0) +
      (if 2 ≤ c then coneAmp a b (c - 2) else 0) := by
  unfold coneAmp
  have r1 : 0 < a → coneSum Twist.toMatrix (a - 1) b c = _ :=
    fun ha => coneSum_succ Twist.toMatrix (a - 1) b c (by omega)
  have r2 : 0 < b → coneSum Twist.toMatrix a (b - 1) c = _ :=
    fun hb => coneSum_succ Twist.toMatrix a (b - 1) c (by omega)
  have r3 : 0 < c → coneSum Twist.toMatrix a b (c - 1) = _ :=
    fun hc => coneSum_succ Twist.toMatrix a b (c - 1) (by omega)
  rw [coneSum_succ Twist.toMatrix a b c (by omega)]
  have ea : (0 < a - 1) ↔ 2 ≤ a := by omega
  have eb : (0 < b - 1) ↔ 2 ≤ b := by omega
  have ec : (0 < c - 1) ↔ 2 ≤ c := by omega
  by_cases ha : 0 < a <;> by_cases hb : 0 < b <;> by_cases hc : 0 < c <;>
    simp only [ha, hb, hc, r1, r2, r3, ↓reduceIte, ea, eb, ec, Nat.sub_sub, mul_add, mul_ite,
      mul_zero, up_up, left_left, slash_slash, left_up, slash_up, slash_left] <;>
    split_ifs <;> first | omega | abel

-- ==========================================
-- §3  The amplitude is the count of paired walks
-- ==========================================

/-- The leftover single twist once every pair has folded to `1`. -/
noncomputable def coneSpin (a b c : ℕ) : M :=
  Twist.up.toMatrix ^ (a % 2) * Twist.left.toMatrix ^ (b % 2) * Twist.slash.toMatrix ^ (c % 2)

theorem coneCount_succ (a b c : ℕ) (h : 0 < a + b + c) :
    (coneCount a b c : ℂ) =
      (if 0 < a then (coneCount (a - 1) b c : ℂ) else 0) +
      (if 0 < b then (coneCount a (b - 1) c : ℂ) else 0) +
      (if 0 < c then (coneCount a b (c - 1) : ℂ) else 0) := by
  have e := coneSum_succ (fun _ => (1 : ℤ)) a b c h
  simp only [coneSum_one, one_mul] at e
  split_ifs at e ⊢ <;> push_cast at e ⊢ <;> exact_mod_cast e

theorem coneSet_zero : coneSet 0 0 0 = {[]} := by
  decide

theorem coneAmp_zero : coneAmp 0 0 0 = 1 := by
  simp [coneAmp, coneSum, coneSet_zero]

theorem coneCount_zero : coneCount 0 0 0 = 1 := by
  simp [coneCount, coneSet_zero]

/-- **The light-cone amplitude.** At most one odd axis: the number of paired walks at half
resolution, times the leftover twist. Two or three odd axes: zero. -/
theorem cone_amplitude (a b c : ℕ) :
    coneAmp a b c = if a % 2 + b % 2 + c % 2 ≤ 1 then
      (coneCount (a / 2) (b / 2) (c / 2) : ℂ) • coneSpin a b c else 0 := by
  induction h : a + b + c using Nat.strong_induction_on generalizing a b c with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- length 0 or 1
    have e0 := coneAmp_zero
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 0 := by omega
      simp [coneAmp_zero, coneCount_zero, coneSpin]
    · unfold coneAmp
      rw [coneSum_succ Twist.toMatrix a b c (by omega)]
      rcases (by omega : (a = 1 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨
          (a = 0 ∧ b = 0 ∧ c = 1)) with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [coneAmp] at e0 <;> simp [e0, coneCount_zero, coneSpin]
  · have IH : ∀ a' b' c' : ℕ, a' + b' + c' < n → coneAmp a' b' c' =
        if a' % 2 + b' % 2 + c' % 2 ≤ 1 then
          (coneCount (a' / 2) (b' / 2) (c' / 2) : ℂ) • coneSpin a' b' c' else 0 :=
      fun a' b' c' hl => ih _ hl a' b' c' rfl
    rw [cone_two_step a b c (by omega)]
    have ka : 2 ≤ a → coneAmp (a - 2) b c = if a % 2 + b % 2 + c % 2 ≤ 1 then
        (coneCount (a / 2 - 1) (b / 2) (c / 2) : ℂ) • coneSpin a b c else 0 := by
      intro ha
      rw [IH _ _ _ (by omega)]
      have h1 : (a - 2) % 2 = a % 2 := by omega
      have h2 : (a - 2) / 2 = a / 2 - 1 := by omega
      simp only [coneSpin, h1, h2]
    have kb : 2 ≤ b → coneAmp a (b - 2) c = if a % 2 + b % 2 + c % 2 ≤ 1 then
        (coneCount (a / 2) (b / 2 - 1) (c / 2) : ℂ) • coneSpin a b c else 0 := by
      intro hb
      rw [IH _ _ _ (by omega)]
      have h1 : (b - 2) % 2 = b % 2 := by omega
      have h2 : (b - 2) / 2 = b / 2 - 1 := by omega
      simp only [coneSpin, h1, h2]
    have kc : 2 ≤ c → coneAmp a b (c - 2) = if a % 2 + b % 2 + c % 2 ≤ 1 then
        (coneCount (a / 2) (b / 2) (c / 2 - 1) : ℂ) • coneSpin a b c else 0 := by
      intro hc
      rw [IH _ _ _ (by omega)]
      have h1 : (c - 2) % 2 = c % 2 := by omega
      have h2 : (c - 2) / 2 = c / 2 - 1 := by omega
      simp only [coneSpin, h1, h2]
    by_cases hp : a % 2 + b % 2 + c % 2 ≤ 1
    · rw [coneCount_succ (a / 2) (b / 2) (c / 2) (by omega)]
      have ea : (0 < a / 2) ↔ 2 ≤ a := by omega
      have eb : (0 < b / 2) ↔ 2 ≤ b := by omega
      have ec : (0 < c / 2) ↔ 2 ≤ c := by omega
      simp only [hp, ↓reduceIte, ea, eb, ec, add_smul, ite_smul, zero_smul]
      split_ifs with h1 h2 h3 <;> simp_all
    · simp only [hp, ↓reduceIte]
      split_ifs <;> simp_all

-- ==========================================
-- §4  The cone words are the channel on the light cone
-- ==========================================

theorem fold_eq_prod (w : List Twist) : twistMatrixFold w = (w.map Twist.toMatrix).prod := by
  induction w with
  | nil => rfl
  | cons t w ih => simp only [twistMatrixFold, List.foldr_cons, List.map_cons,
      List.prod_cons] at ih ⊢; rw [ih]

theorem length_eq_counts (w : List Twist) : w.length =
    w.count Twist.up + w.count Twist.down + w.count Twist.left + w.count Twist.right +
    w.count Twist.slash + w.count Twist.backslash + w.count Twist.plus + w.count Twist.minus := by
  induction w with
  | nil => simp
  | cons t w ih => cases t <;> simp +decide [List.count_cons] <;> omega

/-- **On the light cone the channel is the cone sum.** A history of length `a + b + c` that ends at
`(a, b, c, 0)` never stepped backward and never used a gauge twist. -/
theorem chanAmp_cone (a b c : ℕ) :
    chanAmp ((a : ℤ), (b : ℤ), (c : ℤ), 0) (a + b + c) = coneAmp a b c := by
  unfold chanAmp coneAmp coneSum coneSet
  rw [Finset.filter_congr (q := fun w => w.count Twist.up = a ∧ w.count Twist.left = b ∧
      w.count Twist.slash = c)]
  · apply sum_congr rfl
    intro w _
    exact fold_eq_prod w
  · intro w hw
    rw [mem_words] at hw
    have hl := length_eq_counts w
    simp only [disp, Prod.mk.injEq]
    omega

-- ==========================================
-- §5  On the cone, the zeros are exactly the mixed channels
-- ==========================================

theorem coneCount_pos (a b c : ℕ) : 0 < coneCount a b c := by
  unfold coneCount
  apply Finset.card_pos.mpr
  refine ⟨List.replicate a Twist.up ++ List.replicate b Twist.left ++
    List.replicate c Twist.slash, ?_⟩
  simp only [coneSet, Finset.mem_filter, mem_words, List.length_append, List.length_replicate,
    List.count_append]
  have z : ∀ (n : ℕ) (s t : Twist), List.count t (List.replicate n s) = if s = t then n else 0 := by
    intro n s t
    induction n with
    | zero => simp
    | succ n ih => cases s <;> cases t <;> simp_all +decide [List.replicate_succ, List.count_cons]
  simp only [z]
  simp

theorem coneSpin_sq (a b c : ℕ) (hp : a % 2 + b % 2 + c % 2 ≤ 1) :
    coneSpin a b c * coneSpin a b c = 1 := by
  unfold coneSpin
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
  simp only [ha, hb, hc, pow_zero, pow_one, one_mul, mul_one] <;>
  first
    | omega
    | rfl
    | simpa using up_up 1
    | simpa using left_left 1
    | simpa using slash_slash 1

theorem mixed_cone_iff (a b c : ℕ) :
    Mixed ((a : ℤ), (b : ℤ), (c : ℤ), 0) ↔ ¬ (a % 2 + b % 2 + c % 2 ≤ 1) := by
  unfold Mixed
  simp only [Int.odd_add, Int.odd_mul, Int.odd_coe_nat, Nat.odd_iff, Int.even_mul,
    Int.even_coe_nat, Nat.even_iff]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
  simp [ha, hb, hc]

/-- **On the light cone a channel vanishes exactly when it is mixed.** -/
theorem cone_zero_iff (a b c : ℕ) :
    chanAmp ((a : ℤ), (b : ℤ), (c : ℤ), 0) (a + b + c) = 0 ↔
      Mixed ((a : ℤ), (b : ℤ), (c : ℤ), 0) := by
  rw [chanAmp_cone, cone_amplitude, mixed_cone_iff]
  by_cases hp : a % 2 + b % 2 + c % 2 ≤ 1
  · simp only [hp, ↓reduceIte, not_true_eq_false, iff_false]
    intro h0
    have hN : (coneCount (a / 2) (b / 2) (c / 2) : ℂ) ≠ 0 := by
      exact_mod_cast (coneCount_pos _ _ _).ne'
    have hs : coneSpin a b c ≠ 0 := by
      intro hz
      have := coneSpin_sq a b c hp
      rw [hz, zero_mul] at this
      exact zero_ne_one this
    exact smul_ne_zero hN hs h0
  · simp [hp]

end QLF.ClosureChannels
