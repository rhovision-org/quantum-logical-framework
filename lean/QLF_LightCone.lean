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

## The shell kernel

From a cone point `v` to a later cone point `w`, the kernel `shellKernel v w` is the cone amplitude
of the outward displacement `w − v`. Every cone history passes each intermediate shell at exactly
one point, so

> **`shellKernel_compose`** — `K(0 → w) = Σ_{v on shell t} K(0 → v) · K(v → w)`,

the composition law of a transfer kernel, with matrix products in order (`coneSum_split`, for any
weight per twist).

## Normalisation

Summed over the whole shell, the cone sums give the power of the summed outward step
(`shell_total`), and the shell holds `3^L` histories (`shell_count`). The summed step squares to
`3` (`outStep_sq`), so its normalisation `(σ_y − σ_x + σ_z)/√3` is unitary and Hermitian:

> **`coneStep_unitary`**, **`shell_total_unitary`** — `Σ_{v on shell L} G_L(v) = (√3)^L · S^L`
> with `S` unitary.

The coherent total over the shell is exactly the square root of its history count times a unitary.
The channel-resolved amplitudes are not normalised by this.

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

-- ==========================================
-- §6  The shell-to-shell kernel and its composition law
-- ==========================================

/-- The intermediate shell: the cone points `(i, j, k) ≤ (a, b, c)` at time `t`. -/
def shellPts (a b c t : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (a + 1) ×ˢ range (b + 1) ×ˢ range (c + 1)).filter (fun x => x.1 + x.2.1 + x.2.2 = t)

theorem mem_coneSet {a b c : ℕ} {w : List Twist} : w ∈ coneSet a b c ↔
    w.length = a + b + c ∧ w.count Twist.up = a ∧ w.count Twist.left = b ∧
      w.count Twist.slash = c := by
  simp [coneSet, mem_words]

theorem count_take_add_drop (t : ℕ) (s : Twist) (w : List Twist) :
    (w.take t).count s + (w.drop t).count s = w.count s := by
  rw [← List.count_append, List.take_append_drop]

/-- **Splitting a cone sum at an intermediate shell**, for any weight per twist. -/
theorem coneSum_split {R : Type} [Ring R] (f : Twist → R) (a b c t : ℕ) (ht : t ≤ a + b + c) :
    coneSum f a b c = ∑ x ∈ shellPts a b c t,
      coneSum f x.1 x.2.1 x.2.2 * coneSum f (a - x.1) (b - x.2.1) (c - x.2.2) := by
  unfold coneSum
  simp only [Finset.sum_mul_sum, ← Finset.sum_product']
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun w => ⟨((w.take t).count Twist.up, (w.take t).count Twist.left,
      (w.take t).count Twist.slash), (w.take t, w.drop t)⟩) (fun y => y.2.1 ++ y.2.2)
    ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [mem_coneSet] at hw
    obtain ⟨hl, hu, hlf, hs⟩ := hw
    have h3 := count_three_le (w.take t)
    have h3' := count_three_le (w.drop t)
    have e1 := count_take_add_drop t Twist.up w
    have e2 := count_take_add_drop t Twist.left w
    have e3 := count_take_add_drop t Twist.slash w
    have lt : (w.take t).length = t := by rw [List.length_take]; omega
    have ld : (w.drop t).length = a + b + c - t := by rw [List.length_drop]; omega
    simp only [Finset.mem_sigma, shellPts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, mem_coneSet]
    refine ⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, ⟨by omega, trivial, trivial, trivial⟩,
      ⟨by omega, by omega, by omega, by omega⟩⟩
  · rintro ⟨x, p, q⟩ hy
    simp only [Finset.mem_sigma, shellPts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, mem_coneSet] at hy
    obtain ⟨⟨⟨h1, h2, h3⟩, hx⟩, ⟨lp, cp1, cp2, cp3⟩, ⟨lq, cq1, cq2, cq3⟩⟩ := hy
    simp only [mem_coneSet, List.length_append, List.count_append]
    omega
  · intro w hw
    simp
  · rintro ⟨x, p, q⟩ hy
    simp only [Finset.mem_sigma, shellPts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, mem_coneSet] at hy
    obtain ⟨⟨⟨h1, h2, h3⟩, hx⟩, ⟨lp, cp1, cp2, cp3⟩, -⟩ := hy
    have hp : (p ++ q).take t = p := by rw [List.take_left' (by omega)]
    have hq : (p ++ q).drop t = q := by rw [List.drop_left' (by omega)]
    obtain ⟨x1, x2, x3⟩ := x
    simp only [hp, hq, cp1, cp2, cp3]
  · intro w hw
    simp

/-- **The shell kernel.** From a cone point `v` to a later cone point `w`: the cone amplitude of
the outward displacement `w − v`, and `0` if `w` is not outward of `v`. -/
noncomputable def shellKernel (v w : ℕ × ℕ × ℕ) : M :=
  if v.1 ≤ w.1 ∧ v.2.1 ≤ w.2.1 ∧ v.2.2 ≤ w.2.2 then
    coneAmp (w.1 - v.1) (w.2.1 - v.2.1) (w.2.2 - v.2.2) else 0

/-- **Composition law (Chapman–Kolmogorov on the light cone).** The kernel from the origin to `w`
is the sum over every point `v` of an intermediate shell of the kernel to `v` times the kernel from
`v` to `w`. -/
theorem shellKernel_compose (a b c t : ℕ) (ht : t ≤ a + b + c) :
    shellKernel (0, 0, 0) (a, b, c) = ∑ v ∈ shellPts a b c t,
      shellKernel (0, 0, 0) v * shellKernel v (a, b, c) := by
  have h := coneSum_split Twist.toMatrix a b c t ht
  unfold shellKernel
  simp only [Nat.zero_le, and_self, ↓reduceIte, Nat.sub_zero]
  rw [show coneAmp a b c = coneSum Twist.toMatrix a b c from rfl, h]
  apply sum_congr rfl
  intro x hx
  simp only [shellPts, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
  simp only [show x.1 ≤ a ∧ x.2.1 ≤ b ∧ x.2.2 ≤ c from ⟨by omega, by omega, by omega⟩]
  rfl

-- ==========================================
-- §7  Normalisation: the shell total is √(count) times a unitary
-- ==========================================

theorem sum_prod_words {R : Type} [Ring R] (g : Twist → R) (n : ℕ) :
    ∑ w ∈ words Twist n, (w.map g).prod = (∑ t : Twist, g t) ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [sum_words_succ, pow_succ', Finset.sum_mul]
    apply sum_congr rfl
    intro t _
    simp only [List.map_cons, List.prod_cons, ← Finset.mul_sum, ih]

/-- A weight cut down to the three outward twists. -/
def cut {R : Type} [Ring R] (f : Twist → R) (t : Twist) : R :=
  if t = Twist.up ∨ t = Twist.left ∨ t = Twist.slash then f t else 0

theorem prod_cut {R : Type} [Ring R] (f : Twist → R) (w : List Twist) :
    (w.map (cut f)).prod = if w.count Twist.up + w.count Twist.left + w.count Twist.slash =
      w.length then (w.map f).prod else 0 := by
  induction w with
  | nil => simp
  | cons t w ih =>
    have hle := count_three_le w
    rw [List.map_cons, List.prod_cons, ih]
    cases t <;> simp +decide only [cut, List.count_cons, List.length_cons, List.map_cons,
      List.prod_cons] <;> split_ifs <;> first | contradiction | rfl | omega | simp

theorem sum_cut_shell {R : Type} [Ring R] (f : Twist → R) (n : ℕ) :
    ∑ w ∈ words Twist n, (w.map (cut f)).prod =
      ∑ x ∈ shellPts n n n n, coneSum f x.1 x.2.1 x.2.2 := by
  simp only [prod_cut]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun w => (w.count Twist.up, w.count Twist.left,
    w.count Twist.slash)) (t := shellPts n n n n)]
  · apply sum_congr rfl
    intro x hx
    simp only [shellPts, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    unfold coneSum
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext w
    simp only [Finset.mem_filter, mem_words, mem_coneSet]
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Prod.mk.injEq] at hx ⊢
    omega
  · intro w hw
    simp only [Finset.mem_filter, mem_words] at hw
    simp only [shellPts, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega

/-- **The shell total.** Summed over every point of the shell, the cone sums give the `n`-th power
of the summed outward step. -/
theorem shell_total {R : Type} [Ring R] (f : Twist → R) (n : ℕ) :
    ∑ x ∈ shellPts n n n n, coneSum f x.1 x.2.1 x.2.2 =
      (f Twist.up + f Twist.left + f Twist.slash) ^ n := by
  rw [← sum_cut_shell, sum_prod_words]
  congr 1
  show ∑ t ∈ ({Twist.up, Twist.down, Twist.left, Twist.right,
    Twist.slash, Twist.backslash, Twist.plus, Twist.minus} : Finset Twist), cut f t = _
  simp [cut, add_assoc]

/-- The shell holds `3^n` histories. -/
theorem shell_count (n : ℕ) :
    ∑ x ∈ shellPts n n n n, (coneCount x.1 x.2.1 x.2.2 : ℤ) = 3 ^ n := by
  have h := shell_total (fun _ => (1 : ℤ)) n
  simp only [coneSum_one] at h
  rw [h]
  norm_num

/-- The summed outward step. -/
noncomputable def outStep : M := Twist.up.toMatrix + Twist.left.toMatrix + Twist.slash.toMatrix

theorem outStep_sq : outStep * outStep = (3 : ℂ) • (1 : M) := by
  have h1 := up_up 1
  have h2 := left_left 1
  have h3 := slash_slash 1
  have h4 := left_up 1
  have h5 := slash_up 1
  have h6 := slash_left 1
  simp only [mul_one] at h1 h2 h3 h4 h5 h6
  unfold outStep
  simp only [add_mul, mul_add, h1, h2, h3, h4, h5, h6]
  rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  abel

theorem outStep_herm : outStep.conjTranspose = outStep := by
  unfold outStep
  simp only [Matrix.conjTranspose_add, ClosureUnitarity.twist_herm]

/-- `√3` as a complex number. -/
noncomputable def r3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)

theorem r3_sq : r3 * r3 = 3 := by
  unfold r3
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem r3_ne : r3 ≠ 0 := by
  intro h
  have := r3_sq
  rw [h, zero_mul] at this
  norm_num at this

/-- **The normalised step**, `(σ_y − σ_x + σ_z)/√3`. -/
noncomputable def coneStep : M := r3⁻¹ • outStep

/-- **The normalised step is unitary** (and Hermitian). -/
theorem coneStep_unitary : coneStep ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold coneStep
  rw [Matrix.conjTranspose_smul, outStep_herm, smul_mul_smul_comm, outStep_sq, smul_smul]
  have hs : star r3⁻¹ = r3⁻¹ := by
    unfold r3
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [hs, show r3⁻¹ * r3⁻¹ * 3 = 1 by rw [← r3_sq]; field_simp [r3_ne], one_smul]

/-- **The shell total is `√(count)` times a unitary.** Summed over the whole light-cone shell at time
`n`, the coherent amplitude is `(√3)^n · coneStep^n`, and the shell holds `3^n` histories
(`shell_count`), so its size is exactly the square root of the history count. -/
theorem shell_total_unitary (n : ℕ) :
    ∑ x ∈ shellPts n n n n, coneAmp x.1 x.2.1 x.2.2 = r3 ^ n • coneStep ^ n := by
  unfold coneAmp
  rw [shell_total, ← smul_pow]
  congr 1
  unfold coneStep
  rw [smul_smul, mul_inv_cancel₀ r3_ne, one_smul]
  rfl

end QLF.ClosureChannels
