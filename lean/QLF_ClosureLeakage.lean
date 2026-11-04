import QLF_FirstReturn
import QLF_ClosureUnitarity

set_option linter.unusedVariables false

/-!
# QLF_ClosureLeakage — **closed channels plus the open channel are complete; the open one never empties**

Third milestone of the closure-algebra programme of issue #207 (U3), after
[`QLF_ClosureUnitarity`](QLF_ClosureUnitarity.lean) and [`QLF_ClosureKernel`](QLF_ClosureKernel.lean).
See [`Closure_Unitarity.md`](../Closure_Unitarity.md) §8.

The issue's warning: `QLF_PolyaTransience` proves that not every possibility closes, so the closed
channels cannot simply be normalized to one. It listed four ways out. This module proves which one the
substrate takes.

## The channel decomposition

Every twist history of length `L` is exactly one of:

* **closed by `L`**: it has a first closure (a prime prefix, `QLF_FirstReturn.IsPrime`) of some length
  `k + 1 ≤ L`, after which anything may follow; or
* **open**: no non-empty prefix of it is balanced (`IsOpen`).

The pieces are disjoint and cover the length-`L` words (`words_partition`, `fiber_disjoint`,
`open_disjoint_fiber`), and each closed fiber is a product, prime × free tail (`sum_fiber`).

## U3 — the leakage identity (measure)

In the cylinder measure `8^{−|h|}`:

> **`leakage_identity`** — `closedMass L + openMass L = 1` at every `L`,

where `closedMass L = Σ_{k ≤ L} I(k)/8^k` is the prime Kraft mass heard by `L` and
`openMass L = #open_L / 8^L`. This is the issue's `S_closed† S_closed + S_open† S_open = I`, read in
the measure: completeness needs **both** channels. And the open channel never empties:

> **`openMass_ge_quarter`** — `1/4 ≤ openMass L` for every `L`, so
> **`closed_channels_incomplete`** — `closedMass L < 1` for every `L`.

So the closed channels alone are never complete, at any capacity. Of the issue's four resolutions,
the substrate takes the second: the complete channel space is closed **plus** open (escape) channels.
Conditioning on closure (resolution 3) would mean dividing by a mass that is at most `3/4`, which is an
added normalization postulate, and kill condition 1 forbids that.

## U3b — the leakage identity (amplitude)

Each twist history is unitary (`QLF_ClosureUnitarity.history_unitary`), but the eight twists cancel
as a sum: `Σ_t U(t) = 0` (`sum_twist_matrices`), so the free amplitude over all words of length
`L ≥ 1` is zero (`sum_fold_words`). Split by channel, every closed fiber with a free tail dies with
it, and only the primes of full length survive:

> **`open_amplitude`** — for `L ≥ 1`, `Σ_{open h} U(h) = −Σ_{prime p, |p| = L} U(p)`.

The open-channel amplitude is exactly minus the prime kernel at that length (`K_L · I` by the phase
rule). It is the amplitude-level form of the same completeness: what closes for the first time at
`L` is balanced by what has not closed.

No axioms.
-/

namespace QLF.ClosureLeakage

open Finset QLF QLF.FirstReturn QLF.PolyaTransience QLF.ProductWalk

-- ==========================================
-- §1  Open histories and the channel partition
-- ==========================================

/-- `h` is **open**: no non-empty prefix of it (itself included) is balanced. -/
def IsOpen (h : List Twist) : Prop :=
  ∀ k ∈ Finset.Icc 1 h.length, ¬ countBalanced (h.take k)

instance : DecidablePred IsOpen := fun h => by unfold IsOpen; infer_instance

/-- The closed fiber at first-closure length `k + 1`. -/
def fiber (L k : ℕ) : Finset (List Twist) :=
  (words Twist L).filter (fun h => decide (IsPrime (h.take (k + 1))))

/-- The open channel at length `L`. -/
def openSet (L : ℕ) : Finset (List Twist) :=
  (words Twist L).filter (fun h => decide (IsOpen h))

/-- The primes of length `n`. -/
def primes (n : ℕ) : Finset (List Twist) :=
  (words Twist n).filter (fun p => decide (IsPrime p))

theorem words_partition (L : ℕ) :
    words Twist L = ((range L).biUnion (fiber L)) ∪ openSet L := by
  ext h
  simp only [fiber, openSet, mem_union, mem_biUnion, mem_filter, mem_range, decide_eq_true_eq]
  constructor
  · intro hw
    by_cases ho : IsOpen h
    · exact Or.inr ⟨hw, ho⟩
    · left
      have hlen := (mem_words L h).1 hw
      unfold IsOpen at ho
      push Not at ho
      obtain ⟨k, hk, hb⟩ := ho
      rw [Finset.mem_Icc] at hk
      have htk : (h.take k).length = k := by rw [List.length_take]; omega
      obtain ⟨ℓ, hℓ, hp⟩ := prime_prefix_exists (h.take k) hb (by omega)
      rw [htk] at hℓ
      rw [List.take_take, min_eq_left hℓ] at hp
      have hℓ0 : 0 < ℓ := by
        have := hp.1
        rw [List.length_take] at this
        omega
      refine ⟨ℓ - 1, by omega, hw, ?_⟩
      rw [show ℓ - 1 + 1 = ℓ by omega]
      exact hp
  · rintro (⟨k, -, hw, -⟩ | ⟨hw, -⟩) <;> exact hw

theorem fiber_disjoint (L : ℕ) : Set.PairwiseDisjoint (↑(range L)) (fiber L) := by
  intro k₁ hk₁ k₂ hk₂ hne
  simp only [coe_range, Set.mem_Iio] at hk₁ hk₂
  apply Finset.disjoint_left.mpr
  intro h h1 h2
  simp only [fiber, mem_filter, decide_eq_true_eq] at h1 h2
  have hlen := (mem_words L h).1 h1.1
  exact hne (by
    have := prime_prefix_unique h (k₁ + 1) (k₂ + 1) (by omega) (by omega) h1.2 h2.2
    omega)

theorem open_disjoint_fiber (L : ℕ) : Disjoint ((range L).biUnion (fiber L)) (openSet L) := by
  apply Finset.disjoint_left.mpr
  intro h h1 h2
  simp only [fiber, openSet, mem_biUnion, mem_filter, mem_range, decide_eq_true_eq] at h1 h2
  obtain ⟨k, hk, hw, hp⟩ := h1
  have hlen := (mem_words L h).1 hw
  apply h2.2 (k + 1) (by rw [Finset.mem_Icc]; omega)
  exact hp.2.1

/-- **Each closed fiber is a product**: a prime of length `k + 1`, then any tail. -/
theorem sum_fiber {β : Type} [AddCommMonoid β] (L k : ℕ) (hk : k < L) (g : List Twist → β) :
    ∑ h ∈ fiber L k, g h =
      ∑ x ∈ primes (k + 1) ×ˢ words Twist (L - (k + 1)), g (x.1 ++ x.2) := by
  refine Finset.sum_nbij' (fun h => (h.take (k + 1), h.drop (k + 1))) (fun x => x.1 ++ x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [fiber, mem_filter, decide_eq_true_eq] at hh
    obtain ⟨hw, hp⟩ := hh
    have hlen := (mem_words L h).1 hw
    simp only [primes, mem_product, mem_filter, mem_words, decide_eq_true_eq]
    refine ⟨⟨by rw [List.length_take]; omega, hp⟩, by rw [List.length_drop]; omega⟩
  · intro x hx
    obtain ⟨p, q⟩ := x
    simp only [primes, mem_product, mem_filter, mem_words, decide_eq_true_eq] at hx
    obtain ⟨⟨hpl, hpp⟩, hql⟩ := hx
    simp only [fiber, mem_filter, mem_words, decide_eq_true_eq]
    refine ⟨by rw [List.length_append, hpl, hql]; omega, ?_⟩
    rw [← hpl, List.take_left]
    exact hpp
  · intro h _
    exact List.take_append_drop (k + 1) h
  · intro x hx
    obtain ⟨p, q⟩ := x
    simp only [primes, mem_product, mem_filter, mem_words, decide_eq_true_eq] at hx
    rw [← hx.1.1]
    simp
  · intro h _
    rw [List.take_append_drop]

/-- The channel decomposition of any additive quantity over the length-`L` words. -/
theorem sum_words_split {β : Type} [AddCommMonoid β] (L : ℕ) (g : List Twist → β) :
    ∑ h ∈ words Twist L, g h =
      ∑ k ∈ range L, ∑ x ∈ primes (k + 1) ×ˢ words Twist (L - (k + 1)), g (x.1 ++ x.2) +
        ∑ h ∈ openSet L, g h := by
  rw [words_partition L, sum_union (open_disjoint_fiber L), sum_biUnion (fiber_disjoint L)]
  congr 1
  apply sum_congr rfl
  intro k hk
  exact sum_fiber L k (mem_range.1 hk) g

-- ==========================================
-- §2  U3 — the leakage identity in the cylinder measure
-- ==========================================

/-- The number of open histories of length `L`. -/
def openCount (L : ℕ) : ℕ := (openSet L).card

theorem card_words_twist (n : ℕ) : (words Twist n).card = 8 ^ n := by
  rw [card_words, card_twist]

/-- **The counting identity**: `8^L = Σ_{k<L} I(k+1)·8^{L−k−1} + #open_L`. -/
theorem count_split (L : ℕ) :
    8 ^ L = ∑ k ∈ range L, primeCount (k + 1) * 8 ^ (L - (k + 1)) + openCount L := by
  have h := sum_words_split (β := ℕ) L (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one, card_product] at h
  rw [card_words_twist] at h
  rw [h]
  unfold openCount
  congr 1
  apply sum_congr rfl
  intro k _
  rw [card_words_twist]
  rfl

/-- The mass heard as closed by length `L`: the prime Kraft mass up to `L`. -/
noncomputable def closedMass (L : ℕ) : ℝ := ∑ k ∈ range (L + 1), a k

/-- The mass still open at length `L`. -/
noncomputable def openMass (L : ℕ) : ℝ := (openCount L : ℝ) / 8 ^ L

/-- **U3 — the leakage identity.** Closed plus open is complete, at every length. -/
theorem leakage_identity (L : ℕ) : closedMass L + openMass L = 1 := by
  have h := count_split L
  have h8 : (0 : ℝ) < 8 ^ L := by positivity
  have hR : ((8 : ℕ) : ℝ) ^ L =
      ∑ k ∈ range L, (primeCount (k + 1) : ℝ) * 8 ^ (L - (k + 1)) + (openCount L : ℝ) := by
    exact_mod_cast h
  unfold closedMass openMass
  rw [sum_range_succ', a_zero, add_zero]
  have hterm : ∀ k ∈ range L, a (k + 1) =
      (primeCount (k + 1) : ℝ) * 8 ^ (L - (k + 1)) / 8 ^ L := by
    intro k hk
    have hkL := mem_range.1 hk
    unfold a
    have hpow : (8 : ℝ) ^ (k + 1) * (8 : ℝ) ^ (L - (k + 1)) = 8 ^ L := by
      rw [← pow_add]; congr 1; omega
    rw [← hpow]
    field_simp
  rw [sum_congr rfl hterm, ← sum_div, ← add_div]
  push_cast at hR
  rw [← hR, div_self (ne_of_gt h8)]

theorem openMass_nonneg (L : ℕ) : 0 ≤ openMass L := by
  unfold openMass; positivity

theorem summable_a : Summable a := by
  apply summable_of_sum_range_le a_nonneg (c := 1)
  intro n
  have h1 : ∑ i ∈ range n, a i ≤ closedMass n := by
    unfold closedMass
    rw [sum_range_succ]
    linarith [a_nonneg n]
  linarith [leakage_identity n, openMass_nonneg n]

/-- The closed mass is at most the total prime mass, which transience caps at `3/4`. -/
theorem closedMass_le (L : ℕ) : closedMass L ≤ 3 / 4 :=
  (summable_a.sum_le_tsum (range (L + 1)) (fun i _ => a_nonneg i)).trans
    at_least_quarter_never_closes

/-- **The open channel never empties**: at least a quarter of the mass is open at every length. -/
theorem openMass_ge_quarter (L : ℕ) : 1 / 4 ≤ openMass L := by
  linarith [leakage_identity L, closedMass_le L]

/-- **Closed channels alone are never complete**, at any capacity. -/
theorem closed_channels_incomplete (L : ℕ) : closedMass L < 1 := by
  linarith [closedMass_le L]

-- ==========================================
-- §3  U3b — the leakage identity at amplitude level
-- ==========================================

/-- The eight twists cancel as a sum. -/
theorem sum_twist_matrices : ∑ t : Twist, t.toMatrix = 0 := by
  show ∑ t ∈ ({Twist.up, Twist.down, Twist.left, Twist.right,
    Twist.slash, Twist.backslash, Twist.plus, Twist.minus} : Finset Twist), t.toMatrix = 0
  simp [Twist.toMatrix]

/-- The free amplitude: the sum of the folds of all words of length `n` is `(Σ_t U(t))^n`. -/
theorem sum_fold_words (n : ℕ) :
    ∑ h ∈ words Twist n, twistMatrixFold h = (∑ t : Twist, t.toMatrix) ^ n := by
  induction n with
  | zero => simp [words, twistMatrixFold]
  | succ n ih =>
    rw [words, sum_biUnion]
    · rw [pow_succ', Finset.sum_mul]
      apply sum_congr rfl
      intro t _
      rw [sum_image (fun _ _ _ _ h => by simpa using h), ← ih, Finset.mul_sum]
      apply sum_congr rfl
      intro w _
      rfl
    · intro t₁ _ t₂ _ hne
      apply Finset.disjoint_left.mpr
      intro h h1 h2
      simp only [mem_image] at h1 h2
      obtain ⟨w₁, -, rfl⟩ := h1
      obtain ⟨w₂, -, he⟩ := h2
      exact hne (List.cons.inj he).1.symm

theorem free_amplitude_zero (n : ℕ) (hn : 0 < n) :
    ∑ h ∈ words Twist n, twistMatrixFold h = 0 := by
  rw [sum_fold_words, sum_twist_matrices, zero_pow (by omega)]

/-- **U3b — the open channel's amplitude is minus the prime kernel at full length.** -/
theorem open_amplitude (L : ℕ) (hL : 0 < L) :
    ∑ h ∈ openSet L, twistMatrixFold h = -∑ p ∈ primes L, twistMatrixFold p := by
  have h := sum_words_split L twistMatrixFold
  rw [free_amplitude_zero L hL] at h
  have hfib : ∀ k ∈ range L,
      ∑ x ∈ primes (k + 1) ×ˢ words Twist (L - (k + 1)), twistMatrixFold (x.1 ++ x.2) =
        if L - 1 = k then ∑ p ∈ primes L, twistMatrixFold p else 0 := by
    intro k hk
    have hkL := mem_range.1 hk
    simp_rw [ClosureUnitarity.fold_append]
    rw [sum_product, ← Finset.sum_mul_sum, sum_fold_words, sum_twist_matrices]
    split_ifs with heq
    · have hk1 : k + 1 = L := by omega
      subst hk1
      simp
    · rw [zero_pow (by omega), mul_zero]
  have hmem : L - 1 ∈ range L := mem_range.2 (by omega)
  rw [sum_congr rfl hfib, sum_ite_eq (range L) (L - 1)] at h
  simp only [hmem, ↓reduceIte] at h
  exact eq_neg_of_add_eq_zero_right h.symm


end QLF.ClosureLeakage
