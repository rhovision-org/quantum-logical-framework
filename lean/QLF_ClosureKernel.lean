import QLF_ClosureUnitarity
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals

set_option linter.unusedVariables false

/-!
# QLF_ClosureKernel — **every channel factors through its first closure; the vacuum renews itself**

Second milestone of the closure-algebra programme of issue #207 (PZ1 and the seed of PZ2),
continuing [`QLF_ClosureUnitarity`](QLF_ClosureUnitarity.lean). See
[`Closure_Unitarity.md`](../Closure_Unitarity.md) §7.

## The closure kernel

For a seed `s` and a threshold `m`, a **first closure** of length `k ≥ m` is a continuation `c`
with `s ++ c` balanced and no `s ++ c.take j` balanced for `m ≤ j < k` (`firstFamily`). Its
signed sum is the **kernel amplitude** `F_k(s) = Σ φ(s ++ c)` (`kernelAmp`). For the vacuum with
`m = 1` the first closures are exactly the primes of [`QLF_FirstReturn`](QLF_FirstReturn.lean),
and `K_k := F_k(∅)` is the **prime closure kernel** (`primeKernel`).

## The factorization (PZ2 seed)

> **`closure_factorization`** — for every seed `s` and `m ≤ L`,
> `A_L(s) = Σ_{k = m}^{L} F_k(s) · A_{L−k}(∅)`.

Every closing history splits uniquely at its first closure past `m` into a first closure and a
vacuum closure (`balanced_drop`), and the phase factorizes across the split (`phase_split`,
from the fold being a monoid homomorphism and each factor being `±I`). This is the signed version of
the Dyson bijection `card_balanced_eq_sum_prime`: the counting identity of `QLF_FirstReturn` lifted
to amplitudes, so cancellation is carried through, not discarded.

## The renewal (PZ1b, scalar channel)

With `s = ∅`, `m = 1` it is the renewal equation of the dressed vacuum amplitude,

    A_0(∅) = 1,   A_L(∅) = Σ_{k=1}^{L} K_k · A_{L−k}(∅)  (L ≥ 1),

that is `G = 1 + K G` (`vacuum_renewal`), the signed form of the issue's `U = 1 + A U`. With
`s` open and `m = 0` it says `G_s = F_s · G_∅`: **the dressed vacuum factor is shared by every
channel**, and channels differ only in their first-closure kernel `F_s`. So whatever pole structure
`G_∅ = (1 − K)⁻¹` acquires under a continuum rendering is common to all channels; only residues are
channel-specific. That last sentence is a reading; the identity is the theorem.

## Zeros live in the kernel

Because `A_0(∅) = 1`, the factorization can be inverted order by order: if `A_L(s) = 0` for all
`L` then `F_k(s) = 0` for all `k` (`kernel_zero_of_amplitude_zero`). So the all-orders
interference zero of the anti-Hermitian seed `^<` is a zero of its **first-closure kernel**, not
an accident of the dressing (`upLeft_kernel_zero`). The vacuum kernel itself is not zero:
`K_2 = −8`, `K_4 = 56` (`primeKernel_two`, `primeKernel_four`).

No axioms; the numerical cross-checks use `native_decide`.
-/

namespace QLF.ClosureKernel

open QLF QLF.PhaseRule QLF.ClosureUnitarity

-- ==========================================
-- §1  Balance and phase across a split
-- ==========================================

theorem balanced_append {a b : List Twist} (ha : countBalanced a) (hb : countBalanced b) :
    countBalanced (a ++ b) := by
  unfold countBalanced at ha hb ⊢
  simp only [List.count_append]
  omega

theorem balanced_of_append {a b : List Twist} (ha : countBalanced a)
    (hab : countBalanced (a ++ b)) : countBalanced b := by
  unfold countBalanced at ha hab ⊢
  simp only [List.count_append] at hab
  omega

/-- **The phase factorizes across a closure point.** -/
theorem phase_mul {a b : List Twist} (ha : countBalanced a) (hb : countBalanced b) :
    predictedPhase (a ++ b) = predictedPhase a * predictedPhase b := by
  have hab := balanced_append ha hb
  have h := fold_append a b
  rw [fold_eq_predictedPhase hab, fold_eq_predictedPhase ha, fold_eq_predictedPhase hb,
    smul_mul_smul_comm, mul_one] at h
  have h00 := congrArg (fun A : M => A 0 0) h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  exact_mod_cast h00

theorem balanced_drop {s c : List Twist} {k : ℕ} (hk : countBalanced (s ++ c.take k))
    (hc : countBalanced (s ++ c)) : countBalanced (c.drop k) := by
  have hsplit : s ++ c = (s ++ c.take k) ++ c.drop k := by
    rw [List.append_assoc, List.take_append_drop]
  rw [hsplit] at hc
  exact balanced_of_append hk hc

theorem phase_split {s c : List Twist} {k : ℕ} (hk : countBalanced (s ++ c.take k))
    (hc : countBalanced (s ++ c)) :
    predictedPhase (s ++ c) = predictedPhase (s ++ c.take k) * predictedPhase (c.drop k) := by
  have hsplit : s ++ c = (s ++ c.take k) ++ c.drop k := by
    rw [List.append_assoc, List.take_append_drop]
  rw [hsplit]
  exact phase_mul hk (balanced_drop hk hc)

-- ==========================================
-- §2  First closures and the kernel
-- ==========================================

/-- **First closures** of `seed` of length `k`, counting only closure points at or after `m`. -/
def firstFamily (seed : List Twist) (m k : ℕ) : Finset (List Twist) :=
  ((words k).filter (fun c => decide (countBalanced (seed ++ c) ∧
    ∀ j ∈ List.range k, m ≤ j → ¬ countBalanced (seed ++ c.take j)))).toFinset

theorem mem_firstFamily (seed : List Twist) (m k : ℕ) (c : List Twist) :
    c ∈ firstFamily seed m k ↔ c.length = k ∧ countBalanced (seed ++ c) ∧
      ∀ j, j < k → m ≤ j → ¬ countBalanced (seed ++ c.take j) := by
  simp [firstFamily, mem_words, List.mem_range]

/-- The **kernel amplitude** `F_k(s)`: the signed sum over first closures. -/
def kernelAmp (seed : List Twist) (m k : ℕ) : ℤ :=
  ∑ c ∈ firstFamily seed m k, predictedPhase (seed ++ c)

/-- The **prime closure kernel** `K_k`: signed sum over the primes of length `k`. -/
def primeKernel (k : ℕ) : ℤ := kernelAmp [] 1 k

-- ==========================================
-- §3  The factorization
-- ==========================================

/-- The first closure point past `m` is unique. -/
theorem first_unique {s c : List Twist} {m k₁ k₂ : ℕ} (hm₁ : m ≤ k₁) (hm₂ : m ≤ k₂)
    (h₁ : c.take k₁ ∈ firstFamily s m k₁) (h₂ : c.take k₂ ∈ firstFamily s m k₂) :
    k₁ = k₂ := by
  rw [mem_firstFamily] at h₁ h₂
  obtain ⟨-, hb₁, hn₁⟩ := h₁
  obtain ⟨-, hb₂, hn₂⟩ := h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply hn₂ k₁ hlt hm₁
    rw [List.take_take, min_eq_left hlt.le]
    exact hb₁
  · apply hn₁ k₂ hgt hm₂
    rw [List.take_take, min_eq_left hgt.le]
    exact hb₂

/-- A closing continuation has a first closure point past `m`, whenever `m ≤ |c|`. -/
theorem first_exists {s c : List Twist} {m : ℕ} (hm : m ≤ c.length)
    (hc : countBalanced (s ++ c)) :
    ∃ k, m ≤ k ∧ k ≤ c.length ∧ c.take k ∈ firstFamily s m k := by
  classical
  have hex : ∃ k, m ≤ k ∧ countBalanced (s ++ c.take k) :=
    ⟨c.length, hm, by rw [List.take_length]; exact hc⟩
  have hk := Nat.find_spec hex
  have hle : Nat.find hex ≤ c.length :=
    Nat.find_min' hex ⟨hm, by rw [List.take_length]; exact hc⟩
  refine ⟨Nat.find hex, hk.1, hle, ?_⟩
  rw [mem_firstFamily]
  refine ⟨by rw [List.length_take]; omega, hk.2, ?_⟩
  intro j hj hmj hb
  rw [List.take_take, min_eq_left hj.le] at hb
  exact Nat.find_min hex hj ⟨hmj, hb⟩

/-- **The closure factorization.** Every channel's signed amplitude is its first-closure kernel
    convolved with the dressed vacuum amplitude: `A_L(s) = Σ_{k=m}^{L} F_k(s) · A_{L−k}(∅)`. -/
theorem closure_factorization (s : List Twist) (m L : ℕ) (hmL : m ≤ L) :
    signedAmplitude s L =
      ∑ k ∈ Finset.Icc m L, kernelAmp s m k * signedAmplitude [] (L - k) := by
  classical
  unfold signedAmplitude kernelAmp
  have hpart : closureFamily s L = (Finset.Icc m L).biUnion
      (fun k => (closureFamily s L).filter (fun c => c.take k ∈ firstFamily s m k)) := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hc
      have hc' := (mem_closureFamily s L c).1 hc
      obtain ⟨k, hmk, hkl, hf⟩ := first_exists (by omega : m ≤ c.length) hc'.2
      exact ⟨k, ⟨hmk, by omega⟩, hc, hf⟩
    · rintro ⟨k, -, hc, -⟩
      exact hc
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc m L))
      (fun k => (closureFamily s L).filter (fun c => c.take k ∈ firstFamily s m k)) := by
    intro k₁ hk₁ k₂ hk₂ hne
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk₁ hk₂
    apply Finset.disjoint_left.mpr
    intro c h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact hne (first_unique hk₁.1 hk₂.1 h1.2 h2.2)
  rw [hpart, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_bij' (fun c _ => (c.take k, c.drop k)) (fun pq _ => pq.1 ++ pq.2)
  case hi =>
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hc, hf⟩ := hc
    have hc' := (mem_closureFamily s L c).1 hc
    have hf' := (mem_firstFamily s m k _).1 hf
    rw [Finset.mem_product]
    refine ⟨hf, ?_⟩
    rw [mem_closureFamily]
    refine ⟨by rw [List.length_drop]; omega, ?_⟩
    rw [List.nil_append]
    exact balanced_drop hf'.2.1 hc'.2
  case hj =>
    intro pq hpq
    obtain ⟨p, q⟩ := pq
    rw [Finset.mem_product] at hpq
    obtain ⟨hp, hq⟩ := hpq
    have hp' := (mem_firstFamily s m k p).1 hp
    have hq' := (mem_closureFamily [] (L - k) q).1 hq
    rw [List.nil_append] at hq'
    have htake : (p ++ q).take k = p := by rw [← hp'.1]; exact List.take_left
    rw [Finset.mem_filter, mem_closureFamily, htake]
    refine ⟨⟨by rw [List.length_append, hp'.1, hq'.1]; omega, ?_⟩, hp⟩
    rw [← List.append_assoc]
    exact balanced_append hp'.2.1 hq'.2
  case left_neg =>
    intro c _
    exact List.take_append_drop k c
  case right_neg =>
    intro pq hpq
    obtain ⟨p, q⟩ := pq
    rw [Finset.mem_product] at hpq
    have hp' := (mem_firstFamily s m k p).1 hpq.1
    rw [← hp'.1]
    simp
  case h =>
    intro c hc
    rw [Finset.mem_filter] at hc
    have hc' := (mem_closureFamily s L c).1 hc.1
    have hf' := (mem_firstFamily s m k _).1 hc.2
    rw [List.nil_append]
    exact phase_split hf'.2.1 hc'.2

-- ==========================================
-- §4  The vacuum renewal and the channel factorization
-- ==========================================

/-- The bare vacuum amplitude: only the empty history closes in zero steps. -/
theorem vacuum_amp_zero : signedAmplitude [] 0 = 1 := by decide

/-- **PZ1b — the vacuum renewal `G = 1 + K G`.** For `L ≥ 1` the dressed vacuum amplitude is the
    prime kernel convolved with itself. -/
theorem vacuum_renewal (L : ℕ) (hL : 1 ≤ L) :
    signedAmplitude [] L = ∑ k ∈ Finset.Icc 1 L, primeKernel k * signedAmplitude [] (L - k) :=
  closure_factorization [] 1 L hL

/-- **PZ2 seed — every channel factors through its first closure**: `G_s = F_s · G_∅`. -/
theorem channel_factorization (s : List Twist) (L : ℕ) :
    signedAmplitude s L =
      ∑ k ∈ Finset.Icc 0 L, kernelAmp s 0 k * signedAmplitude [] (L - k) :=
  closure_factorization s 0 L (Nat.zero_le L)

-- ==========================================
-- §5  Zeros live in the kernel
-- ==========================================

theorem Icc_zero_eq_range (k : ℕ) : Finset.Icc 0 k = Finset.range (k + 1) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

/-- **An all-orders zero is a zero of the first-closure kernel.** Since `A_0(∅) = 1`, the
    channel factorization inverts order by order. -/
theorem kernel_zero_of_amplitude_zero (s : List Twist) (h : ∀ L, signedAmplitude s L = 0) :
    ∀ k, kernelAmp s 0 k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hf := channel_factorization s k
    rw [h k, Icc_zero_eq_range, Finset.sum_range_succ, Nat.sub_self, vacuum_amp_zero,
      mul_one] at hf
    have hrest : ∑ j ∈ Finset.range k, kernelAmp s 0 j * signedAmplitude [] (k - j) = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [ih j (Finset.mem_range.1 hj), zero_mul])
    rw [hrest, zero_add] at hf
    exact hf.symm

/-- **The `^<` zero is in its kernel**: no first closure of `^<` survives cancellation, at any
    length. -/
theorem upLeft_kernel_zero (k : ℕ) : kernelAmp [Twist.up, Twist.left] 0 k = 0 :=
  kernel_zero_of_amplitude_zero _ upLeft_forbidden_all_orders k

/-- The vacuum kernel is not zero: the eight Hermitian pairs, each `−I`. -/
theorem primeKernel_two : primeKernel 2 = -8 := by native_decide

/-- At length four the signed prime sum is `56`. -/
theorem primeKernel_four : primeKernel 4 = 56 := by native_decide

/-- Cross-check of the renewal at `L = 4`: `A_4(∅) = K_2 A_2 + K_4 A_0 = (−8)(−8) + 56 = 120`,
    the registry's signed census. -/
theorem vacuum_amp_four : signedAmplitude [] 4 = 120 := by native_decide

-- ==========================================
-- §6  The resolvent, as a formal power series (PZ1c)
-- ==========================================

/-- The dressed vacuum amplitude as a generating function `G(z) = Σ A_L(∅) z^L`. -/
def vacuumSeries : PowerSeries ℤ := PowerSeries.mk (fun L => signedAmplitude [] L)

/-- The prime kernel as a generating function `K(z) = Σ_{k ≥ 1} K_k z^k` (no constant term:
    the empty history is not a prime). -/
def kernelSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun k => if k = 0 then 0 else primeKernel k)

theorem sum_Icc_one (L : ℕ) (g : ℕ → ℤ) :
    ∑ k ∈ Finset.Icc 1 L, g k = ∑ k ∈ Finset.range L, g (k + 1) := by
  have h : Finset.Icc 1 L = Finset.Ico 1 (L + 1) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_comm]

/-- **PZ1c — the resolvent `G = 1 + K G`, as an identity of formal power series.** -/
theorem vacuum_resolvent : vacuumSeries = 1 + kernelSeries * vacuumSeries := by
  ext L
  rw [map_add, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ', PowerSeries.coeff_one]
  simp only [vacuumSeries, kernelSeries, PowerSeries.coeff_mk, ↓reduceIte, zero_mul, add_zero]
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp [vacuum_amp_zero]
  · have hL0 : L ≠ 0 := by omega
    simp only [hL0, ↓reduceIte, zero_add]
    rw [vacuum_renewal L hL, sum_Icc_one]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Nat.add_one_ne_zero, ↓reduceIte]

/-- **…so `G = (1 − K)⁻¹`**: `G · (1 − K) = 1`. -/
theorem vacuum_resolvent_inverse : vacuumSeries * (1 - kernelSeries) = 1 := by
  have h := vacuum_resolvent
  calc vacuumSeries * (1 - kernelSeries)
      = vacuumSeries - kernelSeries * vacuumSeries := by ring
    _ = 1 := by rw [sub_eq_iff_eq_add]; exact h

theorem closure_kernel_summary : True := trivial

end QLF.ClosureKernel
