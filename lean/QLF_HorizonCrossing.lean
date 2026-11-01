import QLF_ProductWalk
import QLF_PhaseRule
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.SpecificLimits.Normed

set_option linter.unusedVariables false

/-!
# QLF_HorizonCrossing — the keep/flip ratio of the horizon crossing tends to `1`

[`BLACK-HOLES.md`](../BLACK-HOLES.md) §4a tests the spatial↔gauge crossing `H` (the `Z` axis
exchanged with the gauge pair, `/ ↔ +`, `\ ↔ −`) on balanced histories. It preserves balance and
fails to preserve the fold, and the census splits every length into a **kept** channel
(`fold (H h) = fold h`) and a **flipped** one (`fold (H h) = −fold h`):

| `L` | `W_keep` | `W_flip` | `R(L)` |
|---:|---:|---:|---|
| 2 | 8 | 0 | ∞ |
| 4 | 136 | 32 | `17/4` |
| 6 | 3392 | 1728 | `53/27` |
| 8 | 110248 | 79872 | `13781/9984` |

and leaves the shape of `R(L) = W_keep/W_flip` open, with three possible answers: `R → 1`,
`R → c > 1`, or `R < 1` eventually. Pre-registered in
[`horizon_crossing.py`](../horizon_crossing.py): `D_L / W_L → 0`, hence `R → 1`.

**Answer: `R(L) → 1` from above. The rebasing channel is strictly ahead at every length, and its lead
vanishes.**

## The three steps

1. **The crossing sign is a one-bit cocycle** (`crossing_fold`). By the phase rule
   ([`QLF_PhaseRule`](QLF_PhaseRule.lean)) a balanced fold is `(−1)^(#neg + inversions)`. `H` keeps
   every sign and turns `Z` letters into gauge letters and back, so the only thing it changes is
   which `Z`s stand before an `X` or `Y`. Summed, `fold (H h) = (−1)^{c(h)} • fold h`, where `c(h)`
   counts the pairs "a `Z`-or-gauge twist, then later an `X`-or-`Y` twist" (`crossCount`). Read as
   a walk: carry one bit, flip it on every `Z`/gauge step, and pay `−1` for every `X`/`Y` step taken
   while it is set.

2. **The signed census collapses to the pure-pair histories** (`dsum_eq`). Cut a history into
   aligned pairs of twists. Swapping the first *mixed* pair (one `X`/`Y` twist and one
   `Z`/gauge twist) changes `c` by exactly one and preserves balance, and it is an involution
   (`nonpure_facts`, `swapFirst_swapFirst`), so every history with a mixed pair cancels against
   its partner. A history made only of pure pairs has `c` even (`pure_even`). So
   `D_L = W_keep − W_flip` **counts** the pure-pair histories, and the planar split of
   [`QLF_ProductWalk`](QLF_ProductWalk.lean) counts those:

       D_{2n} = Σₖ C(n,k) · C(2k,k)² · C(2n−2k, n−k)²        (signedCount)

   (In transfer-matrix terms: the bit-augmented step matrix `T = [[a, c], [c, −a]]` squares to
   `(a² + c²)·I`, so the signed census is a walk in *pair steps*. The involution is that identity
   counted.)

3. **The signed census is exponentially thinner** (`crossRatio_tendsto_zero`).
   `D_{2n} ≤ 32ⁿ` (`signedCount_le`), while `64ⁿ ≤ W_{2n} · (n+1)²(2n+1)⁴` (`walkCount_lower`).
   So `D_L / W_L ≤ 32·(n+1)⁶/2^{n+1}` and tends to `0`, and since
   `R = (W + D)/(W − D) = (1 + D/W)/(1 − D/W)` it tends to `1` (`keep_flip_tendsto_one`).
   Numerically `D_L / W_L ≈ 2^{1 − L/2}`, so the ratio halves every two steps; the Lean bound is
   cruder and only needs to reach zero.

`D_L > 0` at every even length (`signedCount_pos`), so `W_flip < W_keep` always
(`flip_lt_keep`): **`R < 1` eventually is ruled out, not merely unobserved.** The table above is
recovered from the closed form (`keep_flip_four`, `keep_flip_six`, `keep_flip_eight`), and
`keep_is_fold_kept` / `flip_is_fold_flipped` tie the counted channels to the fold itself.

## What this says, and what it does not

Within every accessible depth the rebasing (fold-kept) channel happens in more ways, and in the
deep limit the two spin-character channels become equally numerous. Read in the nested-black-hole
picture: a shallow crossing is a rebasing; a deep crossing is an even split between rebasing and
spin-character flip. This counts histories under the crossing `H` of `BLACK-HOLES.md` §4a. Whether
a physical horizon *induces* `H` is the open bridge recorded in
[`QLF_HorizonBasis`](QLF_HorizonBasis.lean), and nothing here addresses it.

No axioms.
-/

namespace QLF.HorizonCrossing

open Finset Filter Topology QLF QLF.PhaseRule QLF.PolyaTransience QLF.ProductWalk

-- ==========================================
-- The crossing and its cocycle
-- ==========================================

/-- **The spatial↔gauge crossing** of `BLACK-HOLES.md` §4a: the `Z` axis exchanged with the gauge
    pair, sign for sign (`/ ↔ +`, `\ ↔ −`), every other twist fixed. -/
def hCross : Twist → Twist
  | Twist.up        => Twist.up
  | Twist.down      => Twist.down
  | Twist.left      => Twist.left
  | Twist.right     => Twist.right
  | Twist.slash     => Twist.plus
  | Twist.backslash => Twist.minus
  | Twist.plus      => Twist.slash
  | Twist.minus     => Twist.backslash

theorem hCross_hCross (t : Twist) : hCross (hCross t) = t := by cases t <;> rfl

theorem count_map_hCross (ts : List Twist) (t : Twist) :
    (ts.map hCross).count t = ts.count (hCross t) := by
  induction ts with
  | nil => rfl
  | cons a r ih => cases a <;> cases t <;> simp +decide [hCross, List.count_cons, ih]

/-- The crossing preserves balance: it permutes the four conjugate pairs among themselves. -/
theorem countBalanced_map_hCross {ts : List Twist} (h : countBalanced ts) :
    countBalanced (ts.map hCross) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [count_map_hCross, count_map_hCross]; exact h1
  · rw [count_map_hCross, count_map_hCross]; exact h2
  · rw [count_map_hCross, count_map_hCross]; exact h4
  · rw [count_map_hCross, count_map_hCross]; exact h3

theorem isNegTwist_hCross (t : Twist) : isNegTwist (hCross t) = isNegTwist t := by
  cases t <;> rfl

/-- The crossing keeps every sign. -/
theorem negCount_map_hCross (ts : List Twist) : negCount (ts.map hCross) = negCount ts := by
  simp only [negCount, List.countP_map, Function.comp_def, isNegTwist_hCross]

theorem marker_cons (t : Twist) (r : List Twist) :
    marker (t :: r) = isPlane1 t :: marker r := rfl

/-- How many `X`/`Y` twists a history holds (the `Plane1` letters `^ v < >`). -/
def xyCount (ts : List Twist) : ℕ := (marker ts).count true

theorem xyCount_cons (t : Twist) (r : List Twist) :
    xyCount (t :: r) = (if isPlane1 t then 1 else 0) + xyCount r := by
  cases t <;> simp [xyCount, marker, isPlane1, List.count_cons] <;> omega

/-- **The crossing cocycle**: the number of pairs "a `Z`-or-gauge twist, then later an `X`-or-`Y`
    twist". Equivalently, carry one bit that flips on every `Z`/gauge step, and count the `X`/`Y`
    steps taken while it is set. -/
def crossCount : List Twist → ℕ
  | [] => 0
  | t :: r => (if isPlane1 t then 0 else xyCount r) + crossCount r

theorem crossCount_cons (t : Twist) (r : List Twist) :
    crossCount (t :: r) = (if isPlane1 t then 0 else xyCount r) + crossCount r := rfl

/-- **The crossing sign** `χ_H(h) = (−1)^{crossCount h}`. -/
def crossSign (ts : List Twist) : ℤ := (-1) ^ crossCount ts

theorem crossSign_eq_or (ts : List Twist) : crossSign ts = 1 ∨ crossSign ts = -1 :=
  neg_one_pow_eq_or ℤ _

/-- The `X` and `Y` letters of the axis word are the `X`/`Y` twists. -/
theorem xy_axis_count (ts : List Twist) :
    (axisWord ts).count Axis.X + (axisWord ts).count Axis.Y = xyCount ts := by
  induction ts with
  | nil => rfl
  | cons t r ih =>
      rw [axisWord_cons, xyCount_cons]
      cases t <;> simp [axisOf, List.count_cons, isPlane1] <;> omega

/-- The crossing leaves the `X` count of the axis word alone. -/
theorem count_X_map_hCross (r : List Twist) :
    (axisWord (r.map hCross)).count Axis.X = (axisWord r).count Axis.X := by
  rw [count_axisWord_X, count_axisWord_X, count_map_hCross, count_map_hCross]; rfl

/-- And the `Y` count. -/
theorem count_Y_map_hCross (r : List Twist) :
    (axisWord (r.map hCross)).count Axis.Y = (axisWord r).count Axis.Y := by
  rw [count_axisWord_Y, count_axisWord_Y, count_map_hCross, count_map_hCross]; rfl

/-- **The inversion counts before and after the crossing differ by the cocycle**, mod 2. `Y`–`X`
    inversions are untouched; a `Z` inverts every later `X`/`Y`, and after the crossing the gauge
    letters do that job instead, so the two counts together see every `Z`-or-gauge letter once. -/
theorem invCount_cross (ts : List Twist) :
    (invCount (axisWord (ts.map hCross)) + invCount (axisWord ts)) % 2 = crossCount ts % 2 := by
  induction ts with
  | nil => rfl
  | cons t r ih =>
      have hX := count_X_map_hCross r
      have hY := count_Y_map_hCross r
      have hxy := xy_axis_count r
      simp only [List.map_cons, axisWord_cons, invCount_cons, crossCount_cons]
      cases t <;>
        simp only [hCross, axisOf, isPlane1, countP_invPair_I, countP_invPair_X,
          countP_invPair_Y, countP_invPair_Z, hX, hY, if_true, if_false,
          Bool.false_eq_true] <;>
        omega

/-- **The crossing acts on a balanced fold by the cocycle sign**:
    `fold (H h) = χ_H(h) • fold h`. -/
theorem crossing_fold {ts : List Twist} (h : countBalanced ts) :
    twistMatrixFold (ts.map hCross) = ((crossSign ts : ℤ) : ℂ) • twistMatrixFold ts := by
  rw [phase_rule (countBalanced_map_hCross h), phase_rule h, smul_smul, negCount_map_hCross]
  congr 1
  have hpar := invCount_cross ts
  unfold crossSign
  push_cast
  rw [← pow_add, neg_one_pow_eq_pow_mod_two (R := ℂ) (negCount ts + _),
    neg_one_pow_eq_pow_mod_two (R := ℂ) (crossCount ts + _)]
  congr 1
  omega

/-- **The cocycle is the keep/flip observable.** On a balanced history, the crossing keeps the fold
    exactly when `χ_H = +1`. -/
theorem fold_kept_iff {ts : List Twist} (h : countBalanced ts) :
    twistMatrixFold (ts.map hCross) = twistMatrixFold ts ↔ crossSign ts = 1 := by
  rw [crossing_fold h]
  rcases crossSign_eq_or ts with hc | hc
  · rw [hc]; simp
  · rw [hc]
    constructor
    · intro heq
      exfalso
      have heq' := congrFun (congrFun heq 0) 0
      rcases phase_rule_real h with h1 | h1 <;> rw [h1] at heq' <;>
        norm_num [Matrix.smul_apply] at heq'
    · intro h'; norm_num at h'

-- ==========================================
-- The census: balanced histories, signed and split
-- ==========================================

/-- Balanced histories of length `L` (the set `card_balanced_twist` counts). -/
def balancedSet (L : ℕ) : Finset (List Twist) :=
  (words Twist L).filter (fun ts => decide (countBalanced ts))

theorem countBalanced_of_mem {L : ℕ} {ts : List Twist} (h : ts ∈ balancedSet L) :
    countBalanced ts :=
  of_decide_eq_true (Finset.mem_filter.mp h).2

/-- **The signed census** `D_L = Σ χ_H` over balanced histories of length `L`. -/
def Dsum (L : ℕ) : ℤ := ∑ ts ∈ balancedSet L, crossSign ts

/-- The rebasing channel: balanced histories whose fold the crossing keeps. -/
def Wkeep (L : ℕ) : ℕ := ((balancedSet L).filter (fun ts => crossSign ts = 1)).card

/-- The flip channel: balanced histories whose fold the crossing negates. -/
def Wflip (L : ℕ) : ℕ := ((balancedSet L).filter (fun ts => crossSign ts = -1)).card

open Classical in
/-- `Wkeep` counts exactly the histories whose fold the crossing keeps. -/
theorem keep_is_fold_kept (L : ℕ) :
    Wkeep L = ((balancedSet L).filter
      (fun ts => twistMatrixFold (ts.map hCross) = twistMatrixFold ts)).card := by
  unfold Wkeep
  congr 1
  apply Finset.filter_congr
  intro ts hts
  exact (fold_kept_iff (countBalanced_of_mem hts)).symm

open Classical in
/-- `Wflip` counts exactly the histories whose fold the crossing changes. -/
theorem flip_is_fold_flipped (L : ℕ) :
    Wflip L = ((balancedSet L).filter
      (fun ts => twistMatrixFold (ts.map hCross) ≠ twistMatrixFold ts)).card := by
  unfold Wflip
  congr 1
  apply Finset.filter_congr
  intro ts hts
  rw [Ne, fold_kept_iff (countBalanced_of_mem hts)]
  rcases crossSign_eq_or ts with hc | hc <;> rw [hc] <;> decide

theorem flip_filter_eq (L : ℕ) :
    (balancedSet L).filter (fun ts => crossSign ts = -1) =
      (balancedSet L).filter (fun ts => ¬ crossSign ts = 1) := by
  apply Finset.filter_congr
  intro ts _
  rcases crossSign_eq_or ts with h | h <;> rw [h] <;> decide

/-- The two channels exhaust the balanced histories: `W_keep + W_flip = W_L`. -/
theorem keep_add_flip (L : ℕ) : Wkeep L + Wflip L = walkCount L := by
  unfold Wkeep Wflip
  rw [flip_filter_eq, Finset.card_filter_add_card_filter_not (fun ts => crossSign ts = 1)]
  exact card_balanced_twist L

/-- And their difference is the signed census: `W_keep − W_flip = D_L`. -/
theorem keep_sub_flip (L : ℕ) : (Wkeep L : ℤ) - Wflip L = Dsum L := by
  have h1 : ∑ ts ∈ (balancedSet L).filter (fun ts => crossSign ts = 1), crossSign ts =
      (((balancedSet L).filter (fun ts => crossSign ts = 1)).card : ℤ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun ts hts => (Finset.mem_filter.mp hts).2)]
    simp
  have h2 : ∑ ts ∈ (balancedSet L).filter (fun ts => ¬ crossSign ts = 1), crossSign ts =
      -(((balancedSet L).filter (fun ts => crossSign ts = -1)).card : ℤ) := by
    rw [← flip_filter_eq,
      Finset.sum_congr rfl (g := fun _ => (-1 : ℤ)) (fun ts hts => (Finset.mem_filter.mp hts).2)]
    simp
  unfold Dsum Wkeep Wflip
  rw [← Finset.sum_filter_add_sum_filter_not (balancedSet L) (fun ts => crossSign ts = 1), h1, h2]
  ring

-- ==========================================
-- The involution: swap the first mixed aligned pair
-- ==========================================

/-- A marker word is **pure-paired** when each aligned pair of positions lies in one plane. -/
def pureM : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => (a == b) && pureM r

theorem pureM_cons2 (a b : Bool) (r : List Bool) : pureM (a :: b :: r) = ((a == b) && pureM r) :=
  rfl

/-- **Swap the first mixed aligned pair** — the sign-reversing involution. -/
def swapFirst : List Twist → List Twist
  | [] => []
  | [a] => [a]
  | a :: b :: r => if isPlane1 a = isPlane1 b then a :: b :: swapFirst r else b :: a :: r

theorem swapFirst_pure {a b : Twist} (r : List Twist) (h : isPlane1 a = isPlane1 b) :
    swapFirst (a :: b :: r) = a :: b :: swapFirst r := by
  simp only [swapFirst, if_pos h]

theorem swapFirst_mixed {a b : Twist} (r : List Twist) (h : ¬ isPlane1 a = isPlane1 b) :
    swapFirst (a :: b :: r) = b :: a :: r := by
  simp only [swapFirst, if_neg h]

theorem swapFirst_perm : ∀ l : List Twist, (swapFirst l).Perm l
  | [] => List.Perm.refl _
  | [a] => List.Perm.refl _
  | a :: b :: r => by
      by_cases h : isPlane1 a = isPlane1 b
      · rw [swapFirst_pure r h]; exact ((swapFirst_perm r).cons b).cons a
      · rw [swapFirst_mixed r h]; exact List.Perm.swap a b r

theorem swapFirst_swapFirst : ∀ l : List Twist, swapFirst (swapFirst l) = l
  | [] => rfl
  | [a] => rfl
  | a :: b :: r => by
      by_cases h : isPlane1 a = isPlane1 b
      · rw [swapFirst_pure r h, swapFirst_pure _ h, swapFirst_swapFirst r]
      · rw [swapFirst_mixed r h, swapFirst_mixed r (Ne.symm h)]

theorem countBalanced_of_perm {l₁ l₂ : List Twist} (hp : l₁.Perm l₂) (h : countBalanced l₂) :
    countBalanced l₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hp.count_eq, hp.count_eq]; exact h1, by rw [hp.count_eq, hp.count_eq]; exact h2,
    by rw [hp.count_eq, hp.count_eq]; exact h3, by rw [hp.count_eq, hp.count_eq]; exact h4⟩

theorem xyCount_swapFirst (r : List Twist) : xyCount (swapFirst r) = xyCount r := by
  unfold xyCount marker
  exact ((swapFirst_perm r).map isPlane1).count_eq true

private theorem mixed_beq (x y : Bool) (h : ¬ x = y) : (y == x) = false := by
  revert h; cases x <;> cases y <;> decide

/-- **The involution reverses the sign off the pure-pair histories.** If some aligned pair is mixed,
    swapping the first one keeps the history mixed, moves it, and changes the cocycle by one. -/
theorem nonpure_facts : ∀ l : List Twist, pureM (marker l) = false →
    pureM (marker (swapFirst l)) = false ∧ swapFirst l ≠ l ∧
      (crossCount (swapFirst l) + crossCount l) % 2 = 1
  | [], h => by simp [pureM, marker] at h
  | [_], h => by simp [pureM, marker] at h
  | a :: b :: r, h => by
      have hxy := xyCount_swapFirst r
      rw [marker_cons, marker_cons, pureM_cons2] at h
      by_cases hab : isPlane1 a = isPlane1 b
      · have hr : pureM (marker r) = false := by
          rw [hab, beq_self_eq_true, Bool.true_and] at h; exact h
        obtain ⟨h1, h2, h3⟩ := nonpure_facts r hr
        rw [swapFirst_pure r hab]
        refine ⟨?_, ?_, ?_⟩
        · rw [marker_cons, marker_cons, pureM_cons2, h1, Bool.and_false]
        · intro he; exact h2 (List.cons.inj (List.cons.inj he).2).2
        · simp only [crossCount_cons, xyCount_cons, hxy, hab]
          split_ifs <;> omega
      · rw [swapFirst_mixed r hab]
        refine ⟨?_, ?_, ?_⟩
        · rw [marker_cons, marker_cons, pureM_cons2, mixed_beq _ _ hab, Bool.false_and]
        · intro he; exact hab (by rw [(List.cons.inj he).1])
        · simp only [crossCount_cons, xyCount_cons]
          revert hab
          cases isPlane1 a <;> cases isPlane1 b <;> simp <;> omega

/-- **On a pure-pair history the cocycle is even**, so `χ_H = +1`: a pure pair either adds no
    `X`/`Y` step under the bit, or flips the bit twice around the same later `X`/`Y` steps. -/
theorem pure_even : ∀ l : List Twist, pureM (marker l) = true → crossCount l % 2 = 0
  | [], _ => rfl
  | [a], _ => by
      rw [crossCount_cons]; cases isPlane1 a <;> rfl
  | a :: b :: r, h => by
      rw [marker_cons, marker_cons, pureM_cons2, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hab, hr⟩ := h
      have ih := pure_even r hr
      simp only [crossCount_cons, xyCount_cons, hab]
      split_ifs <;> omega

/-- **The mixed histories cancel.** -/
theorem sum_nonpure_zero (L : ℕ) :
    ∑ ts ∈ (balancedSet L).filter (fun ts => ¬ pureM (marker ts) = true), crossSign ts = 0 := by
  refine Finset.sum_involution (fun ts _ => swapFirst ts) ?_ ?_ ?_ ?_
  · intro ts hts
    have hnp : pureM (marker ts) = false := by
      simpa using (Finset.mem_filter.mp hts).2
    have hpar := (nonpure_facts ts hnp).2.2
    unfold crossSign
    rw [neg_one_pow_eq_pow_mod_two (R := ℤ) (crossCount ts),
      neg_one_pow_eq_pow_mod_two (R := ℤ) (crossCount (swapFirst ts))]
    have : (crossCount ts % 2 = 0 ∧ crossCount (swapFirst ts) % 2 = 1) ∨
        (crossCount ts % 2 = 1 ∧ crossCount (swapFirst ts) % 2 = 0) := by omega
    rcases this with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> norm_num
  · intro ts hts _
    have hnp : pureM (marker ts) = false := by
      simpa using (Finset.mem_filter.mp hts).2
    exact (nonpure_facts ts hnp).2.1
  · intro ts hts
    obtain ⟨hmem, hnp⟩ := Finset.mem_filter.mp hts
    have hnp' : pureM (marker ts) = false := by simpa using hnp
    obtain ⟨hw, hbal⟩ := Finset.mem_filter.mp hmem
    have hperm := swapFirst_perm ts
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [mem_words] at hw ⊢; rw [hperm.length_eq, hw]
    · exact decide_eq_true (countBalanced_of_perm hperm (of_decide_eq_true hbal))
    · rw [(nonpure_facts ts hnp').1]; decide
  · intro ts _
    exact swapFirst_swapFirst ts

-- ==========================================
-- Counting the pure-pair histories
-- ==========================================

/-- Each letter of a marker word, doubled: the marker of a pure-pair history. -/
def dbl : List Bool → List Bool
  | [] => []
  | a :: m => a :: a :: dbl m

theorem pureM_dbl : ∀ m : List Bool, pureM (dbl m) = true
  | [] => rfl
  | a :: m => by
      show ((a == a) && pureM (dbl m)) = true
      rw [beq_self_eq_true, Bool.true_and]; exact pureM_dbl m

theorem length_dbl : ∀ m : List Bool, (dbl m).length = 2 * m.length
  | [] => rfl
  | a :: m => by
      show (dbl m).length + 1 + 1 = 2 * (m.length + 1)
      rw [length_dbl m]; ring

theorem count_dbl (b : Bool) : ∀ m : List Bool, (dbl m).count b = 2 * m.count b
  | [] => rfl
  | a :: m => by
      show (a :: a :: dbl m).count b = 2 * (a :: m).count b
      rw [List.count_cons, List.count_cons, List.count_cons, count_dbl b m]
      split_ifs <;> omega

theorem dbl_injective : ∀ {m₁ m₂ : List Bool}, dbl m₁ = dbl m₂ → m₁ = m₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [dbl] at h
  | _ :: _, [], h => by simp [dbl] at h
  | a :: m₁, b :: m₂, h => by
      simp only [dbl, List.cons.injEq] at h
      obtain ⟨rfl, -, h⟩ := h
      rw [dbl_injective h]

/-- A pure-paired marker of length `2n` is a doubled word of length `n`. -/
theorem exists_dbl : ∀ (n : ℕ) (m : List Bool), m.length = 2 * n → pureM m = true →
    ∃ m', m'.length = n ∧ m = dbl m'
  | 0, m, hl, _ => ⟨[], rfl, List.eq_nil_of_length_eq_zero (by simpa using hl)⟩
  | n + 1, [], hl, _ => by simp only [List.length_nil] at hl; omega
  | n + 1, [_], hl, _ => by simp only [List.length_singleton] at hl; omega
  | n + 1, a :: b :: r, hl, hp => by
      rw [pureM_cons2, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨hab, hr⟩ := hp
      have hlr : r.length = 2 * n := by simp only [List.length_cons] at hl; omega
      obtain ⟨m', hm'l, hm'⟩ := exists_dbl n r hlr hr
      refine ⟨a :: m', by simp [hm'l], ?_⟩
      rw [← hab, hm']; rfl

/-- **The signed census in closed form**: `Σₖ C(n,k) · C(2k,k)² · C(2n−2k,n−k)²`. -/
def signedCount (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), n.choose k * w₂ (2 * k) * w₂ (2 * (n - k))

theorem signedCount_one : signedCount 1 = 8 := by decide
theorem signedCount_two : signedCount 2 = 104 := by decide
theorem signedCount_three : signedCount 3 = 1664 := by decide
theorem signedCount_four : signedCount 4 = 30376 := by decide

/-- The pure-pair balanced histories, sorted by their (doubled) marker. -/
theorem pureBal_eq (n : ℕ) :
    (balancedSet (2 * n)).filter (fun ts => pureM (marker ts) = true) =
      (words Bool n).biUnion (fun m =>
        (words Twist (2 * n)).filter (fun ts => decide (countBalanced ts ∧ marker ts = dbl m))) := by
  ext ts
  simp only [balancedSet, Finset.mem_filter, Finset.mem_biUnion, mem_words, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hlen, hbal⟩, hp⟩
    have hml : (marker ts).length = 2 * n := by rw [length_marker, hlen]
    obtain ⟨m', hm'l, hm'⟩ := exists_dbl n (marker ts) hml hp
    exact ⟨m', hm'l, hlen, hbal, hm'⟩
  · rintro ⟨m, _, hlen, hbal, hm⟩
    exact ⟨⟨hlen, hbal⟩, by rw [hm]; exact pureM_dbl m⟩

/-- **The pure-pair balanced histories are counted by `signedCount`.** Each is a doubled marker
    `m ∈ {0,1}ⁿ` with a balanced `X`/`Y` word riffled against a balanced `Z`/gauge word, which is
    `card_fiber_marker` from the planar split. -/
theorem card_pureBal (n : ℕ) :
    ((balancedSet (2 * n)).filter (fun ts => pureM (marker ts) = true)).card = signedCount n := by
  rw [pureBal_eq]
  have hdisj : ∀ m1 ∈ words Bool n, ∀ m2 ∈ words Bool n, m1 ≠ m2 →
      Disjoint ((words Twist (2 * n)).filter
                  (fun ts => decide (countBalanced ts ∧ marker ts = dbl m1)))
               ((words Twist (2 * n)).filter
                  (fun ts => decide (countBalanced ts ∧ marker ts = dbl m2))) := by
    intro m1 _ m2 _ hne
    apply Finset.disjoint_left.mpr
    intro ts hts1 hts2
    simp only [Finset.mem_filter, decide_eq_true_eq] at hts1 hts2
    exact hne (dbl_injective (hts1.2.2.symm.trans hts2.2.2))
  rw [Finset.card_biUnion hdisj]
  have hstep1 : ∀ m ∈ words Bool n, ((words Twist (2 * n)).filter
      (fun ts => decide (countBalanced ts ∧ marker ts = dbl m))).card =
      w₂ (2 * m.count true) * w₂ (2 * (n - m.count true)) := by
    intro m hm
    have hlen := (mem_words n m).mp hm
    have hdm : dbl m ∈ words Bool (2 * n) := by rw [mem_words, length_dbl, hlen]
    rw [card_fiber_marker (2 * n) (dbl m) hdm, count_dbl, count_dbl]
    have hc : m.count true + m.count false = m.length := List.count_true_add_count_false m
    have : m.count false = n - m.count true := by omega
    rw [this]
  rw [Finset.sum_congr rfl hstep1]
  have hpart : words Bool n = (Finset.range (n + 1)).biUnion
      (fun k => (words Bool n).filter (fun m => decide (m.count true = k))) := by
    apply Finset.ext
    intro m
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, decide_eq_true_eq]
    constructor
    · intro hm
      have hlen := (mem_words n m).mp hm
      have : m.count true ≤ m.length := List.count_le_length
      exact ⟨m.count true, by omega, hm, rfl⟩
    · rintro ⟨k, _, hm, _⟩
      exact hm
  rw [hpart]
  have hdisj2 : ∀ k1 ∈ Finset.range (n + 1), ∀ k2 ∈ Finset.range (n + 1), k1 ≠ k2 →
      Disjoint ((words Bool n).filter (fun m => decide (m.count true = k1)))
               ((words Bool n).filter (fun m => decide (m.count true = k2))) := by
    intro k1 _ k2 _ hne
    apply Finset.disjoint_left.mpr
    intro m hm1 hm2
    simp only [Finset.mem_filter, decide_eq_true_eq] at hm1 hm2
    exact hne (hm1.2.symm.trans hm2.2)
  rw [Finset.sum_biUnion hdisj2]
  have hstep2 : ∀ k ∈ Finset.range (n + 1),
      (∑ m ∈ (words Bool n).filter (fun m => decide (m.count true = k)),
        w₂ (2 * m.count true) * w₂ (2 * (n - m.count true))) =
      n.choose k * w₂ (2 * k) * w₂ (2 * (n - k)) := by
    intro k _
    have hconst : ∀ m ∈ (words Bool n).filter (fun m => decide (m.count true = k)),
        w₂ (2 * m.count true) * w₂ (2 * (n - m.count true)) = w₂ (2 * k) * w₂ (2 * (n - k)) := by
      intro m hm
      simp only [Finset.mem_filter, decide_eq_true_eq] at hm
      rw [hm.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_filter_count_true]
    ring
  rw [Finset.sum_congr rfl hstep2]
  rfl

/-- **The signed census, solved**: `D_{2n} = Σₖ C(n,k) · C(2k,k)² · C(2n−2k,n−k)²`. -/
theorem dsum_eq (n : ℕ) : Dsum (2 * n) = signedCount n := by
  unfold Dsum
  rw [← Finset.sum_filter_add_sum_filter_not (balancedSet (2 * n))
    (fun ts => pureM (marker ts) = true), sum_nonpure_zero, add_zero]
  have hone : ∀ ts ∈ (balancedSet (2 * n)).filter (fun ts => pureM (marker ts) = true),
      crossSign ts = 1 := by
    intro ts hts
    unfold crossSign
    rw [neg_one_pow_eq_pow_mod_two (R := ℤ), pure_even ts (Finset.mem_filter.mp hts).2]
    rfl
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one, card_pureBal]

-- ==========================================
-- The exact table, recovered
-- ==========================================

theorem keep_flip_four : Wkeep 4 = 136 ∧ Wflip 4 = 32 := by
  have h1 := keep_add_flip 4
  have h2 := keep_sub_flip 4
  have h3 : Dsum 4 = 104 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, dsum_eq, signedCount_two] <;> norm_num
  rw [walkCount_four] at h1
  rw [h3] at h2
  omega

theorem keep_flip_six : Wkeep 6 = 3392 ∧ Wflip 6 = 1728 := by
  have h1 := keep_add_flip 6
  have h2 := keep_sub_flip 6
  have h3 : Dsum 6 = 1664 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, dsum_eq, signedCount_three] <;> norm_num
  rw [walkCount_six] at h1
  rw [h3] at h2
  omega

/-- `R(8) = 110248 / 79872 = 13781/9984`. -/
theorem keep_flip_eight : Wkeep 8 = 110248 ∧ Wflip 8 = 79872 := by
  have h1 := keep_add_flip 8
  have h2 := keep_sub_flip 8
  have h3 : Dsum 8 = 30376 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, dsum_eq, signedCount_four] <;> norm_num
  rw [walkCount_eight] at h1
  rw [h3] at h2
  omega

-- ==========================================
-- The rebasing channel is ahead at every depth
-- ==========================================

theorem w₂_two_mul (k : ℕ) : w₂ (2 * k) = Nat.centralBinom k ^ 2 := by
  unfold w₂
  rw [if_pos (by omega), Nat.mul_div_cancel_left k (by norm_num)]

theorem signedCount_pos (n : ℕ) : 0 < signedCount n := by
  have h0 : n.choose 0 * w₂ (2 * 0) * w₂ (2 * (n - 0)) ≤ signedCount n :=
    Finset.single_le_sum (f := fun k => n.choose k * w₂ (2 * k) * w₂ (2 * (n - k)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos n))
  have hpos : 0 < n.choose 0 * w₂ (2 * 0) * w₂ (2 * (n - 0)) := by
    rw [w₂_two_mul, w₂_two_mul, Nat.choose_zero_right]
    have := Nat.centralBinom_pos 0
    have := Nat.centralBinom_pos (n - 0)
    positivity
  omega

/-- **The flipped channel never catches up**: at every even length the rebasing channel happens in
    strictly more ways. `R(L) < 1` eventually is ruled out. -/
theorem flip_lt_keep (n : ℕ) : Wflip (2 * n) < Wkeep (2 * n) := by
  have h2 := keep_sub_flip (2 * n)
  rw [dsum_eq] at h2
  have := signedCount_pos n
  omega

-- ==========================================
-- … and its lead vanishes
-- ==========================================

theorem centralBinom_sq_le (k : ℕ) : Nat.centralBinom k ^ 2 ≤ 16 ^ k :=
  le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (centralBinom_sq_mul_le k)

/-- `D_{2n} ≤ 32ⁿ`. -/
theorem signedCount_le (n : ℕ) : signedCount n ≤ 32 ^ n := by
  calc signedCount n ≤ ∑ k ∈ range (n + 1), n.choose k * 16 ^ n := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [w₂_two_mul, w₂_two_mul, mul_assoc]
        apply Nat.mul_le_mul_left
        calc Nat.centralBinom k ^ 2 * Nat.centralBinom (n - k) ^ 2 ≤ 16 ^ k * 16 ^ (n - k) :=
              Nat.mul_le_mul (centralBinom_sq_le k) (centralBinom_sq_le _)
          _ = 16 ^ n := by rw [← pow_add, Nat.add_sub_cancel' hk']
    _ = 32 ^ n := by
        rw [← Finset.sum_mul, Nat.sum_range_choose, ← mul_pow]

/-- `64ⁿ ≤ W_{2n} · (n+1)² (2n+1)⁴`: one term of the planar split already carries almost all of
    `8^{2n}`. -/
theorem walkCount_lower (n : ℕ) :
    64 ^ n ≤ walkCount (2 * n) * ((n + 1) ^ 2 * (2 * n + 1) ^ 4) := by
  have hjn : n / 2 ≤ n := Nat.div_le_self n 2
  have hF2 : 2 ^ n ≤ (n + 1) * n.choose (n / 2) := by
    calc 2 ^ n = ∑ r ∈ range (n + 1), n.choose r := (Nat.sum_range_choose n).symm
      _ ≤ ∑ r ∈ range (n + 1), n.choose (n / 2) :=
          Finset.sum_le_sum (fun r _ => Nat.choose_le_middle r n)
      _ = (n + 1) * n.choose (n / 2) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hF1 : n.choose (n / 2) ^ 2 ≤ (2 * n).choose (2 * (n / 2)) := by
    rw [two_mul, two_mul, Nat.add_choose_eq, sq]
    exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => n.choose ij.1 * n.choose ij.2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_antidiagonal.mpr rfl)
  have hF3 : ∀ i ≤ n, 16 ^ i ≤ (2 * n + 1) ^ 2 * Nat.centralBinom i ^ 2 := by
    intro i hi
    have h4 : 4 ^ i ≤ (2 * n + 1) * Nat.centralBinom i := by
      have := Nat.four_pow_le_two_mul_add_one_mul_central_binom i
      rw [← Nat.centralBinom_eq_two_mul_choose] at this
      exact le_trans this (Nat.mul_le_mul_right _ (by omega))
    calc 16 ^ i = (4 ^ i) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul] <;> norm_num
      _ ≤ ((2 * n + 1) * Nat.centralBinom i) ^ 2 := Nat.pow_le_pow_left h4 2
      _ = (2 * n + 1) ^ 2 * Nat.centralBinom i ^ 2 := by ring
  have hterm : (2 * n).choose (2 * (n / 2)) * w₂ (2 * (n / 2)) * w₂ (2 * n - 2 * (n / 2))
      ≤ walkCount (2 * n) := by
    unfold walkCount
    exact Finset.single_le_sum (f := fun k => (2 * n).choose k * w₂ k * w₂ (2 * n - k))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hsub : 2 * n - 2 * (n / 2) = 2 * (n - n / 2) := by omega
  rw [hsub, w₂_two_mul, w₂_two_mul] at hterm
  have h16 : 16 ^ (n / 2) * 16 ^ (n - n / 2) = 16 ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hjn]
  have h64 : 64 ^ n = (2 ^ n) ^ 2 * 16 ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow] <;> norm_num
  calc 64 ^ n = (2 ^ n) ^ 2 * (16 ^ (n / 2) * 16 ^ (n - n / 2)) := by rw [h16, h64]
    _ ≤ ((n + 1) * n.choose (n / 2)) ^ 2 * (((2 * n + 1) ^ 2 * Nat.centralBinom (n / 2) ^ 2) *
          ((2 * n + 1) ^ 2 * Nat.centralBinom (n - n / 2) ^ 2)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hF2 2)
          (Nat.mul_le_mul (hF3 (n / 2) hjn) (hF3 (n - n / 2) (by omega)))
    _ = (n.choose (n / 2) ^ 2 * Nat.centralBinom (n / 2) ^ 2 * Nat.centralBinom (n - n / 2) ^ 2) *
          ((n + 1) ^ 2 * (2 * n + 1) ^ 4) := by ring
    _ ≤ ((2 * n).choose (2 * (n / 2)) * Nat.centralBinom (n / 2) ^ 2 *
          Nat.centralBinom (n - n / 2) ^ 2) * ((n + 1) ^ 2 * (2 * n + 1) ^ 4) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hF1))
    _ ≤ walkCount (2 * n) * ((n + 1) ^ 2 * (2 * n + 1) ^ 4) := Nat.mul_le_mul_right _ hterm

theorem walkCount_pos (n : ℕ) : 0 < walkCount (2 * n) := by
  rcases Nat.eq_zero_or_pos (walkCount (2 * n)) with h | h
  · have := walkCount_lower n
    rw [h, zero_mul] at this
    exact absurd this (Nat.not_le.mpr (by positivity))
  · exact h

/-- `D_{2n} · 2^{n+1} ≤ 32 (n+1)⁶ · W_{2n}`. -/
theorem key_bound (n : ℕ) :
    signedCount n * 2 ^ (n + 1) ≤ 32 * (n + 1) ^ 6 * walkCount (2 * n) := by
  have h1 : signedCount n * 2 ^ n ≤ 64 ^ n :=
    calc signedCount n * 2 ^ n ≤ 32 ^ n * 2 ^ n := Nat.mul_le_mul_right _ (signedCount_le n)
      _ = 64 ^ n := (mul_pow 32 2 n).symm.trans (by norm_num)
  have h2 : (2 * n + 1) ^ 4 ≤ 16 * (n + 1) ^ 4 :=
    calc (2 * n + 1) ^ 4 ≤ (2 * (n + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = 16 * (n + 1) ^ 4 := by ring
  calc signedCount n * 2 ^ (n + 1) = 2 * (signedCount n * 2 ^ n) := by ring
    _ ≤ 2 * (walkCount (2 * n) * ((n + 1) ^ 2 * (2 * n + 1) ^ 4)) :=
        Nat.mul_le_mul_left _ (h1.trans (walkCount_lower n))
    _ ≤ 2 * (walkCount (2 * n) * ((n + 1) ^ 2 * (16 * (n + 1) ^ 4))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2))
    _ = 32 * (n + 1) ^ 6 * walkCount (2 * n) := by ring

/-- `D_{2n} / W_{2n} ≤ 32 (n+1)⁶ / 2^{n+1}`. -/
theorem crossRatio_le (n : ℕ) :
    (signedCount n : ℝ) / walkCount (2 * n) ≤ 32 * (((n + 1 : ℕ) : ℝ) ^ 6 / 2 ^ (n + 1)) := by
  have hW : (0 : ℝ) < walkCount (2 * n) := by exact_mod_cast walkCount_pos n
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hk : (signedCount n : ℝ) * 2 ^ (n + 1) ≤
      32 * ((n + 1 : ℕ) : ℝ) ^ 6 * walkCount (2 * n) := by
    exact_mod_cast key_bound n
  rw [div_le_iff₀ hW]
  calc (signedCount n : ℝ) = (signedCount n : ℝ) * 2 ^ (n + 1) / 2 ^ (n + 1) :=
        (mul_div_cancel_right₀ _ h2.ne').symm
    _ ≤ 32 * ((n + 1 : ℕ) : ℝ) ^ 6 * walkCount (2 * n) / 2 ^ (n + 1) := by gcongr
    _ = 32 * (((n + 1 : ℕ) : ℝ) ^ 6 / 2 ^ (n + 1)) * walkCount (2 * n) := by ring

/-- **The signed census is negligible**: `D_L / W_L → 0`. -/
theorem crossRatio_tendsto_zero :
    Tendsto (fun n : ℕ => (signedCount n : ℝ) / walkCount (2 * n)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 32 * (((n + 1 : ℕ) : ℝ) ^ 6 / 2 ^ (n + 1))) atTop (𝓝 0) := by
    have h := ((tendsto_pow_const_div_const_pow_of_one_lt 6 (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)).const_mul 32
    rw [mul_zero] at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => by positivity) (fun n => crossRatio_le n)

/-- **`R(L) → 1`.** The keep/flip ratio of the horizon crossing tends to one: in the deep limit the
    rebasing and spin-flip channels are equally numerous, though the rebasing channel stays ahead at
    every finite depth (`flip_lt_keep`). -/
theorem keep_flip_tendsto_one :
    Tendsto (fun n : ℕ => (Wkeep (2 * n) : ℝ) / Wflip (2 * n)) atTop (𝓝 1) := by
  have hr := crossRatio_tendsto_zero
  have hlim : Tendsto (fun n : ℕ => (1 + (signedCount n : ℝ) / walkCount (2 * n)) /
      (1 - (signedCount n : ℝ) / walkCount (2 * n))) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hr |>.div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hr) (by norm_num)
    rwa [add_zero, sub_zero, div_one] at h
  refine Tendsto.congr (fun n => ?_) hlim
  have hW : (walkCount (2 * n) : ℝ) ≠ 0 := by exact_mod_cast (walkCount_pos n).ne'
  have h1 := keep_add_flip (2 * n)
  have h2 := keep_sub_flip (2 * n)
  rw [dsum_eq] at h2
  have hK : (2 : ℝ) * Wkeep (2 * n) = walkCount (2 * n) + signedCount n := by
    have : (2 : ℤ) * Wkeep (2 * n) = walkCount (2 * n) + signedCount n := by omega
    exact_mod_cast this
  have hF : (2 : ℝ) * Wflip (2 * n) = walkCount (2 * n) - signedCount n := by
    have : (2 : ℤ) * Wflip (2 * n) = (walkCount (2 * n) : ℤ) - signedCount n := by omega
    exact_mod_cast this
  set W : ℝ := walkCount (2 * n)
  set D : ℝ := signedCount n
  calc (1 + D / W) / (1 - D / W) = (W * (1 + D / W)) / (W * (1 - D / W)) :=
        (mul_div_mul_left _ _ hW).symm
    _ = (W + D) / (W - D) := by
        rw [mul_add, mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ hW]
    _ = (2 * (Wkeep (2 * n) : ℝ)) / (2 * Wflip (2 * n)) := by rw [hK, hF]
    _ = (Wkeep (2 * n) : ℝ) / Wflip (2 * n) := mul_div_mul_left _ _ two_ne_zero

end QLF.HorizonCrossing
