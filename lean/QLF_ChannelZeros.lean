import QLF_ClosureChannels

set_option linter.unusedVariables false

/-!
# QLF_ChannelZeros — **mixed spatial channels vanish at every order, and the zero is in the open amplitude**

Continues [`QLF_ClosureChannels`](QLF_ClosureChannels.lean) (issue #207, PZ2/PZ3). See
[`Closure_Unitarity.md`](../Closure_Unitarity.md) §10.

## The reversal sign

Every twist matrix is `±σ` or `±I`. Two of them anticommute exactly when they sit on **different
spatial axes** (`anti`), and otherwise commute (`twist_mul_comm`). Reversing a history therefore
reorders its factors at the cost of one sign per anticommuting pair:

> **`fold_reverse_sign`** — `U(reverse h) = (−1)^{P(h)} · U(h)`,

and the number of such pairs is fixed by the axis counts alone:

> **`pairs_eq`** — `P(h) = c_y c_x + c_y c_z + c_x c_z`,

where `c_a` counts the twists on spatial axis `a`, both signs. Since `U(reverse h) = U(h)†`
(`ClosureUnitarity.fold_reverse`), every fold is Hermitian or anti-Hermitian, and which one depends
only on the parities of the three spatial counts.

## Channel zeros

The parity of `c_a` is the parity of the channel coordinate `v_a = #(+) − #(−)`. Call a boundary
state **mixed** when `v_y v_x + v_y v_z + v_x v_z` is odd, that is, when its displacement is odd on
two or three spatial axes. Then every history in the channel folds to an anti-Hermitian matrix, and
reversal maps the channel to itself, so the channel cancels in pairs:

> **`mixed_channel_zero`** — `chanAmp v L = 0` for every `L` when `v` is mixed.

This is the channel form of `antiHermitian_seed_forbidden`, with the same mechanism. By the last-exit
factorization and `G_0 = 1`, the zero is carried by the channel's own open amplitude and not by the
shared vacuum dressing:

> **`mixed_open_zero`** — `O_n(v) = 0` for every `n` when `v` is mixed.

A channel odd on one spatial axis is Hermitian and does not cancel this way (`openAmp_up_one`).

## Open equals first arrival

Read backwards, a history that leaves the origin for good is one that reaches `v` for the first
time at its last step (`reverse_mem_firstSet`). With the reversal sign this gives

> **`openAmp_eq_firstAmp`** — `O_n(v) = F_n(v)`, and **`channel_two_sided`** —
> `G(v) = G_∅ · F(v) = F(v) · G_∅`.

No axioms.
-/

namespace QLF.ClosureChannels

open Finset QLF QLF.FirstReturn QLF.ClosureLeakage

-- ==========================================
-- §1  Which twists anticommute
-- ==========================================

/-- The axis of a twist: `0` = y (`^ v`), `1` = x (`< >`), `2` = z (`/ \`), `3` = gauge (`+ −`). -/
def axisOf : Twist → ℕ
  | .up => 0 | .down => 0 | .left => 1 | .right => 1
  | .slash => 2 | .backslash => 2 | .plus => 3 | .minus => 3

/-- Two twists **anticommute** when they lie on different spatial axes. -/
def anti (t s : Twist) : Bool :=
  axisOf t ≠ axisOf s && axisOf t ≠ 3 && axisOf s ≠ 3

theorem twist_mul_comm (t s : Twist) :
    t.toMatrix * s.toMatrix = (if anti t s then (-1 : ℂ) else 1) • (s.toMatrix * t.toMatrix) := by
  cases t <;> cases s <;>
    simp [anti, axisOf, Twist.toMatrix, PhaseRule.anti_yx, PhaseRule.anti_zx, PhaseRule.anti_zy]

/-- Moving one twist across a whole history: one sign per anticommuting factor. -/
theorem twist_mul_fold (t : Twist) (w : List Twist) :
    t.toMatrix * twistMatrixFold w =
      ((-1 : ℂ) ^ (w.countP (anti t))) • (twistMatrixFold w * t.toMatrix) := by
  induction w with
  | nil => simp [twistMatrixFold]
  | cons s w ih =>
    have hf : twistMatrixFold (s :: w) = s.toMatrix * twistMatrixFold w := rfl
    rw [hf, ← mul_assoc, twist_mul_comm, smul_mul_assoc, mul_assoc, ih, mul_smul_comm, smul_smul,
      ← mul_assoc, List.countP_cons]
    split_ifs <;> simp [pow_succ, mul_comm]

/-- The number of anticommuting ordered pairs in a history. -/
def pairs : List Twist → ℕ
  | [] => 0
  | t :: w => pairs w + w.countP (anti t)

/-- **The reversal sign.** Reversing a history costs one sign per anticommuting pair. -/
theorem fold_reverse_sign (w : List Twist) :
    twistMatrixFold w.reverse = ((-1 : ℂ) ^ pairs w) • twistMatrixFold w := by
  induction w with
  | nil => simp [twistMatrixFold, pairs]
  | cons t w ih =>
    have hf : twistMatrixFold (t :: w) = t.toMatrix * twistMatrixFold w := rfl
    rw [List.reverse_cons, ClosureUnitarity.fold_append, ih, ClosureUnitarity.fold_singleton,
      hf, twist_mul_fold, smul_smul, smul_mul_assoc, pairs, pow_add]
    congr 1
    rw [mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

-- ==========================================
-- §2  The pair count is fixed by the axis counts
-- ==========================================

/-- Twists on axis `a`, both signs. -/
def axisCount (a : ℕ) (w : List Twist) : ℕ := w.countP (fun s => axisOf s = a)

theorem axisCount_cons (a : ℕ) (s : Twist) (w : List Twist) :
    axisCount a (s :: w) = axisCount a w + if axisOf s = a then 1 else 0 := by
  simp [axisCount, List.countP_cons]

/-- The twists of `w` that anticommute with `t`: the counts on the other two spatial axes. -/
def others (t : Twist) (w : List Twist) : ℕ :=
  match axisOf t with
  | 0 => axisCount 1 w + axisCount 2 w
  | 1 => axisCount 0 w + axisCount 2 w
  | 2 => axisCount 0 w + axisCount 1 w
  | _ => 0

theorem countP_anti (t : Twist) (w : List Twist) : w.countP (anti t) = others t w := by
  induction w with
  | nil => cases t <;> simp [others, axisCount, axisOf]
  | cons s w ih =>
    rw [List.countP_cons, ih]
    cases t <;> cases s <;> simp [others, anti, axisOf, axisCount_cons] <;> omega

/-- **The pair count is the second symmetric function of the spatial axis counts.** -/
theorem pairs_eq (w : List Twist) :
    pairs w = axisCount 0 w * axisCount 1 w + axisCount 0 w * axisCount 2 w +
      axisCount 1 w * axisCount 2 w := by
  induction w with
  | nil => simp [pairs, axisCount]
  | cons t w ih =>
    rw [pairs, ih, countP_anti]
    cases t <;> simp [others, axisOf, axisCount_cons] <;> ring

-- ==========================================
-- §3  Every fold is Hermitian or anti-Hermitian, by its channel
-- ==========================================

theorem axisCount_counts (w : List Twist) :
    axisCount 0 w = w.count Twist.up + w.count Twist.down ∧
    axisCount 1 w = w.count Twist.left + w.count Twist.right ∧
    axisCount 2 w = w.count Twist.slash + w.count Twist.backslash := by
  induction w with
  | nil => simp [axisCount]
  | cons s w ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [axisCount_cons, axisCount_cons, axisCount_cons, h0, h1, h2]
    cases s <;> simp +decide [axisOf, List.count_cons] <;> omega

theorem axisCount_disp (w : List Twist) :
    (axisCount 0 w : ℤ) = (disp w).1 + 2 * w.count Twist.down ∧
    (axisCount 1 w : ℤ) = (disp w).2.1 + 2 * w.count Twist.right ∧
    (axisCount 2 w : ℤ) = (disp w).2.2.1 + 2 * w.count Twist.backslash := by
  obtain ⟨h0, h1, h2⟩ := axisCount_counts w
  simp only [disp, h0, h1, h2]
  push_cast
  refine ⟨by ring, by ring, by ring⟩

/-- A boundary state is **mixed** when it is odd on two or three spatial axes. -/
def Mixed (v : ℤ × ℤ × ℤ × ℤ) : Prop :=
  Odd (v.1 * v.2.1 + v.1 * v.2.2.1 + v.2.1 * v.2.2.1)

/-- The pair count, read through the boundary state: `P(h) = e₂(v) + 2·(…)`. -/
theorem pairs_cast (w : List Twist) : ∃ X : ℤ, (pairs w : ℤ) =
    ((disp w).1 * (disp w).2.1 + (disp w).1 * (disp w).2.2.1 + (disp w).2.1 * (disp w).2.2.1)
      + 2 * X := by
  obtain ⟨h0, h1, h2⟩ := axisCount_disp w
  refine ⟨(disp w).1 * w.count Twist.right + (disp w).2.1 * w.count Twist.down
        + 2 * w.count Twist.down * w.count Twist.right
        + (disp w).1 * w.count Twist.backslash + (disp w).2.2.1 * w.count Twist.down
        + 2 * w.count Twist.down * w.count Twist.backslash
        + (disp w).2.1 * w.count Twist.backslash + (disp w).2.2.1 * w.count Twist.right
        + 2 * w.count Twist.right * w.count Twist.backslash, ?_⟩
  rw [pairs_eq]
  push_cast
  rw [h0, h1, h2]
  ring

/-- **The reversal sign is decided by the channel**: odd exactly when the channel is mixed. -/
theorem pairs_odd_iff (w : List Twist) : Odd (pairs w) ↔ Mixed (disp w) := by
  obtain ⟨X, hX⟩ := pairs_cast w
  rw [← Int.odd_coe_nat, hX, Mixed]
  constructor
  · intro h
    have := h.sub_even (even_two_mul X)
    simpa using this
  · intro h
    exact h.add_even (even_two_mul X)

theorem pairs_odd_of_mixed {w : List Twist} {v : ℤ × ℤ × ℤ × ℤ} (hw : disp w = v)
    (hv : Mixed v) : Odd (pairs w) := (pairs_odd_iff w).2 (hw ▸ hv)

/-- **In a mixed channel every fold is anti-Hermitian**: reversal flips its sign. -/
theorem fold_reverse_mixed {w : List Twist} {v : ℤ × ℤ × ℤ × ℤ} (hw : disp w = v)
    (hv : Mixed v) : twistMatrixFold w.reverse = -twistMatrixFold w := by
  rw [fold_reverse_sign, (pairs_odd_of_mixed hw hv).neg_one_pow, neg_one_smul]

theorem fold_antiHermitian_of_mixed {w : List Twist} {v : ℤ × ℤ × ℤ × ℤ} (hw : disp w = v)
    (hv : Mixed v) : (twistMatrixFold w).conjTranspose = -twistMatrixFold w := by
  rw [ClosureUnitarity.fold_reverse, fold_reverse_mixed hw hv]

theorem disp_reverse (w : List Twist) : disp w.reverse = disp w := by
  simp [disp, List.count_reverse]

-- ==========================================
-- §4  Mixed channels vanish at every order
-- ==========================================

/-- **PZ3 for channels: a mixed channel vanishes at every length.** -/
theorem mixed_channel_zero {v : ℤ × ℤ × ℤ × ℤ} (hv : Mixed v) (L : ℕ) : chanAmp v L = 0 := by
  unfold chanAmp
  set S := (words Twist L).filter (fun h => disp h = v)
  have hrev : ∑ h ∈ S, twistMatrixFold h = ∑ h ∈ S, twistMatrixFold h.reverse := by
    refine Finset.sum_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [S, mem_filter, mem_words] at hh ⊢
      exact ⟨by rw [List.length_reverse]; exact hh.1, by rw [disp_reverse]; exact hh.2⟩
    · intro h hh
      simp only [S, mem_filter, mem_words] at hh ⊢
      exact ⟨by rw [List.length_reverse]; exact hh.1, by rw [disp_reverse]; exact hh.2⟩
    · intro h _; exact List.reverse_reverse h
    · intro h _; exact List.reverse_reverse h
    · intro h _; rw [List.reverse_reverse]
  have hneg : ∑ h ∈ S, twistMatrixFold h.reverse = -∑ h ∈ S, twistMatrixFold h := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro h hh
    simp only [S, mem_filter] at hh
    exact fold_reverse_mixed hh.2 hv
  rw [hneg] at hrev
  have h2 : (2 : ℂ) • ∑ h ∈ S, twistMatrixFold h = 0 := by
    rw [two_smul]
    nth_rw 2 [hrev]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem vacAmp_zero : vacAmp 0 = 1 := by
  rw [vacAmp_eq, ClosureKernel.vacuum_amp_zero]
  simp

/-- **The zero is in the open amplitude**, not in the shared dressing. -/
theorem mixed_open_zero {v : ℤ × ℤ × ℤ × ℤ} (hv : Mixed v) (n : ℕ) : openAmp v n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := mixed_channel_zero hv n
    rw [channel_last_exit, sum_range_succ', vacAmp_zero, one_mul, Nat.sub_zero] at h
    rw [sum_eq_zero, zero_add] at h
    · exact h
    · intro k hk
      rw [mem_range] at hk
      rw [ih (n - (k + 1)) (by omega), mul_zero]

/-- One `^` and one `>` make a mixed channel. -/
theorem mixed_up_right : Mixed (1, -1, 0, 0) := ⟨-1, by norm_num⟩

-- ==========================================
-- §5  Open from the origin = first arrival at the channel
-- ==========================================

/-- Histories of length `n` that reach `v` for the first time at their last step. -/
def firstSet (v : ℤ × ℤ × ℤ × ℤ) (n : ℕ) : Finset (List Twist) :=
  (words Twist n).filter (fun f => disp f = v ∧ ∀ j < f.length, disp (f.take j) ≠ v)

/-- The first-arrival amplitude at `v`. -/
noncomputable def firstAmp (v : ℤ × ℤ × ℤ × ℤ) (n : ℕ) : M :=
  ∑ f ∈ firstSet v n, twistMatrixFold f

theorem disp_drop (q : List Twist) (k : ℕ) : disp (q.drop k) = disp q - disp (q.take k) := by
  have h := disp_append (q.take k) (q.drop k)
  rw [List.take_append_drop] at h
  rw [h]
  abel

/-- Reading a history backwards turns its prefixes into complements of its suffixes. -/
theorem disp_take_reverse (q : List Twist) (j : ℕ) :
    disp (q.reverse.take j) = disp q - disp (q.take (q.length - j)) := by
  rw [List.take_reverse, disp_reverse, disp_drop]

/-- **Reversal exchanges open histories and first arrivals** in the same channel. -/
theorem reverse_mem_firstSet {v : ℤ × ℤ × ℤ × ℤ} {n : ℕ} {q : List Twist} :
    q ∈ (openSet n).filter (fun q => disp q = v) ↔ q.reverse ∈ firstSet v n := by
  simp only [openSet, firstSet, mem_filter, mem_words, decide_eq_true_eq, List.length_reverse,
    disp_reverse]
  constructor
  · rintro ⟨⟨hl, ho⟩, hd⟩
    refine ⟨hl, hd, fun j hj heq => ?_⟩
    rw [disp_take_reverse, hd, sub_eq_self] at heq
    exact ho (q.length - j) (by rw [Finset.mem_Icc]; omega) ((balanced_iff_disp _).2 heq)
  · rintro ⟨hl, hd, hf⟩
    refine ⟨⟨hl, fun k hk hb => ?_⟩, hd⟩
    rw [Finset.mem_Icc] at hk
    apply hf (q.length - k) (by omega)
    rw [disp_take_reverse, hd, show q.length - (q.length - k) = k by omega,
      (balanced_iff_disp _).1 hb, sub_zero]

/-- **The open amplitude is the first-arrival amplitude.** Leaving the origin for good and arriving
    at `v` for the first time are the same amplitude, at every length. -/
theorem openAmp_eq_firstAmp (v : ℤ × ℤ × ℤ × ℤ) (n : ℕ) : openAmp v n = firstAmp v n := by
  by_cases hv : Mixed v
  · rw [mixed_open_zero hv]
    unfold firstAmp
    -- every first arrival is the reverse of an open history, so the sum is the open one up to sign
    have : ∑ f ∈ firstSet v n, twistMatrixFold f =
        ∑ q ∈ (openSet n).filter (fun q => disp q = v), twistMatrixFold q.reverse := by
      refine Finset.sum_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_ ?_
      · intro f hf
        rw [reverse_mem_firstSet, List.reverse_reverse]
        exact hf
      · intro q hq
        exact reverse_mem_firstSet.1 hq
      · intro f _; exact List.reverse_reverse f
      · intro q _; exact List.reverse_reverse q
      · intro f _; rw [List.reverse_reverse]
    rw [this, sum_congr rfl (fun q hq => by
      simp only [mem_filter] at hq
      exact fold_reverse_mixed hq.2 hv), sum_neg_distrib]
    have h0 := mixed_open_zero hv n
    unfold openAmp at h0
    rw [h0, neg_zero]
  · unfold openAmp firstAmp
    refine Finset.sum_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_ ?_
    · intro q hq
      exact reverse_mem_firstSet.1 hq
    · intro f hf
      rw [reverse_mem_firstSet, List.reverse_reverse]
      exact hf
    · intro q _; exact List.reverse_reverse q
    · intro f _; exact List.reverse_reverse f
    · intro q hq
      simp only [mem_filter] at hq
      have heven : Even (pairs q) := by
        rcases Nat.even_or_odd (pairs q) with h | h
        · exact h
        · exact absurd (hq.2 ▸ (pairs_odd_iff q).1 h) hv
      rw [fold_reverse_sign, heven.neg_one_pow, one_smul]

/-- The first-arrival series `F(v)`. -/
noncomputable def firstSeries (v : ℤ × ℤ × ℤ × ℤ) : PowerSeries M := PowerSeries.mk (firstAmp v)

theorem vacAmp_comm (k : ℕ) (A : M) : vacAmp k * A = A * vacAmp k := by
  rw [vacAmp_eq, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- **Two-sided channel factorization**: `G(v) = G_∅ · F(v) = F(v) · G_∅`. The shared dressing can
    be put before the channel's kernel or after it, and the kernel is the same. -/
theorem channel_two_sided (v : ℤ × ℤ × ℤ × ℤ) :
    chanSeries v = vacSeries * firstSeries v ∧ chanSeries v = firstSeries v * vacSeries := by
  have hO : openSeries v = firstSeries v := by
    refine PowerSeries.ext (fun n => ?_)
    rw [openSeries, firstSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, openAmp_eq_firstAmp]
  refine ⟨by rw [channel_series, hO], ?_⟩
  rw [channel_series, hO]
  refine PowerSeries.ext (fun n => ?_)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  apply sum_congr rfl
  intro x _
  simp only [Prod.fst_swap, Prod.snd_swap, vacSeries, PowerSeries.coeff_mk]
  exact vacAmp_comm _ _

end QLF.ClosureChannels
