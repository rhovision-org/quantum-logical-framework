import QLF_ClosureLeakage
import QLF_ClosureKernel

set_option linter.unusedVariables false

/-!
# QLF_ClosureChannels — **every boundary channel is the shared vacuum dressing times a matrix-valued open amplitude**

Fourth milestone of the closure-algebra programme of issue #207 (PZ2), after
[`QLF_ClosureUnitarity`](QLF_ClosureUnitarity.lean), [`QLF_ClosureKernel`](QLF_ClosureKernel.lean)
and [`QLF_ClosureLeakage`](QLF_ClosureLeakage.lean). See
[`Closure_Unitarity.md`](../Closure_Unitarity.md) §9.

`QLF_ClosureKernel` factorized every *seeded* channel through its **first** closure, with a scalar
kernel. The review of #208 asked for the step beyond that: channels as **boundary states**, and
amplitudes that are matrices rather than signs. This module gives it.

## Channels are boundary states

A history's boundary state is its net displacement `disp h ∈ ℤ⁴`, the signed twist count on each
axis (`disp`). A history closes exactly when its boundary state is the origin (`balanced_iff_disp`).
The channel `v` at length `L` is the coherent sum of the actual `2×2` folds of every length-`L`
history ending at `v`:

    chanAmp v L = Σ_{|h| = L, disp h = v} U(h)          (a matrix, not a sign)

## The last-exit factorization

Cut each history at its **last** closure, the longest balanced prefix (`lastExit`). What comes before
is a vacuum closure. What comes after leaves the origin and never returns, so it is an **open**
history in the sense of `QLF_ClosureLeakage`. The cut is unique (`lastExit_append`), so:

> **`channel_last_exit`** — `chanAmp v L = Σ_{k=0}^{L} G_k · O_{L−k}(v)` for every channel `v`,

where `G_k` is the vacuum's matrix amplitude and `O_n(v)` the open amplitude to `v`. The vacuum
factor is scalar, `G_k = A_k(∅) · I` (`vacAmp_eq`), so **every boundary channel carries the same
dressing**, and channels differ only in their open amplitude `O(v)`, which is a genuine matrix: one
step to `v = e_up` gives `O_1 = σy` (`openAmp_up_one`). As generating functions over the matrix ring:

> **`channel_series`** — `G(v) = G_∅ · O(v)`.

The origin channel is the vacuum itself (`origin_channel`): an open history cannot end at the origin,
so `O(0) = 1`.

This is the multi-channel, matrix-valued form of `channel_factorization`. It is the *last*-exit dual
of that theorem's first-closure cut. It does not yet give a transfer kernel `K_{vw}` between two
boundary states, or residues at a rendered pole: those stay open.

No axioms.
-/

namespace QLF.ClosureChannels

open Finset QLF QLF.FirstReturn QLF.ClosureLeakage

-- ==========================================
-- §1  Boundary states
-- ==========================================

/-- The **boundary state** of a history: its net signed twist count on each of the four axes. -/
def disp (h : List Twist) : ℤ × ℤ × ℤ × ℤ :=
  ((h.count Twist.up : ℤ) - h.count Twist.down,
   (h.count Twist.left : ℤ) - h.count Twist.right,
   (h.count Twist.slash : ℤ) - h.count Twist.backslash,
   (h.count Twist.plus : ℤ) - h.count Twist.minus)

theorem disp_append (a b : List Twist) : disp (a ++ b) = disp a + disp b := by
  simp only [disp, List.count_append, Nat.cast_add, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **A history closes exactly when its boundary state is the origin.** -/
theorem balanced_iff_disp (h : List Twist) : countBalanced h ↔ disp h = 0 := by
  unfold countBalanced disp
  simp only [Prod.mk_eq_zero, sub_eq_zero, Nat.cast_inj]

theorem disp_of_balanced_append {p q : List Twist} (hp : countBalanced p) :
    disp (p ++ q) = disp q := by
  rw [disp_append, (balanced_iff_disp p).1 hp, zero_add]

-- ==========================================
-- §2  The last exit from the origin
-- ==========================================

/-- The **last exit**: the length of the longest balanced prefix. -/
def lastExit (h : List Twist) : ℕ :=
  Nat.findGreatest (fun k => countBalanced (h.take k)) h.length

theorem lastExit_le (h : List Twist) : lastExit h ≤ h.length := Nat.findGreatest_le _

theorem lastExit_balanced (h : List Twist) : countBalanced (h.take (lastExit h)) :=
  Nat.findGreatest_spec (P := fun k => countBalanced (h.take k)) (Nat.zero_le _)
    (by simp [countBalanced])

/-- What follows the last exit never returns: it is **open**. -/
theorem drop_lastExit_open (h : List Twist) : IsOpen (h.drop (lastExit h)) := by
  intro j hj hb
  rw [Finset.mem_Icc, List.length_drop] at hj
  have hk := lastExit_balanced h
  have hsplit : h.take (lastExit h + j) = h.take (lastExit h) ++ (h.drop (lastExit h)).take j := by
    rw [List.take_add]
  have hbal : countBalanced (h.take (lastExit h + j)) := by
    rw [hsplit]
    exact ClosureKernel.balanced_append hk hb
  have hle : lastExit h + j ≤ lastExit h :=
    Nat.le_findGreatest (P := fun k => countBalanced (h.take k)) (by omega) hbal
  omega

/-- **The cut is unique**: a balanced prefix followed by an open history is cut exactly there. -/
theorem lastExit_append {p q : List Twist} (hp : countBalanced p) (hq : IsOpen q) :
    lastExit (p ++ q) = p.length := by
  unfold lastExit
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    set m := Nat.findGreatest (fun k => countBalanced ((p ++ q).take k)) (p ++ q).length
    have hspec : countBalanced ((p ++ q).take m) :=
      Nat.findGreatest_spec (P := fun k => countBalanced ((p ++ q).take k))
        (m := p.length) (by rw [List.length_append]; omega) (by simpa using hp)
    have hmle : m ≤ (p ++ q).length := Nat.findGreatest_le _
    rw [List.length_append] at hmle
    rw [List.take_append, List.take_of_length_le (by omega)] at hspec
    have hqb := ClosureKernel.balanced_of_append hp hspec
    exact hq (m - p.length) (by rw [Finset.mem_Icc]; omega) hqb
  · exact Nat.le_findGreatest (P := fun k => countBalanced ((p ++ q).take k))
      (by rw [List.length_append]; omega) (by simpa using hp)

-- ==========================================
-- §3  The decomposition of any additive quantity
-- ==========================================

/-- The vacuum closures of length `k`. -/
def balWords (k : ℕ) : Finset (List Twist) :=
  (words Twist k).filter (fun p => decide (countBalanced p))

/-- Histories of length `L` whose last exit is at `k`. -/
def exitFiber (L k : ℕ) : Finset (List Twist) :=
  (words Twist L).filter (fun h => lastExit h = k)

theorem sum_exitFiber {β : Type} [AddCommMonoid β] (L k : ℕ) (hk : k ≤ L) (g : List Twist → β) :
    ∑ h ∈ exitFiber L k, g h = ∑ x ∈ balWords k ×ˢ openSet (L - k), g (x.1 ++ x.2) := by
  refine Finset.sum_nbij' (fun h => (h.take k, h.drop k)) (fun x => x.1 ++ x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [exitFiber, mem_filter] at hh
    obtain ⟨hw, he⟩ := hh
    have hlen := (mem_words L h).1 hw
    have hkL : k ≤ L := by rw [← he, ← hlen]; exact lastExit_le h
    simp only [balWords, openSet, mem_product, mem_filter, mem_words, decide_eq_true_eq]
    refine ⟨⟨by rw [List.length_take]; omega, by rw [← he]; exact lastExit_balanced h⟩,
      by rw [List.length_drop]; omega, by rw [← he]; exact drop_lastExit_open h⟩
  · intro x hx
    obtain ⟨p, q⟩ := x
    simp only [balWords, openSet, mem_product, mem_filter, mem_words, decide_eq_true_eq] at hx
    obtain ⟨⟨hpl, hpb⟩, hql, hqo⟩ := hx
    simp only [exitFiber, mem_filter, mem_words]
    refine ⟨?_, by rw [lastExit_append hpb hqo, hpl]⟩
    rw [List.length_append, hpl, hql]
    omega
  · intro h _
    exact List.take_append_drop k h
  · intro x hx
    obtain ⟨p, q⟩ := x
    simp only [balWords, openSet, mem_product, mem_filter, mem_words, decide_eq_true_eq] at hx
    rw [← hx.1.1]
    simp
  · intro h _
    rw [List.take_append_drop]

/-- **Last-exit decomposition** of any additive quantity over the length-`L` histories. -/
theorem sum_words_last_exit {β : Type} [AddCommMonoid β] (L : ℕ) (g : List Twist → β) :
    ∑ h ∈ words Twist L, g h =
      ∑ k ∈ range (L + 1), ∑ x ∈ balWords k ×ˢ openSet (L - k), g (x.1 ++ x.2) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := lastExit) (t := range (L + 1))]
  · apply sum_congr rfl
    intro k hk
    exact sum_exitFiber L k (by rw [mem_range] at hk; omega) g
  · intro h hh
    rw [mem_range]
    have := lastExit_le h
    have := (mem_words L h).1 hh
    omega

-- ==========================================
-- §4  The channel factorization
-- ==========================================

/-- The vacuum's matrix amplitude at length `k`. -/
noncomputable def vacAmp (k : ℕ) : M := ∑ p ∈ balWords k, twistMatrixFold p

/-- The open amplitude from the origin to the boundary state `v` at length `n`. -/
noncomputable def openAmp (v : ℤ × ℤ × ℤ × ℤ) (n : ℕ) : M :=
  ∑ q ∈ (openSet n).filter (fun q => disp q = v), twistMatrixFold q

/-- The channel amplitude: every length-`L` history ending at `v`, folded and summed. -/
noncomputable def chanAmp (v : ℤ × ℤ × ℤ × ℤ) (L : ℕ) : M :=
  ∑ h ∈ (words Twist L).filter (fun h => disp h = v), twistMatrixFold h

/-- **PZ2 — the last-exit factorization of every boundary channel.** -/
theorem channel_last_exit (v : ℤ × ℤ × ℤ × ℤ) (L : ℕ) :
    chanAmp v L = ∑ k ∈ range (L + 1), vacAmp k * openAmp v (L - k) := by
  unfold chanAmp
  rw [sum_filter, sum_words_last_exit]
  apply sum_congr rfl
  intro k _
  unfold vacAmp openAmp
  rw [sum_filter, Finset.sum_mul_sum, ← sum_product']
  apply sum_congr rfl
  intro x hx
  simp only [balWords, mem_product, mem_filter, decide_eq_true_eq] at hx
  rw [disp_of_balanced_append hx.1.2, ClosureUnitarity.fold_append]
  split_ifs <;> simp

/-- The vacuum closures of length `k` are the vacuum's closure family. -/
theorem balWords_eq (k : ℕ) : balWords k = ClosureUnitarity.closureFamily [] k := by
  ext p
  rw [ClosureUnitarity.mem_closureFamily]
  simp [balWords, mem_words]

/-- **The vacuum dressing is scalar**: `G_k = A_k(∅) · I`. -/
theorem vacAmp_eq (k : ℕ) :
    vacAmp k = ((ClosureUnitarity.signedAmplitude [] k : ℤ) : ℂ) • (1 : M) := by
  rw [← ClosureUnitarity.matrix_amplitude, vacAmp, balWords_eq]
  rfl

/-- The scalar form: every channel is the signed vacuum amplitude times its own open amplitude. -/
theorem channel_last_exit_scalar (v : ℤ × ℤ × ℤ × ℤ) (L : ℕ) :
    chanAmp v L = ∑ k ∈ range (L + 1),
      ((ClosureUnitarity.signedAmplitude [] k : ℤ) : ℂ) • openAmp v (L - k) := by
  rw [channel_last_exit]
  apply sum_congr rfl
  intro k _
  rw [vacAmp_eq, smul_mul_assoc, one_mul]

/-- An open history never ends at the origin, except the empty one. -/
theorem openAmp_origin (n : ℕ) : openAmp 0 n = if n = 0 then 1 else 0 := by
  unfold openAmp
  split_ifs with hn
  · subst hn
    have : (openSet 0).filter (fun q => disp q = 0) = {[]} := by
      ext q
      simp only [openSet, mem_filter, mem_words, decide_eq_true_eq, mem_singleton]
      constructor
      · rintro ⟨⟨hl, -⟩, -⟩
        exact List.length_eq_zero_iff.1 hl
      · rintro rfl
        refine ⟨⟨rfl, ?_⟩, rfl⟩
        intro j hj
        simp at hj
    rw [this, sum_singleton]
    rfl
  · apply sum_eq_zero
    intro q hq
    simp only [openSet, mem_filter, mem_words, decide_eq_true_eq] at hq
    obtain ⟨⟨hl, ho⟩, hd⟩ := hq
    exfalso
    apply ho q.length (by rw [Finset.mem_Icc]; omega)
    rw [List.take_length]
    exact (balanced_iff_disp q).2 hd

/-- **The origin channel is the vacuum.** -/
theorem origin_channel (L : ℕ) : chanAmp 0 L = vacAmp L := by
  rw [channel_last_exit, sum_range_succ, Nat.sub_self, openAmp_origin]
  simp only [↓reduceIte, mul_one]
  rw [sum_eq_zero, zero_add]
  intro k hk
  rw [mem_range] at hk
  have hne : L - k ≠ 0 := by omega
  simp only [openAmp_origin, hne, ↓reduceIte, mul_zero]

-- ==========================================
-- §5  Generating functions over the matrix ring
-- ==========================================

/-- The channel series `G(v) = Σ_L chanAmp v L · X^L`. -/
noncomputable def chanSeries (v : ℤ × ℤ × ℤ × ℤ) : PowerSeries M :=
  PowerSeries.mk (chanAmp v)

/-- The vacuum series over the matrix ring. -/
noncomputable def vacSeries : PowerSeries M := PowerSeries.mk vacAmp

/-- The open series `O(v)`. -/
noncomputable def openSeries (v : ℤ × ℤ × ℤ × ℤ) : PowerSeries M := PowerSeries.mk (openAmp v)

/-- **`G(v) = G_∅ · O(v)`**: one dressing for every boundary channel. -/
theorem channel_series (v : ℤ × ℤ × ℤ × ℤ) : chanSeries v = vacSeries * openSeries v := by
  refine PowerSeries.ext (fun L => ?_)
  rw [chanSeries, vacSeries, openSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    channel_last_exit, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro k _
  simp only [PowerSeries.coeff_mk]

/-- The origin channel's open series is `1`. -/
theorem openSeries_origin : openSeries 0 = 1 := by
  refine PowerSeries.ext (fun n => ?_)
  rw [openSeries, PowerSeries.coeff_mk, openAmp_origin, PowerSeries.coeff_one]

-- ==========================================
-- §6  The open amplitude is a matrix
-- ==========================================

/-- One step up reaches `e_up` and is open: `O_1(e_up) = σy`, not a multiple of the identity. -/
theorem openAmp_up_one : openAmp (1, 0, 0, 0) 1 = σy := by
  have hset : (openSet 1).filter (fun q => disp q = (1, 0, 0, 0)) = {[Twist.up]} := by
    ext q
    simp only [openSet, mem_filter, mem_words, decide_eq_true_eq, mem_singleton]
    constructor
    · rintro ⟨⟨hl, -⟩, hd⟩
      match q, hl with
      | [t], _ => cases t <;> revert hd <;> decide
    · rintro rfl
      refine ⟨⟨rfl, ?_⟩, by decide⟩
      intro j hj hb
      simp only [List.length_singleton, Finset.mem_Icc] at hj
      obtain rfl : j = 1 := by omega
      revert hb
      unfold countBalanced
      decide
  rw [openAmp, hset, sum_singleton]
  simp [twistMatrixFold, Twist.toMatrix]

end QLF.ClosureChannels
