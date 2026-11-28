import QLF_HolographicArea

/-!
# QLF_SphereCount — the spatial ℓ¹ sphere has exactly `4R² + 2` sites

[`QLF_HolographicArea`](QLF_HolographicArea.lean) proved that the spatial `ℓ¹` sphere
`sphere3 R = {(x, y, z) : |x| + |y| + |z| = R}` has `Θ(R²)` sites (`horizon_area_law`), and recorded
the exact count `4R² + 2` as checked by enumeration only. This module proves the exact count for
every `R ≥ 1` (`sphere3_card`), with `1` site at `R = 0`.

The count comes from fibring twice. The `ℓ¹` circle `|y| + |z| = m` has `4m` sites for `m ≥ 1`
and one at `m = 0` (`circle_card`). The sphere is a stack of circles of radius `R − |x|`, so its
count is `4R + 2·(1 + Σ_{j=1}^{R−1} 4j) = 4R² + 2`.

This replaces the definitional `holographic_event_count := 4πR²` with a derived quadratic on the
substrate's own lattice, with the leading coefficient `4` rather than `4π`. That the `ℓ¹` sphere is
the physical horizon remains a bridge (`Holography_Audit.md` §3). No axioms.

Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.SphereCount

open Finset QLF.HolographicArea

/-- Fibre count over a product. -/
lemma card_filter_product {α β : Type*} (s : Finset α) (t : Finset β) (p : α → β → Prop)
    [∀ a b, Decidable (p a b)] :
    ((s ×ˢ t).filter (fun q => p q.1 q.2)).card = ∑ a ∈ s, (t.filter (p a)).card := by
  rw [card_eq_sum_ones, sum_filter, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [card_eq_sum_ones, sum_filter]

/-- The symmetric interval, one shell larger. -/
lemma Icc_succ (R : ℕ) :
    Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ) =
      insert (-((R + 1 : ℕ) : ℤ)) (insert ((R + 1 : ℕ) : ℤ) (Icc (-(R : ℤ)) R)) := by
  ext y
  simp only [mem_Icc, mem_insert]
  push_cast
  omega

/-- A sum over the symmetric interval of a function of `|x|`. -/
lemma sum_Icc_natAbs (g : ℕ → ℕ) (R : ℕ) :
    ∑ x ∈ Icc (-(R : ℤ)) R, g x.natAbs = g 0 + 2 * ∑ k ∈ range R, g (k + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Icc_succ, sum_insert, sum_insert, ih, sum_range_succ]
    · have h1 : (-((R + 1 : ℕ) : ℤ)).natAbs = R + 1 := by omega
      have h2 : ((R + 1 : ℕ) : ℤ).natAbs = R + 1 := by omega
      rw [h1, h2]
      ring
    · simp only [mem_Icc]; push_cast; omega
    · simp only [mem_insert, mem_Icc]; push_cast; omega

/-- The integers in `[−R, R]` with `|y| = k`, for `k ≤ R`. -/
lemma card_natAbs_eq (R k : ℕ) (hk : k ≤ R) :
    ((Icc (-(R : ℤ)) R).filter (fun y => y.natAbs = k)).card = if k = 0 then 1 else 2 := by
  by_cases h : k = 0
  · subst h
    have : (Icc (-(R : ℤ)) R).filter (fun y => y.natAbs = 0) = {0} := by
      ext y; simp only [mem_filter, mem_Icc, mem_singleton]; omega
    rw [this]; simp
  · have : (Icc (-(R : ℤ)) R).filter (fun y => y.natAbs = k) = {(k : ℤ), -(k : ℤ)} := by
      ext y; simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]; omega
    rw [this, card_pair (by omega)]
    simp [h]

/-- The per-shell weight of the circle count. -/
def shell (m k : ℕ) : ℕ := if k ≤ m then (if k = m then 1 else 2) else 0

lemma sum_shell (m n : ℕ) :
    ∑ k ∈ range n, shell m (k + 1) = if n < m then 2 * n else (if m = 0 then 0 else 2 * m - 1) := by
  induction n with
  | zero => by_cases hm : m = 0 <;> simp [hm]
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold shell
    by_cases h1 : n + 1 < m
    · simp only [h1, if_true, show n < m by omega, show n + 1 ≤ m by omega,
        show n + 1 ≠ m by omega, if_false]
      ring
    · by_cases h2 : n + 1 = m
      · subst h2
        simp
        omega
      · have h3 : ¬ n + 1 ≤ m := by omega
        simp only [h1, h3, if_false, show ¬ n < m by omega, add_zero]

/-- The `ℓ¹` circle count. -/
def circleCount (m : ℕ) : ℕ := if m = 0 then 1 else 4 * m

/-- **The `ℓ¹` circle of radius `m ≤ R` has `4m` sites, or one at `m = 0`.** -/
theorem circle_card (R m : ℕ) (hm : m ≤ R) :
    ((Icc (-(R : ℤ)) R ×ˢ Icc (-(R : ℤ)) R).filter
      (fun q => q.1.natAbs + q.2.natAbs = m)).card = circleCount m := by
  rw [card_filter_product (p := fun (y z : ℤ) => y.natAbs + z.natAbs = m)]
  have hfib : ∀ y ∈ Icc (-(R : ℤ)) R,
      ((Icc (-(R : ℤ)) R).filter (fun z => y.natAbs + z.natAbs = m)).card = shell m y.natAbs := by
    intro y _
    unfold shell
    by_cases hy : y.natAbs ≤ m
    · rw [filter_congr (q := fun z => z.natAbs = m - y.natAbs) (fun z _ => by omega),
        card_natAbs_eq R (m - y.natAbs) (by omega)]
      by_cases he : y.natAbs = m
      · simp [he]
      · simp [hy, he, show m - y.natAbs ≠ 0 by omega]
    · rw [filter_false_of_mem (fun z _ => by omega)]
      simp [hy]
  rw [sum_congr rfl hfib, sum_Icc_natAbs (shell m) R, sum_shell, circleCount]
  unfold shell
  by_cases hm0 : m = 0
  · subst hm0; simp
  · have : ¬ R < m := by omega
    simp only [hm0, this, if_false, Nat.zero_le, if_true, show ¬ (0 = m) by omega]
    omega

lemma sum_circle (n : ℕ) :
    ∑ j ∈ range n, circleCount j = if n = 0 then 0 else 1 + 2 * n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold circleCount
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp only [show n ≠ 0 by omega, if_false, show n + 1 ≠ 0 by omega]
      cases n with
      | zero => omega
      | succ n =>
        simp only [Nat.add_sub_cancel]
        ring

/-- The sphere as a stack of circles. -/
lemma sphere3_card_stack (R : ℕ) :
    (sphere3 R).card = circleCount R + 2 * ∑ j ∈ range R, circleCount j := by
  unfold sphere3
  rw [card_filter_product (p := fun (x : ℤ) (q : ℤ × ℤ) => x.natAbs + q.1.natAbs + q.2.natAbs = R)]
  have hfib : ∀ x ∈ Icc (-(R : ℤ)) R,
      ((Icc (-(R : ℤ)) R ×ˢ Icc (-(R : ℤ)) R).filter
        (fun q => x.natAbs + q.1.natAbs + q.2.natAbs = R)).card = circleCount (R - x.natAbs) := by
    intro x hx
    rw [mem_Icc] at hx
    rw [filter_congr (q := fun q => q.1.natAbs + q.2.natAbs = R - x.natAbs) (fun q _ => by omega)]
    exact circle_card R (R - x.natAbs) (by omega)
  rw [sum_congr rfl hfib, sum_Icc_natAbs (fun k => circleCount (R - k)) R, Nat.sub_zero]
  congr 2
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  congr 1
  omega

/-- **The spatial `ℓ¹` sphere has exactly `4R² + 2` sites for `R ≥ 1`.** -/
theorem sphere3_card (R : ℕ) (hR : 1 ≤ R) : (sphere3 R).card = 4 * R ^ 2 + 2 := by
  rw [sphere3_card_stack, sum_circle]
  unfold circleCount
  cases R with
  | zero => omega
  | succ n =>
    simp only [show n + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
    ring

/-- The sphere of radius `0` is the origin. -/
theorem sphere3_card_zero : (sphere3 0).card = 1 := by
  rw [sphere3_card_stack]
  simp [circleCount]

end QLF.SphereCount
