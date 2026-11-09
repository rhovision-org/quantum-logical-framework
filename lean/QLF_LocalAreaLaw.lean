import QLF_HolographicArea

set_option linter.unusedVariables false

/-!
# QLF_LocalAreaLaw — **only local information has effect ⟹ an area law**

[`QLF_HolographicBoundary`](QLF_HolographicBoundary.lean) proved the area law from locality for an
abstract adjacency relation, and [`QLF_HolographicArea`](QLF_HolographicArea.lean) proved that two
halves of a pair related through `k` steps each lie within `ℓ¹` distance `2k`. Neither yet gave the
statement a reviewer asks for: a **fixed** range and an area law with a coefficient that does not grow
with the region. This module proves it on the spatial lattice `ℤ³`.

**The principle** (Jim, 2026-11-09: *logic is timeless; only local information has any effect*): every
shared pair links two sites within step distance `d`. No time enters — `d` counts steps of history
(by `pair_range_le`, halves `k` steps from their shared event are within `2k`), not an age.

**The theorem** (`local_area_law`): for the `ℓ¹` ball of radius `R`, the shared pairs it cuts number
at most `4d(2d+1)³(2R+1)²`. For fixed `d` that is `O(R²)` — area, not volume — with a coefficient
fixed by the range alone. The proof is the light-cone argument: a cut pair's inner end lies in the
shell of width `d` under the boundary (`shell_card_le`, at most `2d(2R+1)²` sites, by the same
injection as `sphere3_card_le`), and its other end is one of `(2d+1)³` offsets (`box_card`).
`local_entropy_law` reads it as entropy at `log 2` per cut pair.

Necessity is already proved: without locality the bound fails (`nonlocal_pairs_break_area_law`).

No axioms.
-/

namespace QLF.LocalAreaLaw

open QLF QLF.HolographicArea

/-- A site of the spatial lattice. -/
abbrev Site := ℤ × ℤ × ℤ

/-- The `ℓ¹` norm of a site. -/
def n1 (p : Site) : ℕ := p.1.natAbs + p.2.1.natAbs + p.2.2.natAbs

/-- The offset from `u` to `v`. -/
def off (u v : Site) : Site := (v.1 - u.1, v.2.1 - u.2.1, v.2.2 - u.2.2)

/-- A pair straddles the boundary of the `ℓ¹` ball of radius `R`. -/
def Cut (R : ℕ) (e : Site × Site) : Prop :=
  (n1 e.1 ≤ R ∧ R < n1 e.2) ∨ (n1 e.2 ≤ R ∧ R < n1 e.1)

instance (R : ℕ) : DecidablePred (Cut R) := fun e => by unfold Cut; infer_instance

/-- The shared pairs the ball's boundary cuts. -/
def cutPairs (R : ℕ) (P : Finset (Site × Site)) : Finset (Site × Site) := P.filter (Cut R)

/-- The offsets of step distance at most `d` (a box containing them). -/
noncomputable def box (d : ℕ) : Finset Site :=
  Finset.Icc (-(d : ℤ)) d ×ˢ (Finset.Icc (-(d : ℤ)) d ×ˢ Finset.Icc (-(d : ℤ)) d)

/-- The shell of width `d` just inside the boundary: `R − d < ‖p‖₁ ≤ R`. -/
noncomputable def shell (R d : ℕ) : Finset Site :=
  (Finset.Icc (-(R : ℤ)) R ×ˢ (Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R)).filter
    (fun p => n1 p ≤ R ∧ R < n1 p + d)

/-- A cut pair, recorded by its inner end, the offset to its outer end, and which end was inner. -/
def cutMap (R : ℕ) (e : Site × Site) : Site × Site × Bool :=
  if n1 e.1 ≤ R then (e.1, off e.1 e.2, true) else (e.2, off e.2 e.1, false)

theorem box_card (d : ℕ) : (box d).card = (2 * d + 1) ^ 3 := by
  unfold box
  rw [Finset.card_product, Finset.card_product, card_Icc_sym]
  ring

/-- **The boundary shell has area, not volume**: at most `2d(2R+1)²` sites. A shell site is fixed by
    its first two coordinates, its depth below the boundary (`< d`) and the sign of its third. -/
theorem shell_card_le (R d : ℕ) : (shell R d).card ≤ 2 * d * (2 * R + 1) ^ 2 := by
  calc (shell R d).card
      ≤ ((Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R) ×ˢ
          (Finset.range d ×ˢ (Finset.univ : Finset Bool))).card := by
        apply Finset.card_le_card_of_injOn
          (fun p : Site => ((p.1, p.2.1), (R - n1 p, decide (0 ≤ p.2.2))))
        · intro p hp
          have hp' : p ∈ shell R d := by simpa using hp
          obtain ⟨x, y, z⟩ := p
          replace hp' := Finset.mem_filter.mp hp'
          simp only [Finset.mem_product, Finset.mem_Icc] at hp'
          simp only [n1] at hp'
          simp only [n1, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_range,
            Finset.mem_univ, and_true]
          omega
        · intro p hp q hq hpq
          have hp' : p ∈ shell R d := by simpa using hp
          have hq' : q ∈ shell R d := by simpa using hq
          obtain ⟨x1, y1, z1⟩ := p
          obtain ⟨x2, y2, z2⟩ := q
          replace hp' := Finset.mem_filter.mp hp'
          replace hq' := Finset.mem_filter.mp hq'
          simp only [n1] at hp' hq'
          simp only [n1, Prod.mk.injEq] at hpq
          obtain ⟨⟨hx, hy⟩, hr, hz⟩ := hpq
          have hz' : (0 ≤ z1 ↔ 0 ≤ z2) := by simpa using hz
          subst hx
          subst hy
          have e1 := hp'.2
          have e2 := hq'.2
          have hzz : z1 = z2 := by
            rcases Int.natAbs_eq z1 with h1 | h1 <;> rcases Int.natAbs_eq z2 with h2 | h2 <;> omega
          rw [hzz]
    _ = 2 * d * (2 * R + 1) ^ 2 := by
        rw [Finset.card_product, Finset.card_product, Finset.card_product, card_Icc_sym,
          Finset.card_range, Finset.card_univ, Fintype.card_bool]
        ring

/-- The `ℓ¹` triangle inequality for an offset. -/
theorem n1_le_add (u v : Site) : n1 v ≤ n1 u + n1 (off u v) := by
  obtain ⟨a, b, c⟩ := u
  obtain ⟨x, y, z⟩ := v
  have h1 : x.natAbs ≤ a.natAbs + (x - a).natAbs := by simpa using Int.natAbs_add_le a (x - a)
  have h2 : y.natAbs ≤ b.natAbs + (y - b).natAbs := by simpa using Int.natAbs_add_le b (y - b)
  have h3 : z.natAbs ≤ c.natAbs + (z - c).natAbs := by simpa using Int.natAbs_add_le c (z - c)
  simp only [n1, off]
  linarith

/-- Step distance is symmetric. -/
theorem n1_off_symm (u v : Site) : n1 (off v u) = n1 (off u v) := by
  obtain ⟨a, b, c⟩ := u
  obtain ⟨x, y, z⟩ := v
  simp only [n1, off]
  omega

/-- An offset is fixed by its endpoints. -/
theorem off_inj {u v w : Site} (h : off u v = off u w) : v = w := by
  obtain ⟨a, b, c⟩ := u
  obtain ⟨x, y, z⟩ := v
  obtain ⟨x', y', z'⟩ := w
  simp only [off, Prod.mk.injEq] at h ⊢
  omega

theorem mem_shell_of {R d : ℕ} {p : Site} (h1 : n1 p ≤ R) (h2 : R < n1 p + d) : p ∈ shell R d := by
  unfold shell
  rw [Finset.mem_filter]
  refine ⟨?_, h1, h2⟩
  obtain ⟨x, y, z⟩ := p
  simp only [n1] at h1
  simp only [Finset.mem_product, Finset.mem_Icc]
  omega

theorem mem_box_of {d : ℕ} {q : Site} (h : n1 q ≤ d) : q ∈ box d := by
  obtain ⟨x, y, z⟩ := q
  simp only [n1] at h
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  omega

/-- A local cut pair lands in (shell) × (offset box) × (which end was inner). -/
theorem cutMap_mem (R d : ℕ) (e : Site × Site) (hc : Cut R e) (hl : n1 (off e.1 e.2) ≤ d) :
    cutMap R e ∈ shell R d ×ˢ (box d ×ˢ (Finset.univ : Finset Bool)) := by
  have t1 := n1_le_add e.1 e.2
  have t2 := n1_le_add e.2 e.1
  have hs := n1_off_symm e.1 e.2
  unfold Cut at hc
  unfold cutMap
  split_ifs with h
  · exact Finset.mem_product.mpr
      ⟨mem_shell_of h (by omega), Finset.mem_product.mpr ⟨mem_box_of hl, Finset.mem_univ _⟩⟩
  · exact Finset.mem_product.mpr
      ⟨mem_shell_of (by omega) (by omega),
        Finset.mem_product.mpr ⟨mem_box_of (by omega), Finset.mem_univ _⟩⟩

/-- `cutMap` loses nothing: a pair is recovered from its record. -/
theorem cutMap_inj (R : ℕ) {e1 e2 : Site × Site} (h : cutMap R e1 = cutMap R e2) : e1 = e2 := by
  unfold cutMap at h
  split_ifs at h
  · have ha : e1.1 = e2.1 := congrArg Prod.fst h
    have hb : off e1.1 e1.2 = off e2.1 e2.2 := congrArg (fun x : Site × Site × Bool => x.2.1) h
    rw [ha] at hb
    exact Prod.ext_iff.mpr ⟨ha, off_inj hb⟩
  · have hb : true = false := congrArg (fun x : Site × Site × Bool => x.2.2) h
    exact absurd hb (by decide)
  · have hb : false = true := congrArg (fun x : Site × Site × Bool => x.2.2) h
    exact absurd hb (by decide)
  · have ha : e1.2 = e2.2 := congrArg Prod.fst h
    have hb : off e1.2 e1.1 = off e2.2 e2.1 := congrArg (fun x : Site × Site × Bool => x.2.1) h
    rw [ha] at hb
    exact Prod.ext_iff.mpr ⟨off_inj hb, ha⟩

/-- **The local area law.** If every shared pair links sites within step distance `d` (only local
    information has effect), the pairs cut by the boundary of the `ℓ¹` ball of radius `R` number at
    most `4d(2d+1)³(2R+1)²`: `O(R²)` with a coefficient fixed by the range `d` alone. -/
theorem local_area_law (R d : ℕ) (P : Finset (Site × Site))
    (hloc : ∀ e ∈ P, n1 (off e.1 e.2) ≤ d) :
    (cutPairs R P).card ≤ 4 * d * (2 * d + 1) ^ 3 * (2 * R + 1) ^ 2 := by
  have hmaps : ∀ e ∈ cutPairs R P,
      cutMap R e ∈ shell R d ×ˢ (box d ×ˢ (Finset.univ : Finset Bool)) := by
    intro e he
    rw [cutPairs, Finset.mem_filter] at he
    exact cutMap_mem R d e he.2 (hloc e he.1)
  have hcard : (cutPairs R P).card ≤ (shell R d ×ˢ (box d ×ˢ (Finset.univ : Finset Bool))).card :=
    Finset.card_le_card_of_injOn (cutMap R) (fun e he => hmaps e (by simpa using he))
      (fun e1 _ e2 _ h => cutMap_inj R h)
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    box_card] at hcard
  have hs := shell_card_le R d
  calc (cutPairs R P).card ≤ (shell R d).card * ((2 * d + 1) ^ 3 * 2) := hcard
    _ ≤ (2 * d * (2 * R + 1) ^ 2) * ((2 * d + 1) ^ 3 * 2) := Nat.mul_le_mul hs le_rfl
    _ = 4 * d * (2 * d + 1) ^ 3 * (2 * R + 1) ^ 2 := by ring

/-- **The local entropy law**: at `log 2` per cut pair, the entropy the ball shares with its outside
    is at most `4d(2d+1)³(2R+1)² · log 2`. -/
theorem local_entropy_law (R d : ℕ) (P : Finset (Site × Site))
    (hloc : ∀ e ∈ P, n1 (off e.1 e.2) ≤ d) :
    ((cutPairs R P).card : ℝ) * per_event_entropy
      ≤ ((4 * d * (2 * d + 1) ^ 3 * (2 * R + 1) ^ 2 : ℕ) : ℝ) * per_event_entropy := by
  apply mul_le_mul_of_nonneg_right
  · have h := local_area_law R d P hloc
    exact_mod_cast h
  · unfold per_event_entropy
    exact Real.log_nonneg (by norm_num)

end QLF.LocalAreaLaw
