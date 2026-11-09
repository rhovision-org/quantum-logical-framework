import Mathlib
import QLF_HolographicBoundary

set_option linter.unusedVariables false

/-!
# QLF_HolographicArea — the horizon's `R²` and the range of shared pairs, derived

[`QLF_HolographicBoundary`](QLF_HolographicBoundary.lean) left two premises of the holographic area
law open ([`Holography_Audit.md`](../Holography_Audit.md) §3): the `R²` growth of the horizon, which
`QLF_GravityFromDelay` *defines* (`holographic_event_count R := 4πR²`), and the locality of shared
pairs. This module derives both from the substrate's own step structure.

**1. The light cone.** Every twist moves the walker one unit along one axis, so after `L` steps the
walker is within `ℓ¹` distance `L` of where it started (`light_cone`). A capacity-`R` horizon is
therefore the `ℓ¹` sphere of radius `R`.

**2. The horizon has `Θ(R²)` sites.** The spatial `ℓ¹` sphere of radius `R` in `ℤ³` has between
`(⌊R/2⌋+1)²` and `2(2R+1)²` lattice sites (`sphere3_card_ge`, `sphere3_card_le`). That is an area,
**proved**, where it used to be defined. (Enumeration gives exactly `4R² + 2`; the continuum's `4πR²`
is the Euclidean sphere, so `4` versus `4π` is a substrate→continuum geometric factor, alongside the
`4 log 2` of `QLF_HolographicDensity`.)

**3. Shared pairs have bounded range.** If the two halves of a shared pair leave one event and are
each carried `k` steps, they end at most `2k` apart (`pair_range_le`). So the locality premise of
`area_law_of_local_pairs` holds with adjacency "within `2k`", and the bound `S_A ≤ |∂A|·log 2`
becomes `S_A ≤ (pairs of range ≤ 2k crossing ∂A)·log 2`: an area law with a boundary layer of
thickness `2k`. This is the light-cone argument for area laws (as in Lieb–Robinson bounds), on the
substrate. **What stays posited** is that a shared pair is born at one event: the two halves of
`[(A,t),(B,t†)]` start together (`QLF_TensorFromClosure`, PR #219, still posits that a shared pair
puts one half on each body).

No axioms.
-/

namespace QLF.HolographicArea

open QLF QLF.PhaseRule QLF.EdgeSign QLF.HolographicBoundary

-- ==========================================
-- 1. The light cone
-- ==========================================

/-- The `ℓ¹` norm of a position on `ℤ⁴`. -/
def norm1 (x : Axis → ℤ) : ℤ := |x Axis.I| + |x Axis.X| + |x Axis.Y| + |x Axis.Z|

/-- The `ℓ¹` distance between two positions. -/
def dist1 (x y : Axis → ℤ) : ℤ :=
  |x Axis.I - y Axis.I| + |x Axis.X - y Axis.X| + |x Axis.Y - y Axis.Y| + |x Axis.Z - y Axis.Z|

theorem abs_add_twistStep (a : ℤ) (t : Twist) : |a + twistStep t| ≤ |a| + 1 := by
  unfold twistStep
  split_ifs
  · exact abs_le.mpr ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
  · exact abs_le.mpr ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩

/-- One step changes one coordinate, by one unit. -/
theorem abs_stepPos_le (x : Axis → ℤ) (t : Twist) (b : Axis) :
    |stepPos x t b| ≤ |x b| + (if axisOf t = b then 1 else 0) := by
  simp only [stepPos]
  split_ifs
  · exact abs_add_twistStep (x b) t
  · simp

/-- **One step, one unit of distance.** -/
theorem norm1_stepPos (x : Axis → ℤ) (t : Twist) : norm1 (stepPos x t) ≤ norm1 x + 1 := by
  have hI := abs_stepPos_le x t Axis.I
  have hX := abs_stepPos_le x t Axis.X
  have hY := abs_stepPos_le x t Axis.Y
  have hZ := abs_stepPos_le x t Axis.Z
  unfold norm1
  cases h : axisOf t <;> simp [h] at hI hX hY hZ <;> linarith

theorem norm1_positionFrom_le (ts : List Twist) :
    ∀ x : Axis → ℤ, norm1 (positionFrom x ts) ≤ norm1 x + ts.length := by
  induction ts with
  | nil => intro x; simp [positionFrom]
  | cons t ts ih =>
    intro x
    simp only [positionFrom, List.length_cons]
    have h1 := ih (stepPos x t)
    have h2 := norm1_stepPos x t
    push_cast
    linarith

/-- **The light cone**: after `L` twists the walker is within `ℓ¹` distance `L` of the origin. -/
theorem light_cone (ts : List Twist) :
    norm1 (positionFrom (fun _ => 0) ts) ≤ ts.length := by
  have h := norm1_positionFrom_le ts (fun _ => 0)
  simpa [norm1] using h

-- ==========================================
-- 3. Shared pairs have bounded range
-- ==========================================

theorem abs_shift_sub (a p q : ℤ) : |a + p - (a + q)| ≤ |p| + |q| := by
  have e : a + p - (a + q) = p - q := by ring
  rw [e]
  exact abs_le.mpr ⟨by linarith [neg_abs_le p, le_abs_self q],
    by linarith [le_abs_self p, neg_abs_le q]⟩

/-- **A shared pair born at one event has range at most the sum of its two carried lengths.** Two
    halves leave `x₀` and are carried by `ts` and `us`; they end at most `|ts| + |us|` apart. -/
theorem pair_range_le (x₀ : Axis → ℤ) (ts us : List Twist) :
    dist1 (positionFrom x₀ ts) (positionFrom x₀ us) ≤ (ts.length : ℤ) + us.length := by
  have hp := light_cone ts
  have hq := light_cone us
  unfold norm1 at hp hq
  unfold dist1
  rw [positionFrom_shift ts x₀ Axis.I, positionFrom_shift ts x₀ Axis.X,
    positionFrom_shift ts x₀ Axis.Y, positionFrom_shift ts x₀ Axis.Z,
    positionFrom_shift us x₀ Axis.I, positionFrom_shift us x₀ Axis.X,
    positionFrom_shift us x₀ Axis.Y, positionFrom_shift us x₀ Axis.Z]
  have h1 := abs_shift_sub (x₀ Axis.I) (positionFrom (fun _ => 0) ts Axis.I)
    (positionFrom (fun _ => 0) us Axis.I)
  have h2 := abs_shift_sub (x₀ Axis.X) (positionFrom (fun _ => 0) ts Axis.X)
    (positionFrom (fun _ => 0) us Axis.X)
  have h3 := abs_shift_sub (x₀ Axis.Y) (positionFrom (fun _ => 0) ts Axis.Y)
    (positionFrom (fun _ => 0) us Axis.Y)
  have h4 := abs_shift_sub (x₀ Axis.Z) (positionFrom (fun _ => 0) ts Axis.Z)
    (positionFrom (fun _ => 0) us Axis.Z)
  linarith

/-- **Locality from the light cone.** Halves carried `k` steps each end within `2k`. (`k` counts steps
    of history, not time.) -/
theorem pair_local_of_steps (x₀ : Axis → ℤ) (ts us : List Twist) (k : ℕ)
    (hts : ts.length ≤ k) (hus : us.length ≤ k) :
    dist1 (positionFrom x₀ ts) (positionFrom x₀ us) ≤ 2 * (k : ℤ) := by
  have h := pair_range_le x₀ ts us
  have a : (ts.length : ℤ) ≤ k := by exact_mod_cast hts
  have b : (us.length : ℤ) ≤ k := by exact_mod_cast hus
  linarith

-- ==========================================
-- 2. The horizon has Θ(R²) sites
-- ==========================================

/-- The spatial `ℓ¹` sphere of radius `R` in `ℤ³`: the sites a capacity-`R` horizon consists of. -/
noncomputable def sphere3 (R : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(R : ℤ)) R ×ˢ (Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R)).filter
    (fun p => p.1.natAbs + p.2.1.natAbs + p.2.2.natAbs = R)

theorem card_Icc_sym (R : ℕ) : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
  rw [Int.card_Icc]
  omega

/-- **Upper bound: area, not volume.** A sphere site is fixed by its first two coordinates and the
    sign of the third, so there are at most `2(2R+1)²`. -/
theorem sphere3_card_le (R : ℕ) : (sphere3 R).card ≤ 2 * (2 * R + 1) ^ 2 := by
  calc (sphere3 R).card
      ≤ ((Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R) ×ˢ (Finset.univ : Finset Bool)).card := by
        apply Finset.card_le_card_of_injOn
          (fun p : ℤ × ℤ × ℤ => ((p.1, p.2.1), decide (0 ≤ p.2.2)))
        · intro p hp
          have hp' : p ∈ sphere3 R := by simpa using hp
          obtain ⟨x, y, z⟩ := p
          simp only [sphere3, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp'
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
          omega
        · intro p hp q hq hpq
          have hp' : p ∈ sphere3 R := by simpa using hp
          have hq' : q ∈ sphere3 R := by simpa using hq
          obtain ⟨x1, y1, z1⟩ := p
          obtain ⟨x2, y2, z2⟩ := q
          simp only [sphere3, Finset.mem_filter] at hp' hq'
          simp only [Prod.mk.injEq] at hpq
          obtain ⟨⟨hx, hy⟩, hz⟩ := hpq
          have hz' : (0 ≤ z1 ↔ 0 ≤ z2) := by simpa using hz
          subst hx
          subst hy
          have e1 := hp'.2
          have e2 := hq'.2
          have hzz : z1 = z2 := by
            rcases Int.natAbs_eq z1 with h1 | h1 <;> rcases Int.natAbs_eq z2 with h2 | h2 <;> omega
          rw [hzz]
    _ = 2 * (2 * R + 1) ^ 2 := by
        rw [Finset.card_product, Finset.card_product, card_Icc_sym, Finset.card_univ,
          Fintype.card_bool]
        ring

/-- **Lower bound: the area really grows.** The sites `(a, b, R − a − b)` with `a, b ≤ R/2` are
    distinct sphere sites, so there are at least `(⌊R/2⌋ + 1)²`. -/
theorem sphere3_card_ge (R : ℕ) : (R / 2 + 1) ^ 2 ≤ (sphere3 R).card := by
  have hS : (Finset.range (R / 2 + 1) ×ˢ Finset.range (R / 2 + 1)).card = (R / 2 + 1) ^ 2 := by
    rw [Finset.card_product, Finset.card_range]
    ring
  rw [← hS]
  apply Finset.card_le_card_of_injOn
    (fun ab : ℕ × ℕ => ((ab.1 : ℤ), (ab.2 : ℤ), (R : ℤ) - ab.1 - ab.2))
  · intro ab hab
    obtain ⟨a, b⟩ := ab
    have h' : a < R / 2 + 1 ∧ b < R / 2 + 1 := by simpa using hab
    have ha : ((a : ℤ).natAbs : ℤ) = a := Int.natAbs_of_nonneg (by omega)
    have hb : ((b : ℤ).natAbs : ℤ) = b := Int.natAbs_of_nonneg (by omega)
    have hc : (((R : ℤ) - a - b).natAbs : ℤ) = (R : ℤ) - a - b :=
      Int.natAbs_of_nonneg (by omega)
    simp only [sphere3, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  · intro ab _ cd _ h
    obtain ⟨a, b⟩ := ab
    obtain ⟨c, d⟩ := cd
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    simp only [Prod.mk.injEq]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **The horizon area law, derived.** The capacity-`R` horizon carries `Θ(R²)` sites — the `R²` that
    `holographic_event_count` had defined. -/
theorem horizon_area_law (R : ℕ) :
    (R / 2 + 1) ^ 2 ≤ (sphere3 R).card ∧ (sphere3 R).card ≤ 2 * (2 * R + 1) ^ 2 :=
  ⟨sphere3_card_ge R, sphere3_card_le R⟩

end QLF.HolographicArea
