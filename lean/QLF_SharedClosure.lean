import Mathlib

/-!
# QLF_SharedClosure — a bond is a shared closure: the two-channel resolvent

Issue #207 (*one molecular/bound-state shared-closure resolvent*). [`Chemistry.md`](../Chemistry.md)
reads a chemical bond as a **shared closure**: two sites that close separately with kernels `a`
and `b` also close jointly with amplitude `g`. The closure kernel of the pair is
`K = [[a, g], [g, b]]`, and its resolvent `(1 − zK)⁻¹` has poles at `z = 1/μ` for the roots `μ` of
`(μ − a)(μ − b) = g²` ([`QLF_PoleFactorization`](QLF_PoleFactorization.lean)).

* **`levels_root`.** `μ± = (a + b)/2 ± √(((a − b)/2)² + g²)` are the two roots.
* **`bonding_above`, `antibonding_below`.** If `g ≠ 0`, `μ₊ > max(a, b)` and `μ₋ < min(a, b)`: the
  shared closure pushes one level above both separate ones and one below. The bonding pole
  `1/μ₊` moves toward the origin, so the shared closure is reached before either site's own.
* **`symmetric_split`.** For two equal sites (`a = b`, as in `H₂`) the levels are `a ± |g|`: the
  splitting `2|g|` is the shared-closure amplitude itself.
* **`resolvent_two`, `feshbach_entry`.** The pair's resolvent is explicit, and its first entry is
  `1/(1 − za − z²g²/(1 − zb))`: a site's dressed resolvent is its own kernel plus the round trip
  through the partner, the Feshbach reduction of the shared channel.

**Not here.** The values of `a`, `b`, `g` for real atoms, bond angles and multiple bonds; this is
the one-shared-closure skeleton. No axioms.

**Credit.** The two-level bonding/antibonding split is the Heitler–London and Hund–Mulliken
picture of `H₂` (Heitler and London, *Z. Phys.* **44**, 455 (1927)); the reduction to one channel is
Feshbach's (*Ann. Phys.* **5**, 357 (1958)). Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.SharedClosure

open Matrix

/-- The discriminant radius `√(((a − b)/2)² + g²)`. -/
noncomputable def rad (a b g : ℝ) : ℝ := Real.sqrt (((a - b) / 2) ^ 2 + g ^ 2)

/-- The bonding level. -/
noncomputable def μp (a b g : ℝ) : ℝ := (a + b) / 2 + rad a b g
/-- The antibonding level. -/
noncomputable def μm (a b g : ℝ) : ℝ := (a + b) / 2 - rad a b g

lemma rad_sq (a b g : ℝ) : rad a b g ^ 2 = ((a - b) / 2) ^ 2 + g ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma rad_gt (a b g : ℝ) (hg : g ≠ 0) : |a - b| / 2 < rad a b g := by
  have hpos : 0 < g ^ 2 := by positivity
  have h0 : 0 ≤ |a - b| / 2 := by positivity
  rw [rad, Real.lt_sqrt h0, div_pow, sq_abs]
  linarith [show ((a - b) / 2) ^ 2 = (a - b) ^ 2 / 2 ^ 2 by rw [div_pow]]

/-- **Both levels solve `(μ − a)(μ − b) = g²`.** -/
theorem levels_root (a b g : ℝ) :
    (μp a b g - a) * (μp a b g - b) = g ^ 2 ∧ (μm a b g - a) * (μm a b g - b) = g ^ 2 := by
  have h := rad_sq a b g
  constructor <;> simp only [μp, μm] <;> linear_combination h

/-- **The bonding level lies above both sites.** -/
theorem bonding_above (a b g : ℝ) (hg : g ≠ 0) : max a b < μp a b g := by
  have h := rad_gt a b g hg
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  rw [μp, max_lt_iff]
  constructor <;> linarith

/-- **The antibonding level lies below both sites.** -/
theorem antibonding_below (a b g : ℝ) (hg : g ≠ 0) : μm a b g < min a b := by
  have h := rad_gt a b g hg
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  rw [μm, lt_min_iff]
  constructor <;> linarith

/-- **Equal sites split by twice the shared amplitude.** -/
theorem symmetric_split (a g : ℝ) : μp a a g = a + |g| ∧ μm a a g = a - |g| := by
  have : rad a a g = |g| := by
    rw [rad, sub_self, zero_div, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs]
  simp only [μp, μm, this]
  constructor <;> ring

/-- The pair's closure kernel. -/
def K (a b g : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, g; g, b]

/-- **The pair's resolvent is explicit.** -/
theorem resolvent_two (a b g z : ℂ)
    (hD : (1 - z * a) * (1 - z * b) - z ^ 2 * g ^ 2 ≠ 0) :
    (1 - z • K a b g) * ((1 / ((1 - z * a) * (1 - z * b) - z ^ 2 * g ^ 2)) •
      !![1 - z * b, z * g; z * g, 1 - z * a]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> field_simp <;> ring

/-- **The Feshbach entry**: a site's dressed resolvent is its own kernel plus the round trip
    through the partner. -/
theorem feshbach_entry (a b g z : ℂ) (hb : 1 - z * b ≠ 0)
    (hD : (1 - z * a) * (1 - z * b) - z ^ 2 * g ^ 2 ≠ 0) :
    (1 / ((1 - z * a) * (1 - z * b) - z ^ 2 * g ^ 2)) * (1 - z * b) =
      1 / (1 - z * a - z ^ 2 * g ^ 2 / (1 - z * b)) := by
  have e : 1 - z * a - z ^ 2 * g ^ 2 / (1 - z * b) =
      ((1 - z * a) * (1 - z * b) - z ^ 2 * g ^ 2) / (1 - z * b) := by
    field_simp
  rw [e, one_div_div]
  field_simp

end QLF.SharedClosure
