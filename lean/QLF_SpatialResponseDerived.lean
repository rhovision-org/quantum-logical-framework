import Mathlib

/-!
# QLF_SpatialResponseDerived — the joint-step identity behind #287 SR3

[`Spatial_Response_Derived.md`](../Spatial_Response_Derived.md) tests whether binding contracts
space with both ledgers derived from the same twist steps. Body `A` steps `p` and body `B` steps `q`,
both unit vectors of `ℤ³`. The orientation ledger is `ΔS = 2 p·q`, the joint-cost identity of
[`QLF_MagneticOrientation`](QLF_MagneticOrientation.lean) applied to the steps. The separation
ledger is the change in `r = x_A − x_B`.

## What is proved

* **`joint_step_identity`.** `|r + p − q|² − |r|² = 2 r·(p − q) + |p|² + |q|² − ΔS`, for all
  vectors. It is the parallelogram law.
* **`symmetric_mean`.** Summed over `r` and `−r`, the cross term cancels:
  `Δ(r) + Δ(−r) = 2(|p|² + |q|² − ΔS)`. For unit steps, the mean growth of `|r|²` is `2 − ΔS`:
  `+4` for opposite steps, `0` for like steps and `2` for orthogonal ones (`unit_symmetric_mean`).
  The binding orientation pushes apart on average.
* **`orthogonal_brings_closer`.** An orthogonal pair (`ΔS = 0`) can bring the bodies closer, so
  `Δd < 0 ⇏ ΔS < 0` (R1).
* **`opposite_pushes_apart`.** An opposite pair (`ΔS = −2`) can push them apart, so
  `ΔS < 0 ⇏ Δd < 0` (R2).

These are identities about vectors, true for any steps. By method rule 4 they are bookkeeping of the
forward map. Their use is negative: the orientation ledger alone cannot carry a contraction law.

No axioms beyond Lean's.
-/

namespace QLF.SpatialResponseDerived

/-- The dot product on `ℤ³`. -/
def dot (a b : Fin 3 → ℤ) : ℤ := ∑ i, a i * b i

/-- The orientation ledger of a joint step. -/
def deltaS (p q : Fin 3 → ℤ) : ℤ := 2 * dot p q

/-- The change in squared separation when `A` steps `p` and `B` steps `q`. -/
def deltaSq (r p q : Fin 3 → ℤ) : ℤ := dot (r + p - q) (r + p - q) - dot r r

/-- **The joint-step identity** (the parallelogram law). -/
theorem joint_step_identity (r p q : Fin 3 → ℤ) :
    deltaSq r p q = 2 * dot r (p - q) + dot p p + dot q q - deltaS p q := by
  simp only [deltaSq, deltaS, dot, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply]
  ring

/-- **The symmetric mean.** Over `r` and `−r`, the cross term cancels. -/
theorem symmetric_mean (r p q : Fin 3 → ℤ) :
    deltaSq r p q + deltaSq (-r) p q = 2 * (dot p p + dot q q - deltaS p q) := by
  simp only [deltaSq, deltaS, dot, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

/-- For unit steps the mean growth of `|r|²` is `2 − ΔS`. -/
theorem unit_symmetric_mean (r p q : Fin 3 → ℤ) (hp : dot p p = 1) (hq : dot q q = 1) :
    deltaSq r p q + deltaSq (-r) p q = 2 * (2 - deltaS p q) := by
  rw [symmetric_mean, hp, hq]
  ring

/-- The `ℓ¹` separation. -/
def l1 (a : Fin 3 → ℤ) : ℤ := ∑ i, |a i|

/-- **R1 witness.** Steps `+x` and `+y` are orthogonal (`ΔS = 0`), yet from `r = (−1, 1, 0)` they
    bring the bodies together. -/
theorem orthogonal_brings_closer :
    deltaS ![1, 0, 0] ![0, 1, 0] = 0 ∧
      l1 (![-1, 1, 0] + ![1, 0, 0] - ![0, 1, 0]) < l1 ![-1, 1, 0] := by
  refine ⟨?_, ?_⟩ <;> simp [deltaS, dot, l1, Fin.sum_univ_three]

/-- **R2 witness.** Steps `+x` and `−x` are opposite (`ΔS = −2`), yet from `r = 0` they push the
    bodies apart. -/
theorem opposite_pushes_apart :
    deltaS ![1, 0, 0] ![-1, 0, 0] = -2 ∧
      l1 ((0 : Fin 3 → ℤ) + ![1, 0, 0] - ![-1, 0, 0]) > l1 (0 : Fin 3 → ℤ) := by
  refine ⟨?_, ?_⟩ <;> simp [deltaS, dot, l1, Fin.sum_univ_three]

end QLF.SpatialResponseDerived
