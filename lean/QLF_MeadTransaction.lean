import QLF_GaugeAxis

set_option linter.unusedVariables false

/-!
# QLF_MeadTransaction — **a step is half offer, half confirmation; the halves move at `±c`**

Companion to [`Collective_Electrodynamics.md`](../Collective_Electrodynamics.md) §6, which compares
Carver Mead's *Collective Electrodynamics* (2000) and Cramer & Mead (2020, *Symmetry* 12, 1373) with
what QLF proves. This module collects the algebra behind that comparison. It reads the realizable
step of [`QLF_RealizableWalk`](QLF_RealizableWalk.lean),

  `realStep t k = e^{ik} · fix t + e^{−ik} · fix t̄`,

as a **matched pair**: a forward (retarded, "offer") half on `fix t` and a backward (advanced,
"confirmation") half on `fix t̄`, the conjugate twist.

> **`mead_transaction`** — the two halves are complementary projectors (`fix t + fix t̄ = 1`), the
> twist is their difference (`M(t) = fix t − fix t̄`), and each half is an eigenspace of the twist:
> `M(t)·fix t = fix t`, `M(t)·fix t̄ = −fix t̄`.
>
> **`trace_fix_spatial`** — on every spatial axis each half has trace `1` of `2`: the step is split
> **exactly half and half**.
>
> **`gauge_no_split`** — on the gauge (time) axis there is no split: one half is everything and the
> other nothing, so the gauge step is a pure clock phase `e^{ik}` (from
> [`QLF_GaugeAxis`](QLF_GaugeAxis.lean)).
>
> **`realStep_sub_neg`, `realStep_add_neg`** — retarded minus advanced is `2i sin k · M(t)`, the
> whole twist with the factor `2`; retarded plus advanced is `2 cos k · 1`, which carries no twist.
>
> **`electric_eq_magnetic_iff`** — time–space (electric) planes equal space–space (magnetic) planes,
> `d = d(d−1)/2`, only for `d = 3` spatial axes: half and half is a three-dimensional fact.

Since the generator of the step is `i·M(t)` (`DiracWalk.realStep_generator`), `M(t)` is the step's
velocity in lattice units, and the halves are its eigenspaces with velocity `+1` and `−1`. The two
halves of one step therefore move at `+c` and `−c`: a spread of `2c`, half each way. This is the
discrete form of Dirac's observation that the velocity operator `cα` of his equation has eigenvalues
`±c` (the root of Schrödinger's 1930 *Zitterbewegung*).

**Scope (method rule 4).** These are identities about one step. They change no count of ways, so they
are a *reading* of the step in Mead's language, not evidence for it. The one step that would carry
content, that the two halves are separately the emitter's offer and the absorber's confirmation in a
two-body exchange, is not proved here. No axioms.
-/

namespace QLF.MeadTransaction

open QLF QLF.ClosureChannels Matrix

-- ==========================================
-- §1  The two halves are the twist's eigenspaces
-- ==========================================

/-- The forward half is the `+1` eigenspace of the twist. -/
theorem twist_mul_fix (t : Twist) : t.toMatrix * fix t = fix t := by
  unfold fix
  rw [mul_smul_comm, mul_add, mul_one, ClosureUnitarity.twist_sq]
  rw [← sub_eq_zero]
  module

/-- The backward half is the `−1` eigenspace of the twist. -/
theorem twist_mul_fix_conj (t : Twist) : t.toMatrix * fix t.conj = -fix t.conj := by
  unfold fix
  rw [ClosureUnitarity.conj_toMatrix, mul_smul_comm, mul_add, mul_one, mul_neg,
    ClosureUnitarity.twist_sq]
  rw [← sub_eq_zero]
  module

/-- **The matched pair.** A realizable step is a forward phase on one half and a backward phase on
the other; the halves are complementary, the twist (the step's velocity) is their difference, and
the halves are its `+1` and `−1` eigenspaces. -/
theorem mead_transaction (t : Twist) (k : ℝ) :
    realStep t k =
        Complex.exp (k * Complex.I) • fix t + Complex.exp (-(k * Complex.I)) • fix t.conj ∧
      fix t + fix t.conj = 1 ∧
      t.toMatrix = fix t - fix t.conj ∧
      t.toMatrix * fix t = fix t ∧
      t.toMatrix * fix t.conj = -fix t.conj :=
  ⟨rfl, fix_add_conj t, (DiracWalk.fix_sub_conj t).symm, twist_mul_fix t, twist_mul_fix_conj t⟩

-- ==========================================
-- §2  Half and half on space; no split on time
-- ==========================================

/-- **Exactly half and half.** On a spatial axis each half carries trace `1` of the identity's `2`. -/
theorem trace_fix_spatial (t : Twist) (hp : t ≠ Twist.plus) (hm : t ≠ Twist.minus) :
    Matrix.trace (fix t) = 1 := by
  cases t <;>
    simp_all [fix, Twist.toMatrix, σx, σy, σz, Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;>
    norm_num

/-- **On the gauge (time) axis there is no split**: the forward half is everything and the backward
half nothing (`GaugeAxis.fix_plus`, `GaugeAxis.fix_minus`), so a gauge step is a pure clock phase
(`GaugeAxis.gaugeStep_eq`). -/
theorem gauge_no_split : fix Twist.plus = 1 ∧ fix Twist.minus = 0 :=
  ⟨GaugeAxis.fix_plus, GaugeAxis.fix_minus⟩

-- ==========================================
-- §3  Retarded and advanced
-- ==========================================

/-- **Retarded minus advanced carries the whole twist, with the factor `2`.** Reversing the momentum
is the adjoint (`realStep_neg`), so this is the step minus its time reverse. -/
theorem realStep_sub_neg (t : Twist) (k : ℝ) :
    realStep t k - realStep t (-k) = (2 * ((Real.sin k : ℝ) : ℂ) * Complex.I) • t.toMatrix := by
  rw [realStep_eq_cos_sin, realStep_eq_cos_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  module

/-- **Retarded plus advanced carries no twist**: it is a multiple of the identity. -/
theorem realStep_add_neg (t : Twist) (k : ℝ) :
    realStep t k + realStep t (-k) =
      (2 * ((Real.cos k : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [realStep_eq_cos_sin, realStep_eq_cos_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  module

-- ==========================================
-- §4  Electric and magnetic: half and half only with three spatial axes
-- ==========================================

/-- **Electric planes equal magnetic planes only for three spatial axes.** With `d` spatial axes and
one gauge (time) axis, the time–space planes (electric, Mead's "lateral") number `d` and the
space–space planes (magnetic, "transverse") number `d(d−1)/2`. They are equal, `2d = d(d−1)`, exactly
when `d = 0` or `d = 3`. This is the counting face of electric–magnetic duality, which needs four
dimensions; QLF's alphabet has three spatial axes, so its orthogonal folds split evenly. -/
theorem electric_eq_magnetic_iff (d : ℕ) : 2 * d = d * (d - 1) ↔ d = 0 ∨ d = 3 := by
  constructor
  · intro h
    by_cases hd : d ≤ 3
    · interval_cases d <;> simp_all
    · exfalso
      obtain ⟨n, rfl⟩ : ∃ n, d = n + 4 := ⟨d - 4, by omega⟩
      have e : n + 4 - 1 = n + 3 := by omega
      rw [e] at h
      nlinarith
  · rintro (rfl | rfl) <;> norm_num

end QLF.MeadTransaction
