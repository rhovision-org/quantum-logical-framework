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
>
> **`equal_split_iff_null`, `closure_equal_split`** — a transverse mode puts equal action on the
> electric and magnetic planes iff it is null; a massless closure (`GaugeAxis.light_cone`) is null, so
> its action splits evenly, `|E| = c|B|`.
>
> **`shared_pair_halves`** — a shared pair (`t` on one body, `t†` on the other) folds to `+1` exactly
> where the bodies are in opposite halves: joint closure pairs offer with confirmation, symmetrically.

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

-- ==========================================
-- §5  A massless closure splits its action evenly: |E| = c|B|
-- ==========================================

/-- **Electric action** of a plane-wave mode `F = K ∧ ε` in temporal gauge (`ε₀ = 0`): the
time–space components `F₀ᵢ = K₀ εᵢ`, squared and summed. -/
noncomputable def electricAction (K0 ex ey ez : ℝ) : ℝ :=
  (K0 * ex) ^ 2 + (K0 * ey) ^ 2 + (K0 * ez) ^ 2

/-- **Magnetic action** of the same mode: the space–space components `Fᵢⱼ = Kᵢ εⱼ − Kⱼ εᵢ`, squared and
summed over the three magnetic planes. -/
noncomputable def magneticAction (Kx Ky Kz ex ey ez : ℝ) : ℝ :=
  (Kx * ey - Ky * ex) ^ 2 + (Ky * ez - Kz * ey) ^ 2 + (Kz * ex - Kx * ez) ^ 2

/-- **Electric minus magnetic** is the mode's mass shell times its amplitude, plus its longitudinal
part: `E² − B² = (K₀² − |K|²)|ε|² + (K·ε)²` (Lagrange's identity). -/
theorem electric_sub_magnetic (K0 Kx Ky Kz ex ey ez : ℝ) :
    electricAction K0 ex ey ez - magneticAction Kx Ky Kz ex ey ez =
      (K0 ^ 2 - (Kx ^ 2 + Ky ^ 2 + Kz ^ 2)) * (ex ^ 2 + ey ^ 2 + ez ^ 2) +
        (Kx * ex + Ky * ey + Kz * ez) ^ 2 := by
  unfold electricAction magneticAction
  ring

/-- **Half electric, half magnetic exactly on the light cone.** For a transverse mode
(`K·ε = 0`) of non-zero amplitude, the electric and magnetic actions are equal if and only if the mode
is null, `K₀² = |K|²`. -/
theorem equal_split_iff_null (K0 Kx Ky Kz ex ey ez : ℝ)
    (ht : Kx * ex + Ky * ey + Kz * ez = 0) (hε : ex ^ 2 + ey ^ 2 + ez ^ 2 ≠ 0) :
    electricAction K0 ex ey ez = magneticAction Kx Ky Kz ex ey ez ↔
      K0 ^ 2 = Kx ^ 2 + Ky ^ 2 + Kz ^ 2 := by
  have h := electric_sub_magnetic K0 Kx Ky Kz ex ey ez
  constructor
  · intro hEB
    have h0 : (K0 ^ 2 - (Kx ^ 2 + Ky ^ 2 + Kz ^ 2)) * (ex ^ 2 + ey ^ 2 + ez ^ 2) = 0 := by
      linear_combination hEB - h - (Kx * ex + Ky * ey + Kz * ez) * ht
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · exact absurd h1 hε
  · intro hK
    linear_combination h + (ex ^ 2 + ey ^ 2 + ez ^ 2) * hK + (Kx * ex + Ky * ey + Kz * ez) * ht

/-- **A massless closure carries equal electric and magnetic action.** If the clock phase `ω` cancels
the spatial phase on a non-zero state (zero free action per step, `GaugeAxis.light_cone`), then every
transverse mode at that `(ω, k)` puts the same action on the electric (time–space) planes as on the
magnetic (space–space) ones: `|E| = c|B|`. Mead's "half lateral, half transverse", read as Jim reads
it, holds exactly for the closure and fails off it. -/
theorem closure_equal_split (w ky kx kz ex ey ez : ℝ) (ψ : Fin 2 → ℂ) (hψ : ψ ≠ 0)
    (hclose : ((w : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Mass.weyl (ky : ℂ) (kx : ℂ) (kz : ℂ)) *ᵥ ψ = 0)
    (ht : kx * ex + ky * ey + kz * ez = 0) :
    electricAction w ex ey ez = magneticAction kx ky kz ex ey ez := by
  have hl := GaugeAxis.light_cone (w : ℂ) (ky : ℂ) (kx : ℂ) (kz : ℂ) ψ hψ hclose
  have hr : w ^ 2 = ky ^ 2 + kx ^ 2 + kz ^ 2 := by exact_mod_cast hl
  have h := electric_sub_magnetic w kx ky kz ex ey ez
  linear_combination h + (ex ^ 2 + ey ^ 2 + ez ^ 2) * hr + (kx * ex + ky * ey + kz * ez) * ht

-- ==========================================
-- §6  A shared pair forces the halves opposite
-- ==========================================

open Kronecker

private theorem kron_sub_left (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, sub_mul]

private theorem kron_sub_right (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, mul_sub]

/-- **A shared pair's joint fold separates opposite halves from equal ones.** When `t` sits on one body
and `t†` on the other, the composite fold `t ⊗ t†` (`QLF_TensorFromClosure`) is `+1` exactly where one
body is in its forward half and the other in its backward half, and `−1` where both are in the same
half. So joint closure pairs an offer with a confirmation. The expression is symmetric under swapping
the bodies, so the fold does not say which body is the emitter. -/
theorem shared_pair_halves (t : Twist) :
    t.toMatrix ⊗ₖ t.conj.toMatrix =
      (fix t ⊗ₖ fix t.conj + fix t.conj ⊗ₖ fix t) -
        (fix t ⊗ₖ fix t + fix t.conj ⊗ₖ fix t.conj) := by
  have h1 := DiracWalk.fix_sub_conj t
  have h2 : fix t.conj - fix t = t.conj.toMatrix := by
    have h := DiracWalk.fix_sub_conj t.conj
    rwa [show t.conj.conj = t by cases t <;> rfl] at h
  rw [← h1, ← h2, kron_sub_left, kron_sub_right, kron_sub_right]
  abel

end QLF.MeadTransaction
