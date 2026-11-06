import QLF_NonAbelianAction

/-!
# QLF_NonAbelianField — the lattice Yang–Mills equation as stationarity

Issue #207. [`QLF_NonAbelianAction`](QLF_NonAbelianAction.lean) gave matrix links Wilson's action.
This module varies it. On distinct directions each plaquette holonomy contains a given link once,
either as `U` or as `Uᴴ`, so the action is **affine in each link**. Its variation at one link is
therefore exact, not a first-order approximation:

* **`hol_bump`.** Replacing the link `U_k(y)` by `U_k(y) + ε D` changes each off-diagonal plaquette
  holonomy by exactly `ε` times a matrix `dHol`, linear in `D`. This needs only `e_i ≠ 0`.
* **`wilsonOff_bump`, `force_eq`.** The action changes by exactly `−(ε/2) · Re tr(D · M)`, where
  `M = staple U k y` is the sum of the three-link products that close each plaquette through the
  link (Wilson's *staples*).
* **`stationary_iff`.** `Re tr(V X M) = 0` for every anti-Hermitian `X` exactly when `M V` is
  Hermitian.
* **`yang_mills_iff`.** The action is unchanged along every tangent direction `U_k(y) X` of the
  unitary group at the link (`Xᴴ = −X`) **if and only if** `M U_k(y) − (M U_k(y))ᴴ = 0`. That is the
  lattice Yang–Mills field equation at the link, here the stationarity condition of a finite action.
* **`wilson_eq_off`.** For unitary links the diagonal plaquettes contribute nothing, so the action
  of `QLF_NonAbelianAction` is the off-diagonal one varied here.

**Not here.** Dynamics (a time step for matrix links and its energy), coupling the colour current of
[`QLF_NonAbelian`](QLF_NonAbelian.lean)'s walk as a source, the non-abelian Gauss law, and which
colour group the twists select. No axioms.

**Credit.** The lattice field equation (the anti-Hermitian part of link times staple sum) is
standard lattice gauge theory after Wilson (*Phys. Rev. D* **10**, 2445 (1974)); see e.g. Creutz,
*Quarks, Gluons and Lattices* (Cambridge, 1983). Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.NonAbelianField

open Matrix QLF.NonAbelian QLF.NonAbelianAction ComplexOrder

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {N n : ℕ}

/-- Wilson's action over plaquettes in distinct directions. -/
noncomputable def wilsonOff (e : Fin n → S) (U : Fin n → S → L N) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, ∑ x, if i = j then 0 else plaq (holonomy e U i j x)

omit [Fintype S] [DecidableEq S] in
lemma holonomy_diag (e : Fin n → S) (U : Fin n → S → L N) (hU : ∀ k x, Unitary (U k x))
    (i : Fin n) (x : S) : holonomy e U i i x = 1 := by
  unfold holonomy
  rw [Matrix.mul_assoc (U i x), (hU i (x + e i)).2, Matrix.mul_one, (hU i x).2]

omit [DecidableEq S] in
/-- **For unitary links only distinct directions contribute.** -/
theorem wilson_eq_off (e : Fin n → S) (U : Fin n → S → L N) (hU : ∀ k x, Unitary (U k x)) :
    wilson e U = wilsonOff e U := by
  unfold wilson wilsonOff
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · subst h
    rw [holonomy_diag e U hU]
    exact (plaq_eq_zero_iff 1 ⟨by simp, by simp⟩).mpr rfl
  · rfl

/-- Replace one link. -/
def bump (k : Fin n) (y : S) (V : L N) (U : Fin n → S → L N) : Fin n → S → L N :=
  fun i x => if i = k ∧ x = y then V else U i x

/-- The change of a plaquette holonomy, per unit `ε`, when `U_k(y)` moves by `ε D`. -/
noncomputable def dHol (e : Fin n → S) (U : Fin n → S → L N) (k : Fin n) (y : S) (D : L N)
    (i j : Fin n) (x : S) : L N :=
  (if i = k ∧ x = y then D * U j (x + e i) * (U i (x + e j))ᴴ * (U j x)ᴴ else 0) +
  (if j = k ∧ x + e i = y then U i x * D * (U i (x + e j))ᴴ * (U j x)ᴴ else 0) +
  (if i = k ∧ x + e j = y then U i x * U j (x + e i) * Dᴴ * (U j x)ᴴ else 0) +
  (if j = k ∧ x = y then U i x * U j (x + e i) * (U i (x + e j))ᴴ * Dᴴ else 0)

omit [Fintype S] in
/-- **Each off-diagonal holonomy is affine in each link.** -/
theorem hol_bump (e : Fin n → S) (he : ∀ i, e i ≠ 0) (U : Fin n → S → L N) (k : Fin n) (y : S)
    (D : L N) (ε : ℝ) {i j : Fin n} (hij : i ≠ j) (x : S) :
    holonomy e (bump k y (U k y + (ε : ℂ) • D) U) i j x =
      holonomy e U i j x + (ε : ℂ) • dHol e U k y D i j x := by
  unfold holonomy bump dHol
  by_cases hi : i = k <;> by_cases hj : j = k
  · exact absurd (hi.trans hj.symm) hij
  · subst hi
    by_cases hx : x = y
    · subst hx
      have h3 : ¬ x + e j = x := fun h => he j (by simpa using h)
      simp [hj, h3, Matrix.add_mul]
    · by_cases hx3 : x + e j = y
      · subst hx3
        simp [hj, hx, conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add]
      · simp [hj, hx, hx3]
  · subst hj
    by_cases hx : x = y
    · subst hx
      have h2 : ¬ x + e i = x := fun h => he i (by simpa using h)
      simp [hi, h2, conjTranspose_add, conjTranspose_smul, Matrix.mul_add]
    · by_cases hx2 : x + e i = y
      · subst hx2
        simp [hi, hx, Matrix.add_mul, Matrix.mul_add]
      · simp [hi, hx, hx2]
  · simp [hi, hj]

/-- The first-variation coefficient. -/
noncomputable def force (e : Fin n → S) (U : Fin n → S → L N) (k : Fin n) (y : S) (D : L N) : ℝ :=
  ∑ i, ∑ j, ∑ x, if i = j then 0 else (trace (dHol e U k y D i j x)).re

/-- **The action changes by exactly `−(ε/2)` times the force.** -/
theorem wilsonOff_bump (e : Fin n → S) (he : ∀ i, e i ≠ 0) (U : Fin n → S → L N) (k : Fin n)
    (y : S) (D : L N) (ε : ℝ) :
    wilsonOff e (bump k y (U k y + (ε : ℂ) • D) U) = wilsonOff e U - ε / 2 * force e U k y D := by
  have hpt : ∀ i j x, (if i = j then (0 : ℝ) else
      plaq (holonomy e (bump k y (U k y + (ε : ℂ) • D) U) i j x)) =
      (if i = j then 0 else plaq (holonomy e U i j x)) -
        ε * (if i = j then 0 else (trace (dHol e U k y D i j x)).re) := by
    intro i j x
    split_ifs with h
    · simp
    · rw [hol_bump e he U k y D ε h]
      unfold plaq
      rw [trace_add, trace_smul]
      simp
      ring
  unfold wilsonOff force
  simp only [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **Wilson's staple sum** at the link `(k, y)`. -/
noncomputable def staple (e : Fin n → S) (U : Fin n → S → L N) (k : Fin n) (y : S) : L N :=
  ∑ i, ∑ j, ∑ x, if i = j then 0 else
    ((if i = k ∧ x = y then U j (x + e i) * (U i (x + e j))ᴴ * (U j x)ᴴ else 0) +
     (if j = k ∧ x + e i = y then (U i (x + e j))ᴴ * (U j x)ᴴ * U i x else 0) +
     (if i = k ∧ x + e j = y then (U i x * U j (x + e i))ᴴ * U j x else 0) +
     (if j = k ∧ x = y then (U i x * U j (x + e i) * (U i (x + e j))ᴴ)ᴴ else 0))

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
lemma re_tr_ct (Z D : L N) : (trace (Z * Dᴴ)).re = (trace (D * Zᴴ)).re := by
  rw [show Z * Dᴴ = (D * Zᴴ)ᴴ by rw [conjTranspose_mul, conjTranspose_conjTranspose],
    trace_conjTranspose]
  simp

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
lemma re_tr_ite (c : Prop) [Decidable c] (X Y D : L N) (h : (trace X).re = (trace (D * Y)).re) :
    (trace (if c then X else 0)).re = (trace (D * if c then Y else 0)).re := by
  split_ifs <;> simp [h]

/-- **The force is `Re tr(D · staple)`.** -/
theorem force_eq (e : Fin n → S) (U : Fin n → S → L N) (k : Fin n) (y : S) (D : L N) :
    force e U k y D = (trace (D * staple e U k y)).re := by
  unfold force staple
  simp only [Finset.mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun x _ => ?_
  by_cases h : i = j
  · simp [h]
  simp only [h, ↓reduceIte]
  unfold dHol
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  simp only [trace_add, Complex.add_re]
  have h1 := re_tr_ite (i = k ∧ x = y) (D * U j (x + e i) * (U i (x + e j))ᴴ * (U j x)ᴴ)
    (U j (x + e i) * (U i (x + e j))ᴴ * (U j x)ᴴ) D (by simp only [Matrix.mul_assoc])
  have h2 := re_tr_ite (j = k ∧ x + e i = y) (U i x * D * (U i (x + e j))ᴴ * (U j x)ᴴ)
    ((U i (x + e j))ᴴ * (U j x)ᴴ * U i x) D (by
      rw [Matrix.mul_assoc (U i x), Matrix.mul_assoc (U i x), trace_mul_comm]
      simp only [Matrix.mul_assoc])
  have h3 := re_tr_ite (i = k ∧ x + e j = y) (U i x * U j (x + e i) * Dᴴ * (U j x)ᴴ)
    ((U i x * U j (x + e i))ᴴ * U j x) D (by
      rw [trace_mul_comm, show (U j x)ᴴ * (U i x * U j (x + e i) * Dᴴ) =
        ((U j x)ᴴ * (U i x * U j (x + e i))) * Dᴴ by simp only [Matrix.mul_assoc], re_tr_ct]
      simp [conjTranspose_mul, Matrix.mul_assoc])
  have h4 := re_tr_ite (j = k ∧ x = y) (U i x * U j (x + e i) * (U i (x + e j))ᴴ * Dᴴ)
    ((U i x * U j (x + e i) * (U i (x + e j))ᴴ)ᴴ) D (re_tr_ct _ _)
  rw [h1, h2, h3, h4]

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
/-- **Stationarity along every anti-Hermitian direction is Hermiticity of `M V`.** -/
theorem stationary_iff (V M : L N) :
    (∀ X : L N, Xᴴ = -X → (trace (V * X * M)).re = 0) ↔ M * V - (M * V)ᴴ = 0 := by
  have cyc : ∀ X : L N, trace (V * X * M) = trace (X * (M * V)) := fun X => by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  constructor
  · intro h
    set Z := M * V
    set B := Z - Zᴴ with hB
    have hBa : Bᴴ = -B := by rw [hB, conjTranspose_sub, conjTranspose_conjTranspose]; abel
    have h0 : (trace (B * Z)).re = 0 := by rw [← cyc]; exact h B hBa
    have h1 : (trace (B * Zᴴ)).re = -(trace (B * Z)).re := by
      rw [re_tr_ct, hBa, Matrix.mul_neg, trace_neg, Complex.neg_re, trace_mul_comm]
    have hn : (trace (Bᴴ * B)).re = 0 := by
      rw [hBa, Matrix.neg_mul, trace_neg, Complex.neg_re]
      conv_lhs => rw [show B * B = B * Z - B * Zᴴ by rw [hB, Matrix.mul_sub]]
      rw [trace_sub, Complex.sub_re, h1, h0]; ring
    have hpos := Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self B).trace_nonneg
    have hz : trace (Bᴴ * B) = 0 := Complex.ext hn hpos.2.symm
    exact trace_conjTranspose_mul_self_eq_zero_iff.mp hz
  · intro h X hX
    have hZ : (M * V)ᴴ = M * V := (sub_eq_zero.mp h).symm
    rw [cyc]
    have h1 := re_tr_ct X (M * V)
    rw [hZ, trace_mul_comm, hX, Matrix.mul_neg, trace_neg, Complex.neg_re, trace_mul_comm] at h1
    linarith

/-- **The lattice Yang–Mills equation is stationarity of Wilson's action.** The action is unchanged
along every tangent direction `U_k(y) X` (`X` anti-Hermitian) at the link `(k, y)` exactly when
`staple · U_k(y)` is Hermitian. -/
theorem yang_mills_iff (e : Fin n → S) (he : ∀ i, e i ≠ 0) (U : Fin n → S → L N) (k : Fin n)
    (y : S) :
    (∀ X : L N, Xᴴ = -X → ∀ ε : ℝ,
        wilsonOff e (bump k y (U k y + (ε : ℂ) • (U k y * X)) U) = wilsonOff e U) ↔
      staple e U k y * U k y - (staple e U k y * U k y)ᴴ = 0 := by
  rw [← stationary_iff]
  refine forall_congr' fun X => imp_congr_right fun _ => ?_
  simp only [wilsonOff_bump e he, force_eq]
  constructor
  · intro h
    have := h 1
    linarith
  · intro h ε
    rw [h]; ring

end QLF.NonAbelianField
