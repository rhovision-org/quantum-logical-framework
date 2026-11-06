import QLF_NonAbelianField

/-!
# QLF_NonAbelianGauss — the non-abelian Gauss identity of Wilson's action

Issue #207. [`QLF_NonAbelianField`](QLF_NonAbelianField.lean) derived the lattice Yang–Mills equation
`A(M_k(z) U_k(z)) = 0` at each link, with `M` Wilson's staple sum and `A(X) = X − Xᴴ`. This module
proves the identity those equations satisfy **off shell**, for every link configuration: the
non-abelian Gauss law in its Noether form.

* **`noether`.** At every site `y`,
  `Σ_k A(U_k(y) M_k(y)) = Σ_k A(M_k(y − e_k) U_k(y − e_k))`.
  Each plaquette through `y` enters twice, once through each of its two links at `y`, and the two
  entries cancel corner by corner. No unitarity is needed.
* **`gauss_covariant`.** For unitary links this reads
  `Σ_k U_k(y) E_k(y) U_k(y)ᴴ = Σ_k E_k(y − e_k)` with `E_k(z) = A(M_k(z) U_k(z))` the field-equation
  value at the link: the **covariant divergence** of the field equation vanishes identically,
  the outgoing values parallel-transported back to `y` balancing the incoming ones.
* **`gauss_on_shell`.** So if the field equation is sourced, `E_k(z) = J_k(z)`, the source must obey
  the same covariant conservation at every site: the colour charge a closure can carry is fixed by
  the field it closes with. This is the non-abelian Gauss law as a consistency condition, the
  analogue of [`QLF_GaussLaw`](QLF_GaussLaw.lean)'s abelian time-link equation.

**Not here.** A time step for matrix links, so Gauss's law as the time-link equation of a dynamical
history, and the walk's colour current as the source. No axioms.

**Credit.** The identity is the lattice form of the Noether identity of gauge invariance (the
contracted Bianchi identity `D_μ D_ν F^{μν} = 0`); see Creutz, *Quarks, Gluons and Lattices*
(Cambridge, 1983), and for the lattice Gauss law Kogut and Susskind (*Phys. Rev. D* **11**, 395
(1975)). Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.NonAbelianGauss

open Matrix QLF.NonAbelian QLF.NonAbelianField

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {N n : ℕ}

/-- The anti-Hermitian part, doubled. -/
def A (X : L N) : L N := X - Xᴴ

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
lemma A_sum {ι : Type*} (s : Finset ι) (f : ι → L N) : A (∑ i ∈ s, f i) = ∑ i ∈ s, A (f i) := by
  simp [A, conjTranspose_sum, Finset.sum_sub_distrib]

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
lemma A_add (X Y : L N) : A (X + Y) = A X + A Y := by
  simp only [A, conjTranspose_add]; abel

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
lemma mul_ite_at (c : Prop) [Decidable c] (Z Z' X : L N) (h : c → Z = Z') :
    Z * (if c then X else 0) = if c then Z' * X else 0 := by
  split_ifs with hc
  · rw [h hc]
  · rw [Matrix.mul_zero]

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
lemma ite_mul_at (c : Prop) [Decidable c] (Z Z' X : L N) (h : c → Z = Z') :
    (if c then X else 0) * Z = if c then X * Z' else 0 := by
  split_ifs with hc
  · rw [h hc]
  · rw [Matrix.zero_mul]

omit [AddCommGroup S] [Fintype S] [DecidableEq S] in
lemma A_ite (c : Prop) [Decidable c] (X : L N) : A (if c then X else 0) = if c then A X else 0 := by
  split_ifs <;> simp [A]

/-- **The Noether identity of Wilson's action** at the site `y`. -/
theorem noether (e : Fin n → S) (U : Fin n → S → L N) (y : S) :
    ∑ k, A (U k y * staple e U k y) = ∑ k, A (staple e U k (y - e k) * U k (y - e k)) := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  unfold staple
  simp only [Finset.mul_sum, Finset.sum_mul, A_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hij : i = j
  · simp [hij, A]
  simp only [hij, ↓reduceIte]
  rw [Fintype.sum_eq_add i j hij]
  · have hji : ¬ j = i := fun h => hij h.symm
    have c : x + e j + e i = x + e i + e j := add_right_comm _ _ _
    simp only [true_and, hij, hji, false_and, ↓reduceIte, add_zero, zero_add,
      eq_sub_iff_add_eq, c, Matrix.mul_add, Matrix.add_mul]
    rw [mul_ite_at (x = y) (U i y) (U i x) _ (fun h => by rw [h]),
      mul_ite_at (x + e j = y) (U i y) (U i (x + e j)) _ (fun h => by rw [h]),
      ite_mul_at (x + e i = y) (U i (y - e i)) (U i x) _
        (fun h => by rw [← h, add_sub_cancel_right]),
      ite_mul_at (x + e i + e j = y) (U i (y - e i)) (U i (x + e j)) _
        (fun h => by rw [← h, show x + e i + e j - e i = x + e j by abel]),
      mul_ite_at (x + e i = y) (U j y) (U j (x + e i)) _ (fun h => by rw [h]),
      mul_ite_at (x = y) (U j y) (U j x) _ (fun h => by rw [h]),
      ite_mul_at (x + e i + e j = y) (U j (y - e j)) (U j (x + e i)) _
        (fun h => by rw [← h, add_sub_cancel_right]),
      ite_mul_at (x + e j = y) (U j (y - e j)) (U j x) _
        (fun h => by rw [← h, add_sub_cancel_right])]
    simp only [A_add, A_ite]
    split_ifs <;>
      simp only [add_zero, zero_add, sub_zero, zero_sub, A, conjTranspose_mul,
        conjTranspose_conjTranspose, Matrix.mul_assoc] <;> abel
  · intro k hk
    have h1 : ¬ i = k := fun h => hk.1 h.symm
    have h2 : ¬ j = k := fun h => hk.2 h.symm
    simp [h1, h2, A]

/-- The field-equation value at the link `(k, z)`: `E_k(z) = A(M_k(z) U_k(z))`. -/
noncomputable def E (e : Fin n → S) (U : Fin n → S → L N) (k : Fin n) (z : S) : L N :=
  A (staple e U k z * U k z)

/-- **The covariant divergence of the field equation vanishes identically.** -/
theorem gauss_covariant (e : Fin n → S) (U : Fin n → S → L N) (hU : ∀ k x, Unitary (U k x))
    (y : S) : ∑ k, U k y * E e U k y * (U k y)ᴴ = ∑ k, E e U k (y - e k) := by
  rw [show ∑ k, E e U k (y - e k) = ∑ k, A (staple e U k (y - e k) * U k (y - e k)) from rfl,
    ← noether]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := (hU k y).2
  simp only [E, A, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (U k y) (U k y)ᴴ, h, Matrix.one_mul]

/-- **A source of the field equation must be covariantly conserved.** -/
theorem gauss_on_shell (e : Fin n → S) (U : Fin n → S → L N) (hU : ∀ k x, Unitary (U k x))
    (J : Fin n → S → L N) (hJ : ∀ k z, E e U k z = J k z) (y : S) :
    ∑ k, U k y * J k y * (U k y)ᴴ = ∑ k, J k (y - e k) := by
  simp only [← hJ]
  exact gauss_covariant e U hU y

end QLF.NonAbelianGauss
