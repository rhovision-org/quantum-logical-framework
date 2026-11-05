import QLF_FieldEnergy

/-!
# QLF_Courant — the Courant bound `nτ² ≤ 1` for the field leapfrog

Issue #207. [`QLF_FieldEnergy`](QLF_FieldEnergy.lean) proved the leapfrog's field energy positive
for `2nτ² ≤ 1`, from the crude bound `|K A|² ≤ 8n ⟨A, K A⟩`. On a periodic lattice the largest
eigenvalue of `K = curl F` is `4n`, so the right condition is `nτ² ≤ 1`. This module proves it.

* **`swap_diff`.** Summation by parts twice: `Σₓ ∂_a f · ∂_b g = Σₓ ∂*_b f · ∂*_a g`, forward
  differences on the left and backward on the right.
* **`weitzenboeck`.** The lattice Weitzenböck identity
  `⟨A, K A⟩ + Σₓ (div A)² = Σᵢ Σⱼ Σₓ (Aᵢ(x + eⱼ) − Aᵢ(x))²`: curl-energy plus divergence-energy is
  the gradient energy.
* **`K_le`.** Hence `⟨A, K A⟩ ≤ 4n |A|²`: each squared difference is at most twice the sum of the
  two squares.
* **`K_sq_le_sharp`.** `|K A|² ≤ 4n ⟨A, K A⟩`, from `K_le` applied to `A − K A/(4n)`.
* **`energy_lower_sharp`, `energy_nonneg_sharp`.** The field energy satisfies
  `½(1 − nτ²) ⟨A, K A⟩ ≤ H` and `½(1 − nτ²) |E|² ≤ H`, so `H ≥ 0` when `nτ² ≤ 1`.
* **`free_bounded_sharp`.** For `nτ² < 1` the free leapfrog keeps both fields bounded for all time,
  by `2H₀/(1 − nτ²)`.

The constant cannot be improved: `4n` is the largest eigenvalue of `K` (the staggered mode, computed
for `n = 2, 3`; see [Closure_Unitarity.md](../Closure_Unitarity.md) §27), and a random field grows
without bound for `τ = 1`, `n = 2`. Lean proves sufficiency, not the eigenvalue. No axioms.

**Credit.** Courant, Friedrichs and Lewy, *Math. Ann.* **100**, 32 (1928); the identity is the
lattice form of `curl curl = grad div − Δ`. Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.Courant

open QLF.LinkAction (F F_antisymm)
open QLF.FieldEnergy

variable {S : Type*} [AddCommGroup S] [Fintype S] {n : ℕ}

/-- **Summation by parts twice.** -/
lemma swap_diff (f g : S → ℝ) (a b : S) :
    ∑ x, (f (x + a) - f x) * (g (x + b) - g x) = ∑ x, (f x - f (x - b)) * (g x - g (x - a)) := by
  have h1 : ∑ x, f (x + a) * g (x + b) = ∑ x, f (x - b) * g (x - a) :=
    Fintype.sum_equiv (Equiv.addRight (a + b)) _ _ (fun x => by
      simp only [Equiv.coe_addRight]
      rw [show x + (a + b) - b = x + a by abel, show x + (a + b) - a = x + b by abel])
  have h2 : ∑ x, f (x + a) * g x = ∑ x, f x * g (x - a) :=
    Fintype.sum_equiv (Equiv.addRight a) _ _ (fun x => by simp)
  have h3 : ∑ x, f x * g (x + b) = ∑ x, f (x - b) * g x :=
    Fintype.sum_equiv (Equiv.addRight b) _ _ (fun x => by simp)
  have e1 : ∑ x, (f (x + a) - f x) * (g (x + b) - g x) =
      ∑ x, f (x + a) * g (x + b) - ∑ x, f (x + a) * g x - ∑ x, f x * g (x + b) +
        ∑ x, f x * g x := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : ∑ x, (f x - f (x - b)) * (g x - g (x - a)) =
      ∑ x, f (x - b) * g (x - a) - ∑ x, f x * g (x - a) - ∑ x, f (x - b) * g x +
        ∑ x, f x * g x := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e2, h1, h2, h3]

/-- The gradient energy `Σᵢ Σⱼ Σₓ (Aᵢ(x + eⱼ) − Aᵢ(x))²`. -/
noncomputable def grad2 (e : Fin n → S) (A : Fin n → S → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ x, (A i (x + e j) - A i x) ^ 2

/-- **The lattice Weitzenböck identity**: `⟨A, K A⟩ + Σ (div A)² = Σ |∇A|²`. -/
theorem weitzenboeck (e : Fin n → S) (A : Fin n → S → ℝ) :
    ip A (K e A) + ∑ x, (Maxwell.div e A x) ^ 2 = grad2 e A := by
  rw [ip_K]
  have hF : ∀ i j x, F e A i j x = (A j (x + e i) - A j x) - (A i (x + e j) - A i x) := by
    intros; simp only [F]; ring
  have hsq : ∀ i j x, F e A i j x * F e A i j x =
      (A j (x + e i) - A j x) ^ 2 + (A i (x + e j) - A i x) ^ 2 -
        2 * ((A j (x + e i) - A j x) * (A i (x + e j) - A i x)) := by
    intros; rw [hF]; ring
  have hcross : ∀ i j, ∑ x, (A j (x + e i) - A j x) * (A i (x + e j) - A i x) =
      ∑ x, (A j x - A j (x - e j)) * (A i x - A i (x - e i)) := fun i j =>
    swap_diff (A j) (A i) (e i) (e j)
  have hdiv : ∑ x, (Maxwell.div e A x) ^ 2 =
      ∑ i, ∑ j, ∑ x, (A j x - A j (x - e j)) * (A i x - A i (x - e i)) := by
    unfold Maxwell.div
    simp only [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring
  have hswap : ∑ i, ∑ j, ∑ x, (A j (x + e i) - A j x) ^ 2 = grad2 e A := by
    unfold grad2; rw [Finset.sum_comm]
  simp only [hsq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcross, hswap]
  rw [hdiv]
  unfold grad2
  ring

omit [AddCommGroup S] in
/-- `|A|²` written out. -/
lemma ip_self (A : Fin n → S → ℝ) : ip A A = ∑ i, ∑ x, A i x ^ 2 := by
  unfold ip; simp only [sq]

/-- **The restoring force is at most `4n`**: `⟨A, K A⟩ ≤ 4n |A|²`. -/
theorem K_le (e : Fin n → S) (A : Fin n → S → ℝ) : ip A (K e A) ≤ 4 * n * ip A A := by
  have hw := weitzenboeck e A
  have hd : 0 ≤ ∑ x, (Maxwell.div e A x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg : grad2 e A ≤ 4 * n * ip A A := by
    unfold grad2
    rw [ip_self, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hj : ∀ j, ∑ x, (A i (x + e j) - A i x) ^ 2 ≤ 4 * ∑ x, A i x ^ 2 := by
      intro j
      have hs : ∑ x, A i (x + e j) ^ 2 = ∑ x, A i x ^ 2 :=
        Fintype.sum_equiv (Equiv.addRight (e j)) _ (fun x => A i x ^ 2) (fun _ => rfl)
      calc ∑ x, (A i (x + e j) - A i x) ^ 2
          ≤ ∑ x, (2 * A i (x + e j) ^ 2 + 2 * A i x ^ 2) :=
            Finset.sum_le_sum fun x _ => by nlinarith [sq_nonneg (A i (x + e j) + A i x)]
        _ = 4 * ∑ x, A i x ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs]; ring
    calc ∑ j, ∑ x, (A i (x + e j) - A i x) ^ 2 ≤ ∑ _j : Fin n, 4 * ∑ x, A i x ^ 2 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = 4 * n * ∑ x, A i x ^ 2 := by simp; ring
  linarith

/-- **The sharp force bound**: `|K A|² ≤ 4n ⟨A, K A⟩`. -/
theorem K_sq_le_sharp (e : Fin n → S) (A : Fin n → S → ℝ) :
    ip (K e A) (K e A) ≤ 4 * n * ip A (K e A) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [ip]
  set B := K e A
  set lam : ℝ := 4 * n
  have hl : 0 < lam := by positivity
  set s : ℝ := lam⁻¹
  have hs : s * lam = 1 := inv_mul_cancel₀ hl.ne'
  have hm := magnetic_nonneg e (fun i y => A i y - s * B i y)
  rw [K_sub_smul] at hm
  simp only [ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right] at hm
  have hAB : ip A (K e B) = ip B B := by rw [← K_symm e B A]
  have hBA : ip B (K e A) = ip B B := rfl
  have hBB := K_le e B
  have hq := ip_self_nonneg B
  have h1 : s * s * ip B (K e B) ≤ s * s * (lam * ip B B) :=
    mul_le_mul_of_nonneg_left hBB (by positivity)
  rw [hAB, hBA] at hm
  have h2 : s * s * (lam * ip B B) = s * ip B B := by
    rw [show s * s * (lam * ip B B) = s * (s * lam) * ip B B by ring, hs, mul_one]
  have h3 : 0 ≤ ip A (K e A) - s * ip B B := by nlinarith
  have h4 : lam * (s * ip B B) = ip B B := by rw [← mul_assoc, mul_comm lam s, hs, one_mul]
  nlinarith

/-- **The Courant bound.** For every `τ`, `½(1 − nτ²)⟨A, K A⟩ ≤ H` and `½(1 − nτ²)|E|² ≤ H`;
    for `nτ² ≤ 1` the field energy therefore bounds both the magnetic and the electric energy. -/
theorem energy_lower_sharp (e : Fin n → S) (τ : ℝ) (A E : Fin n → S → ℝ) :
    (1 / 2) * (1 - n * τ ^ 2) * ip A (K e A) ≤ energy e τ A E ∧
      (1 / 2) * (1 - n * τ ^ 2) * ip E E ≤ energy e τ A E := by
  constructor
  · have hu := ip_self_nonneg (fun i y => 2 * E i y + τ * K e A i y)
    rw [ip_comb] at hu
    have hK := K_sq_le_sharp e A
    have hKτ : τ ^ 2 * ip (K e A) (K e A) ≤ τ ^ 2 * (4 * n * ip A (K e A)) :=
      mul_le_mul_of_nonneg_left hK (sq_nonneg τ)
    unfold energy
    nlinarith
  · have hm := magnetic_nonneg e (fun i y => A i y - (-(τ / 2)) * E i y)
    rw [K_sub_smul] at hm
    simp only [ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right] at hm
    have hs : ip E (K e A) = ip A (K e E) := K_symm e A E
    have hKE := K_le e E
    have hKτ : τ ^ 2 * ip E (K e E) ≤ τ ^ 2 * (4 * n * ip E E) :=
      mul_le_mul_of_nonneg_left hKE (sq_nonneg τ)
    have h' : 0 ≤ ip A (K e A) + τ * ip E (K e A) + τ ^ 2 / 4 * ip E (K e E) := by
      rw [← hs] at hm; ring_nf; ring_nf at hm; linarith
    unfold energy
    nlinarith [h', hKτ]

/-- The energy is non-negative for `nτ² ≤ 1`. -/
theorem energy_nonneg_sharp (e : Fin n → S) (τ : ℝ) (A E : Fin n → S → ℝ) (hτ : n * τ ^ 2 ≤ 1) :
    0 ≤ energy e τ A E := by
  have h := (energy_lower_sharp e τ A E).2
  have : 0 ≤ (1 / 2) * (1 - n * τ ^ 2) * ip E E :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (ip_self_nonneg E)
  linarith

/-- **The free leapfrog is stable for `nτ² < 1`**: both fields stay bounded by `2H₀/(1 − nτ²)`. -/
theorem free_bounded_sharp (e : Fin n → S) (τ : ℝ) (hτ : n * τ ^ 2 < 1)
    (AE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) (m : ℕ) :
    ip (freeEvolve e τ AE m).1 (K e (freeEvolve e τ AE m).1) ≤
        2 * energy e τ AE.1 AE.2 / (1 - n * τ ^ 2) ∧
      ip (freeEvolve e τ AE m).2 (freeEvolve e τ AE m).2 ≤
        2 * energy e τ AE.1 AE.2 / (1 - n * τ ^ 2) := by
  have hc : 0 < 1 - n * τ ^ 2 := by linarith
  have hH := freeEvolve_energy e τ AE m
  have hb := energy_lower_sharp e τ (freeEvolve e τ AE m).1 (freeEvolve e τ AE m).2
  rw [hH] at hb
  constructor <;> rw [le_div_iff₀ hc] <;> nlinarith [hb.1, hb.2]

end QLF.Courant
