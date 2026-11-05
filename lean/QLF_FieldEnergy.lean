import QLF_CoupledEvolution

/-!
# QLF_FieldEnergy — the field's energy and the work the walk does on it

Issue #207. [`QLF_CoupledEvolution`](QLF_CoupledEvolution.lean) let the walk and the links evolve
together and kept Gauss's law, the norm and gauge covariance. It left energy open. This module
finds the field energy that the leapfrog update conserves exactly, and shows that with the walk
coupled it changes by exactly the work the field does on the walk's current.

Write `K A = curl F(A)` for the magnetic restoring force and `⟨X, Y⟩ = Σᵢ Σₓ Xᵢ(x) Yᵢ(x)`.

* **`ip_K`.** `⟨B, K A⟩ = ½ Σ F(A)·F(B)`: summation by parts on the closed lattice. So `K` is
  symmetric (**`K_symm`**) and `⟨A, K A⟩ = ½ Σ F²` is the magnetic energy, twice over.
* **`energy`.** With time step `τ`, `H(A, E) = ½⟨E, E⟩ + (τ/2)⟨E, K A⟩ + ½⟨A, K A⟩`, that is
  `½|E|² + (τ/2)⟨E, curl F⟩ + ¼ΣF²` (**`energy_eq`**). The middle term is the leapfrog's: it is
  `½⟨E, E⁺⟩ + ¼ΣF²` with `E⁺ = E + τ K A` the next field, the electric energy read across the
  time step (Yee's staggered energy).
* **`energy_balance`.** For any field update `E' = E + τ K A − J`, `A' = A − τ E'`,
  `H(A', E') − H(A, E) = −⟨J, (E + E')/2⟩`. Exactly, for every `J`: the discrete Poynting theorem.
  The field loses what it does on the current, with the field read at the midpoint of the step.
* **`energy_conserved`.** With no current the field energy is conserved exactly.
* **`K_sq_le`.** `|K A|² ≤ 8n ⟨A, K A⟩`: each component of `curl F` sums `n` plaquette differences.
* **`energy_lower`, `energy_bounds`, `free_stable`.** If `2nτ² ≤ 1` the energy is non-negative and
  bounds the magnetic energy; if `4nτ² ≤ 1` it bounds both, `⟨A, K A⟩ ≤ 4H` and `|E|² ≤ 8H`, so the
  free field stays bounded at every step. A sufficient Courant condition, not the sharp one:
  numerically the largest eigenvalue of `K` is `4n` (8 for `n = 2`, 12 for `n = 3`), so the sharp
  condition is `nτ² < 1`, and `τ = 1` grows without bound for `n ≥ 2`.
* **`J_sq_le`.** The walk's current is bounded by its charge: `|J(ψ)|² ≤ Q²`, `Q = Σ‖ψ‖²`, because the
  two hops across each link carry the charge once (`hops_total`).
* **`evolve_sqrt_energy`, `evolve_field_bound`.** With the walk coupled and `4nτ² ≤ 1`,
  `√H_m ≤ √H_0 + √2·Q·m` and `|E_m|² ≤ 8(√H_0 + √2·Q·m)²`. The walk's charge is conserved, so the
  coupled field can grow at most quadratically in the number of steps, never exponentially.
* **`step_energy`.** In the coupled evolution the field energy changes at every step by exactly
  `−⟨J(ψ), (E + E')/2⟩`, the work done on the walk's current along the step's axis.

**Not here.** The walk's own energy. The walk is a unitary step, so its natural "energy" is a
quasi-energy (a phase), and no exact walk energy that absorbs this work is proved. So a conserved
total energy for the coupled system is still open, and with it a bound on the coupled field that
does not grow with time. The sharp Courant bound is not proved. No axioms.

**Credit.** The staggered leapfrog and its conserved discrete energy are Yee's (*IEEE Trans.
Antennas Propag.* **14**, 302 (1966)); the stability condition is Courant, Friedrichs and Lewy's
(*Math. Ann.* **100**, 32 (1928)); the energy balance is Poynting's theorem (1884) on the
lattice. Kogut and Susskind (*Phys. Rev. D* **11**, 395 (1975)) give the Hamiltonian
`½ΣE² + ¼ΣF²` of which this is the time-staggered form.
-/

namespace QLF.FieldEnergy

open QLF.LinkAction (F F_antisymm)

variable {S : Type*} [AddCommGroup S] [Fintype S] {n : ℕ}

/-- The pairing of two link fields. -/
noncomputable def ip (X Y : Fin n → S → ℝ) : ℝ := ∑ i, ∑ x, X i x * Y i x

/-- The magnetic restoring force `curl F(A)`. -/
noncomputable def K (e : Fin n → S) (A : Fin n → S → ℝ) : Fin n → S → ℝ := Maxwell.curl e (F e A)

omit [AddCommGroup S] in
lemma ip_symm (X Y : Fin n → S → ℝ) : ip X Y = ip Y X := by
  unfold ip; simp only [mul_comm]

omit [AddCommGroup S] in
lemma ip_add_left (X Y Z : Fin n → S → ℝ) :
    ip (fun i y => X i y + Y i y) Z = ip X Z + ip Y Z := by
  unfold ip; simp only [add_mul, Finset.sum_add_distrib]

omit [AddCommGroup S] in
lemma ip_sub_left (X Y Z : Fin n → S → ℝ) :
    ip (fun i y => X i y - Y i y) Z = ip X Z - ip Y Z := by
  unfold ip; simp only [sub_mul, Finset.sum_sub_distrib]

omit [AddCommGroup S] in
lemma ip_sub_right (X Y Z : Fin n → S → ℝ) :
    ip Z (fun i y => X i y - Y i y) = ip Z X - ip Z Y := by
  unfold ip; simp only [mul_sub, Finset.sum_sub_distrib]

omit [AddCommGroup S] in
lemma ip_smul_left (c : ℝ) (X Z : Fin n → S → ℝ) :
    ip (fun i y => c * X i y) Z = c * ip X Z := by
  unfold ip; simp only [Finset.mul_sum, mul_assoc]

omit [AddCommGroup S] in
lemma ip_smul_right (c : ℝ) (X Z : Fin n → S → ℝ) :
    ip Z (fun i y => c * X i y) = c * ip Z X := by
  unfold ip; simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

omit [AddCommGroup S] in
lemma ip_self_nonneg (X : Fin n → S → ℝ) : 0 ≤ ip X X :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _))

omit [AddCommGroup S] in
/-- `|aX + bY|² = a²|X|² + 2ab⟨X, Y⟩ + b²|Y|²`. -/
lemma ip_comb (a b : ℝ) (X Y : Fin n → S → ℝ) :
    ip (fun i y => a * X i y + b * Y i y) (fun i y => a * X i y + b * Y i y) =
      a ^ 2 * ip X X + 2 * a * b * ip X Y + b ^ 2 * ip Y Y := by
  unfold ip
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

omit [Fintype S] in
lemma K_sub_smul (e : Fin n → S) (c : ℝ) (X Y : Fin n → S → ℝ) :
    K e (fun i y => X i y - c * Y i y) = fun i y => K e X i y - c * K e Y i y := by
  funext i y
  simp only [K, Maxwell.curl, F, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Summation by parts**: `⟨B, curl F(A)⟩ = ½ Σ F(A)·F(B)`. -/
theorem ip_K (e : Fin n → S) (A B : Fin n → S → ℝ) :
    ip B (K e A) = (1 / 2) * ∑ i, ∑ j, ∑ x, F e A i j x * F e B i j x := by
  have hT : ip B (K e A) = ∑ i, ∑ j, ∑ x, F e A i j x * (B i x - B i (x + e j)) := by
    unfold ip K Maxwell.curl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hs : ∑ x, B i x * F e A i j (x - e j) = ∑ x, B i (x + e j) * F e A i j x :=
      Fintype.sum_equiv (Equiv.subRight (e j)) _ _ (fun x => by simp)
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hs]
    congr 1
    · exact Finset.sum_congr rfl (fun x _ => by ring)
    · exact Finset.sum_congr rfl (fun x _ => by ring)
  have hT' : ∑ i, ∑ j, ∑ x, F e A i j x * (B j (x + e i) - B j x) =
      ∑ i, ∑ j, ∑ x, F e A i j x * (B i x - B i (x + e j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun x _ => ?_)))
    rw [F_antisymm e A i j x]; ring
  have hF : ∀ i j x, F e B i j x = (B i x - B i (x + e j)) + (B j (x + e i) - B j x) := by
    intros; simp only [F]; ring
  rw [hT]
  simp only [hF, mul_add, Finset.sum_add_distrib, hT']
  ring

/-- **The restoring force is symmetric**: `⟨B, K A⟩ = ⟨A, K B⟩`. -/
theorem K_symm (e : Fin n → S) (A B : Fin n → S → ℝ) : ip B (K e A) = ip A (K e B) := by
  rw [ip_K, ip_K]; simp only [mul_comm (F e A _ _ _)]

/-- The magnetic energy `½⟨A, K A⟩ = ¼ΣF²` is non-negative. -/
theorem magnetic_nonneg (e : Fin n → S) (A : Fin n → S → ℝ) : 0 ≤ ip A (K e A) := by
  rw [ip_K]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun x _ => mul_self_nonneg _))))

/-- **The restoring force is bounded**: `|K A|² ≤ 8n ⟨A, K A⟩`. Each component of `curl F` is a sum
    of `n` differences of plaquettes, and each plaquette enters two components. -/
theorem K_sq_le (e : Fin n → S) (A : Fin n → S → ℝ) :
    ip (K e A) (K e A) ≤ 8 * n * ip A (K e A) := by
  rw [ip_K e A A]
  have hcs : ∀ i x, K e A i x * K e A i x ≤
      (n : ℝ) * ∑ j, (2 * F e A i j x ^ 2 + 2 * F e A i j (x - e j) ^ 2) := by
    intro i x
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => F e A i j x - F e A i j (x - e j))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [← sq]
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => ?_)) (by positivity))
    nlinarith [sq_nonneg (F e A i j x + F e A i j (x - e j))]
  have hshift : ∀ i j, ∑ x, F e A i j (x - e j) ^ 2 = ∑ x, F e A i j x ^ 2 := fun i j =>
    Fintype.sum_equiv (Equiv.subRight (e j)) _ (fun x => F e A i j x ^ 2) (fun _ => rfl)
  calc ip (K e A) (K e A) = ∑ i, ∑ x, K e A i x * K e A i x := rfl
    _ ≤ ∑ i, ∑ x, (n : ℝ) * ∑ j, (2 * F e A i j x ^ 2 + 2 * F e A i j (x - e j) ^ 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun x _ => hcs i x))
    _ = 4 * (n : ℝ) * ∑ i, ∑ j, ∑ x, F e A i j x * F e A i j x := by
        have key : ∀ i, ∑ x, (n : ℝ) * ∑ j, (2 * F e A i j x ^ 2 + 2 * F e A i j (x - e j) ^ 2) =
            4 * n * ∑ j, ∑ x, F e A i j x * F e A i j x := by
          intro i
          rw [← Finset.mul_sum, Finset.sum_comm]
          have h4 : ∀ j, ∑ x, (2 * F e A i j x ^ 2 + 2 * F e A i j (x - e j) ^ 2) =
              4 * ∑ x, F e A i j x * F e A i j x := by
            intro j
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hshift]
            simp only [sq]; ring
          rw [Finset.sum_congr rfl (fun j _ => h4 j), ← Finset.mul_sum]; ring
        rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum]
    _ = 8 * n * ((1 / 2) * ∑ i, ∑ j, ∑ x, F e A i j x * F e A i j x) := by ring

/-- The field energy of the leapfrog with time step `τ`. -/
noncomputable def energy (e : Fin n → S) (τ : ℝ) (A E : Fin n → S → ℝ) : ℝ :=
  (1 / 2) * ip E E + (τ / 2) * ip E (K e A) + (1 / 2) * ip A (K e A)

/-- `H = ½|E|² + (τ/2)⟨E, curl F⟩ + ¼ΣF²`. -/
theorem energy_eq (e : Fin n → S) (τ : ℝ) (A E : Fin n → S → ℝ) :
    energy e τ A E = (1 / 2) * ip E E + (τ / 2) * ip E (K e A) +
      (1 / 4) * ∑ i, ∑ j, ∑ x, F e A i j x ^ 2 := by
  unfold energy; rw [ip_K e A A]; simp only [sq]; ring

/-- **The discrete Poynting theorem.** For the update `E' = E + τ K A − J`, `A' = A − τ E'`, the
    field energy changes by exactly `−⟨J, (E + E')/2⟩`. -/
theorem energy_balance (e : Fin n → S) (τ : ℝ) (A E A' E' J : Fin n → S → ℝ)
    (hE : ∀ i y, E' i y = E i y + τ * K e A i y - J i y)
    (hA : ∀ i y, A' i y = A i y - τ * E' i y) :
    energy e τ A' E' - energy e τ A E = -((1 / 2) * (ip J E + ip J E')) := by
  have hJ : J = fun i y => (E i y + τ * K e A i y) - E' i y := by
    funext i y; rw [hE]; ring
  have hA' : A' = fun i y => A i y - τ * E' i y := by funext i y; exact hA i y
  have hK : K e A' = fun i y => K e A i y - τ * K e E' i y := by
    rw [hA']; exact K_sub_smul e τ A E'
  unfold energy
  rw [hK, hA', hJ]
  simp only [ip_sub_left, ip_sub_right, ip_add_left, ip_smul_left, ip_smul_right]
  have h1 : τ * ip A (K e E') = τ * ip E' (K e A) := by rw [K_symm e E' A]
  have h2 := ip_symm E E'
  have h3 : τ * ip (K e A) E = τ * ip E (K e A) := by rw [ip_symm (K e A) E]
  have h4 : τ * ip (K e A) E' = τ * ip E' (K e A) := by rw [ip_symm (K e A) E']
  linarith

/-- **With no current the field energy is conserved exactly.** -/
theorem energy_conserved (e : Fin n → S) (τ : ℝ) (A E A' E' : Fin n → S → ℝ)
    (hE : ∀ i y, E' i y = E i y + τ * K e A i y) (hA : ∀ i y, A' i y = A i y - τ * E' i y) :
    energy e τ A' E' = energy e τ A E := by
  have := energy_balance e τ A E A' E' (fun _ _ => 0) (fun i y => by rw [hE]; ring) hA
  simp only [ip, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, neg_zero] at this
  linarith

/-! ## Stability: the energy is positive for a small enough time step -/

/-- **The energy bounds the magnetic energy** when `2nτ² ≤ 1`:
    `½(1 − 2nτ²)⟨A, K A⟩ ≤ H`, so `H ≥ 0`. -/
theorem energy_lower (e : Fin n → S) (τ : ℝ) (A E : Fin n → S → ℝ) (hτ : 2 * n * τ ^ 2 ≤ 1) :
    (1 / 2) * (1 - 2 * n * τ ^ 2) * ip A (K e A) ≤ energy e τ A E ∧ 0 ≤ energy e τ A E := by
  have hu := ip_self_nonneg (fun i y => 2 * E i y + τ * K e A i y)
  rw [ip_comb] at hu
  have hK := K_sq_le e A
  have hm := magnetic_nonneg e A
  have hKτ : τ ^ 2 * ip (K e A) (K e A) ≤ τ ^ 2 * (8 * n * ip A (K e A)) :=
    mul_le_mul_of_nonneg_left hK (sq_nonneg τ)
  have hpos : 0 ≤ (1 - 2 * n * τ ^ 2) * ip A (K e A) := mul_nonneg (by linarith) hm
  unfold energy
  constructor <;> nlinarith

/-- **Bounded field** when `4nτ² ≤ 1`: `⟨A, K A⟩ ≤ 4H` and `|E|² ≤ 8H`. -/
theorem energy_bounds (e : Fin n → S) (τ : ℝ) (A E : Fin n → S → ℝ) (hτ : 4 * n * τ ^ 2 ≤ 1) :
    ip A (K e A) ≤ 4 * energy e τ A E ∧ ip E E ≤ 8 * energy e τ A E := by
  have hlow := (energy_lower e τ A E (by nlinarith [sq_nonneg τ])).1
  have hw := ip_self_nonneg (fun i y => 3 * E i y + (2 * τ) * K e A i y)
  rw [ip_comb] at hw
  have hK := K_sq_le e A
  have hm := magnetic_nonneg e A
  have hKτ : τ ^ 2 * ip (K e A) (K e A) ≤ τ ^ 2 * (8 * n * ip A (K e A)) :=
    mul_le_mul_of_nonneg_left hK (sq_nonneg τ)
  have hτm : (4 * n * τ ^ 2) * ip A (K e A) ≤ 1 * ip A (K e A) :=
    mul_le_mul_of_nonneg_right hτ hm
  unfold energy at hlow ⊢
  constructor <;> nlinarith

/-- The free leapfrog: no current. -/
noncomputable def freeStep (e : Fin n → S) (τ : ℝ) (AE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) :
    (Fin n → S → ℝ) × (Fin n → S → ℝ) :=
  let E' : Fin n → S → ℝ := fun i y => AE.2 i y + τ * K e AE.1 i y
  (fun i y => AE.1 i y - τ * E' i y, E')

/-- The free leapfrog, iterated. -/
noncomputable def freeEvolve (e : Fin n → S) (τ : ℝ) (AE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) :
    ℕ → (Fin n → S → ℝ) × (Fin n → S → ℝ)
  | 0 => AE
  | m + 1 => freeStep e τ (freeEvolve e τ AE m)

theorem freeEvolve_energy (e : Fin n → S) (τ : ℝ) (AE : (Fin n → S → ℝ) × (Fin n → S → ℝ))
    (m : ℕ) : energy e τ (freeEvolve e τ AE m).1 (freeEvolve e τ AE m).2 = energy e τ AE.1 AE.2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih]
    exact energy_conserved e τ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- **The free field is stable** when `4nτ² ≤ 1`: at every step its electric and magnetic energy
    stay below a fixed multiple of the initial energy. -/
theorem free_stable (e : Fin n → S) (τ : ℝ) (hτ : 4 * n * τ ^ 2 ≤ 1)
    (AE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) (m : ℕ) :
    ip (freeEvolve e τ AE m).1 (K e (freeEvolve e τ AE m).1) ≤ 4 * energy e τ AE.1 AE.2 ∧
      ip (freeEvolve e τ AE m).2 (freeEvolve e τ AE m).2 ≤ 8 * energy e τ AE.1 AE.2 := by
  rw [← freeEvolve_energy e τ AE m]
  exact energy_bounds e τ _ _ hτ

open QLF.CoupledEvolution in
/-- **In the coupled evolution the field energy changes by exactly the work on the walk's
    current**, `−⟨J(ψ), (E + E')/2⟩`, at every step. -/
theorem step_energy (e : Fin n → S) (τ : ℝ) (k : Fin n) (t : QLF.Twist) (s : State S n) :
    energy e τ (step e τ k t s).A (step e τ k t s).E - energy e τ s.A s.E =
      -((1 / 2) * (ip (J e k t s.ψ) s.E + ip (J e k t s.ψ) (step e τ k t s).E)) :=
  energy_balance e τ s.A s.E _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

/-! ## The coupled field cannot blow up -/

section Coupled

open Matrix QLF.CoupledEvolution QLF.ClosureChannels
open QLF.LocalGauge (nsq V)

omit [AddCommGroup S] in
/-- **Cauchy–Schwarz** for the link pairing. -/
lemma ip_le_sqrt (X Y : Fin n → S → ℝ) : ip X Y ≤ √(ip X X) * √(ip Y Y) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n × S))
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  simp only [Fintype.sum_prod_type, sq] at h
  exact h

omit [AddCommGroup S] in
lemma neg_ip_le_sqrt (X Y : Fin n → S → ℝ) : -ip X Y ≤ √(ip X X) * √(ip Y Y) := by
  have h := ip_le_sqrt X (fun i y => -Y i y)
  have h1 : ip X (fun i y => -Y i y) = -ip X Y := by
    unfold ip; simp only [mul_neg, Finset.sum_neg_distrib]
  have h2 : ip (fun i y => -Y i y) (fun i y => -Y i y) = ip Y Y := by
    unfold ip; simp only [neg_mul_neg]
  rwa [h1, h2] at h

/-- The walk's charge `Q = Σ‖ψ‖²`. -/
noncomputable def charge (ψ : S → V) : ℝ := ∑ x, (nsq (ψ x)).re

omit [AddCommGroup S] in
lemma charge_nonneg (ψ : S → V) : 0 ≤ charge ψ :=
  Finset.sum_nonneg (fun x _ => nsq_re_nonneg (ψ x))

/-- The two hops across every link carry the whole charge once. -/
lemma hops_total (t : QLF.Twist) (e : S) (ψ : S → V) :
    ∑ y, ((nsq (fix t *ᵥ ψ y)).re + (nsq (fix t.conj *ᵥ ψ (y + e))).re) = charge ψ := by
  have hs : ∑ y, (nsq (fix t.conj *ᵥ ψ (y + e))).re = ∑ y, (nsq (fix t.conj *ᵥ ψ y)).re :=
    Fintype.sum_equiv (Equiv.addRight e) _ (fun y => (nsq (fix t.conj *ᵥ ψ y)).re) (fun _ => rfl)
  rw [Finset.sum_add_distrib, hs, ← Finset.sum_add_distrib]
  unfold charge
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [LocalGauge.nsq_split t (ψ y), Complex.add_re]

/-- **The walk's current is bounded by its charge**: `|J(ψ)|² ≤ Q²`. -/
theorem J_sq_le (e : Fin n → S) (k : Fin n) (t : QLF.Twist) (ψ : S → V) :
    ip (CoupledEvolution.J e k t ψ) (CoupledEvolution.J e k t ψ) ≤ charge ψ ^ 2 := by
  set c : S → ℝ := fun y => (Maxwell.current t (e k) ψ y).re
  set w : S → ℝ := fun y => (nsq (fix t *ᵥ ψ y)).re + (nsq (fix t.conj *ᵥ ψ (y + e k))).re
  have hJ : ip (CoupledEvolution.J e k t ψ) (CoupledEvolution.J e k t ψ) = ∑ y, c y * c y := by
    unfold ip CoupledEvolution.J
    have : ∀ i, ∑ y, (if i = k then c y else 0) * (if i = k then c y else 0) =
        if i = k then ∑ y, c y * c y else 0 := by
      intro i; by_cases h : i = k
      · simp [h]
      · simp [h]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true, c]
  have hcw : ∀ y, |c y| ≤ w y := by
    intro y
    have h1 := nsq_re_nonneg (fix t *ᵥ ψ y)
    have h2 := nsq_re_nonneg (fix t.conj *ᵥ ψ (y + e k))
    simp only [c, w, Maxwell.current, Complex.sub_re]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hw0 : ∀ y, 0 ≤ w y := fun y => (abs_nonneg _).trans (hcw y)
  have hwQ : ∑ y, w y = charge ψ := hops_total t (e k) ψ
  have hwle : ∀ y, w y ≤ charge ψ := fun y => by
    rw [← hwQ]; exact Finset.single_le_sum (fun z _ => hw0 z) (Finset.mem_univ y)
  rw [hJ]
  calc ∑ y, c y * c y ≤ ∑ y, w y * charge ψ := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        rw [← abs_mul_abs_self]
        exact mul_le_mul (hcw y) ((hcw y).trans (hwle y)) (abs_nonneg _) (hw0 y)
    _ = charge ψ ^ 2 := by rw [← Finset.sum_mul, hwQ, sq]

/-- **One coupled step raises `√H` by at most `√2·Q`** when `4nτ² ≤ 1`. -/
theorem step_sqrt_energy (e : Fin n → S) (τ : ℝ) (hτ : 4 * n * τ ^ 2 ≤ 1) (k : Fin n)
    (t : QLF.Twist) (s : State S n) :
    √(energy e τ (step e τ k t s).A (step e τ k t s).E) ≤
      √(energy e τ s.A s.E) + √2 * charge s.ψ := by
  set H := energy e τ s.A s.E
  set H' := energy e τ (step e τ k t s).A (step e τ k t s).E
  set Q := charge s.ψ
  have hQ := charge_nonneg s.ψ
  have hH := (energy_lower e τ s.A s.E (by nlinarith [sq_nonneg τ])).2
  have hH' := (energy_lower e τ (step e τ k t s).A (step e τ k t s).E (by nlinarith [sq_nonneg τ])).2
  have hb := (energy_bounds e τ s.A s.E hτ).2
  have hb' := (energy_bounds e τ (step e τ k t s).A (step e τ k t s).E hτ).2
  have hbal := step_energy e τ k t s
  have hJ : √(ip (CoupledEvolution.J e k t s.ψ) (CoupledEvolution.J e k t s.ψ)) ≤ Q := by
    rw [show Q = √(Q ^ 2) from (Real.sqrt_sq (hQ : 0 ≤ Q)).symm]
    exact Real.sqrt_le_sqrt (J_sq_le e k t s.ψ)
  have h8 : √8 = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hE : √(ip s.E s.E) ≤ 2 * √2 * √H := by
    rw [← h8, ← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hb
  have hE' : √(ip (step e τ k t s).E (step e τ k t s).E) ≤ 2 * √2 * √H' := by
    rw [← h8, ← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hb'
  have c1 := neg_ip_le_sqrt (CoupledEvolution.J e k t s.ψ) s.E
  have c2 := neg_ip_le_sqrt (CoupledEvolution.J e k t s.ψ) (step e τ k t s).E
  have s1 : √(ip (CoupledEvolution.J e k t s.ψ) (CoupledEvolution.J e k t s.ψ)) * √(ip s.E s.E) ≤ Q * (2 * √2 * √H) :=
    mul_le_mul hJ hE (Real.sqrt_nonneg _) hQ
  have s2 : √(ip (CoupledEvolution.J e k t s.ψ) (CoupledEvolution.J e k t s.ψ)) * √(ip (step e τ k t s).E (step e τ k t s).E) ≤
      Q * (2 * √2 * √H') := mul_le_mul hJ hE' (Real.sqrt_nonneg _) hQ
  have hsq : √H' ^ 2 ≤ √H ^ 2 + √2 * Q * (√H + √H') := by
    rw [Real.sq_sqrt hH, Real.sq_sqrt hH']
    linarith
  have h0 := Real.sqrt_nonneg H
  have h0' := Real.sqrt_nonneg H'
  have h2 : 0 ≤ √2 * Q := mul_nonneg (Real.sqrt_nonneg 2) hQ
  nlinarith [mul_nonneg h0 h0', mul_nonneg h2 h0, mul_nonneg h2 h0']

/-- **The coupled field cannot blow up**: when `4nτ² ≤ 1`, `√H` grows at most linearly,
    `√H_m ≤ √H_0 + √2·Q·m`, with `Q` the walk's conserved charge. -/
theorem evolve_sqrt_energy (e : Fin n → S) (τ : ℝ) (hτ : 4 * n * τ ^ 2 ≤ 1) (ax : ℕ → Fin n)
    (tw : ℕ → QLF.Twist) (s₀ : State S n) (m : ℕ) :
    √(energy e τ (evolve e τ ax tw s₀ m).A (evolve e τ ax tw s₀ m).E) ≤
      √(energy e τ s₀.A s₀.E) + √2 * charge s₀.ψ * m := by
  induction m with
  | zero => simp [evolve]
  | succ m ih =>
    have hQ : charge (evolve e τ ax tw s₀ m).ψ = charge s₀.ψ := by
      have := congrArg Complex.re (evolve_norm e τ ax tw s₀ m)
      simpa [charge, LatticeGauge.total, Complex.re_sum] using this
    have := step_sqrt_energy e τ hτ (ax m) (tw m) (evolve e τ ax tw s₀ m)
    rw [hQ] at this
    simp only [evolve]
    push_cast
    linarith

/-- **The coupled electric field stays bounded at every step**: `|E_m|² ≤ 8(√H_0 + √2·Q·m)²`.
    It can grow at most quadratically in the number of steps, never exponentially. -/
theorem evolve_field_bound (e : Fin n → S) (τ : ℝ) (hτ : 4 * n * τ ^ 2 ≤ 1) (ax : ℕ → Fin n)
    (tw : ℕ → QLF.Twist) (s₀ : State S n) (m : ℕ) :
    ip (evolve e τ ax tw s₀ m).E (evolve e τ ax tw s₀ m).E ≤
      8 * (√(energy e τ s₀.A s₀.E) + √2 * charge s₀.ψ * m) ^ 2 := by
  have hb := (energy_bounds e τ (evolve e τ ax tw s₀ m).A (evolve e τ ax tw s₀ m).E hτ).2
  have hH := (energy_lower e τ (evolve e τ ax tw s₀ m).A (evolve e τ ax tw s₀ m).E
    (by nlinarith [sq_nonneg τ])).2
  have hg := evolve_sqrt_energy e τ hτ ax tw s₀ m
  have h0 := Real.sqrt_nonneg (energy e τ (evolve e τ ax tw s₀ m).A (evolve e τ ax tw s₀ m).E)
  have hsq := Real.sq_sqrt hH
  nlinarith [mul_le_mul hg hg h0 (h0.trans hg)]

end Coupled

end QLF.FieldEnergy
