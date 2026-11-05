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
* **`energy`.** `H(A, E) = ½⟨E, E⟩ + ½⟨E, K A⟩ + ½⟨A, K A⟩`, that is
  `½|E|² + ½⟨E, curl F⟩ + ¼ΣF²` (**`energy_eq`**). The middle term is the leapfrog's: it is
  `½⟨E, E⁺⟩ + ¼ΣF²` with `E⁺ = E + K A` the next field, the electric energy read across the time
  step (Yee's staggered energy).
* **`energy_balance`.** For any field update `E' = E + K A − J`, `A' = A − E'`,
  `H(A', E') − H(A, E) = −⟨J, (E + E')/2⟩`. Exactly, for every `J`: the discrete Poynting theorem.
  The field loses what it does on the current, with the field read at the midpoint of the step.
* **`energy_conserved`.** With no current the field energy is conserved exactly.
* **`step_energy`.** In the coupled evolution the field energy changes at every step by exactly
  `−⟨J(ψ), (E + E')/2⟩`, the work done on the walk's current along the step's axis.

**Not here.** The walk's own energy. The walk is a unitary step, so its natural "energy" is a
quasi-energy (a phase), and no exact walk energy that absorbs this work is proved. So a conserved
total energy for the coupled system is still open. Positivity of `H` needs a step-size (CFL)
condition on `K`, also not proved. No axioms.

**Credit.** The staggered leapfrog and its conserved discrete energy are Yee's (*IEEE Trans.
Antennas Propag.* **14**, 302 (1966)); the energy balance is Poynting's theorem (1884) on the
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

omit [Fintype S] in
lemma K_sub (e : Fin n → S) (X Y : Fin n → S → ℝ) :
    K e (fun i y => X i y - Y i y) = fun i y => K e X i y - K e Y i y := by
  funext i y
  simp only [K, Maxwell.curl, F, ← Finset.sum_sub_distrib]
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

/-- The field energy of the leapfrog. -/
noncomputable def energy (e : Fin n → S) (A E : Fin n → S → ℝ) : ℝ :=
  (1 / 2) * ip E E + (1 / 2) * ip E (K e A) + (1 / 2) * ip A (K e A)

/-- `H = ½|E|² + ½⟨E, curl F⟩ + ¼ΣF²`. -/
theorem energy_eq (e : Fin n → S) (A E : Fin n → S → ℝ) :
    energy e A E = (1 / 2) * ip E E + (1 / 2) * ip E (K e A) +
      (1 / 4) * ∑ i, ∑ j, ∑ x, F e A i j x ^ 2 := by
  unfold energy; rw [ip_K e A A]; simp only [sq]; ring

/-- **The discrete Poynting theorem.** For the update `E' = E + K A − J`, `A' = A − E'`, the field
    energy changes by exactly `−⟨J, (E + E')/2⟩`. -/
theorem energy_balance (e : Fin n → S) (A E A' E' J : Fin n → S → ℝ)
    (hE : ∀ i y, E' i y = E i y + K e A i y - J i y) (hA : ∀ i y, A' i y = A i y - E' i y) :
    energy e A' E' - energy e A E = -((1 / 2) * (ip J E + ip J E')) := by
  have hJ : J = fun i y => (E i y + K e A i y) - E' i y := by
    funext i y; rw [hE]; ring
  have hA' : A' = fun i y => A i y - E' i y := by funext i y; exact hA i y
  have hK : K e A' = fun i y => K e A i y - K e E' i y := by rw [hA']; exact K_sub e A E'
  unfold energy
  rw [hK, hA', hJ]
  simp only [ip_sub_left, ip_sub_right, ip_add_left]
  have h1 := K_symm e E' A
  have h2 := ip_symm E E'
  have h3 := ip_symm (K e A) E
  have h4 := ip_symm (K e A) E'
  linarith

/-- **With no current the field energy is conserved exactly.** -/
theorem energy_conserved (e : Fin n → S) (A E A' E' : Fin n → S → ℝ)
    (hE : ∀ i y, E' i y = E i y + K e A i y) (hA : ∀ i y, A' i y = A i y - E' i y) :
    energy e A' E' = energy e A E := by
  have := energy_balance e A E A' E' (fun _ _ => 0) (fun i y => by rw [hE]; ring) hA
  simp only [ip, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, neg_zero] at this
  linarith

open QLF.CoupledEvolution in
/-- **In the coupled evolution the field energy changes by exactly the work on the walk's
    current**, `−⟨J(ψ), (E + E')/2⟩`, at every step. -/
theorem step_energy (e : Fin n → S) (k : Fin n) (t : QLF.Twist)
    (s : State S n) :
    energy e (step e k t s).A (step e k t s).E - energy e s.A s.E =
      -((1 / 2) * (ip (J e k t s.ψ) s.E + ip (J e k t s.ψ) (step e k t s).E)) :=
  energy_balance e s.A s.E _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

end QLF.FieldEnergy
