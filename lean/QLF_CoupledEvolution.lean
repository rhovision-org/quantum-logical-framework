import QLF_WalkCoupling

/-!
# QLF_CoupledEvolution — the walk and the links evolve together

Issue #207. Up to [`QLF_WalkCoupling`](QLF_WalkCoupling.lean) each side was taken one at a time:
the walk stepped on given links, and the links obeyed field equations with a given source. This
module lets them act on each other, step after step, and shows that what matters survives.

A state is a walk `ψ`, link phases `A i x` on every axis and an electric field `E i x`. One coupled
step along axis `k` with twist `t` is the leapfrog update of
[`QLF_MaxwellTime`](QLF_MaxwellTime.lean) driven by the walk itself:

  `ψ' = U_{A_k} ψ`  (the walk moves on the *current* links),
  `E' = E + curl F(A) − J(ψ)`  (the field is pushed by the walk's current),
  `A' = A − E'`  (so `E' = −(A' − A)`, the electric field of the time link).

Iterating, the links the walk sees at step `m + 1` already carry the current it made at step `m`:
the back-reaction.

* **`gauss_neutral`, `no_background_no_walk`.** The lattice is closed, so the divergence of any
  field sums to zero (`sum_div_zero`). Gauss's law `div E = ‖ψ‖²` would then force `ψ = 0`. The walk's
  charge is non-negative, so it needs a static neutralizing background `b`, and Gauss's law is
  `div E = ‖ψ‖² − b`, which forces `Σ‖ψ‖² = Σ b`.
* **`neutral_admissible`, `exists_nonzero_admissible`.** Every walk, with any links and zero
  electric field, satisfies Gauss's law against its own initial charge as background, so non-zero
  admissible states exist.
* **`step_gauss`, `evolve_gauss`, `evolve_gauss_neutral`.** If Gauss's law holds at the start, it
  holds after every step, for every schedule of axes and twists; in particular from any walk
  against its neutralizing background. **`gauss_gauge`**: Gauss's law is gauge invariant.
* **`step_norm`, `evolve_norm`.** The walk's total norm is conserved at every step, whatever the
  links have become.
* **`step_covariant`, `evolve_covariant`.** A site-dependent phase change `θ` of the initial walk,
  with the links shifted by `θ(x + e) − θ(x)`, commutes with the whole coupled evolution: the
  history is gauge covariant at every step.

**Not here.** The background is static (fixed ions, not a second dynamical species). The update is
the non-compact (quadratic) one, and the field `E` is real while the
walk's current is read through its real part (it is real, `‖·‖²`-valued, but carried in `ℂ`).
The field's energy balance is [`QLF_FieldEnergy`](QLF_FieldEnergy.lean); a conserved total
energy of the coupled system, compact links and non-abelian links are not included.
No axioms.

**Credit.** Self-consistent evolution of a charged lattice field with a dynamical lattice gauge
field is the Hamiltonian lattice gauge theory of Kogut and Susskind (*Phys. Rev. D* **11**, 395
(1975)) and, as a leapfrog scheme, Yee's (1966). Gauge-coupled quantum walks: Arnault and Debbasch
(arXiv:1508.00038) and Márquez-Martín, Arnault, Di Molfetta and Pérez (*Phys. Rev. A* **98**,
032333 (2018)). QLF supplies the walk (realizable twist parts) and its exactly conserved current.
-/

namespace QLF.CoupledEvolution

open Matrix
open QLF.ClosureChannels
open QLF.LocalGauge (ph nsq V)
open QLF.LatticeGauge (axisStep localPhase total)

variable {S : Type*} [AddCommGroup S] [Fintype S] {n : ℕ}

/-- A coupled state: the walk, the link phases and the electric field. -/
@[ext]
structure State (S : Type*) (n : ℕ) where
  ψ : S → V
  A : Fin n → S → ℝ
  E : Fin n → S → ℝ

/-- The walk's current as a real link field, along axis `k` only. -/
noncomputable def J (e : Fin n → S) (k : Fin n) (t : Twist) (ψ : S → V) : Fin n → S → ℝ :=
  fun i y => if i = k then (Maxwell.current t (e k) ψ y).re else 0

/-- The field after one step: pushed by the curl of the links and by the walk's current. -/
noncomputable def newE (e : Fin n → S) (k : Fin n) (t : Twist) (s : State S n) :
    Fin n → S → ℝ :=
  fun i y => s.E i y + Maxwell.curl e (LinkAction.F e s.A) i y - J e k t s.ψ i y

/-- **One coupled step** along axis `k` with twist `t`. -/
noncomputable def step (e : Fin n → S) (k : Fin n) (t : Twist) (s : State S n) : State S n where
  ψ := axisStep t (e k) (s.A k) s.ψ
  A := fun i y => s.A i y - newE e k t s i y
  E := newE e k t s

/-- The coupled evolution under a schedule of axes and twists. -/
noncomputable def evolve (e : Fin n → S) (ax : ℕ → Fin n) (tw : ℕ → Twist) (s₀ : State S n) :
    ℕ → State S n
  | 0 => s₀
  | m + 1 => step e (ax m) (tw m) (evolve e ax tw s₀ m)

omit [Fintype S] in
/-- The new field is the electric field of the time link: `E' = −(A' − A)`. -/
theorem step_elec (e : Fin n → S) (k : Fin n) (t : Twist) (s : State S n) (i : Fin n) (y : S) :
    (step e k t s).E i y = -((step e k t s).A i y - s.A i y) := by
  simp only [step]; ring

/-- Gauss's law for a coupled state with a static background charge `b`:
    `div E = ‖ψ‖² − b`. On a closed lattice the divergence sums to zero, so the walk's charge must
    be neutralized (`gauss_neutral`); with no background only the empty walk is admissible
    (`no_background_no_walk`). -/
def Gauss (e : Fin n → S) (b : S → ℝ) (s : State S n) : Prop :=
  ∀ x, Maxwell.div e s.E x = (nsq (s.ψ x)).re - b x

/-! ## The closed lattice forces neutrality -/

/-- On a finite lattice the divergence of any field sums to zero. -/
theorem sum_div_zero (e : Fin n → S) (E : Fin n → S → ℝ) : ∑ x, Maxwell.div e E x = 0 := by
  unfold Maxwell.div
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact (Fintype.sum_equiv (Equiv.subRight (e i)) _ _ (fun _ => rfl)).symm

/-- `Re ‖v‖²` is non-negative and vanishes only at `v = 0`. -/
lemma nsq_re_eq (v : V) : (nsq v).re = ∑ i, Complex.normSq (v i) := by
  unfold nsq
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.star_def, mul_comm, Complex.mul_conj]
  exact Complex.ofReal_re _

lemma nsq_re_nonneg (v : V) : 0 ≤ (nsq v).re := by
  rw [nsq_re_eq]; exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)

lemma eq_zero_of_nsq_re (v : V) (h : (nsq v).re = 0) : v = 0 := by
  rw [nsq_re_eq] at h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (v j))).mp h i
    (Finset.mem_univ i)
  simpa using this

/-- **Gauss's law forces neutrality**: the walk's total charge equals the background's. -/
theorem gauss_neutral (e : Fin n → S) (b : S → ℝ) (s : State S n) (h : Gauss e b s) :
    ∑ x, (nsq (s.ψ x)).re = ∑ x, b x := by
  have h0 := sum_div_zero e s.E
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_sub_distrib, sub_eq_zero] at h0
  exact h0

/-- **Without a background, only the empty walk satisfies Gauss's law** on a closed lattice. -/
theorem no_background_no_walk (e : Fin n → S) (s : State S n) (h : Gauss e (fun _ => 0) s) :
    s.ψ = 0 := by
  have hsum := gauss_neutral e _ s h
  simp only [Finset.sum_const_zero] at hsum
  funext x
  exact eq_zero_of_nsq_re _ ((Finset.sum_eq_zero_iff_of_nonneg
    (fun y _ => nsq_re_nonneg (s.ψ y))).mp hsum x (Finset.mem_univ x))

omit [Fintype S] in
/-- **Every walk is Gauss-admissible against its own neutralizing background**, with any links and
    zero electric field. -/
theorem neutral_admissible (e : Fin n → S) (ψ : S → V) (A : Fin n → S → ℝ) :
    Gauss e (fun x => (nsq (ψ x)).re) ⟨ψ, A, fun _ _ => 0⟩ := by
  intro x
  simp [Maxwell.div]

omit [Fintype S] in
/-- **A non-zero Gauss-admissible state exists** on every non-empty lattice. -/
theorem exists_nonzero_admissible (e : Fin n → S) [Nonempty S] :
    ∃ (b : S → ℝ) (s : State S n), s.ψ ≠ 0 ∧ Gauss e b s := by
  let ψ : S → V := fun _ _ => 1
  refine ⟨_, ⟨ψ, fun _ _ => 0, fun _ _ => 0⟩, ?_, neutral_admissible e ψ _⟩
  intro h
  have := congrFun (congrFun h (Classical.arbitrary S)) 0
  simp [ψ] at this

omit [Fintype S] in
lemma div_J (e : Fin n → S) (k : Fin n) (t : Twist) (ψ : S → V) (x : S) :
    Maxwell.div e (J e k t ψ) x =
      (Maxwell.current t (e k) ψ x).re - (Maxwell.current t (e k) ψ (x - e k)).re := by
  unfold Maxwell.div J
  have : ∀ i, ((if i = k then (Maxwell.current t (e k) ψ x).re else 0) -
      (if i = k then (Maxwell.current t (e k) ψ (x - e i)).re else 0)) =
      if i = k then (Maxwell.current t (e k) ψ x).re -
        (Maxwell.current t (e k) ψ (x - e k)).re else 0 := by
    intro i
    by_cases h : i = k
    · subst h; simp
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Fintype S] in
/-- **One coupled step keeps Gauss's law.** -/
theorem step_gauss (e : Fin n → S) (b : S → ℝ) (k : Fin n) (t : Twist) (s : State S n)
    (h : Gauss e b s) : Gauss e b (step e k t s) := by
  intro x
  have hcont := congrArg Complex.re (Maxwell.continuity t (e k) (s.A k) s.ψ x)
  simp only [Complex.add_re, Complex.sub_re, Complex.zero_re] at hcont
  have hc : (nsq ((step e k t s).ψ x)).re - (nsq (s.ψ x)).re +
      Maxwell.div e (J e k t s.ψ) x = 0 := by
    rw [div_J]; simpa [step, Maxwell.rho] using hcont
  exact Maxwell.gauss_preserved e s.E (J e k t s.ψ) (LinkAction.F e s.A)
    (fun i j y => LinkAction.F_antisymm e s.A i j y) (fun x => (nsq (s.ψ x)).re - b x)
    (fun x => (nsq ((step e k t s).ψ x)).re - b x) x (h x) (by linear_combination hc)

/-- **One coupled step conserves the walk's norm.** -/
theorem step_norm (e : Fin n → S) (k : Fin n) (t : Twist) (s : State S n) :
    total (step e k t s).ψ = total s.ψ :=
  LatticeGauge.axisStep_norm t (e k) (s.A k) s.ψ

omit [Fintype S] in
/-- **Gauss's law holds at every step of the coupled evolution.** -/
theorem evolve_gauss (e : Fin n → S) (b : S → ℝ) (ax : ℕ → Fin n) (tw : ℕ → Twist)
    (s₀ : State S n) (h : Gauss e b s₀) (m : ℕ) : Gauss e b (evolve e ax tw s₀ m) := by
  induction m with
  | zero => exact h
  | succ m ih => exact step_gauss e b (ax m) (tw m) _ ih

omit [Fintype S] in
/-- **Non-trivial back-reaction**: from any walk against its neutralizing background, Gauss's law
    holds at every step of the coupled evolution. -/
theorem evolve_gauss_neutral (e : Fin n → S) (ax : ℕ → Fin n) (tw : ℕ → Twist) (ψ : S → V)
    (A : Fin n → S → ℝ) (m : ℕ) :
    Gauss e (fun x => (nsq (ψ x)).re) (evolve e ax tw ⟨ψ, A, fun _ _ => 0⟩ m) :=
  evolve_gauss e _ ax tw _ (neutral_admissible e ψ A) m

/-- **The walk's norm is conserved at every step**, whatever the links have become. -/
theorem evolve_norm (e : Fin n → S) (ax : ℕ → Fin n) (tw : ℕ → Twist) (s₀ : State S n) (m : ℕ) :
    total (evolve e ax tw s₀ m).ψ = total s₀.ψ := by
  induction m with
  | zero => rfl
  | succ m ih => rw [evolve, step_norm, ih]

/-! ## Gauge covariance of the coupled evolution -/

/-- A site-dependent phase change of a coupled state. -/
noncomputable def gauge (e : Fin n → S) (θ : S → ℝ) (s : State S n) : State S n where
  ψ := localPhase θ s.ψ
  A := LinkAction.gaugeShift e θ s.A
  E := s.E

omit [Fintype S] in
lemma newE_gauge (e : Fin n → S) (k : Fin n) (t : Twist) (θ : S → ℝ) (s : State S n) :
    newE e k t (gauge e θ s) = newE e k t s := by
  funext i y
  simp only [newE, gauge, J, Maxwell.curl, LinkAction.F_gauge, Maxwell.current_invariant]

omit [Fintype S] in
/-- **One coupled step is gauge covariant.** -/
theorem step_covariant (e : Fin n → S) (k : Fin n) (t : Twist) (θ : S → ℝ) (s : State S n) :
    step e k t (gauge e θ s) = gauge e θ (step e k t s) := by
  ext1
  · exact LatticeGauge.axisStep_covariant t (e k) (s.A k) θ s.ψ
  · funext i y
    simp only [step, newE_gauge]
    simp only [gauge, LinkAction.gaugeShift]; ring
  · exact newE_gauge e k t θ s

omit [Fintype S] in
/-- **The whole coupled history is gauge covariant.** -/
theorem evolve_covariant (e : Fin n → S) (ax : ℕ → Fin n) (tw : ℕ → Twist) (θ : S → ℝ)
    (s₀ : State S n) (m : ℕ) :
    evolve e ax tw (gauge e θ s₀) m = gauge e θ (evolve e ax tw s₀ m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [evolve, evolve, ih, step_covariant]

omit [Fintype S] in
/-- Gauss's law is gauge invariant. -/
theorem gauss_gauge (e : Fin n → S) (b : S → ℝ) (θ : S → ℝ) (s : State S n) :
    Gauss e b (gauge e θ s) ↔ Gauss e b s := by
  simp only [Gauss, gauge, localPhase, LocalGauge.nsq_ph]

end QLF.CoupledEvolution
