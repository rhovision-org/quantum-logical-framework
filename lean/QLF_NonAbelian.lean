import QLF_CompactLinks

/-!
# QLF_NonAbelian — matrix links on a colour index

Issue #207. Up to [`QLF_CompactLinks`](QLF_CompactLinks.lean) a link carried a phase `e^{ia}`, an
element of `U(1)`. This module lets a link carry any unitary `N × N` matrix, acting on an internal
colour index that the twists do not touch. A walk value at a site is a `2 × N` matrix: rows are
spin, on which the twists act from the left, and columns are colour, on which the links act from
the right. One realizable step along `e` with links `U` is

  `ψ'(x) = fix t · ψ(x − e) · U(x − e) + fix t̄ · ψ(x + e) · U(x)ᴴ`,

hopping forward through the link and backward through its inverse.

* **`step_norm`.** The step conserves `Σₓ tr(ψ(x)ᴴ ψ(x))` for **every** assignment of unitary
  links. The two hops land in orthogonal spin subspaces (`fix t · fix t̄ = 0`), and a unitary on the
  colour side does not change a norm. The links need not commute with each other.
* **`step_covariant`.** A site-dependent colour rotation `g(x)` (unitary), applied as
  `ψ(x) ↦ ψ(x) g(x)` with the links moved to `g(x)ᴴ U(x) g(x + e)`, commutes with the step.
* **`holonomy_gauge`, `wilson_loop_invariant`.** The plaquette holonomy
  `U_i(x) U_j(x + e_i) U_i(x + e_j)ᴴ U_j(x)ᴴ` is conjugated by `g(x)`, so its trace, the Wilson
  loop, is gauge invariant. For `N = 1` this is the abelian plaquette phase of
  [`QLF_LatticeGauge`](QLF_LatticeGauge.lean).

Nothing here uses commutativity of the links; the abelian results are the case `N = 1`.
**Not here.** Field dynamics for the matrix links (the non-abelian Wilson action and its
variation), the non-abelian Gauss law, and which colour group the twists select (the Weyl qutrit
of [`QLF_ColourFlux`](QLF_ColourFlux.lean) is not connected to these links here). No axioms.

**Credit.** Non-abelian gauge fields are Yang and Mills's (*Phys. Rev.* **96**, 191 (1954)); the
lattice form with link matrices and the plaquette trace is Wilson's (*Phys. Rev. D* **10**, 2445
(1974)). Quantum walks with non-abelian gauge fields: Arnault, Di Molfetta, Brachet and Debbasch,
*Phys. Rev. A* **94**, 012335 (2016).
-/

namespace QLF.NonAbelian

open Matrix QLF.ClosureChannels

variable {S : Type*} [AddCommGroup S] [Fintype S] {N : ℕ}

/-- A walk value: spin rows, colour columns. -/
abbrev W (N : ℕ) := Matrix (Fin 2) (Fin N) ℂ

/-- A link: a colour matrix. -/
abbrev L (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-- A unitary colour matrix. -/
def Unitary (u : L N) : Prop := uᴴ * u = 1 ∧ u * uᴴ = 1

/-- The squared norm `tr(ψᴴ ψ)`. -/
noncomputable def nsq (w : W N) : ℂ := trace (wᴴ * w)

/-- The total norm. -/
noncomputable def total (ψ : S → W N) : ℂ := ∑ x, nsq (ψ x)

/-- **One realizable step with matrix links.** -/
noncomputable def step (t : Twist) (e : S) (U : S → L N) (ψ : S → W N) : S → W N :=
  fun x => fix t * ψ (x - e) * U (x - e) + fix t.conj * ψ (x + e) * (U x)ᴴ

lemma nsq_hop (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : Pᴴ = P) (hP2 : P * P = P) (a : W N) (u : L N)
    (hu : Unitary u) : nsq (P * a * u) = trace (aᴴ * P * a) := by
  unfold nsq
  rw [conjTranspose_mul, conjTranspose_mul, hP]
  rw [show uᴴ * (aᴴ * P) * (P * a * u) = uᴴ * (aᴴ * (P * P) * a * u) by
    simp only [Matrix.mul_assoc]]
  rw [hP2, trace_mul_comm, show aᴴ * P * a * u * uᴴ = aᴴ * P * a * (u * uᴴ) by
    simp only [Matrix.mul_assoc], hu.2, Matrix.mul_one]

lemma cross_zero (t : Twist) (a b : W N) (u v : L N) :
    (fix t * a * u)ᴴ * (fix t.conj * b * v) = 0 := by
  rw [conjTranspose_mul, conjTranspose_mul, fix_herm]
  rw [show uᴴ * (aᴴ * fix t) * (fix t.conj * b * v) = uᴴ * (aᴴ * (fix t * fix t.conj) * b * v) by
    simp only [Matrix.mul_assoc]]
  rw [fix_mul_conj]; simp

lemma cross_zero' (t : Twist) (a b : W N) (u v : L N) :
    (fix t.conj * b * v)ᴴ * (fix t * a * u) = 0 := by
  rw [conjTranspose_mul, conjTranspose_mul, fix_herm]
  rw [show vᴴ * (bᴴ * fix t.conj) * (fix t * a * u) = vᴴ * (bᴴ * (fix t.conj * fix t) * a * u) by
    simp only [Matrix.mul_assoc]]
  rw [fix_conj_mul]; simp

/-- At one site the two hops add in norm. -/
lemma nsq_site (t : Twist) (a b : W N) (u v : L N) (hu : Unitary u) (hv : Unitary v) :
    nsq (fix t * a * u + fix t.conj * b * v) =
      trace (aᴴ * fix t * a) + trace (bᴴ * fix t.conj * b) := by
  have h1 := nsq_hop (fix t) (fix_herm t) (fix_idem t) a u hu
  have h2 := nsq_hop (fix t.conj) (fix_herm t.conj) (fix_idem t.conj) b v hv
  unfold nsq at h1 h2 ⊢
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, cross_zero, cross_zero',
    add_zero, zero_add, trace_add, h1, h2]

lemma unitary_ct {u : L N} (hu : Unitary u) : Unitary uᴴ := by
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact hu.2
  · rw [conjTranspose_conjTranspose]; exact hu.1

/-- **The step is unitary for every assignment of unitary links.** -/
theorem step_norm (t : Twist) (e : S) (U : S → L N) (hU : ∀ x, Unitary (U x)) (ψ : S → W N) :
    total (step t e U ψ) = total ψ := by
  unfold total step
  simp only [fun x => nsq_site t (ψ (x - e)) (ψ (x + e)) (U (x - e)) (U x)ᴴ (hU _)
    (unitary_ct (hU x))]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ x : S, trace ((ψ (x - e))ᴴ * fix t * ψ (x - e)) =
      ∑ x : S, trace ((ψ x)ᴴ * fix t * ψ x) :=
    Fintype.sum_equiv (Equiv.subRight e) _ (fun x => trace ((ψ x)ᴴ * fix t * ψ x)) (fun _ => rfl)
  have e2 : ∑ x : S, trace ((ψ (x + e))ᴴ * fix t.conj * ψ (x + e)) =
      ∑ x : S, trace ((ψ x)ᴴ * fix t.conj * ψ x) :=
    Fintype.sum_equiv (Equiv.addRight e) _ (fun x => trace ((ψ x)ᴴ * fix t.conj * ψ x))
      (fun _ => rfl)
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold nsq
  rw [← trace_add, ← Matrix.add_mul, ← Matrix.mul_add, fix_add_conj, Matrix.mul_one]

/-! ## Gauge covariance -/

/-- A site-dependent colour rotation of the walk. -/
noncomputable def rotate (g : S → L N) (ψ : S → W N) : S → W N := fun x => ψ x * g x

/-- The links after the colour rotation. -/
noncomputable def rotateLinks (e : S) (g : S → L N) (U : S → L N) : S → L N :=
  fun x => (g x)ᴴ * U x * g (x + e)

omit [Fintype S] in
/-- **The step is gauge covariant** under every site-dependent unitary colour rotation. -/
theorem step_covariant (t : Twist) (e : S) (U : S → L N) (g : S → L N) (hg : ∀ x, Unitary (g x))
    (ψ : S → W N) :
    step t e (rotateLinks e g U) (rotate g ψ) = rotate g (step t e U ψ) := by
  funext x
  unfold step rotate rotateLinks
  rw [sub_add_cancel, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.add_mul]
  congr 1
  · rw [show fix t * (ψ (x - e) * g (x - e)) * ((g (x - e))ᴴ * U (x - e) * g x) =
        fix t * ψ (x - e) * (g (x - e) * (g (x - e))ᴴ) * U (x - e) * g x by
      simp only [Matrix.mul_assoc], (hg _).2, Matrix.mul_one]
  · rw [show fix t.conj * (ψ (x + e) * g (x + e)) * ((g (x + e))ᴴ * ((U x)ᴴ * g x)) =
        fix t.conj * ψ (x + e) * (g (x + e) * (g (x + e))ᴴ) * (U x)ᴴ * g x by
      simp only [Matrix.mul_assoc], (hg _).2, Matrix.mul_one]

/-! ## The plaquette holonomy and the Wilson loop -/

variable {n : ℕ}

/-- The holonomy around the plaquette at `x` in the `(i, j)` plane. -/
noncomputable def holonomy (e : Fin n → S) (U : Fin n → S → L N) (i j : Fin n) (x : S) : L N :=
  U i x * U j (x + e i) * (U i (x + e j))ᴴ * (U j x)ᴴ

omit [Fintype S] in
/-- **The holonomy is conjugated by the rotation at its base point.** -/
theorem holonomy_gauge (e : Fin n → S) (U : Fin n → S → L N) (g : S → L N)
    (hg : ∀ x, Unitary (g x)) (i j : Fin n) (x : S) :
    holonomy e (fun k => rotateLinks (e k) g (U k)) i j x = (g x)ᴴ * holonomy e U i j x * g x := by
  unfold holonomy rotateLinks
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [show x + e j + e i = x + e i + e j by abel]
  have h1 := (hg (x + e i)).2
  have h2 := (hg (x + e i + e j)).2
  have h3 := (hg (x + e j)).2
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (g (x + e i)) (g (x + e i))ᴴ, h1, Matrix.one_mul,
    ← Matrix.mul_assoc (g (x + e i + e j)) (g (x + e i + e j))ᴴ, h2, Matrix.one_mul,
    ← Matrix.mul_assoc (g (x + e j)) (g (x + e j))ᴴ, h3, Matrix.one_mul]

omit [Fintype S] in
/-- **The Wilson loop `tr(holonomy)` is gauge invariant.** -/
theorem wilson_loop_invariant (e : Fin n → S) (U : Fin n → S → L N) (g : S → L N)
    (hg : ∀ x, Unitary (g x)) (i j : Fin n) (x : S) :
    trace (holonomy e (fun k => rotateLinks (e k) g (U k)) i j x) =
      trace (holonomy e U i j x) := by
  rw [holonomy_gauge e U g hg, trace_mul_comm, ← Matrix.mul_assoc, (hg x).2, Matrix.one_mul]

end QLF.NonAbelian
