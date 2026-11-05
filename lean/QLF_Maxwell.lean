import QLF_LatticeGauge

/-!
# QLF_Maxwell — the walk carries a conserved current, and that is what Gauss's law needs

Issue #207. [`QLF_LatticeGauge`](QLF_LatticeGauge.lean) gave the source-free half of Maxwell's
equations (the Bianchi identity). The other half couples the field to charge: Gauss's law
`div E = ρ` and the Ampère–Maxwell update `E' = E + curl B − J`. This module shows what QLF supplies
for that half and what it does not.

* **`continuity`.** A realizable step along any axis conserves the norm *locally*: the change of
  `ρ(x) = ‖ψ(x)‖²` at each site is minus the difference of a link current,
  `ρ'(x) − ρ(x) + J(x) − J(x − e) = 0`, where `J(x)` is what the step carries across the link from
  `x` to `x + e` (the forward part leaving `x` minus the backward part arriving from `x + e`). This
  is exact at every site, for every link field. **`current_invariant`**: the current is unchanged
  by a local phase change, so it is a physical quantity.
* **`div_curl`.** On any lattice, in any number of axes, the divergence of a curl of an oriented
  (antisymmetric) plaquette field is zero. An identity, like Bianchi.
* **`gauss_preserved`.** If `div E = ρ` now and charge obeys continuity, then after an
  Ampère–Maxwell update `div E' = ρ'`. **`gauss_preserved_by_walk`** applies this to the walk's own
  charge and current: Gauss's law is kept by the update exactly because the walk is unitary site by
  site.

What is proved is consistency: a conserved current exists, and Gauss's law is compatible with the
update because of it. What is **not** derived is the update itself, `E' = E + curl B − J`, which is
taken as the form here; [`QLF_MaxwellTime`](QLF_MaxwellTime.lean) derives it as the stationarity
of a finite link action over time. The charge here is the
walk's norm density; identifying it with electric charge is a reading. No axioms.

**Credit.** Lattice continuity and the compatibility of Gauss's law with charge conservation are
standard (Maxwell's displacement current exists to make them agree; on a lattice this is Yee's 1966
scheme, *IEEE Trans. Antennas Propag.* **14**, 302). QLF supplies the conserved current, from the
realizability of each step.
-/

namespace QLF.Maxwell

open Matrix
open QLF.ClosureChannels
open QLF.LocalGauge (ph nsq V)
open QLF.LatticeGauge (axisStep localPhase)

variable {S : Type*} [AddCommGroup S]

/-! ## 1. The walk's local continuity equation -/

/-- The charge density: the squared length at a site. -/
def rho (ψ : S → V) (x : S) : ℂ := nsq (ψ x)

/-- The current across the link from `x` to `x + e`: the forward part leaving `x` minus the
    backward part arriving from `x + e`. -/
noncomputable def current (t : Twist) (e : S) (ψ : S → V) (x : S) : ℂ :=
  nsq (fix t *ᵥ ψ x) - nsq (fix t.conj *ᵥ ψ (x + e))

lemma rho_step (t : Twist) (e : S) (a : S → ℝ) (ψ : S → V) (x : S) :
    rho (axisStep t e a ψ) x = nsq (fix t *ᵥ ψ (x - e)) + nsq (fix t.conj *ᵥ ψ (x + e)) := by
  unfold rho axisStep
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
    LocalGauge.nsq_add _ _ (LocalGauge.ortho t _ _) (LocalGauge.ortho' t _ _),
    Matrix.mulVec_smul, Matrix.mulVec_smul, LocalGauge.nsq_ph, LocalGauge.nsq_ph]

/-- **Local continuity.** Every realizable axis step conserves charge site by site:
    `ρ'(x) − ρ(x) + J(x) − J(x − e) = 0`. -/
theorem continuity (t : Twist) (e : S) (a : S → ℝ) (ψ : S → V) (x : S) :
    rho (axisStep t e a ψ) x - rho ψ x + (current t e ψ x - current t e ψ (x - e)) = 0 := by
  rw [rho_step]
  unfold rho current
  rw [LocalGauge.nsq_split t (ψ x), sub_add_cancel]
  ring

/-- **The current is gauge invariant.** -/
theorem current_invariant (t : Twist) (e : S) (θ : S → ℝ) (ψ : S → V) (x : S) :
    current t e (localPhase θ ψ) x = current t e ψ x := by
  unfold current localPhase
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, LocalGauge.nsq_ph, LocalGauge.nsq_ph]

/-! ## 2. Divergence, curl, and Gauss's law -/

variable {R : Type*} [Field R] [CharZero R] {n : ℕ}

/-- Lattice divergence of a link field (`E i` lives on the axis-`i` links). -/
def div (e : Fin n → S) (E : Fin n → S → R) (x : S) : R := ∑ i, (E i x - E i (x - e i))

/-- Lattice curl of a plaquette field (`B i j` lives on the `(i, j)` plaquettes). -/
def curl (e : Fin n → S) (B : Fin n → Fin n → S → R) (i : Fin n) (x : S) : R :=
  ∑ j, (B i j x - B i j (x - e j))

/-- **`div ∘ curl = 0`** for an oriented plaquette field. -/
theorem div_curl (e : Fin n → S) (B : Fin n → Fin n → S → R)
    (hB : ∀ i j y, B j i y = -B i j y) (x : S) : div e (curl e B) x = 0 := by
  let G : Fin n → Fin n → R := fun i j =>
    B i j x - B i j (x - e j) - B i j (x - e i) + B i j (x - e i - e j)
  have hG : ∀ i j, G j i = -G i j := by
    intro i j
    simp only [G]
    rw [hB i j x, hB i j (x - e i), hB i j (x - e j),
      show x - e j - e i = x - e i - e j by abel, hB i j (x - e i - e j)]
    ring
  have hsum : div e (curl e B) x = ∑ i, ∑ j, G i j := by
    unfold div curl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [G]
    ring
  have hanti : ∑ i, ∑ j, G i j = -∑ i, ∑ j, G i j :=
    calc ∑ i, ∑ j, G i j = ∑ j, ∑ i, G i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -G j i :=
          Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hG j i))
      _ = -∑ j, ∑ i, G j i := by simp only [Finset.sum_neg_distrib]
  rw [hsum]
  have h2 : (2 : R) * ∑ i, ∑ j, G i j = 0 := by
    rw [two_mul]; nth_rewrite 2 [hanti]; ring
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- **Gauss's law is kept by the Ampère–Maxwell update when charge is conserved.** -/
theorem gauss_preserved (e : Fin n → S) (E J : Fin n → S → R) (B : Fin n → Fin n → S → R)
    (hB : ∀ i j y, B j i y = -B i j y) (ρ ρ' : S → R) (x : S)
    (hgauss : div e E x = ρ x) (hcont : ρ' x - ρ x + div e J x = 0) :
    div e (fun i y => E i y + curl e B i y - J i y) x = ρ' x := by
  have hlin : div e (fun i y => E i y + curl e B i y - J i y) x =
      div e E x + div e (curl e B) x - div e J x := by
    unfold div
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hlin, div_curl e B hB, hgauss]
  linear_combination (-1 : R) * hcont

/-- The walk's current as a link field: along axis `k` only. -/
noncomputable def walkCurrent (e : Fin n → S) (k : Fin n) (t : Twist) (ψ : S → V) :
    Fin n → S → ℂ :=
  fun i y => if i = k then current t (e k) ψ y else 0

/-- **Gauss's law is kept by the walk.** If `div E = ρ` before a realizable step along axis `k`,
    then after the step and the Ampère–Maxwell update with the walk's own current, `div E' = ρ'`. -/
theorem gauss_preserved_by_walk (e : Fin n → S) (k : Fin n) (t : Twist) (a : S → ℝ)
    (ψ : S → V) (E : Fin n → S → ℂ) (B : Fin n → Fin n → S → ℂ)
    (hB : ∀ i j y, B j i y = -B i j y) (x : S) (hgauss : div e E x = rho ψ x) :
    div e (fun i y => E i y + curl e B i y - walkCurrent e k t ψ i y) x =
      rho (axisStep t (e k) a ψ) x := by
  apply gauss_preserved e E _ B hB (rho ψ) _ x hgauss
  have hJ : div e (walkCurrent e k t ψ) x = current t (e k) ψ x - current t (e k) ψ (x - e k) := by
    unfold div walkCurrent
    simp
  rw [hJ]
  exact continuity t (e k) a ψ x

end QLF.Maxwell
