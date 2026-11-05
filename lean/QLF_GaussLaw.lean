import QLF_MaxwellTime

/-!
# QLF_GaussLaw — Gauss's law is the equation of the time-link phase

Issue #207. [`QLF_MaxwellTime`](QLF_MaxwellTime.lean) put no phase on the time links (temporal
gauge), so Gauss's law was a constraint the update kept, not an equation the action produced. This
module puts the phase back and derives it.

A history now carries a phase `A τ i x` on every space link and a phase `φ τ x` on every time link
(from `(τ, x)` to `(τ + 1, x)`), with time the cycle `ZMod N`. The electric field is the plaquette
in a time–space plane, `E = −Δ_t A − ∇φ`:

  `E τ i x = −(A (τ+1) i x − A τ i x) − (φ τ (x + e i) − φ τ x)`.

With a charge `ρ` on the time links and a current `J` on the space links the action is

  `S[A, φ] = ½ Σ E² − Σ_τ S_link[A τ] − Σ_τ Σₓ ρ τ x · φ τ x`,

where `S_link = ¼ΣF² − ΣJ·a` is the link action of [`QLF_LinkAction`](QLF_LinkAction.lean).

* **`gauss_variation`, `stationary_iff_gauss`.** Moving one time-link phase `(σ, y)` by `±ε`
  changes the action by exactly `div E σ y − ρ σ y`, so the action is stationary under every
  time-link variation iff `div E = ρ` at every time and site: **Gauss's law, derived.**
* **`ampere_variation`, `stationary_iff_ampere`.** Moving one space link gives
  `(E σ − E (σ−1)) − (curl F − J)` exactly, as in `QLF_MaxwellTime`: the Ampère–Maxwell update.
* **`stationary_forces_continuity`.** The two equations together force
  `ρ σ − ρ (σ−1) + div J σ = 0`: charge must be conserved for the field equations to have a
  solution, because `div curl = 0`.
* **`E_gauge`, `action_gauge_shift`, `gauge_invariant_iff_continuity`.** A spacetime phase change
  `θ` leaves `E` (and `F`) unchanged, and shifts the action by `−Σ θ · (ρ τ − ρ (τ−1) + div J τ)`.
  So the coupling is gauge invariant iff charge obeys continuity: Noether's second theorem on the
  full spacetime lattice. The walk's charge and current of [`QLF_Maxwell`](QLF_Maxwell.lean) obey
  exactly this (`continuity`), so it is a source the links can carry.

All four are finite identities: the action is quadratic, so the symmetric difference is the first
variation. No axioms.

**Credit.** `E = −∂_t A − ∇φ` and Gauss's law as the `φ` equation are Maxwell's; the lattice form
is standard (Kogut and Susskind, *Phys. Rev. D* **11**, 395 (1975), where Gauss's law is the
generator of time-independent gauge transformations). The gauge/conservation link is Noether's
(1918).
-/

namespace QLF.GaussLaw

open QLF.LinkAction (F action ampere)
open QLF.MaxwellTime (vary tbump)

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {n : ℕ}
variable {N : ℕ} [NeZero N]

/-- The electric field: the plaquette in the time–space plane, `E = −Δ_t A − ∇φ`. -/
def E (e : Fin n → S) (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) (τ : ZMod N) (i : Fin n)
    (x : S) : ℝ :=
  -(A (τ + 1) i x - A τ i x) - (φ τ (x + e i) - φ τ x)

/-- The full action of a history with time-link phases. -/
noncomputable def fullAction (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ) (ρ : ZMod N → S → ℝ)
    (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) : ℝ :=
  (1 / 2) * ∑ τ, ∑ x, ∑ i, E e A φ τ i x ^ 2 - ∑ τ, action e (J τ) (A τ) - ∑ τ, ∑ x, ρ τ x * φ τ x

/-- The time-link phase at `(σ, y)` moved by `c`. -/
def varyφ (φ : ZMod N → S → ℝ) (c : ℝ) (σ : ZMod N) (y : S) : ZMod N → S → ℝ :=
  fun τ z => φ τ z + c * (if τ = σ ∧ z = y then 1 else 0)

/-! ## Gauss's law from the time links -/

omit [NeZero N] in
/-- Pairing `E` with the gradient of a point bump gives minus the divergence. -/
lemma sum_E_grad (G : Fin n → S → ℝ) (e : Fin n → S) (y : S) :
    ∑ x, ∑ i, G i x * ((if x + e i = y then 1 else 0) - (if x = y then 1 else 0)) =
      -Maxwell.div e G y := by
  rw [Finset.sum_comm]
  have h : ∀ i, ∑ x, G i x * ((if x + e i = y then (1 : ℝ) else 0) - (if x = y then 1 else 0)) =
      G i (y - e i) - G i y := by
    intro i
    have hx : ∀ x : S, (x + e i = y) ↔ (x = y - e i) := fun x => (eq_sub_iff_add_eq).symm
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, hx,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [h, Maxwell.div, Finset.sum_sub_distrib]
  ring

/-- **The time-link variation is `div E − ρ`**, exactly, for every `ε ≠ 0`. -/
theorem gauss_variation (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ) (ρ : ZMod N → S → ℝ)
    (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) (σ : ZMod N) (y : S) (ε : ℝ) (hε : ε ≠ 0) :
    (fullAction e J ρ A (varyφ φ ε σ y) - fullAction e J ρ A (varyφ φ (-ε) σ y)) / (2 * ε) =
      Maxwell.div e (E e A φ σ) y - ρ σ y := by
  classical
  -- the bump on time-link `(σ, y)` and its spatial gradient
  set g : ZMod N → Fin n → S → ℝ := fun τ i x =>
    if τ = σ then (if x + e i = y then 1 else 0) - (if x = y then 1 else 0) else 0 with hg
  have hE : ∀ (c : ℝ) τ i x, E e A (varyφ φ c σ y) τ i x = E e A φ τ i x - c * g τ i x := by
    intro c τ i x
    simp only [E, varyφ, hg]
    by_cases hτ : τ = σ
    · simp only [hτ, true_and, ite_true]; ring
    · simp only [hτ, false_and, ite_false]; ring
  have hpair : ∑ τ, ∑ x, ∑ i, E e A φ τ i x * g τ i x = -Maxwell.div e (E e A φ σ) y := by
    have : ∀ τ, ∑ x, ∑ i, E e A φ τ i x * g τ i x =
        if τ = σ then -Maxwell.div e (E e A φ τ) y else 0 := by
      intro τ
      by_cases hτ : τ = σ
      · subst hτ
        simp only [hg, ite_true]
        exact sum_E_grad (E e A φ τ) e y
      · simp [hg, hτ]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hkin : (1 / 2 : ℝ) * ∑ τ, ∑ x, ∑ i, E e A (varyφ φ ε σ y) τ i x ^ 2 -
      (1 / 2 : ℝ) * ∑ τ, ∑ x, ∑ i, E e A (varyφ φ (-ε) σ y) τ i x ^ 2 =
      2 * ε * Maxwell.div e (E e A φ σ) y := by
    simp only [hE]
    have hsum : ∑ τ, ∑ x, ∑ i, (E e A φ τ i x - ε * g τ i x) ^ 2 -
        ∑ τ, ∑ x, ∑ i, (E e A φ τ i x - -ε * g τ i x) ^ 2 =
        ∑ τ, ∑ x, ∑ i, -4 * ε * (E e A φ τ i x * g τ i x) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [← mul_sub, hsum]
    simp only [← Finset.mul_sum]
    rw [hpair]; ring
  have hρ : ∑ τ, ∑ x, ρ τ x * varyφ φ ε σ y τ x - ∑ τ, ∑ x, ρ τ x * varyφ φ (-ε) σ y τ x =
      2 * ε * ρ σ y := by
    have : ∀ τ x, ρ τ x * varyφ φ ε σ y τ x - ρ τ x * varyφ φ (-ε) σ y τ x =
        2 * ε * (if τ = σ then (if x = y then ρ τ x else 0) else 0) := by
      intro τ x
      simp only [varyφ]
      by_cases hτ : τ = σ <;> by_cases hx : x = y <;> simp [hτ, hx] <;> ring
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib, this, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
      Finset.sum_const_zero]
  have hsplit : fullAction e J ρ A (varyφ φ ε σ y) - fullAction e J ρ A (varyφ φ (-ε) σ y) =
      2 * ε * (Maxwell.div e (E e A φ σ) y - ρ σ y) := by
    unfold fullAction
    linear_combination hkin - hρ
  rw [hsplit, div_eq_iff (mul_ne_zero two_ne_zero hε)]
  ring

/-- **Stationary under every time-link variation ⇔ Gauss's law `div E = ρ`.** -/
theorem stationary_iff_gauss (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ) (ρ : ZMod N → S → ℝ)
    (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) :
    (∀ σ y, fullAction e J ρ A (varyφ φ 1 σ y) = fullAction e J ρ A (varyφ φ (-1) σ y)) ↔
      ∀ σ y, Maxwell.div e (E e A φ σ) y = ρ σ y := by
  constructor
  · intro h σ y
    have := gauss_variation e J ρ A φ σ y 1 one_ne_zero
    rw [h σ y, sub_self, zero_div] at this
    linarith
  · intro h σ y
    have := gauss_variation e J ρ A φ σ y 1 one_ne_zero
    rw [h σ y, sub_self, div_eq_iff (by norm_num : (2 : ℝ) * 1 ≠ 0)] at this
    linarith

/-! ## Ampère–Maxwell from the space links -/

/-- **The space-link variation**, exactly: the change of `E` across the varied time minus
    `curl F − J`. -/
theorem ampere_variation (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ) (ρ : ZMod N → S → ℝ)
    (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) (σ : ZMod N) (k : Fin n) (y : S) (ε : ℝ)
    (hε : ε ≠ 0) :
    (fullAction e J ρ (vary A ε σ k y) φ - fullAction e J ρ (vary A (-ε) σ k y) φ) / (2 * ε) =
      (E e A φ σ k y - E e A φ (σ - 1) k y) - (ampere e (A σ) k y - J σ k y) := by
  have hE : ∀ (c : ℝ) τ i x, E e (vary A c σ k y) φ τ i x =
      E e A φ τ i x - c * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x) := by
    intros; simp only [E, vary]; ring
  have hpick : ∀ c₀ : ZMod N, ∑ τ, ∑ x, ∑ i, E e A φ τ i x * tbump σ k y (τ + c₀) i x =
      E e A φ (σ - c₀) k y := by
    intro c₀
    have : ∀ τ, ∑ x, ∑ i, E e A φ τ i x * tbump σ k y (τ + c₀) i x =
        if τ = σ - c₀ then E e A φ τ k y else 0 := by
      intro τ
      by_cases h : τ = σ - c₀
      · subst h
        rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        simp only [tbump, sub_add_cancel, ite_true]
        exact MaxwellTime.sum_bump_link (E e A φ (σ - c₀)) k y
      · have h' : τ + c₀ ≠ σ := fun h2 => h (eq_sub_of_add_eq h2)
        simp [tbump, h', h]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hpick1 := hpick 1
  have hpick0 := hpick 0
  simp only [add_zero, sub_zero] at hpick0
  have hkin : (1 / 2 : ℝ) * ∑ τ, ∑ x, ∑ i, E e (vary A ε σ k y) φ τ i x ^ 2 -
      (1 / 2 : ℝ) * ∑ τ, ∑ x, ∑ i, E e (vary A (-ε) σ k y) φ τ i x ^ 2 =
      2 * ε * (E e A φ σ k y - E e A φ (σ - 1) k y) := by
    simp only [hE]
    have hsum : ∑ τ, ∑ x, ∑ i,
          (E e A φ τ i x - ε * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x)) ^ 2 -
        ∑ τ, ∑ x, ∑ i,
          (E e A φ τ i x - -ε * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x)) ^ 2 =
        ∑ τ, ∑ x, ∑ i, -4 * ε *
          (E e A φ τ i x * tbump σ k y (τ + 1) i x - E e A φ τ i x * tbump σ k y τ i x) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [← mul_sub, hsum]
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hpick1, hpick0]
    ring
  have hsplit : fullAction e J ρ (vary A ε σ k y) φ - fullAction e J ρ (vary A (-ε) σ k y) φ =
      2 * ε * ((E e A φ σ k y - E e A φ (σ - 1) k y) - (ampere e (A σ) k y - J σ k y)) := by
    unfold fullAction
    linear_combination hkin - MaxwellTime.potential_var e J A ε hε σ k y
  rw [hsplit, div_eq_iff (mul_ne_zero two_ne_zero hε)]
  ring

/-- **Stationary under every space-link variation ⇔ the Ampère–Maxwell update.** -/
theorem stationary_iff_ampere (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ) (ρ : ZMod N → S → ℝ)
    (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) :
    (∀ σ k y, fullAction e J ρ (vary A 1 σ k y) φ = fullAction e J ρ (vary A (-1) σ k y) φ) ↔
      ∀ σ k y, E e A φ σ k y = E e A φ (σ - 1) k y + ampere e (A σ) k y - J σ k y := by
  constructor
  · intro h σ k y
    have := ampere_variation e J ρ A φ σ k y 1 one_ne_zero
    rw [h σ k y, sub_self, zero_div] at this
    linarith
  · intro h σ k y
    have := ampere_variation e J ρ A φ σ k y 1 one_ne_zero
    rw [h σ k y, div_eq_iff (by norm_num : (2 : ℝ) * 1 ≠ 0)] at this
    linarith

omit [Fintype S] [DecidableEq S] [NeZero N] in
/-- **The field equations force charge conservation.** -/
theorem stationary_forces_continuity (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ)
    (ρ : ZMod N → S → ℝ) (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ)
    (hG : ∀ σ y, Maxwell.div e (E e A φ σ) y = ρ σ y)
    (hA : ∀ σ k y, E e A φ σ k y = E e A φ (σ - 1) k y + ampere e (A σ) k y - J σ k y)
    (σ : ZMod N) (x : S) : ρ σ x - ρ (σ - 1) x + Maxwell.div e (J σ) x = 0 := by
  have hc := Maxwell.div_curl e (F e (A σ)) (fun i j y => LinkAction.F_antisymm e (A σ) i j y) x
  have hlin : Maxwell.div e (E e A φ σ) x =
      Maxwell.div e (E e A φ (σ - 1)) x + Maxwell.div e (Maxwell.curl e (F e (A σ))) x -
        Maxwell.div e (J σ) x := by
    unfold Maxwell.div
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hA σ i x, hA σ i (x - e i)]
    simp only [LinkAction.ampere_eq_curl]
    ring
  rw [hG σ x, hG (σ - 1) x, hc] at hlin
  linarith

/-! ## Spacetime gauge invariance ⇔ continuity -/

/-- A spacetime phase change `θ` on the space and the time links. -/
def gaugeA (e : Fin n → S) (θ : ZMod N → S → ℝ) (A : ZMod N → Fin n → S → ℝ) :
    ZMod N → Fin n → S → ℝ :=
  fun τ => LinkAction.gaugeShift e (θ τ) (A τ)

def gaugeφ (θ : ZMod N → S → ℝ) (φ : ZMod N → S → ℝ) : ZMod N → S → ℝ :=
  fun τ x => φ τ x - (θ (τ + 1) x - θ τ x)

omit [Fintype S] [DecidableEq S] [NeZero N] in
/-- **The electric field is gauge invariant.** -/
theorem E_gauge (e : Fin n → S) (θ : ZMod N → S → ℝ) (A : ZMod N → Fin n → S → ℝ)
    (φ : ZMod N → S → ℝ) (τ : ZMod N) (i : Fin n) (x : S) :
    E e (gaugeA e θ A) (gaugeφ θ φ) τ i x = E e A φ τ i x := by
  simp only [E, gaugeA, gaugeφ, LinkAction.gaugeShift]; ring

omit [DecidableEq S] in
/-- **A spacetime phase change shifts the action by `−Σ θ · (ρ τ − ρ (τ−1) + div J τ)`.** -/
theorem action_gauge_shift (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ) (ρ : ZMod N → S → ℝ)
    (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) (θ : ZMod N → S → ℝ) :
    fullAction e J ρ (gaugeA e θ A) (gaugeφ θ φ) =
      fullAction e J ρ A φ -
        ∑ τ, ∑ x, θ τ x * (ρ τ x - ρ (τ - 1) x + Maxwell.div e (J τ) x) := by
  unfold fullAction
  simp only [E_gauge]
  have hlink : ∀ τ, action e (J τ) (gaugeA e θ A τ) =
      action e (J τ) (A τ) + ∑ x, θ τ x * Maxwell.div e (J τ) x :=
    fun τ => LinkAction.action_gauge_shift e (J τ) (A τ) (θ τ)
  simp only [hlink, Finset.sum_add_distrib]
  have hshift : ∑ τ, ∑ x, ρ τ x * θ (τ + 1) x = ∑ τ, ∑ x, θ τ x * ρ (τ - 1) x :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _
      (fun τ => by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [Equiv.coe_addRight, add_sub_cancel_right]; ring)
  have hcoup : ∑ τ, ∑ x, ρ τ x * gaugeφ θ φ τ x =
      ∑ τ, ∑ x, ρ τ x * φ τ x - ∑ τ, ∑ x, θ τ x * ρ (τ - 1) x + ∑ τ, ∑ x, θ τ x * ρ τ x := by
    rw [← hshift]
    simp only [gaugeφ, mul_sub, Finset.sum_sub_distrib]
    have : ∀ τ x, ρ τ x * θ τ x = θ τ x * ρ τ x := fun _ _ => mul_comm _ _
    simp only [this]
    ring
  rw [hcoup]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

omit [DecidableEq S] in
/-- **The coupling is gauge invariant ⇔ charge obeys continuity** at every time and site. -/
theorem gauge_invariant_iff_continuity (e : Fin n → S) (J : ZMod N → Fin n → S → ℝ)
    (ρ : ZMod N → S → ℝ) (A : ZMod N → Fin n → S → ℝ) (φ : ZMod N → S → ℝ) :
    (∀ θ : ZMod N → S → ℝ,
        fullAction e J ρ (gaugeA e θ A) (gaugeφ θ φ) = fullAction e J ρ A φ) ↔
      ∀ τ x, ρ τ x - ρ (τ - 1) x + Maxwell.div e (J τ) x = 0 := by
  classical
  constructor
  · intro h τ₀ x₀
    have := h (fun τ x => if τ = τ₀ ∧ x = x₀ then 1 else 0)
    rw [action_gauge_shift] at this
    have h0 : ∑ τ, ∑ x, (if τ = τ₀ ∧ x = x₀ then (1 : ℝ) else 0) *
        (ρ τ x - ρ (τ - 1) x + Maxwell.div e (J τ) x) = 0 := by linarith
    simpa [ite_and, ite_mul, Finset.sum_ite_eq', Finset.mem_univ] using h0
  · intro h θ
    rw [action_gauge_shift]
    simp [h]

end QLF.GaussLaw
