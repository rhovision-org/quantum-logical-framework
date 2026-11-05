import QLF_LinkAction

/-!
# QLF_MaxwellTime — the Ampère–Maxwell update is the stationarity of a finite history

Issue #207. [`QLF_Maxwell`](QLF_Maxwell.lean) took the update `E' = E + curl F − J` as its form, and
[`QLF_LinkAction`](QLF_LinkAction.lean) derived only the static law `curl F = J`. This module adds
time and derives the update itself.

A history is a link field at every time, `A τ i x`, with time the cycle `ZMod N` (a history
that closes on itself, so there are no boundary terms). The electric field lives on the time link
from `τ` to `τ + 1`: `E τ = −(A (τ+1) − A τ)` (temporal gauge: no phase on the time links). The
action of the history is

  `S[A] = ½ Σ_τ Σₓ Σᵢ (E τ i x)² − Σ_τ S_link[A τ]`,

kinetic electric energy minus, at each time, the link action of `QLF_LinkAction`
(`¼ΣF² − ΣJ·a`).

* **`first_variation`.** Move one link `(k, y)` at one time `σ` by `±ε`. The symmetric difference
  of the action is *exactly* `(E σ − E (σ − 1)) − (curl F − J)` at that link, for every `ε ≠ 0`.
  The action is quadratic, so no derivative or limit is needed.
* **`stationary_iff_update`.** The history is stationary under every variation iff, at every time
  and link, `E σ = E (σ − 1) + curl F (A σ) − J σ`: the Ampère–Maxwell update, derived.
* **`gauss_from_action`.** On a stationary history, if Gauss's law holds before a step and the
  charge obeys continuity, it holds after: the update that `QLF_Maxwell` assumed is the one the
  action selects.

**Not here.** Gauss's law itself is the equation of a phase on the time links; in temporal gauge it
is a constraint the update keeps (above), not one the variation produces; with the time-link
phase restored, [`QLF_GaussLaw`](QLF_GaussLaw.lean) derives it. The links are non-compact
(the weak-coupling, quadratic form); compact and non-abelian links, and the walk's own action, are
not included. No axioms.

**Credit.** The discrete-time lattice Maxwell action and its leapfrog equations are standard (Yee,
*IEEE Trans. Antennas Propag.* **14**, 302 (1966); the Hamiltonian lattice form is Kogut and
Susskind, *Phys. Rev. D* **11**, 395 (1975)). QLF supplies the conserved current that feeds them
([`QLF_Maxwell`](QLF_Maxwell.lean)).
-/

namespace QLF.MaxwellTime

open QLF.LinkAction (F action bump ampere)

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {n : ℕ}
variable {N : ℕ} [NeZero N]

/-- The electric field on the time link from `τ` to `τ + 1`. -/
def elec (A : ZMod N → Fin n → S → ℝ) (τ : ZMod N) (i : Fin n) (x : S) : ℝ := -(A (τ + 1) i x - A τ i x)

/-- The kinetic (electric) energy of a history. -/
noncomputable def kinetic (A : ZMod N → Fin n → S → ℝ) : ℝ :=
  (1 / 2) * ∑ τ, ∑ x, ∑ i, elec A τ i x ^ 2

/-- The action of a history: electric energy minus the link action at every time. -/
noncomputable def histAction (e : Fin n → S) (J A : ZMod N → Fin n → S → ℝ) : ℝ :=
  kinetic A - ∑ τ, action e (J τ) (A τ)

/-- The unit variation of the link `(k, y)` at time `σ`. -/
def tbump (σ : ZMod N) (k : Fin n) (y : S) : ZMod N → Fin n → S → ℝ :=
  fun τ i x => if τ = σ then bump k y i x else 0

/-- The history with the link `(k, y)` at time `σ` moved by `c`. -/
def vary (A : ZMod N → Fin n → S → ℝ) (c : ℝ) (σ : ZMod N) (k : Fin n) (y : S) : ZMod N → Fin n → S → ℝ :=
  fun τ l z => A τ l z + c * tbump σ k y τ l z

omit [NeZero N] in
/-- Pairing with one link's bump picks out that link. -/
lemma sum_bump_link (f : Fin n → S → ℝ) (k : Fin n) (y : S) :
    ∑ x, ∑ i, f i x * bump k y i x = f k y := by
  rw [Finset.sum_comm]
  have h0 : ∀ i, ∑ x, f i x * bump k y i x = if i = k then f i y else 0 :=
    fun i => LinkAction.sum_bump0 (f i) i k y
  simp only [h0, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [AddCommGroup S] [Fintype S] [NeZero N] in
lemma vary_self (A : ZMod N → Fin n → S → ℝ) (c : ℝ) (σ : ZMod N) (k : Fin n) (y : S) :
    vary A c σ k y σ = fun l z => A σ l z + c * bump k y l z := by
  funext l z; simp [vary, tbump]

omit [AddCommGroup S] [Fintype S] [NeZero N] in
lemma vary_other (A : ZMod N → Fin n → S → ℝ) (c : ℝ) (σ τ : ZMod N) (k : Fin n) (y : S) (h : τ ≠ σ) :
    vary A c σ k y τ = A τ := by
  funext l z; simp [vary, tbump, h]

/-- The kinetic term's variation: the change in `E` across the varied time. -/
lemma kinetic_var (A : ZMod N → Fin n → S → ℝ) (ε : ℝ) (σ : ZMod N) (k : Fin n) (y : S) :
    kinetic (vary A ε σ k y) - kinetic (vary A (-ε) σ k y) =
      2 * ε * (elec A σ k y - elec A (σ - 1) k y) := by
  have hE : ∀ (c : ℝ) τ i x, elec (vary A c σ k y) τ i x =
      elec A τ i x - c * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x) := by
    intros; simp only [elec, vary]; ring
  -- Σ_τ Σ_x Σ_i E τ · tbump (τ + c₀) picks out the time `σ − c₀`.
  have hpick : ∀ c₀ : ZMod N, ∑ τ, ∑ x, ∑ i, elec A τ i x * tbump σ k y (τ + c₀) i x =
      elec A (σ - c₀) k y := by
    intro c₀
    have : ∀ τ, ∑ x, ∑ i, elec A τ i x * tbump σ k y (τ + c₀) i x =
        if τ = σ - c₀ then elec A τ k y else 0 := by
      intro τ
      by_cases h : τ = σ - c₀
      · subst h
        rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        simp only [tbump, sub_add_cancel, ite_true]
        exact sum_bump_link (elec A (σ - c₀)) k y
      · have h' : τ + c₀ ≠ σ := fun h2 => h (eq_sub_of_add_eq h2)
        simp [tbump, h', h]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hpick1 := hpick 1
  have hpick0 := hpick 0
  simp only [add_zero, sub_zero] at hpick0
  unfold kinetic
  simp only [hE]
  have hq : ∀ τ x i, (elec A τ i x - ε * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x)) ^ 2 -
      (elec A τ i x - -ε * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x)) ^ 2 =
      -4 * ε * (elec A τ i x * tbump σ k y (τ + 1) i x - elec A τ i x * tbump σ k y τ i x) := by
    intros; ring
  have hsum : ∑ τ, ∑ x, ∑ i,
        (elec A τ i x - ε * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x)) ^ 2 -
      ∑ τ, ∑ x, ∑ i,
        (elec A τ i x - -ε * (tbump σ k y (τ + 1) i x - tbump σ k y τ i x)) ^ 2 =
      ∑ τ, ∑ x, ∑ i,
        -4 * ε * (elec A τ i x * tbump σ k y (τ + 1) i x - elec A τ i x * tbump σ k y τ i x) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => hq τ x i)
  have hlin : ∑ τ, ∑ x, ∑ i,
        -4 * ε * (elec A τ i x * tbump σ k y (τ + 1) i x - elec A τ i x * tbump σ k y τ i x) =
      -4 * ε * (∑ τ, ∑ x, ∑ i, elec A τ i x * tbump σ k y (τ + 1) i x -
        ∑ τ, ∑ x, ∑ i, elec A τ i x * tbump σ k y τ i x) := by
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← mul_sub, hsum, hlin, hpick1, hpick0]
  ring

/-- The link action's variation, read at the varied time only. -/
lemma potential_var (e : Fin n → S) (J A : ZMod N → Fin n → S → ℝ) (ε : ℝ) (hε : ε ≠ 0) (σ : ZMod N)
    (k : Fin n) (y : S) :
    ∑ τ, action e (J τ) (vary A ε σ k y τ) - ∑ τ, action e (J τ) (vary A (-ε) σ k y τ) =
      2 * ε * (ampere e (A σ) k y - J σ k y) := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single σ]
  · rw [vary_self, vary_self]
    have h := LinkAction.first_variation e (J σ) (A σ) k y ε hε
    rw [div_eq_iff (mul_ne_zero two_ne_zero hε)] at h
    rw [h]; ring
  · intro τ _ h
    rw [vary_other A _ σ τ k y h, vary_other A _ σ τ k y h, sub_self]
  · intro h; exact absurd (Finset.mem_univ σ) h

/-- **The first variation of the history's action**, exactly, for every `ε ≠ 0`:
    the change in `E` across the varied time minus `curl F − J` there. -/
theorem first_variation (e : Fin n → S) (J A : ZMod N → Fin n → S → ℝ) (σ : ZMod N) (k : Fin n) (y : S)
    (ε : ℝ) (hε : ε ≠ 0) :
    (histAction e J (vary A ε σ k y) - histAction e J (vary A (-ε) σ k y)) / (2 * ε) =
      (elec A σ k y - elec A (σ - 1) k y) - (ampere e (A σ) k y - J σ k y) := by
  have hsplit : histAction e J (vary A ε σ k y) - histAction e J (vary A (-ε) σ k y) =
      2 * ε * ((elec A σ k y - elec A (σ - 1) k y) - (ampere e (A σ) k y - J σ k y)) := by
    unfold histAction
    linear_combination kinetic_var A ε σ k y - potential_var e J A ε hε σ k y
  rw [hsplit, div_eq_iff (mul_ne_zero two_ne_zero hε)]
  ring

/-- **Stationary history ⇔ the Ampère–Maxwell update** `E σ = E (σ − 1) + curl F − J`
    at every time and link. -/
theorem stationary_iff_update (e : Fin n → S) (J A : ZMod N → Fin n → S → ℝ) :
    (∀ σ k y, histAction e J (vary A 1 σ k y) = histAction e J (vary A (-1) σ k y)) ↔
      ∀ σ k y, elec A σ k y = elec A (σ - 1) k y + ampere e (A σ) k y - J σ k y := by
  constructor
  · intro h σ k y
    have := first_variation e J A σ k y 1 one_ne_zero
    rw [h σ k y, sub_self, zero_div] at this
    linarith
  · intro h σ k y
    have := first_variation e J A σ k y 1 one_ne_zero
    rw [h σ k y, div_eq_iff (by norm_num : (2 : ℝ) * 1 ≠ 0)] at this
    linarith

omit [Fintype S] [DecidableEq S] [NeZero N] in
/-- **Gauss's law is kept by the update the action selects.** -/
theorem gauss_from_action (e : Fin n → S) (J A : ZMod N → Fin n → S → ℝ) (σ : ZMod N)
    (h : ∀ k y, elec A σ k y = elec A (σ - 1) k y + ampere e (A σ) k y - J σ k y)
    (ρ ρ' : S → ℝ) (x : S) (hgauss : Maxwell.div e (elec A (σ - 1)) x = ρ x)
    (hcont : ρ' x - ρ x + Maxwell.div e (J σ) x = 0) :
    Maxwell.div e (elec A σ) x = ρ' x := by
  have hE : elec A σ = fun i y => elec A (σ - 1) i y + Maxwell.curl e (F e (A σ)) i y - J σ i y := by
    funext i y; exact h i y
  rw [hE]
  exact Maxwell.gauss_preserved e (elec A (σ - 1)) (J σ) (F e (A σ))
    (fun i j y => LinkAction.F_antisymm e (A σ) i j y) ρ ρ' x hgauss hcont

end QLF.MaxwellTime
