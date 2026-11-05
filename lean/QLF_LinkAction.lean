import QLF_Maxwell

/-!
# QLF_LinkAction — a finite action for the links, and Ampère's law as its stationarity

Issue #207. [`QLF_Maxwell`](QLF_Maxwell.lean) took the Ampère–Maxwell update as given. This module
derives the (static) Ampère law from a finite action for the link phases, with no limit anywhere.

The lattice is any finite abelian group of sites with axes `e : Fin n → S`. A link field `a` puts a
phase `a i x` on the axis-`i` link at `x`, and its plaquette field is
`F i j x = a i x + a j (x + e i) − a i (x + e j) − a j x` (as in
[`QLF_LatticeGauge`](QLF_LatticeGauge.lean)). The action, with a current `J` on the links, is

  `S[a] = ¼ Σₓ Σᵢ Σⱼ F i j x² − Σₓ Σᵢ J i x · a i x`

(each unordered plaquette appears twice, so the first term is `½ Σ_{i<j} F²`).

* **`first_variation`.** Move one link `(k, y)` by `±ε`. The symmetric difference of the action is
  *exactly* the curl of `F` minus the current, for every `ε ≠ 0`:
  `(S[a + ε δ] − S[a − ε δ]) / 2ε = (curl F)_k(y) − J_k(y)`. The action is quadratic, so this
  finite difference is the first variation: no derivative and no limit are needed.
* **`stationary_iff_ampere`.** The action is stationary under every link variation iff
  `curl F = J` at every link: the static Ampère law.
* **`stationary_conserves_current`.** If a stationary configuration exists, the current is
  conserved, `div J = 0`, because `div curl = 0`.
* **`action_gauge_shift`, `gauge_invariant_iff_conserved`.** A local phase change shifts the action
  by `Σₓ θ(x) · div J(x)`. So the coupling is gauge invariant iff the current is conserved: the
  lattice form of Noether's second theorem.

This is a concrete instance of the open bridge in [`Stationary_Action.md`](../Stationary_Action.md):
here an action, its admissible variations and its first-variation identity are all explicit and
finite. It is the link sector only; the walk's own action and the time direction are not included.

**Credit.** This is the standard lattice (Wilson) action at weak coupling, in its quadratic,
non-compact form, and the Euler–Lagrange equations are the lattice Maxwell equations; the gauge/
conservation link is Noether's (1918). No axioms.
-/

namespace QLF.LinkAction

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {n : ℕ}

/-- The plaquette field of a link field `a`. -/
def F (e : Fin n → S) (a : Fin n → S → ℝ) (i j : Fin n) (x : S) : ℝ :=
  a i x + a j (x + e i) - a i (x + e j) - a j x

omit [Fintype S] [DecidableEq S] in
theorem F_antisymm (e : Fin n → S) (a : Fin n → S → ℝ) (i j : Fin n) (x : S) :
    F e a j i x = -F e a i j x := by
  simp only [F]; ring

omit [Fintype S] [DecidableEq S] in
theorem F_linear (e : Fin n → S) (a b : Fin n → S → ℝ) (c : ℝ) (i j : Fin n) (x : S) :
    F e (fun l z => a l z + c * b l z) i j x = F e a i j x + c * F e b i j x := by
  simp only [F]; ring

/-- The link action with current `J`. -/
noncomputable def action (e : Fin n → S) (J a : Fin n → S → ℝ) : ℝ :=
  (1 / 4) * ∑ x, ∑ i, ∑ j, F e a i j x ^ 2 - ∑ x, ∑ i, J i x * a i x

/-- The unit variation of the single link `(k, y)`. -/
def bump (k : Fin n) (y : S) : Fin n → S → ℝ := fun i x => if i = k ∧ x = y then 1 else 0

/-- The curl of the plaquette field at the link `(k, y)`. -/
def ampere (e : Fin n → S) (a : Fin n → S → ℝ) (k : Fin n) (y : S) : ℝ :=
  ∑ j, (F e a k j y - F e a k j (y - e j))

omit [Fintype S] [DecidableEq S] in
theorem ampere_eq_curl (e : Fin n → S) (a : Fin n → S → ℝ) :
    ampere e a = Maxwell.curl e (F e a) := rfl

/-- Summing against a shifted bump picks out one value. -/
lemma sum_bump (f : S → ℝ) (i k : Fin n) (y c : S) :
    ∑ x, f x * bump k y i (x + c) = if i = k then f (y - c) else 0 := by
  by_cases h : i = k
  · subst h
    simp only [bump, true_and, ite_true, mul_ite, mul_one, mul_zero]
    have : ∀ x : S, (x + c = y) ↔ (x = y - c) := fun x => (eq_sub_iff_add_eq).symm
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · simp [bump, h]

lemma sum_bump0 (f : S → ℝ) (i k : Fin n) (y : S) :
    ∑ x, f x * bump k y i x = if i = k then f y else 0 := by
  have := sum_bump f i k y 0
  simpa using this

/-- The pairing of `F` with the variation of one link. -/
lemma sum_F_bump (e : Fin n → S) (a : Fin n → S → ℝ) (k : Fin n) (y : S) (i j : Fin n) :
    ∑ x, F e a i j x * F e (bump k y) i j x =
      (if i = k then F e a i j y - F e a i j (y - e j) else 0) +
      (if j = k then F e a i j (y - e i) - F e a i j y else 0) := by
  simp only [F, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_bump0 (fun x => _), sum_bump (fun x => _) j k y (e i), sum_bump (fun x => _) i k y (e j),
    sum_bump0 (fun x => _)]
  split_ifs <;> ring

/-- The whole quadratic pairing: twice the curl at the varied link. -/
lemma sum_F_bump_total (e : Fin n → S) (a : Fin n → S → ℝ) (k : Fin n) (y : S) :
    ∑ x, ∑ i, ∑ j, F e a i j x * F e (bump k y) i j x = 2 * ampere e a k y := by
  rw [Finset.sum_comm]
  have h1 : ∀ i, ∑ x, ∑ j, F e a i j x * F e (bump k y) i j x =
      ∑ j, ∑ x, F e a i j x * F e (bump k y) i j x := fun i => Finset.sum_comm
  simp only [h1, sum_F_bump, Finset.sum_add_distrib]
  have h0 : ∑ i, ∑ j, (if i = k then F e a i j y - F e a i j (y - e j) else 0) =
      ∑ j, (F e a k j y - F e a k j (y - e j)) := by
    have : ∀ i, ∑ j, (if i = k then F e a i j y - F e a i j (y - e j) else 0) =
        if i = k then ∑ j, (F e a i j y - F e a i j (y - e j)) else 0 := by
      intro i; split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h0]
  have h2 : ∑ i, ∑ j, (if j = k then F e a i j (y - e i) - F e a i j y else 0) =
      ∑ i, (F e a i k (y - e i) - F e a i k y) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq' Finset.univ k (fun j => F e a i j (y - e i) - F e a i j y)]
    simp
  rw [h2]
  unfold ampere
  have h3 : ∑ i, (F e a i k (y - e i) - F e a i k y) = ∑ j, (F e a k j y - F e a k j (y - e j)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [F_antisymm e a k i, F_antisymm e a k i]; ring
  rw [h3]; ring

/-- **The first variation of the link action is curl F − J**, exactly, for every `ε ≠ 0`. -/
theorem first_variation (e : Fin n → S) (J a : Fin n → S → ℝ) (k : Fin n) (y : S) (ε : ℝ)
    (hε : ε ≠ 0) :
    (action e J (fun l z => a l z + ε * bump k y l z) -
        action e J (fun l z => a l z + (-ε) * bump k y l z)) / (2 * ε) =
      ampere e a k y - J k y := by
  unfold action
  simp only [F_linear]
  have hq : ∀ x i j, (F e a i j x + ε * F e (bump k y) i j x) ^ 2 -
      (F e a i j x + -ε * F e (bump k y) i j x) ^ 2 =
      4 * ε * (F e a i j x * F e (bump k y) i j x) := by intros; ring
  have hsq : (1 / 4 : ℝ) * ∑ x, ∑ i, ∑ j, (F e a i j x + ε * F e (bump k y) i j x) ^ 2 -
      (1 / 4 : ℝ) * ∑ x, ∑ i, ∑ j, (F e a i j x + -ε * F e (bump k y) i j x) ^ 2 =
      ε * (2 * ampere e a k y) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib, hq]
    rw [← sum_F_bump_total e a k y]
    simp only [← Finset.mul_sum]
    ring
  have hJ : ∑ x, ∑ i, J i x * (a i x + ε * bump k y i x) -
      ∑ x, ∑ i, J i x * (a i x + -ε * bump k y i x) = 2 * ε * J k y := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ x, ∑ i, J i x * (a i x + ε * bump k y i x) - ∑ i, J i x * (a i x + -ε * bump k y i x)
        = 2 * ε * ∑ i, J i x * bump k y i x := by
      intro x; rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    simp only [this, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have h0 : ∀ i, ∑ x, J i x * bump k y i x = if i = k then J i y else 0 :=
      fun i => sum_bump0 (J i) i k y
    simp only [h0, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hsplit : (1 / 4 * ∑ x, ∑ i, ∑ j, (F e a i j x + ε * F e (bump k y) i j x) ^ 2 -
        ∑ x, ∑ i, J i x * (a i x + ε * bump k y i x)) -
      (1 / 4 * ∑ x, ∑ i, ∑ j, (F e a i j x + -ε * F e (bump k y) i j x) ^ 2 -
        ∑ x, ∑ i, J i x * (a i x + -ε * bump k y i x)) = 2 * ε * (ampere e a k y - J k y) := by
    linear_combination hsq - hJ
  rw [hsplit]
  field_simp

/-- **Stationary under every link variation ⇔ the static Ampère law `curl F = J`.** -/
theorem stationary_iff_ampere (e : Fin n → S) (J a : Fin n → S → ℝ) :
    (∀ k y, action e J (fun l z => a l z + bump k y l z) =
        action e J (fun l z => a l z + (-1) * bump k y l z)) ↔
      ∀ k y, ampere e a k y = J k y := by
  constructor
  · intro h k y
    have := first_variation e J a k y 1 one_ne_zero
    simp only [one_mul] at this
    rw [h k y] at this
    simp only [sub_self, zero_div] at this
    linarith
  · intro h k y
    have := first_variation e J a k y 1 one_ne_zero
    simp only [one_mul] at this
    rw [h k y, sub_self] at this
    have h2 : (2 : ℝ) * 1 ≠ 0 := by norm_num
    have := (div_eq_zero_iff.mp this).resolve_right h2
    linarith

omit [Fintype S] [DecidableEq S] in
/-- **Stationarity forces a conserved current.** -/
theorem stationary_conserves_current (e : Fin n → S) (J a : Fin n → S → ℝ)
    (h : ∀ k y, ampere e a k y = J k y) (x : S) : Maxwell.div e J x = 0 := by
  have hJ : J = ampere e a := by funext k y; exact (h k y).symm
  rw [hJ, ampere_eq_curl]
  exact Maxwell.div_curl e (F e a) (fun i j y => F_antisymm e a i j y) x

/-! ## Gauge invariance and current conservation (Noether) -/

/-- Link field after a local phase change `θ`. -/
def gaugeShift (e : Fin n → S) (θ : S → ℝ) (a : Fin n → S → ℝ) : Fin n → S → ℝ :=
  fun i x => a i x + θ (x + e i) - θ x

omit [Fintype S] [DecidableEq S] in
theorem F_gauge (e : Fin n → S) (θ : S → ℝ) (a : Fin n → S → ℝ) (i j : Fin n) (x : S) :
    F e (gaugeShift e θ a) i j x = F e a i j x := by
  simp only [F, gaugeShift]
  rw [show x + e i + e j = x + e j + e i by abel]
  ring

omit [DecidableEq S] in
/-- **A local phase change shifts the action by `Σ θ · div J`.** -/
theorem action_gauge_shift (e : Fin n → S) (J a : Fin n → S → ℝ) (θ : S → ℝ) :
    action e J (gaugeShift e θ a) = action e J a + ∑ x, θ x * Maxwell.div e J x := by
  unfold action
  simp only [F_gauge]
  have hsh : ∀ i, ∑ x, J i x * θ (x + e i) = ∑ x, J i (x - e i) * θ x := by
    intro i
    exact Fintype.sum_equiv (Equiv.addRight (e i)) _ _ (fun x => by simp)
  have key : ∑ x, ∑ i, J i x * gaugeShift e θ a i x =
      ∑ x, ∑ i, J i x * a i x - ∑ x, θ x * Maxwell.div e J x := by
    simp only [gaugeShift, Maxwell.div, mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun x i => J i x * θ (x + e i)), Finset.sum_congr rfl
      (fun i _ => hsh i), Finset.sum_comm (f := fun i x => J i (x - e i) * θ x)]
    have : ∀ x : S, ∀ i : Fin n, θ x * J i (x - e i) = J i (x - e i) * θ x := fun _ _ => mul_comm _ _
    have h2 : ∀ x : S, ∀ i : Fin n, θ x * J i x = J i x * θ x := fun _ _ => mul_comm _ _
    simp only [this, h2]
    ring
  rw [key]; ring

/-- **The coupling is gauge invariant iff the current is conserved.** -/
theorem gauge_invariant_iff_conserved (e : Fin n → S) (J a : Fin n → S → ℝ) :
    (∀ θ : S → ℝ, action e J (gaugeShift e θ a) = action e J a) ↔
      ∀ x, Maxwell.div e J x = 0 := by
  constructor
  · intro h x
    have := h (fun z => if z = x then 1 else 0)
    rw [action_gauge_shift] at this
    simpa [ite_mul] using this
  · intro h θ
    rw [action_gauge_shift]
    simp [h]

end QLF.LinkAction
