import QLF_KraftMeasure

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# QLF_RelativityScale — the relativity principle holds in the large and fails at the Planck step

Each twist **is** a Minkowski unit vector. `Twist.toMatrix` sends the gauge twists `±` to `±I`, the
time direction of the Hermitian `Form`, and the spatial twists to `±σ_a`, the three space
directions (`QLF_Minkowski`: the trace is time, the Pauli coordinates are space). So a history's net
displacement `disp w : Fin 4 → ℤ` (index `0` = time, `1,2,3` = `x,y,z`) is a point of the integer
lattice `ℤ^{1,3}`, and a closure is a history whose displacement is zero. This module asks whether
the census of histories looks the same to observers in uniform relative motion, and answers in two
parts. No axioms.

## Where it fails: the single step picks a frame

* **`l1_le_length`** — a history of length `L` displaces by at most `L` in the `ℓ¹` norm.
* **`boost`** is a genuine integer Lorentz boost, `γ = 3`, along `(1,1,0)/√2`
  (`boost_preserves_interval`, `boost_unboost`, `unboost_boost`). It carries the rest observer `e_t`
  to `(3,2,2,0)`.
* **`step_census_frame_dependent`** — one step reaches `e_t`; no history shorter than 7 steps
  reaches its boosted image. The same event seen by two inertial observers is reached in different
  numbers of ways. At the level of individual steps the census has a preferred frame, so exact
  invariance under continuous boosts is impossible on the substrate.

## Where it holds: every frame-dependence dies with scale

Sum over all `8^L` histories of length `L`:

* **`covariance_isotropic`** — `4·Σ x_i x_j = δ_ij · L·8^L` exactly, at every `L`. The census
  spreads equally along time and along each space axis and correlates none of them. The ratio of
  temporal to spatial spread is `1`: the invariant speed is one Planck length per Planck tick,
  computed rather than cancelled.
* **`first_moment_zero`, `third_moment_zero`** — every odd moment vanishes, so no correction linear
  in the scale appears: the census is symmetric under each reflection.
* **`fourth_moment_anisotropy`** — the first frame-dependent quantity is the hypercubic fourth-moment
  anisotropy `Σ x_i⁴ − 3 Σ x_i² x_j²`, which an isotropic distribution sets to zero. Here it equals
  `Σ x_i²` exactly, so relative to `Σ x_i⁴` it is
  **`anisotropy_ratio`**: `4 / (3L + 1)` — total (`= 1`) at a single step, and
  **`anisotropy_vanishes`**: below any `ε > 0` at large enough `L`.

The spread grows as `r² = L/4` (Planck units), so the leading violation is `≈ (1/3)(L_P/r)²`:
quadratic in the ratio of the Planck length to the scale, the same `(E/E_P)²` form that passes the
LHAASO GRB 221009A bound. See [`Relativity_Principle.md`](../Relativity_Principle.md).

## What this does not cover

Isotropy across the time and space axes is the Euclidean (`O(4)`) form of the symmetry: counting
ways treats time like space. The Lorentz signature comes from the phases, in
[`QLF_LorentzSymbol`](QLF_LorentzSymbol.lean): keeping each history's Pauli fold, the census's
momentum symbol is `2i·Form(sin k)`, whose determinant is the Minkowski interval.
-/

namespace QLF.RelativityScale

open Finset QLF

-- ==========================================
-- §0  Each twist is a Minkowski unit vector
-- ==========================================

/-- The Minkowski unit vector of each twist (index `0` = time, `1,2,3` = `x,y,z`), read off
    `Twist.toMatrix`: `± ↦ ±I` (time), `>/< ↦ ±σx`, `^/v ↦ ±σy`, `/ \ ↦ ±σz`. -/
def step : Twist → Fin 4 → ℤ
  | .plus => ![1, 0, 0, 0]
  | .minus => ![-1, 0, 0, 0]
  | .right => ![0, 1, 0, 0]
  | .left => ![0, -1, 0, 0]
  | .up => ![0, 0, 1, 0]
  | .down => ![0, 0, -1, 0]
  | .slash => ![0, 0, 0, 1]
  | .backslash => ![0, 0, 0, -1]

/-- A history's net displacement in `ℤ^{1,3}`. -/
def disp (w : List Twist) (i : Fin 4) : ℤ := (w.map (fun t => step t i)).sum

@[simp] theorem disp_nil (i : Fin 4) : disp [] i = 0 := rfl

@[simp] theorem disp_cons (t : Twist) (w : List Twist) (i : Fin 4) :
    disp (t :: w) i = step t i + disp w i := by
  simp [disp]

theorem sum_twist {β : Type} [AddCommMonoid β] (f : Twist → β) :
    ∑ t : Twist, f t = f .up + (f .down + (f .left + (f .right + (f .slash + (f .backslash +
      (f .plus + (f .minus + 0))))))) := rfl

theorem sum_words_succ {β : Type} [AddCommMonoid β] (m : ℕ) (g : List Twist → β) :
    ∑ w ∈ words Twist (m + 1), g w = ∑ t : Twist, ∑ w ∈ words Twist m, g (t :: w) := by
  rw [words, sum_biUnion]
  · apply sum_congr rfl
    intro t _
    rw [sum_image (fun _ _ _ _ h => by simpa using h)]
  · intro t₁ _ t₂ _ hne
    apply Finset.disjoint_left.mpr
    intro h h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨w₁, -, rfl⟩ := h1
    obtain ⟨w₂, -, he⟩ := h2
    exact hne (List.cons.inj he).1.symm

theorem card_words_twist (L : ℕ) : ((words Twist L).card : ℤ) = 8 ^ L := by
  rw [card_words, card_twist]; push_cast; ring

-- ==========================================
-- §1  Where it fails: the single step picks a frame
-- ==========================================

/-- The Minkowski interval `t² − x² − y² − z²` on `ℤ^{1,3}`. -/
def interval (v : Fin 4 → ℤ) : ℤ := v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2

/-- The `ℓ¹` norm: the fewest axis steps that can reach `v`. -/
def l1 (v : Fin 4 → ℤ) : ℤ := |v 0| + |v 1| + |v 2| + |v 3|

theorem l1_step (t : Twist) : l1 (step t) = 1 := by
  cases t <;> simp [l1, step]

/-- **A history of length `L` displaces by at most `L`** in the `ℓ¹` norm. -/
theorem l1_le_length (w : List Twist) : l1 (disp w) ≤ w.length := by
  induction w with
  | nil => simp [l1]
  | cons t w ih =>
      have h1 := l1_step t
      have a0 := abs_add_le (step t 0) (disp w 0)
      have a1 := abs_add_le (step t 1) (disp w 1)
      have a2 := abs_add_le (step t 2) (disp w 2)
      have a3 := abs_add_le (step t 3) (disp w 3)
      simp only [l1] at h1 ih ⊢
      simp only [disp_cons, List.length_cons]
      push_cast
      linarith

/-- An integer Lorentz boost with `γ = 3` along `(1,1,0)/√2`: the symmetric matrix
    `!![3,2,2,0; 2,2,1,0; 2,1,2,0; 0,0,0,1]`. -/
def boost (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![3 * v 0 + 2 * v 1 + 2 * v 2, 2 * v 0 + 2 * v 1 + v 2, 2 * v 0 + v 1 + 2 * v 2, v 3]

/-- The inverse boost (velocity reversed). -/
def unboost (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![3 * v 0 - 2 * v 1 - 2 * v 2, -2 * v 0 + 2 * v 1 + v 2, -2 * v 0 + v 1 + 2 * v 2, v 3]

/-- **The boost is a Lorentz transformation**: it preserves the interval. -/
theorem boost_preserves_interval (v : Fin 4 → ℤ) : interval (boost v) = interval v := by
  simp [interval, boost]; ring

theorem unboost_boost (v : Fin 4 → ℤ) : unboost (boost v) = v := by
  funext i; fin_cases i <;> simp [unboost, boost] <;> ring

theorem boost_unboost (v : Fin 4 → ℤ) : boost (unboost v) = v := by
  funext i; fin_cases i <;> simp [unboost, boost] <;> ring

/-- The rest observer's unit time vector. -/
def eT : Fin 4 → ℤ := ![1, 0, 0, 0]

theorem boost_eT : boost eT = ![3, 2, 2, 0] := by
  funext i; fin_cases i <;> simp [boost, eT]

/-- The boosted observer moves: `γ = 3`, so `|v| = √8/3 ≈ 0.943 c`. -/
theorem boost_eT_timelike : interval (boost eT) = 1 ∧ boost eT 0 = 3 := by
  rw [boost_eT]; simp [interval]

/-- The number of histories of length `L` that displace by exactly `v`. -/
def reach (L : ℕ) (v : Fin 4 → ℤ) : ℕ := ((words Twist L).filter (fun w => disp w = v)).card

/-- A displacement `v` is reached in `L` steps only if `l1 v ≤ L`. -/
theorem reach_eq_zero_of_lt {L : ℕ} {v : Fin 4 → ℤ} (h : (L : ℤ) < l1 v) : reach L v = 0 := by
  rw [reach, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw hdisp
  have hlen := (mem_words L w).mp hw
  have := l1_le_length w
  rw [hdisp, hlen] at this
  linarith

/-- **The step-level census is frame-dependent.** One step reaches the rest observer's tick
    `e_t`; its image under the `γ = 3` boost needs at least 7 steps, so no history of fewer than 7
    steps reaches it. Two inertial observers describing the same event disagree on how many ways
    it is reached. -/
theorem step_census_frame_dependent :
    0 < reach 1 eT ∧ ∀ L < 7, reach L (boost eT) = 0 := by
  constructor
  · rw [reach, Finset.card_pos]
    refine ⟨[Twist.plus], ?_⟩
    rw [Finset.mem_filter, mem_words]
    refine ⟨rfl, ?_⟩
    funext i; fin_cases i <;> simp [step, eT]
  · intro L hL
    apply reach_eq_zero_of_lt
    rw [boost_eT]
    simp [l1]
    omega

-- ==========================================
-- §2  Single-step sums
-- ==========================================

theorem step_sum1 (i : Fin 4) (d : ℤ) : ∑ t : Twist, (step t i + d) = 8 * d := by
  rw [sum_twist]; fin_cases i <;> simp [step] <;> ring

theorem step_sum2 (i : Fin 4) (d : ℤ) : ∑ t : Twist, (step t i + d) ^ 2 = 2 + 8 * d ^ 2 := by
  rw [sum_twist]; fin_cases i <;> simp [step] <;> ring

theorem step_sum3 (i : Fin 4) (d : ℤ) :
    ∑ t : Twist, (step t i + d) ^ 3 = 6 * d + 8 * d ^ 3 := by
  rw [sum_twist]; fin_cases i <;> simp [step] <;> ring

theorem step_sum4 (i : Fin 4) (d : ℤ) :
    ∑ t : Twist, (step t i + d) ^ 4 = 2 + 12 * d ^ 2 + 8 * d ^ 4 := by
  rw [sum_twist]; fin_cases i <;> simp [step] <;> ring

theorem step_sum11 {i j : Fin 4} (hij : i ≠ j) (d e : ℤ) :
    ∑ t : Twist, (step t i + d) * (step t j + e) = 8 * (d * e) := by
  rw [sum_twist]; fin_cases i <;> fin_cases j <;> simp_all [step] <;> ring

theorem step_sum22 {i j : Fin 4} (hij : i ≠ j) (d e : ℤ) :
    ∑ t : Twist, (step t i + d) ^ 2 * (step t j + e) ^ 2 =
      2 * d ^ 2 + 2 * e ^ 2 + 8 * (d ^ 2 * e ^ 2) := by
  rw [sum_twist]; fin_cases i <;> fin_cases j <;> simp_all [step] <;> ring

/-- One step of the moment recursion: sum over the first twist, then over the rest. -/
theorem sum_succ_swap (L : ℕ) (g : List Twist → ℤ) :
    ∑ w ∈ words Twist (L + 1), g w = ∑ w ∈ words Twist L, ∑ t : Twist, g (t :: w) := by
  rw [sum_words_succ, Finset.sum_comm]

-- ==========================================
-- §3  Where it holds: the moments of the census
-- ==========================================

/-- **No linear term.** The first moment vanishes on every axis. -/
theorem first_moment_zero (L : ℕ) (i : Fin 4) : ∑ w ∈ words Twist L, disp w i = 0 := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
      rw [sum_succ_swap]
      simp only [disp_cons, step_sum1, ← Finset.mul_sum, ih, mul_zero]

/-- The second moment on any axis: `4 · Σ x_i² = L · 8^L`. -/
theorem second_moment (L : ℕ) (i : Fin 4) :
    4 * ∑ w ∈ words Twist L, disp w i ^ 2 = L * 8 ^ L := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
      rw [sum_succ_swap]
      simp only [disp_cons, step_sum2, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      rw [card_words_twist]
      push_cast
      have h : 4 * (8 * ∑ w ∈ words Twist L, disp w i ^ 2) = 8 * (L * 8 ^ L) := by
        rw [← ih]; ring
      linear_combination h

/-- **No correlation between axes**: for `i ≠ j`, `Σ x_i x_j = 0`. -/
theorem cross_moment_zero (L : ℕ) {i j : Fin 4} (hij : i ≠ j) :
    ∑ w ∈ words Twist L, disp w i * disp w j = 0 := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
      rw [sum_succ_swap]
      simp only [disp_cons, step_sum11 hij, ← Finset.mul_sum, ih, mul_zero]

/-- **The covariance is isotropic at every scale.** `4 · Σ x_i x_j = δ_ij · L · 8^L`: time and
    every space axis spread equally, and none is correlated with another. -/
theorem covariance_isotropic (L : ℕ) (i j : Fin 4) :
    4 * ∑ w ∈ words Twist L, disp w i * disp w j = if i = j then (L : ℤ) * 8 ^ L else 0 := by
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [← second_moment L i]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    ring
  · simp only [hij, ↓reduceIte]
    rw [cross_moment_zero L hij, mul_zero]

/-- **The invariant speed is one.** The spread along time equals the spread along each space
    axis, so `c² = Σ_tt / Σ_xx = 1` in Planck units. -/
theorem light_speed_from_spread (L : ℕ) (a : Fin 4) :
    ∑ w ∈ words Twist L, disp w 0 ^ 2 = ∑ w ∈ words Twist L, disp w a ^ 2 := by
  have h0 := second_moment L 0
  have ha := second_moment L a
  linarith

/-- **No cubic term.** The third moment vanishes on every axis. -/
theorem third_moment_zero (L : ℕ) (i : Fin 4) : ∑ w ∈ words Twist L, disp w i ^ 3 = 0 := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
      rw [sum_succ_swap]
      simp only [disp_cons, step_sum3, Finset.sum_add_distrib, ← Finset.mul_sum, ih,
        first_moment_zero, mul_zero, add_zero]

/-- The fourth moment on one axis: `16 · Σ x_i⁴ = (3L² + L) · 8^L`. -/
theorem fourth_moment (L : ℕ) (i : Fin 4) :
    16 * ∑ w ∈ words Twist L, disp w i ^ 4 = (3 * (L : ℤ) ^ 2 + L) * 8 ^ L := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
      rw [sum_succ_swap]
      simp only [disp_cons, step_sum4, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      rw [card_words_twist]
      have h2 := second_moment L i
      push_cast
      linear_combination 8 * ih + 48 * h2

/-- The mixed fourth moment: for `i ≠ j`, `16 · Σ x_i² x_j² = (L² − L) · 8^L`. -/
theorem mixed_fourth_moment (L : ℕ) {i j : Fin 4} (hij : i ≠ j) :
    16 * ∑ w ∈ words Twist L, disp w i ^ 2 * disp w j ^ 2 = ((L : ℤ) ^ 2 - L) * 8 ^ L := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
      rw [sum_succ_swap]
      simp only [disp_cons, step_sum22 hij, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hi := second_moment L i
      have hj := second_moment L j
      push_cast
      linear_combination 8 * ih + 8 * hi + 8 * hj

/-- **The anisotropy is exactly the second moment.** An isotropic distribution has
    `Σ x_i⁴ = 3 Σ x_i² x_j²`; the census misses that by exactly `Σ x_i²`. -/
theorem fourth_moment_anisotropy (L : ℕ) {i j : Fin 4} (hij : i ≠ j) :
    ∑ w ∈ words Twist L, disp w i ^ 4 - 3 * ∑ w ∈ words Twist L, disp w i ^ 2 * disp w j ^ 2 =
      ∑ w ∈ words Twist L, disp w i ^ 2 := by
  have h4 := fourth_moment L i
  have h22 := mixed_fourth_moment L hij
  have h2 := second_moment L i
  have h16 : 16 * (∑ w ∈ words Twist L, disp w i ^ 4 -
      3 * ∑ w ∈ words Twist L, disp w i ^ 2 * disp w j ^ 2 -
      ∑ w ∈ words Twist L, disp w i ^ 2) = 0 := by
    linear_combination h4 - 3 * h22 - 4 * h2
  linarith

/-- **The relative anisotropy is `4 / (3L + 1)`.** Total at a single step (`L = 1` gives `1`). -/
theorem anisotropy_ratio (L : ℕ) (hL : 0 < L) {i j : Fin 4} (hij : i ≠ j) :
    ((∑ w ∈ words Twist L, disp w i ^ 4 - 3 * ∑ w ∈ words Twist L, disp w i ^ 2 * disp w j ^ 2 :
      ℤ) : ℚ) / ((∑ w ∈ words Twist L, disp w i ^ 4 : ℤ) : ℚ) = 4 / (3 * L + 1) := by
  rw [fourth_moment_anisotropy L hij]
  have h2 := second_moment L i
  have h4 := fourth_moment L i
  have h2q : ((∑ w ∈ words Twist L, disp w i ^ 2 : ℤ) : ℚ) = (L : ℚ) * 8 ^ L / 4 := by
    have : (4 : ℚ) * ((∑ w ∈ words Twist L, disp w i ^ 2 : ℤ) : ℚ) = (L : ℚ) * 8 ^ L := by
      exact_mod_cast h2
    linarith
  have h4q : ((∑ w ∈ words Twist L, disp w i ^ 4 : ℤ) : ℚ) = (3 * (L : ℚ) ^ 2 + L) * 8 ^ L / 16 := by
    have : (16 : ℚ) * ((∑ w ∈ words Twist L, disp w i ^ 4 : ℤ) : ℚ) = (3 * (L : ℚ) ^ 2 + L) * 8 ^ L := by
      exact_mod_cast h4
    linarith
  rw [h2q, h4q]
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have h8 : (0 : ℚ) < 8 ^ L := by positivity
  field_simp
  norm_num

/-- **The frame-dependence vanishes in the large.** For every `ε > 0` the relative anisotropy is
    below `ε` at every scale beyond some `L₀`. -/
theorem anisotropy_vanishes (ε : ℚ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, (4 : ℚ) / (3 * L + 1) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  refine ⟨N, fun L hL => ?_⟩
  have hLN : (N : ℚ) ≤ L := by exact_mod_cast hL
  have hpos : (0 : ℚ) < 3 * L + 1 := by positivity
  rw [div_lt_iff₀ hpos]
  have : 4 < ε * N := by rwa [div_lt_iff₀ hε, mul_comm] at hN
  nlinarith

/-- **Summary.** The census is frame-dependent at the Planck step
    (`step_census_frame_dependent`) and isotropic in the large: the covariance is exactly
    isotropic at every scale (`covariance_isotropic`), odd moments vanish, and the first
    frame-dependent moment falls as `4 / (3L + 1)` (`anisotropy_ratio`, `anisotropy_vanishes`). -/
theorem relativity_scale_summary : True := trivial

end QLF.RelativityScale
