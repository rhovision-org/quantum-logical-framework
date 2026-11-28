import Mathlib
import QLF_StationaryAction

set_option linter.unusedVariables false

/-!
# QLF_CensusActionLimit — the continuum rendering of census stationarity

`QLF_StationaryAction` proves a discrete fact: in the one-axis census `W_n(k) = C(2n, k)`, ZFA
balance `k = n` is a stationary, strictly maximal point (`ways_symmetric`, `first_variation_zero`,
`balance_is_mode`, `balance_strict_max`). This module renders that fact in the continuum and proves
the rendering converges, for values **and** for variations.

The normalized census cost is

  `I_n(d) = log W_n(n) − log W_n(n + d)`,

the log-count price of displacing a balanced history by `d` up-steps. Everything rests on one exact
finite identity, `W_n(n+j+1)·(n+j+1) = W_n(n+j)·(n−j)`, which makes each increment
`I_n(j+1) − I_n(j) = log((n+j+1)/(n−j))`, and the two elementary log bounds turn that into an exact
sandwich for every `d ≤ n` (`censusCost_sandwich`):

  `d² / (n + d)  ≤  I_n(d)  ≤  d² / (n − d + 1)`.

No Stirling, no asymptotic series. From the sandwich, with `d = ⌊x √n⌋`:

* `censusCost_gaussian_limit` — `I_n(⌊x√n⌋) → x²` (proof obligation S1 of issue #303);
* `censusCost_variation_limit` — the scaled discrete variation `√n·(I_n(d+1) − I_n(d)) → 2x`, the
  derivative of the limit (`limit_hasDerivAt`). This is proved separately from the value limit,
  because value convergence does not give derivative convergence (#303 K3: `sin(nx)/n`);
* `censusCost_curvature_limit` — the conservative return: the exact second difference at balance,
  scaled, `n·(I_n(1) + I_n(−1) − 2 I_n(0)) → 2`, recovers the continuum curvature from the count.
* `censusCost_eq_zero_iff` — the limit's unique minimizer `x = 0` returns to `d = 0`, which is
  `balance_is_mode`: the reverse map recovers the discrete mode.

**What `ħ` does.** Nothing here takes a limit in `ħ`. A Euclidean reading `S^E = ħ·I` multiplies by
a fixed positive constant (`euclidean_action_limit`); the scaling is `x = d/√n`, the relative scale
of one step against the census width. That is the sense in which the continuum is a rendering with
`S ≫ ħ`, not a vanishing quantum.

**Scope.** This is a stationary continuum functional for a specified finite counting functional
(#303 level S-MATH). It is a Euclidean, large-deviation weight `−log W`, not the Lorentzian action
`S` with its phase `e^{iS/ħ}`; that identification (S3–S5) is open. It does not make the modal
census the event-selection rule: first closure is priority (`depth_one_not_modal`). No axioms.
-/

open Filter Topology

namespace QLF.CensusActionLimit

open QLF.StationaryAction

/-- **The normalized census cost** of displacing a balanced `2n`-step history by `d` up-steps. -/
noncomputable def censusCost (n d : ℕ) : ℝ :=
  Real.log (ways n n) - Real.log (ways n (n + d))

/-- The same cost for a displacement of `d` down-steps. -/
noncomputable def censusCostLeft (n d : ℕ) : ℝ :=
  Real.log (ways n n) - Real.log (ways n (n - d))

lemma ways_pos (n k : ℕ) (hk : k ≤ 2 * n) : 0 < (ways n k : ℝ) := by
  unfold ways
  exact_mod_cast Nat.choose_pos hk

/-- Balance costs nothing. -/
theorem censusCost_zero (n : ℕ) : censusCost n 0 = 0 := by
  simp [censusCost]

/-- **Conjugate symmetry:** displacing up or down by `d` costs the same, `I_n(d) = I_n(−d)`. -/
theorem censusCost_symmetric (n d : ℕ) (hd : d ≤ n) : censusCostLeft n d = censusCost n d := by
  unfold censusCostLeft censusCost
  rw [ways_symmetric n d hd]

/-- **The cost is non-negative** — `balance_is_mode` read through `log`. -/
theorem censusCost_nonneg (n d : ℕ) (hd : d ≤ n) : 0 ≤ censusCost n d := by
  unfold censusCost
  have h := Real.log_le_log (ways_pos n (n + d) (by omega))
    (Nat.cast_le.mpr (balance_is_mode n (n + d)))
  linarith

/-- The exact finite identity behind everything: one more up-step multiplies the count by
    `(n − j)/(n + j + 1)`. -/
lemma ways_step (n j : ℕ) (hj : j < n) :
    ways n (n + j + 1) * (n + j + 1) = ways n (n + j) * (n - j) := by
  unfold ways
  have h := Nat.choose_succ_right_eq (2 * n) (n + j)
  rw [show 2 * n - (n + j) = n - j by omega] at h
  exact h

/-- **The increment of the cost** is a single logarithm. -/
theorem censusCost_succ (n j : ℕ) (hj : j < n) :
    censusCost n (j + 1) = censusCost n j + Real.log (((n : ℝ) + j + 1) / ((n : ℝ) - j)) := by
  have hA := ways_pos n (n + j) (by omega)
  have hB := ways_pos n (n + j + 1) (by omega)
  have hnj : (0 : ℝ) < (n : ℝ) - j := by
    have : (j : ℝ) < n := by exact_mod_cast hj
    linarith
  have hnj1 : (0 : ℝ) < (n : ℝ) + j + 1 := by positivity
  have h := congrArg (fun m : ℕ => (m : ℝ)) (ways_step n j hj)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj.le] at h
  have hl := congrArg Real.log h
  rw [Real.log_mul hB.ne' hnj1.ne', Real.log_mul hA.ne' hnj.ne'] at hl
  unfold censusCost
  rw [show n + (j + 1) = n + j + 1 by ring, Real.log_div hnj1.ne' hnj.ne']
  linarith

lemma step_lower (n j : ℕ) (hj : j < n) :
    (2 * (j : ℝ) + 1) / ((n : ℝ) + j + 1) ≤ Real.log (((n : ℝ) + j + 1) / ((n : ℝ) - j)) := by
  have hnj : (0 : ℝ) < (n : ℝ) - j := by
    have : (j : ℝ) < n := by exact_mod_cast hj
    linarith
  have hnj1 : (0 : ℝ) < (n : ℝ) + j + 1 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hnj1 hnj)
  have e : 1 - (((n : ℝ) + j + 1) / ((n : ℝ) - j))⁻¹ = (2 * (j : ℝ) + 1) / ((n : ℝ) + j + 1) := by
    rw [inv_div, eq_div_iff hnj1.ne', sub_mul, one_mul, div_mul_cancel₀ _ hnj1.ne']
    ring
  rw [e] at h
  exact h

lemma step_upper (n j : ℕ) (hj : j < n) :
    Real.log (((n : ℝ) + j + 1) / ((n : ℝ) - j)) ≤ (2 * (j : ℝ) + 1) / ((n : ℝ) - j) := by
  have hnj : (0 : ℝ) < (n : ℝ) - j := by
    have : (j : ℝ) < n := by exact_mod_cast hj
    linarith
  have hnj1 : (0 : ℝ) < (n : ℝ) + j + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hnj1 hnj)
  have e : ((n : ℝ) + j + 1) / ((n : ℝ) - j) - 1 = (2 * (j : ℝ) + 1) / ((n : ℝ) - j) := by
    rw [eq_div_iff hnj.ne', sub_mul, one_mul, div_mul_cancel₀ _ hnj.ne']
    ring
  rw [e] at h
  exact h

/-- **The exact sandwich.** For every `d ≤ n`, `d²/(n+d) ≤ I_n(d) ≤ d²/(n−d+1)`. Finite, exact,
    no asymptotics. -/
theorem censusCost_sandwich (n d : ℕ) (hd : d ≤ n) :
    (d : ℝ) ^ 2 / ((n : ℝ) + d) ≤ censusCost n d ∧
      censusCost n d ≤ (d : ℝ) ^ 2 / ((n : ℝ) - d + 1) := by
  induction d with
  | zero => simp [censusCost_zero]
  | succ d ih =>
    have hdn : d < n := by omega
    obtain ⟨lo, hi⟩ := ih (by omega)
    have sl := step_lower n d hdn
    have su := step_upper n d hdn
    rw [censusCost_succ n d hdn]
    have hND : (d : ℝ) < n := by exact_mod_cast hdn
    have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hpos : (0 : ℝ) < (n : ℝ) - d := by linarith
    push_cast
    constructor
    · have h1 : (d : ℝ) ^ 2 / ((n : ℝ) + d + 1) ≤ (d : ℝ) ^ 2 / ((n : ℝ) + d) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
      have e : ((d : ℝ) + 1) ^ 2 / ((n : ℝ) + ((d : ℝ) + 1)) =
          (d : ℝ) ^ 2 / ((n : ℝ) + d + 1) + (2 * (d : ℝ) + 1) / ((n : ℝ) + d + 1) := by
        rw [← add_div, show (n : ℝ) + ((d : ℝ) + 1) = (n : ℝ) + d + 1 by ring]
        congr 1
        ring
      rw [e]
      linarith
    · have h2 : (d : ℝ) ^ 2 / ((n : ℝ) - d + 1) ≤ (d : ℝ) ^ 2 / ((n : ℝ) - d) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hpos (by linarith)
      have e : ((d : ℝ) + 1) ^ 2 / ((n : ℝ) - ((d : ℝ) + 1) + 1) =
          (d : ℝ) ^ 2 / ((n : ℝ) - d) + (2 * (d : ℝ) + 1) / ((n : ℝ) - d) := by
        rw [← add_div, show (n : ℝ) - ((d : ℝ) + 1) + 1 = (n : ℝ) - d by ring]
        congr 1
        ring
      rw [e]
      linarith

/-- Off balance the cost is strictly positive. -/
theorem censusCost_pos (n d : ℕ) (h1 : 1 ≤ d) (hd : d ≤ n) : 0 < censusCost n d := by
  have hD : (0 : ℝ) < d := by exact_mod_cast h1
  have hN : (0 : ℝ) < (n : ℝ) + d := by positivity
  exact lt_of_lt_of_le (div_pos (pow_pos hD 2) hN) (censusCost_sandwich n d hd).1

/-- **The unique minimizer is balance** — the finite side of the return map. -/
theorem censusCost_eq_zero_iff (n d : ℕ) (hd : d ≤ n) : censusCost n d = 0 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hne
    have := censusCost_pos n d (by omega) hd
    linarith
  · rintro rfl
    exact censusCost_zero n

/-! ## The continuum limit, `d = ⌊x √n⌋` -/

private lemma sqrt_tendsto : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

private lemma inv_sqrt_tendsto : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp sqrt_tendsto

/-- The scaled displacement `⌊x√n⌋/√n → x`. -/
private lemma scaled_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n) atTop (𝓝 x) := by
  have hlo : Tendsto (fun n : ℕ => x - (Real.sqrt n)⁻¹) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub inv_sqrt_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hf := Nat.lt_floor_add_one (x * Real.sqrt n)
    rw [le_div_iff₀ hs, sub_mul, inv_mul_cancel₀ hs.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [div_le_iff₀ hs]
    exact Nat.floor_le (mul_nonneg hx hs.le)

/-- On `n ≥ 1`, write `n = t²` and `d = u t`: the four bounds become functions of `u` and `v = 1/t`. -/
private lemma rescale_identities (n : ℕ) (hn : 1 ≤ n) (D : ℝ) :
    let t := Real.sqrt n
    (n : ℝ) = t * t ∧ D / (n : ℝ) = D / t * t⁻¹ := by
  intro t
  have hs : 0 < t := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnt : (n : ℝ) = t * t := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  refine ⟨hnt, ?_⟩
  rw [hnt, ← div_eq_mul_inv, div_div]

private lemma ratio_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => (⌊x * Real.sqrt n⌋₊ : ℝ) / n) atTop (𝓝 0) := by
  have h := (scaled_tendsto x hx).mul inv_sqrt_tendsto
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact ((rescale_identities n hn _).2).symm

/-- Eventually `⌊x√n⌋ < n`, so the sandwich applies. -/
private lemma floor_lt_eventually (x : ℝ) (hx : 0 ≤ x) :
    ∀ᶠ n : ℕ in atTop, ⌊x * Real.sqrt n⌋₊ < n := by
  filter_upwards [(ratio_tendsto x hx).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with n h hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_one hn'] at h
  exact_mod_cast h

private lemma alg_lo (t D : ℝ) (ht : 0 < t) (hD : 0 ≤ D) :
    (D / t) ^ 2 / (1 + D / t * t⁻¹) = D ^ 2 / (t * t + D) := by
  field_simp

private lemma alg_hi (t D : ℝ) (ht : 0 < t) (hD : D < t * t) :
    (D / t) ^ 2 / (1 - D / t * t⁻¹ + t⁻¹ ^ 2) = D ^ 2 / (t * t - D + 1) := by
  have h : 0 < t * t - D + 1 := by linarith
  field_simp

private lemma alg_vlo (t D : ℝ) (ht : 0 < t) (hD : 0 ≤ D) :
    (2 * (D / t) + t⁻¹) / (1 + D / t * t⁻¹ + t⁻¹ ^ 2) = t * ((2 * D + 1) / (t * t + D + 1)) := by
  field_simp

private lemma alg_vhi (t D : ℝ) (ht : 0 < t) (hD : D < t * t) :
    (2 * (D / t) + t⁻¹) / (1 - D / t * t⁻¹) = t * ((2 * D + 1) / (t * t - D)) := by
  have h : 0 < t * t - D := by linarith
  field_simp

/-- **S1: the Gaussian limit.** `I_n(⌊x√n⌋) → x²` for every `x ≥ 0` (the other side by
    `censusCost_symmetric`). -/
theorem censusCost_gaussian_limit (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => censusCost n ⌊x * Real.sqrt n⌋₊) atTop (𝓝 (x ^ 2)) := by
  set u : ℕ → ℝ := fun n => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n with hu
  set v : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with hv
  have hU : Tendsto u atTop (𝓝 x) := scaled_tendsto x hx
  have hV : Tendsto v atTop (𝓝 0) := inv_sqrt_tendsto
  have glim : Tendsto (fun n => u n ^ 2 / (1 + u n * v n)) atTop (𝓝 (x ^ 2)) := by
    have h := (hU.pow 2).div (tendsto_const_nhds.add (hU.mul hV)) (by norm_num : (1 : ℝ) + x * 0 ≠ 0)
    rw [show x ^ 2 / (1 + x * 0) = x ^ 2 by ring] at h
    exact h
  have hlim : Tendsto (fun n => u n ^ 2 / (1 - u n * v n + v n ^ 2)) atTop (𝓝 (x ^ 2)) := by
    have h := (hU.pow 2).div ((tendsto_const_nhds.sub (hU.mul hV)).add (hV.pow 2))
      (by norm_num : (1 : ℝ) - x * 0 + 0 ^ 2 ≠ 0)
    rw [show x ^ 2 / (1 - x * 0 + 0 ^ 2) = x ^ 2 by ring] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' glim hlim ?_ ?_
  · filter_upwards [floor_lt_eventually x hx, eventually_ge_atTop 1] with n hlt hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hnt : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
      (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    have e0 := alg_lo (Real.sqrt n) (⌊x * Real.sqrt n⌋₊ : ℝ) hs (Nat.cast_nonneg _)
    rw [← hnt] at e0
    have e : u n ^ 2 / (1 + u n * v n) =
        ((⌊x * Real.sqrt n⌋₊ : ℕ) : ℝ) ^ 2 / ((n : ℝ) + ⌊x * Real.sqrt n⌋₊) := e0
    rw [e]
    exact (censusCost_sandwich n _ hlt.le).1
  · filter_upwards [floor_lt_eventually x hx, eventually_ge_atTop 1] with n hlt hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hnt : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
      (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    have hlt' : (⌊x * Real.sqrt n⌋₊ : ℝ) < Real.sqrt n * Real.sqrt n := by
      rw [← hnt]; exact_mod_cast hlt
    have e0 := alg_hi (Real.sqrt n) (⌊x * Real.sqrt n⌋₊ : ℝ) hs hlt'
    rw [← hnt] at e0
    have e : u n ^ 2 / (1 - u n * v n + v n ^ 2) =
        ((⌊x * Real.sqrt n⌋₊ : ℕ) : ℝ) ^ 2 / ((n : ℝ) - ⌊x * Real.sqrt n⌋₊ + 1) := e0
    rw [e]
    exact (censusCost_sandwich n _ hlt.le).2

/-- The limit functional `x ↦ x²` has derivative `2x`; at balance it is stationary. -/
theorem limit_hasDerivAt (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

/-- **S2: the variations converge.** The scaled discrete first variation
    `√n·(I_n(d+1) − I_n(d))` at `d = ⌊x√n⌋` tends to `2x`, the derivative of the limit. -/
theorem censusCost_variation_limit (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => Real.sqrt n *
      (censusCost n (⌊x * Real.sqrt n⌋₊ + 1) - censusCost n ⌊x * Real.sqrt n⌋₊))
      atTop (𝓝 (2 * x)) := by
  set u : ℕ → ℝ := fun n => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n with hu
  set v : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with hv
  have hU : Tendsto u atTop (𝓝 x) := scaled_tendsto x hx
  have hV : Tendsto v atTop (𝓝 0) := inv_sqrt_tendsto
  have glim : Tendsto (fun n => (2 * u n + v n) / (1 + u n * v n + v n ^ 2)) atTop
      (𝓝 (2 * x)) := by
    have h := (((tendsto_const_nhds (x := (2 : ℝ))).mul hU).add hV).div
      ((tendsto_const_nhds.add (hU.mul hV)).add (hV.pow 2))
      (by norm_num : (1 : ℝ) + x * 0 + 0 ^ 2 ≠ 0)
    rw [show (2 * x + 0) / (1 + x * 0 + 0 ^ 2) = 2 * x by ring] at h
    exact h
  have hlim : Tendsto (fun n => (2 * u n + v n) / (1 - u n * v n)) atTop (𝓝 (2 * x)) := by
    have h := (((tendsto_const_nhds (x := (2 : ℝ))).mul hU).add hV).div
      (tendsto_const_nhds.sub (hU.mul hV)) (by norm_num : (1 : ℝ) - x * 0 ≠ 0)
    rw [show (2 * x + 0) / (1 - x * 0) = 2 * x by ring] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' glim hlim ?_ ?_
  · filter_upwards [floor_lt_eventually x hx, eventually_ge_atTop 1] with n hlt hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hnt : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
      (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    rw [censusCost_succ n _ hlt, add_sub_cancel_left]
    have hb := mul_le_mul_of_nonneg_left (step_lower n _ hlt) hs.le
    have e0 := alg_vlo (Real.sqrt n) (⌊x * Real.sqrt n⌋₊ : ℝ) hs (Nat.cast_nonneg _)
    rw [← hnt] at e0
    have e : (2 * u n + v n) / (1 + u n * v n + v n ^ 2) = Real.sqrt n *
        ((2 * ((⌊x * Real.sqrt n⌋₊ : ℕ) : ℝ) + 1) / ((n : ℝ) + ⌊x * Real.sqrt n⌋₊ + 1)) := e0
    rw [e]
    exact hb
  · filter_upwards [floor_lt_eventually x hx, eventually_ge_atTop 1] with n hlt hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hnt : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
      (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    rw [censusCost_succ n _ hlt, add_sub_cancel_left]
    have hb := mul_le_mul_of_nonneg_left (step_upper n _ hlt) hs.le
    have hlt' : (⌊x * Real.sqrt n⌋₊ : ℝ) < Real.sqrt n * Real.sqrt n := by
      rw [← hnt]; exact_mod_cast hlt
    have e0 := alg_vhi (Real.sqrt n) (⌊x * Real.sqrt n⌋₊ : ℝ) hs hlt'
    rw [← hnt] at e0
    have e : (2 * u n + v n) / (1 - u n * v n) = Real.sqrt n *
        ((2 * ((⌊x * Real.sqrt n⌋₊ : ℕ) : ℝ) + 1) / ((n : ℝ) - ⌊x * Real.sqrt n⌋₊)) := e0
    rw [e]
    exact hb

/-- **The conservative return: curvature from the count.** The exact second difference of the
    cost at balance, scaled by `n`, tends to `2`, the second derivative of `x²`. -/
theorem censusCost_curvature_limit :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (censusCost n 1 + censusCostLeft n 1 - 2 * censusCost n 0)) atTop (𝓝 2) := by
  have glim : Tendsto (fun n : ℕ => 2 * ((n : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 2) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul 2
  have hc : ∀ n : ℕ, 1 ≤ n → censusCost n 1 = Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
    intro n hn
    have h := censusCost_succ n 0 (by omega)
    rw [censusCost_zero, zero_add] at h
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' glim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [censusCost_symmetric n 1 hn, censusCost_zero, hc n hn]
    have hb := step_lower n 0 (by omega)
    simp only [Nat.cast_zero, mul_zero, zero_add, add_zero, sub_zero] at hb
    have hm := mul_le_mul_of_nonneg_left hb hn'.le
    have e : (n : ℝ) / ((n : ℝ) + 1) = (n : ℝ) * (1 / ((n : ℝ) + 1)) := by ring
    rw [e]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [censusCost_symmetric n 1 hn, censusCost_zero, hc n hn]
    have hb := step_upper n 0 (by omega)
    simp only [Nat.cast_zero, mul_zero, zero_add, add_zero, sub_zero] at hb
    have hm := mul_le_mul_of_nonneg_left hb hn'.le
    have e : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
    linarith

/-- **`ħ` is held fixed.** A Euclidean reading `S^E = ħ·I` converges to `ħ x²` for a constant `ħ`;
    the limit is in the census scale `x = d/√n`, never in `ħ`. -/
theorem euclidean_action_limit (hbar x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => hbar * censusCost n ⌊x * Real.sqrt n⌋₊) atTop (𝓝 (hbar * x ^ 2)) :=
  (censusCost_gaussian_limit x hx).const_mul hbar

/-- **The census action limit, summarized.** Exact sandwich; value limit `x²`; variation limit
    `2x`; curvature return `2`; the unique minimizer is balance. -/
theorem census_action_limit (x : ℝ) (hx : 0 ≤ x) :
    (∀ n d : ℕ, d ≤ n → (d : ℝ) ^ 2 / ((n : ℝ) + d) ≤ censusCost n d ∧
        censusCost n d ≤ (d : ℝ) ^ 2 / ((n : ℝ) - d + 1)) ∧
    Tendsto (fun n : ℕ => censusCost n ⌊x * Real.sqrt n⌋₊) atTop (𝓝 (x ^ 2)) ∧
    Tendsto (fun n : ℕ => Real.sqrt n *
      (censusCost n (⌊x * Real.sqrt n⌋₊ + 1) - censusCost n ⌊x * Real.sqrt n⌋₊))
      atTop (𝓝 (2 * x)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) *
      (censusCost n 1 + censusCostLeft n 1 - 2 * censusCost n 0)) atTop (𝓝 2) ∧
    (∀ n d : ℕ, d ≤ n → (censusCost n d = 0 ↔ d = 0)) :=
  ⟨censusCost_sandwich, censusCost_gaussian_limit x hx, censusCost_variation_limit x hx,
    censusCost_curvature_limit, censusCost_eq_zero_iff⟩

end QLF.CensusActionLimit
