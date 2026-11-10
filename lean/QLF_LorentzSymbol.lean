import QLF_RelativityScale
import QLF_Minkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# QLF_LorentzSymbol — the phases turn the Euclidean census Lorentzian

[`QLF_RelativityScale`](QLF_RelativityScale.lean) proved that the *unsigned* census (a count of
ways) becomes isotropic across time and space together: Euclidean `O(4)` symmetry, with
frame-dependence `4/(3L+1)`. Euclidean is not Lorentzian. This module shows that the census
already carries Lorentz signature once each history keeps its Pauli fold, the amplitude QLF
assigns it. No Wick rotation is needed, and no axioms are used.

## The census in momentum space

Weight each history by a plane wave `exp(i k·x)` at its displacement `x`.

* **`unsigned_symbol`** — counting ways, the census is `(Σ_t e^{i k·e_t})^L`, whose real form is
  `(2 Σ_μ cos k_μ)^L`: every axis enters alike, time included. That is the Euclidean symbol.
* **`characteristic_isotropic`** — rescaled by the diffusive scale `k = q/√L`, the census's
  characteristic function `((1/4) Σ cos(q_μ/√L))^L` tends to `exp(−|q|²/8)`, which depends on `q`
  only through `|q|²`. So the whole distribution, not just its moments, becomes `O(4)`-isotropic in
  the large (the central limit theorem for this walk, proved for its characteristic function).
* **`census_symbol`** — keeping the fold, the matrix-valued census is `H(k)^L` with
  **`symbol_eq_form`**: `H(k) = 2i · Form(sin k₀, sin k₁, sin k₂, sin k₃)`. The twist alphabet maps
  the gauge twists to `±I` and the spatial twists to `±σ`, so the momentum symbol of the census
  **is** the Hermitian `Form` of the lattice momentum: time on the identity, space on the Paulis.
* **`symbol_det`** — `det H(k) = −4 (sin²k₀ − sin²k₁ − sin²k₂ − sin²k₃)`: the determinant of the
  census symbol is the Minkowski interval of the lattice momentum, by `det_toMatrix_eq_interval`.
* **`symbol_light_cone`** — `H(k)` is singular exactly on the lattice light cone
  `sin²k₀ = Σ sin²k_a`: the census's massless modes propagate at `c = 1`.

## Lorentz covariance in the large, and where it fails

`QLF_LorentzCover` proves `X ↦ A X A†` (`A ∈ SL(2,ℂ)`) acts as the Lorentz group on `Form`s and
preserves the interval. With `sin k ≈ k` the symbol is `2i · Form(k)`, so the census law is
covariant (the Weyl operator `σ^μ k_μ`). **`symbol_deviation`**: each component differs from the
covariant `k_μ` by at most `|k|³/6 + |k|⁵/100` (`|k| ≤ 1`), a relative correction quadratic in
`k`, the same `(L_P/r)²` suppression as the unsigned census. At `|k| ~ 1` (the Planck scale) the
lattice symbol is not covariant. The 16 zeros of `sin` per period are the lattice doublers.

## Loop leakage, reduced to one number

**`quadratic_form_frame_invariant`** — a quadratic form on momentum space invariant under the
substrate's frame group (axis reflections and spatial transpositions) is `diag(a, b, b, b)`. The
only quadratic Lorentz violation the symmetry permits is the ratio `b/a`, the speed of light, which
the census fixes at `1`. Whether interactions renormalize it (Collins et al. 2004) is now a single
number, not an open-ended worry. It is not settled here.

See [`Relativity_Principle.md`](../Relativity_Principle.md).
-/

namespace QLF.LorentzSymbol

open Finset QLF QLF.RelativityScale QLF.Minkowski Complex

/-- The plane-wave phase `k · v` of a lattice displacement. -/
noncomputable def kdot (k : Fin 4 → ℝ) (v : Fin 4 → ℤ) : ℝ := ∑ i, k i * (v i : ℝ)

theorem kdot_add (k : Fin 4 → ℝ) (u v : Fin 4 → ℤ) :
    kdot k (fun i => u i + v i) = kdot k u + kdot k v := by
  simp only [kdot, Int.cast_add, mul_add, Finset.sum_add_distrib]

theorem kdot_cons (k : Fin 4 → ℝ) (t : Twist) (w : List Twist) :
    kdot k (disp (t :: w)) = kdot k (step t) + kdot k (disp w) := by
  rw [← kdot_add]
  congr 1

/-- The plane wave `e^{i k·v}`. -/
noncomputable def wave (k : Fin 4 → ℝ) (v : Fin 4 → ℤ) : ℂ := Complex.exp (Complex.I * (kdot k v))

theorem wave_cons (k : Fin 4 → ℝ) (t : Twist) (w : List Twist) :
    wave k (disp (t :: w)) = wave k (step t) * wave k (disp w) := by
  simp only [wave, kdot_cons, Complex.ofReal_add, mul_add, Complex.exp_add]


section waves
variable (k : Fin 4 → ℝ)
theorem wave_plus : wave k (step .plus) = Complex.exp (Complex.I * (k 0 : ℂ)) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
theorem wave_minus : wave k (step .minus) = Complex.exp (-(Complex.I * (k 0 : ℂ))) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
theorem wave_right : wave k (step .right) = Complex.exp (Complex.I * (k 1 : ℂ)) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
theorem wave_left : wave k (step .left) = Complex.exp (-(Complex.I * (k 1 : ℂ))) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
theorem wave_up : wave k (step .up) = Complex.exp (Complex.I * (k 2 : ℂ)) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
theorem wave_down : wave k (step .down) = Complex.exp (-(Complex.I * (k 2 : ℂ))) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
theorem wave_slash : wave k (step .slash) = Complex.exp (Complex.I * (k 3 : ℂ)) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
theorem wave_backslash : wave k (step .backslash) = Complex.exp (-(Complex.I * (k 3 : ℂ))) := by
  simp [wave, kdot, Fin.sum_univ_four, step]
end waves

-- ==========================================
-- §1  The unsigned census: Euclidean symbol
-- ==========================================

/-- The one-step unsigned symbol `Σ_t e^{i k·e_t}`. -/
noncomputable def usym (k : Fin 4 → ℝ) : ℂ := ∑ t : Twist, wave k (step t)

/-- **The unsigned census is a power of its one-step symbol.** -/
theorem unsigned_symbol (k : Fin 4 → ℝ) (L : ℕ) :
    ∑ w ∈ words Twist L, wave k (disp w) = usym k ^ L := by
  induction L with
  | zero => simp [words, wave, kdot]
  | succ L ih =>
      rw [sum_words_succ, pow_succ', ← ih, usym, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [wave_cons]

theorem wave_step (k : Fin 4 → ℝ) (t : Twist) :
    wave k (step t) = Complex.exp (Complex.I * (kdot k (step t))) := rfl

/-- The real form: `Σ_t e^{i k·e_t} = 2 Σ_μ cos k_μ`. Every axis, time included, enters alike. -/
theorem usym_eq_cos (k : Fin 4 → ℝ) :
    usym k = 2 * (Real.cos (k 0) + Real.cos (k 1) + Real.cos (k 2) + Real.cos (k 3)) := by
  have h : ∀ x : ℝ, Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-(Complex.I * (x : ℂ))) =
      2 * Complex.cos x := by
    intro x
    rw [Complex.cos]
    ring_nf
  rw [usym, sum_twist, wave_plus, wave_minus, wave_right, wave_left, wave_up, wave_down,
    wave_slash, wave_backslash]
  push_cast
  linear_combination h (k 0) + h (k 1) + h (k 2) + h (k 3)

/-- The characteristic function of the census at the diffusive scale `k = q/√L`. -/
noncomputable def charFn (q : Fin 4 → ℝ) (L : ℕ) : ℝ :=
  ((Real.cos (q 0 / Real.sqrt L) + Real.cos (q 1 / Real.sqrt L) + Real.cos (q 2 / Real.sqrt L) +
    Real.cos (q 3 / Real.sqrt L)) / 4) ^ L

/-- The census sum at `k = q/√L`, normalised by the `8^L` histories, is `charFn q L`. -/
theorem charFn_eq (q : Fin 4 → ℝ) (L : ℕ) :
    (∑ w ∈ words Twist L, wave (fun i => q i / Real.sqrt L) (disp w)) / 8 ^ L =
      (charFn q L : ℂ) := by
  rw [unsigned_symbol, usym_eq_cos, charFn, ← div_pow]
  push_cast
  congr 1
  ring

/-- One axis of the diffusive limit: `L·(cos(q/√L) − 1) → −q²/2`. -/
theorem axis_limit (q : ℝ) :
    Filter.Tendsto (fun L : ℕ => (L : ℝ) * (Real.cos (q / Real.sqrt L) - 1)) Filter.atTop
      (nhds (-(q ^ 2) / 2)) := by
  -- the error is at most `(5/96) q⁴ / L` once `|q/√L| ≤ 1`
  have herr : ∀ᶠ L : ℕ in Filter.atTop,
      |(L : ℝ) * (Real.cos (q / Real.sqrt L) - 1) - (-(q ^ 2) / 2)| ≤ (5 / 96) * q ^ 4 / L := by
    obtain ⟨N, hN⟩ := exists_nat_gt (q ^ 2)
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
    have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
    set x := q / Real.sqrt L with hx
    have hx2 : x ^ 2 = q ^ 2 / L := by rw [hx, div_pow, hsq]
    have hxle : |x| ≤ 1 := by
      have hNL : (N : ℝ) + 1 ≤ L := by exact_mod_cast hL
      have : x ^ 2 ≤ 1 := by
        rw [hx2, div_le_one hLpos]; linarith
      rw [← sq_le_one_iff_abs_le_one]; exact this
    have hb := Real.cos_bound hxle
    have hx4 : |x| ^ 4 = q ^ 4 / L ^ 2 := by
      rw [show |x| ^ 4 = (x ^ 2) ^ 2 by rw [← sq_abs x]; ring, hx2]; ring
    have key : (L : ℝ) * (Real.cos x - 1) - (-(q ^ 2) / 2) =
        L * (Real.cos x - (1 - x ^ 2 / 2)) := by
      rw [hx2]; field_simp; ring
    rw [key, abs_mul, abs_of_pos hLpos]
    calc (L : ℝ) * |Real.cos x - (1 - x ^ 2 / 2)| ≤ L * (|x| ^ 4 * (5 / 96)) :=
          mul_le_mul_of_nonneg_left hb hLpos.le
      _ = (5 / 96) * q ^ 4 / L := by rw [hx4]; field_simp
  have hbound : Filter.Tendsto (fun L : ℕ => (5 / 96) * q ^ 4 / (L : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun L => norm_nonneg _) ?_ hbound
  filter_upwards [herr] with L hL
  rwa [Real.norm_eq_abs]

/-- **The whole census becomes `O(4)`-isotropic in the large.** At the diffusive scale the
    characteristic function tends to `exp(−|q|²/8)`, a function of `|q|²` alone. -/
theorem characteristic_isotropic (q : Fin 4 → ℝ) :
    Filter.Tendsto (charFn q) Filter.atTop
      (nhds (Real.exp (-(q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) / 8))) := by
  have h := ((((axis_limit (q 0)).add (axis_limit (q 1))).add (axis_limit (q 2))).add
    (axis_limit (q 3))).div_const 4
  have hg : Filter.Tendsto (fun L : ℕ => (L : ℝ) * ((Real.cos (q 0 / Real.sqrt L) +
      Real.cos (q 1 / Real.sqrt L) + Real.cos (q 2 / Real.sqrt L) + Real.cos (q 3 / Real.sqrt L)) /
        4 - 1)) Filter.atTop (nhds (-(q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) / 8)) := by
    convert h using 1
    · funext L; ring
    · ring_nf
  have := Real.tendsto_one_add_pow_exp_of_tendsto hg
  refine this.congr (fun L => ?_)
  rw [charFn]; ring_nf

-- ==========================================
-- §2  The signed census: Lorentzian symbol
-- ==========================================

/-- The one-step matrix symbol `H(k) = Σ_t e^{i k·e_t} · M(t)`. -/
noncomputable def msym (k : Fin 4 → ℝ) : M := ∑ t : Twist, wave k (step t) • t.toMatrix

/-- **The matrix-valued census is a power of its symbol.** Weighting each history by its plane
    wave and keeping its Pauli fold, `Σ_w e^{i k·x(w)} U(w) = H(k)^L`. -/
theorem census_symbol (k : Fin 4 → ℝ) (L : ℕ) :
    ∑ w ∈ words Twist L, wave k (disp w) • twistMatrixFold w = msym k ^ L := by
  induction L with
  | zero => simp [words, wave, kdot, twistMatrixFold]
  | succ L ih =>
      rw [sum_words_succ, pow_succ', ← ih, msym, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      have hf : twistMatrixFold (t :: w) = t.toMatrix * twistMatrixFold w := rfl
      rw [wave_cons, hf, smul_mul_smul_comm, mul_smul]

/-- The lattice momentum as a `Form`: `(sin k₀, sin k₁, sin k₂, sin k₃)`. -/
noncomputable def sinForm (k : Fin 4 → ℝ) : Form :=
  ⟨Real.sin (k 0), Real.sin (k 1), Real.sin (k 2), Real.sin (k 3)⟩

theorem exp_sub_exp (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (-(x : ℂ))) =
      2 * Complex.I * Complex.sin x := by
  rw [Complex.sin]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The census symbol is the `Form` of the lattice momentum.** `H(k) = 2i · Form(sin k)`:
    time on the identity, space on the Pauli matrices. -/
theorem symbol_eq_form (k : Fin 4 → ℝ) :
    msym k = (2 * Complex.I) • (sinForm k).toMatrix := by
  have e0 := exp_sub_exp (k 0)
  have e1 := exp_sub_exp (k 1)
  have e2 := exp_sub_exp (k 2)
  have e3 := exp_sub_exp (k 3)
  simp only [mul_neg] at e0 e1 e2 e3
  rw [msym, sum_twist, wave_plus, wave_minus, wave_right, wave_left, wave_up, wave_down,
    wave_slash, wave_backslash]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j
  · simp [Twist.toMatrix, σx, σy, σz, sinForm, Form.toMatrix, Complex.ofReal_sin]
    linear_combination e0 + e3
  · simp [Twist.toMatrix, σx, σy, σz, sinForm, Form.toMatrix, Complex.ofReal_sin]
    linear_combination e1 - Complex.I * e2
  · simp [Twist.toMatrix, σx, σy, σz, sinForm, Form.toMatrix, Complex.ofReal_sin]
    linear_combination e1 + Complex.I * e2
  · simp [Twist.toMatrix, σx, σy, σz, sinForm, Form.toMatrix, Complex.ofReal_sin]
    linear_combination e0 - e3

/-- **The determinant of the census symbol is the Minkowski interval of the lattice momentum.** -/
theorem symbol_det (k : Fin 4 → ℝ) :
    (msym k).det = -4 * ((Real.sin (k 0) ^ 2 - Real.sin (k 1) ^ 2 - Real.sin (k 2) ^ 2 -
      Real.sin (k 3) ^ 2 : ℝ) : ℂ) := by
  rw [symbol_eq_form, Matrix.det_smul, det_toMatrix_eq_interval]
  simp only [Fintype.card_fin, Form.interval, sinForm]
  rw [mul_pow, Complex.I_sq]
  ring

/-- **The census's massless modes lie on the lattice light cone.** `H(k)` is singular exactly
    when `sin²k₀ = sin²k₁ + sin²k₂ + sin²k₃`. -/
theorem symbol_light_cone (k : Fin 4 → ℝ) :
    (msym k).det = 0 ↔
      Real.sin (k 0) ^ 2 = Real.sin (k 1) ^ 2 + Real.sin (k 2) ^ 2 + Real.sin (k 3) ^ 2 := by
  rw [symbol_det]
  constructor
  · intro h
    have h' : ((Real.sin (k 0) ^ 2 - Real.sin (k 1) ^ 2 - Real.sin (k 2) ^ 2 -
        Real.sin (k 3) ^ 2 : ℝ) : ℂ) = 0 := by
      have h4 : (-4 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h).resolve_left h4
    have := Complex.ofReal_eq_zero.mp h'
    linarith
  · intro h
    have : (Real.sin (k 0) ^ 2 - Real.sin (k 1) ^ 2 - Real.sin (k 2) ^ 2 -
        Real.sin (k 3) ^ 2 : ℝ) = 0 := by linarith
    rw [this]; simp

/-- **Covariant in the large, broken at the Planck scale.** Each component of the census symbol
    differs from the Lorentz-covariant momentum `k_μ` by at most `|k|³/6 + |k|⁵/100` for
    `|k| ≤ 1`: a relative correction quadratic in `k`. -/
theorem symbol_deviation {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - x| ≤ |x| ^ 3 / 6 + |x| ^ 5 / 100 := by
  have hb := Real.sin_bound hx
  have h3 : |x ^ 3 / 6| = |x| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  calc |Real.sin x - x| = |(Real.sin x - (x - x ^ 3 / 6)) + (-(x ^ 3 / 6))| := by ring_nf
    _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |-(x ^ 3 / 6)| := abs_add_le _ _
    _ ≤ |x| ^ 5 / 100 + |x| ^ 3 / 6 := by rw [abs_neg, h3]; linarith
    _ = |x| ^ 3 / 6 + |x| ^ 5 / 100 := by ring

/-- **Summary.** Counting ways gives the Euclidean symbol `2Σcos k_μ`, isotropic in the large
    (`characteristic_isotropic`). Keeping each history's fold gives `H(k) = 2i·Form(sin k)`
    (`census_symbol`, `symbol_eq_form`), whose determinant is the Minkowski interval
    (`symbol_det`) and whose zeros are the light cone (`symbol_light_cone`): the phases carry the
    Lorentz signature. Covariance holds to `O(k³)` (`symbol_deviation`). -/
theorem lorentz_symbol_summary : True := trivial

end QLF.LorentzSymbol

namespace QLF.LorentzSymbol

-- ==========================================
-- §3  Loop leakage reduced to one number
-- ==========================================

/-- Sign of axis `i` under the reflection of axis `a`. -/
def flip (a i : Fin 4) : ℝ := if i = a then -1 else 1

/-- **The frame group leaves exactly one Lorentz-violating quadratic coefficient.** A quadratic
    form `Q` on momentum space that is invariant under every axis reflection and under the spatial
    axis transpositions `x ↔ y`, `y ↔ z` (generators of the 48 signed spatial permutations, plus
    time reversal) is `diag(a, b, b, b)`. So the only quadratic Lorentz violation the substrate's
    symmetry permits is the ratio `b/a`: the speed of light. The census fixes it at `1`
    (`light_speed_from_spread`, `symbol_eq_form`). Whether interactions renormalize it is the
    loop-leakage question (Collins et al. 2004), reduced here to that single number. -/
theorem quadratic_form_frame_invariant (Q : Fin 4 → Fin 4 → ℝ)
    (hflip : ∀ a i j, Q i j = flip a i * flip a j * Q i j)
    (hxy : ∀ i j, Q (Equiv.swap 1 2 i) (Equiv.swap 1 2 j) = Q i j)
    (hyz : ∀ i j, Q (Equiv.swap 2 3 i) (Equiv.swap 2 3 j) = Q i j) :
    ∀ i j, Q i j = if i = j then (if i = 0 then Q 0 0 else Q 1 1) else 0 := by
  have off : ∀ i j, i ≠ j → Q i j = 0 := by
    intro i j hij
    have h := hflip i i j
    simp only [flip, Ne.symm hij, ↓reduceIte] at h
    linarith
  have h22 : Q 2 2 = Q 1 1 := by simpa using hxy 1 1
  have h33 : Q 3 3 = Q 2 2 := by simpa using hyz 2 2
  intro i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [h22, h33]
  · simp only [hij, ↓reduceIte]
    exact off i j hij

end QLF.LorentzSymbol
