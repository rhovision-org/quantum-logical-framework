import QLF_RelativityScale
import QLF_Minkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# QLF_LorentzSymbol — the phases turn the Euclidean census Lorentzian

[`QLF_RelativityScale`](QLF_RelativityScale.lean) proved that the *unsigned* census (a count of
ways) becomes isotropic across time and space together: Euclidean `O(4)` symmetry, with
cubic anisotropy `4/(3L+1)`. Euclidean is not Lorentzian, and Euclidean isotropy does not give boost
invariance (`boost_not_euclidean`). This module shows that the census's momentum symbol already
carries Lorentz signature once each history keeps its Pauli fold, the amplitude QLF assigns it. No
Wick rotation is needed, and no axioms are used. What the symbol does *not* yet give is a derived
propagation law (next section).

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
  `sin²k₀ = Σ sin²k_a`.

**What is not derived: that these zeros are the propagating modes.** `census_symbol` gives the
census's powers `H(k)^L`; `symbol_light_cone` says where `H` is singular. Reading the singular set
as a dispersion law assumes a kinetic equation, the Weyl-type `H(k)ψ = 0`. The census alone does not
supply it: the generating resolvent of the powers is `(I − zH)⁻¹`, whose poles are not at
`det H = 0` (at `k = 0`, `H = 0` and the resolvent is `I`). Every statement below about light,
dispersion or black holes is conditional on that kinetic reading, which is labelled as an
assumption. A second QLF propagation law, the palindromic Weyl walk of
[`QM_Postulates_QLF.md`](../QM_Postulates_QLF.md) §5b, gives the opposite off-axis sign, so which
law light follows is open.

## Lorentz covariance in the large, and where it fails

`QLF_LorentzCover` proves `X ↦ A X A†` (`A ∈ SL(2,ℂ)`) acts as the Lorentz group on `Form`s and
preserves the interval. With `sin k ≈ k` the symbol is `2i · Form(k)`, so the symbol is
covariant (the Weyl operator `σ^μ k_μ`). **`symbol_deviation`**: each component differs from the
covariant `k_μ` by at most `|k|³/6 + |k|⁵/100` (`|k| ≤ 1`), a relative correction quadratic in
`k`, the same `(L_P/r)²` suppression as the unsigned census. At `|k| ~ 1` (the Planck scale) the
lattice symbol is not covariant. The 16 zeros of `sin` per period are the lattice doublers.

## Loop leakage, reduced to one number

**`quadratic_form_frame_invariant`** — a quadratic form on momentum space invariant under the
substrate's frame group (axis reflections and spatial transpositions) is `diag(a, b, b, b)`. The
only quadratic Lorentz violation the symmetry permits is the ratio `b/a`, the speed of light, which
the free census fixes at `1` (equal temporal and spatial spread). Whether interactions renormalize
it (Collins et al. 2004) is that single number. §5 settles it for interactions by shared Hermitian
pairs: **`marginal_uniform`** / **`marginal_normalized`**, a coupling equal on all eight twists
leaves each strand's normalized spread unchanged at every order, for every coupling with
`8 + g ≠ 0` (for real `g > −8`, as a genuine probability distribution); **`marginal_proportional_iff`**, an axis-dependent coupling shifts `c` unless gauge and
spatial couplings agree; **`shared_pair_fold_axis_blind`**, every shared pair folds to the same `−I`.
Strands created or destroyed are not covered.

## The lattice light cone (under the kinetic reading)

**`axis_light_exact`** — along a lattice axis the singular set is exact, `ω = κ`.
**`diagonal_light_superluminal`** — along a diagonal `(κ, κ, 0)`, `ω > √2 κ = |k|`: if the singular
set is the dispersion law, light outruns `c` at order `(κ L_P)²`. Black-hole consequences: [`lattice_hawking.py`](../lattice_hawking.py).

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

namespace QLF.LorentzSymbol

-- ==========================================
-- §4  The lattice light cone: exact on the axes, faster off them
-- ==========================================

/-- **Light is exact along a lattice axis.** On the lattice light cone `sin²ω = sin²κ` (momentum
    `(κ, 0, 0)`), with `ω, κ ∈ [0, π/2]`, the frequency equals the wavenumber: `ω = κ`. -/
theorem axis_light_exact {ω κ : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ Real.pi / 2) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ Real.pi / 2) (h : Real.sin ω ^ 2 = Real.sin κ ^ 2) : ω = κ := by
  have hsω : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω0 (by linarith [Real.pi_pos])
  have hsκ : 0 ≤ Real.sin κ := Real.sin_nonneg_of_nonneg_of_le_pi hκ0 (by linarith [Real.pi_pos])
  have hs : Real.sin ω = Real.sin κ := by
    have := (sq_eq_sq₀ hsω hsκ).mp h
    exact this
  exact Real.injOn_sin ⟨by linarith [Real.pi_pos], hω1⟩ ⟨by linarith [Real.pi_pos], hκ1⟩ hs

/-- The gap behind diagonal superluminality: `sin(√2 κ) < √2 sin κ` for `0 < κ ≤ 1/2`. -/
theorem diagonal_sin_gap {κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2) :
    Real.sin (Real.sqrt 2 * κ) < Real.sqrt 2 * Real.sin κ := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hs1 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hx : |Real.sqrt 2 * κ| ≤ 1 := by
    rw [abs_of_pos (by positivity)]; nlinarith
  have hk : |κ| ≤ 1 := by rw [abs_of_pos h0]; linarith
  have b1 := Real.sin_bound hk
  have b2 := Real.sin_bound hx
  have hxa : |Real.sqrt 2 * κ| = Real.sqrt 2 * κ := abs_of_pos (mul_pos hs0 h0)
  have hka : |κ| = κ := abs_of_pos h0
  rw [hka] at b1
  rw [hxa] at b2
  have e3 : (Real.sqrt 2 * κ) ^ 3 = 2 * Real.sqrt 2 * κ ^ 3 := by
    rw [mul_pow, show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hs2]
  have e5 : (Real.sqrt 2 * κ) ^ 5 = 4 * Real.sqrt 2 * κ ^ 5 := by
    rw [mul_pow, show Real.sqrt 2 ^ 5 = (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 by ring, hs2]; ring
  rw [e3, e5] at b2
  have l1 := (abs_le.mp b1).1
  have u2 := (abs_le.mp b2).2
  have hκ2 : κ ^ 2 ≤ 1 / 4 := by nlinarith
  have key : 0 < Real.sqrt 2 * κ ^ 3 * (1 / 6 - κ ^ 2 / 20) := by
    have : 0 < 1 / 6 - κ ^ 2 / 20 := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left l1 hs0.le]

/-- **Light outruns `c` along a lattice diagonal.** On the lattice light cone with momentum
    `(κ, κ, 0)` (magnitude `|k| = √2 κ`), `sin²ω = 2 sin²κ` forces `ω > |k|`: the phase velocity
    exceeds `c`, by a relative amount of order `(κ L_P)²`. With `axis_light_exact`, the census's
    light cone is direction-dependent at the Planck scale. -/
theorem diagonal_light_superluminal {ω κ : ℝ} (h0 : 0 < κ) (h1 : κ ≤ 1 / 2) (hω0 : 0 ≤ ω)
    (hω1 : ω ≤ Real.pi / 2) (h : Real.sin ω ^ 2 = Real.sin κ ^ 2 + Real.sin κ ^ 2) :
    Real.sqrt 2 * κ < ω := by
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hsω : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω0 (by linarith [Real.pi_pos])
  have hsκ : 0 < Real.sin κ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_gt_three])
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsin : Real.sin ω = Real.sqrt 2 * Real.sin κ := by
    have hpos : 0 ≤ Real.sqrt 2 * Real.sin κ := by positivity
    have : Real.sin ω ^ 2 = (Real.sqrt 2 * Real.sin κ) ^ 2 := by rw [mul_pow, hs2, h]; ring
    exact (sq_eq_sq₀ hsω hpos).mp this
  have gap := diagonal_sin_gap h0 h1
  by_contra hle'
  have hle := not_lt.mp hle'
  have hs1 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hk : Real.sqrt 2 * κ ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hk hle
  linarith

end QLF.LorentzSymbol

-- ==========================================
-- §5  Shared-pair interactions cannot change c
-- ==========================================

namespace QLF.LorentzSymbol

open Finset QLF QLF.RelativityScale Complex

/-!
## Two strands that interact by sharing Hermitian pairs

Two histories `A` and `B` run side by side, one twist each per tick. On an ordinary tick they step
independently. On a **shared** tick they close a Hermitian pair between them: `A` takes `t`, `B`
takes `t†`, weighted by a coupling `g t`. A joint history is a word over
`JStep = (Twist × Twist) ⊕ Twist` (free pair, or shared twist), and the joint census, weighted by
plane waves at momenta `k_A`, `k_B`, sums every way of interleaving free and shared ticks, so it is
exact to all orders in `g` (every "loop" of the interaction is in it).

* **`joint_census`** — the joint census is a power of its one-tick symbol.
* **`shared_wave`** — a shared tick carries `e^{i(k_A − k_B)·e_t}`: since `t†` steps opposite to
  `t`, the pair has zero net displacement and sees only the **relative** momentum.
* **`joint_symbol`** — the one-tick symbol is `usym k_A · usym k_B + Σ_t g_t e^{i(k_A−k_B)·e_t}`.
* **`marginal_symbol`** — summing over where `B` ends (`k_B = 0`) leaves `A` with
  `Σ_t (8 + g_t) e^{i k_A·e_t}`.
* **`marginal_uniform`** — if the coupling is the same on all eight twists, `A`'s marginal census
  is `(8 + g)^L` times its free census, an unnormalized identity for any `g : ℂ`.
* **`marginal_normalized`** — when `8 + g ≠ 0`, dividing by the total weight leaves `A`'s
  normalized census equal to the free one, `usym^L / 8^L`: the interaction changes nothing about
  how `A` spreads, to all orders. At `g = −8` the marginal vanishes identically and has no
  normalization. For real `g > −8` the marginal weight on each twist, `8 + g`, is positive, so `A`'s
  marginal is a genuine probability distribution, the free one (for `g ≥ 0` the joint weights are
  positive too). For complex `g` the normalized census is a complex weight, not a probability.
* **`marginal_proportional_iff`** — conversely, with coupling `g₀` on the gauge pair and `g_s` on
  the spatial pairs, `A`'s marginal is proportional to its free census **iff `g₀ = g_s`**. A
  coupling that treats time and space differently does renormalize `c`: this is the substrate form
  of the Collins et al. (2004) leakage.
* **`joint_symbol_swap`** — with a coupling equal on `t` and `t†` (which the fold is), swapping which
  strand takes `t` and which takes `t†` leaves the joint census unchanged: the census cannot tell
  emitter from absorber.
* **`shared_pair_fold_axis_blind`** — and the substrate does not treat them differently: every
  shared pair folds to the same `−I`, gauge or spatial (`hermitian_pair_folds_to_negI`). If a
  shared pair's weight is its fold, the coupling is uniform and `c` is protected.

Scope. This covers interactions by shared Hermitian pairs between strands that persist. It does
not cover strands that are created or destroyed (a variable number of histories), and that a pair's
weight is its fold is the reading the last theorem supports, not a theorem about all couplings.
-/

/-- Summing over words of length `n+1` peels off the first letter, for any finite alphabet. -/
theorem sum_words_succ' {α β : Type} [DecidableEq α] [Fintype α] [AddCommMonoid β]
    (m : ℕ) (g : List α → β) :
    ∑ w ∈ words α (m + 1), g w = ∑ a : α, ∑ w ∈ words α m, g (a :: w) := by
  rw [words, sum_biUnion]
  · apply sum_congr rfl
    intro a _
    rw [sum_image (fun _ _ _ _ h => by simpa using h)]
  · intro a₁ _ a₂ _ hne
    apply Finset.disjoint_left.mpr
    intro h h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨w₁, -, rfl⟩ := h1
    obtain ⟨w₂, -, he⟩ := h2
    exact hne (List.cons.inj he).1.symm

/-- One tick of a two-strand history: a free pair `(a, b)`, or a shared Hermitian pair `t / t†`. -/
abbrev JStep := (Twist × Twist) ⊕ Twist

/-- The plane-wave amplitude of one tick, with coupling `g` on shared ticks. -/
noncomputable def jamp (kA kB : Fin 4 → ℝ) (g : Twist → ℂ) : JStep → ℂ
  | .inl (a, b) => wave kA (step a) * wave kB (step b)
  | .inr t => g t * (wave kA (step t) * wave kB (step t.conj))

/-- **The joint census is a power of its one-tick symbol.** -/
theorem joint_census (kA kB : Fin 4 → ℝ) (g : Twist → ℂ) (L : ℕ) :
    ∑ w ∈ words JStep L, (w.map (jamp kA kB g)).prod = (∑ s : JStep, jamp kA kB g s) ^ L := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
      rw [sum_words_succ', pow_succ', ← ih, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp

/-- The conjugate twist steps the opposite way. -/
theorem step_conj (t : Twist) (i : Fin 4) : step t.conj i = -step t i := by
  cases t <;> fin_cases i <;> rfl

/-- **A shared pair sees only the relative momentum.** -/
theorem shared_wave (kA kB : Fin 4 → ℝ) (t : Twist) :
    wave kA (step t) * wave kB (step t.conj) = wave (kA - kB) (step t) := by
  simp only [wave, kdot, step_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Pi.sub_apply, Fin.sum_univ_four]
  push_cast
  ring

/-- **The one-tick joint symbol**: free product plus a relative-momentum shared term. -/
theorem joint_symbol (kA kB : Fin 4 → ℝ) (g : Twist → ℂ) :
    ∑ s : JStep, jamp kA kB g s =
      usym kA * usym kB + ∑ t : Twist, g t * wave (kA - kB) (step t) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, usym, usym, Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [jamp, shared_wave]

theorem wave_zero (v : Fin 4 → ℤ) : wave 0 v = 1 := by
  simp [wave, kdot]

theorem usym_zero : usym 0 = 8 := by
  simp [usym, wave_zero]
  rfl

/-- **`B` summed out**: `A` sees `Σ_t (8 + g_t) e^{i k_A·e_t}`. -/
theorem marginal_symbol (kA : Fin 4 → ℝ) (g : Twist → ℂ) :
    ∑ s : JStep, jamp kA 0 g s = ∑ t : Twist, (8 + g t) * wave kA (step t) := by
  rw [joint_symbol, usym_zero, sub_zero, usym, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **A uniform shared-pair coupling cannot change `A`'s spread.** At every length and every
    coupling, `A`'s marginal census is `(8 + g)^L` times its free census `usym^L`. -/
theorem marginal_uniform (kA : Fin 4 → ℝ) (g : ℂ) (L : ℕ) :
    ∑ w ∈ words JStep L, (w.map (jamp kA 0 (fun _ => g))).prod = (8 + g) ^ L * usym kA ^ L := by
  rw [joint_census, marginal_symbol, ← Finset.mul_sum, ← usym, mul_pow]

/-- **Normalized, the marginal is the free census.** When `8 + g ≠ 0`, `A`'s marginal census divided
    by the total joint weight is `usym kA ^ L / 8 ^ L`, the free census's characteristic function. -/
theorem marginal_normalized (kA : Fin 4 → ℝ) (g : ℂ) (hg : 8 + g ≠ 0) (L : ℕ) :
    (∑ w ∈ words JStep L, (w.map (jamp kA 0 (fun _ => g))).prod) /
      (∑ w ∈ words JStep L, (w.map (jamp 0 0 (fun _ => g))).prod) = usym kA ^ L / 8 ^ L := by
  rw [marginal_uniform, marginal_uniform, usym_zero]
  exact mul_div_mul_left _ _ (pow_ne_zero L hg)

/-- Coupling `g₀` on the gauge pair, `gs` on the six spatial twists. -/
def axisCoupling (g₀ gs : ℂ) : Twist → ℂ
  | .plus => g₀
  | .minus => g₀
  | _ => gs

/-- **`c` is protected exactly when the coupling is axis-blind.** `A`'s marginal one-tick symbol is
    a constant multiple of its free symbol, for all momenta, iff `g₀ = gs`. -/
theorem marginal_proportional_iff (g₀ gs : ℂ) :
    (∃ c : ℂ, ∀ kA : Fin 4 → ℝ,
      ∑ s : JStep, jamp kA 0 (axisCoupling g₀ gs) s = c * usym kA) ↔ g₀ = gs := by
  constructor
  · rintro ⟨c, hc⟩
    have h0 := hc 0
    have hπ := hc ![Real.pi, 0, 0, 0]
    rw [marginal_symbol, usym_zero] at h0
    rw [marginal_symbol, usym_eq_cos] at hπ
    simp only [sum_twist, axisCoupling, wave_zero] at h0
    simp only [sum_twist, axisCoupling, wave_plus, wave_minus, wave_right, wave_left, wave_up,
      wave_down, wave_slash, wave_backslash] at hπ
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_zero, mul_zero, neg_zero,
      Complex.exp_zero, Real.cos_pi, Real.cos_zero] at hπ
    have he : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
      rw [mul_comm]; exact Complex.exp_pi_mul_I
    have he' : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
      rw [Complex.exp_neg, he]; norm_num
    rw [he, he'] at hπ
    push_cast at hπ
    linear_combination (1 / 6 : ℂ) * h0 - (1 / 3 : ℂ) * hπ
  · rintro rfl
    refine ⟨8 + g₀, fun kA => ?_⟩
    rw [marginal_symbol, usym, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    cases t <;> rfl

theorem conj_conj' (t : Twist) : t.conj.conj = t := by cases t <;> rfl

/-- The wave of the conjugate step is the wave of the step at reversed momentum. -/
theorem wave_conj (k : Fin 4 → ℝ) (t : Twist) : wave k (step t.conj) = wave (-k) (step t) := by
  simp only [wave, kdot, step_conj, Pi.neg_apply, Int.cast_neg, mul_neg, neg_mul]

/-- **The joint census cannot tell emitter from absorber.** If the coupling is the same on a twist
    and its conjugate, swapping the two strands (which one takes `t`, which takes `t†`) leaves the
    one-tick symbol, and so the whole joint census, unchanged. -/
theorem joint_symbol_swap (kA kB : Fin 4 → ℝ) (g : Twist → ℂ) (hg : ∀ t, g t.conj = g t) :
    ∑ s : JStep, jamp kA kB g s = ∑ s : JStep, jamp kB kA g s := by
  rw [joint_symbol, joint_symbol, mul_comm (usym kA)]
  congr 1
  refine Fintype.sum_equiv (Function.Involutive.toPerm _ conj_conj') _ _ (fun t => ?_)
  show _ = g t.conj * wave (kB - kA) (step t.conj)
  rw [hg, wave_conj, neg_sub]

/-- **Every shared pair folds to the same scalar**, gauge or spatial: the substrate's own weight on
    a shared pair does not distinguish time from space. -/
theorem shared_pair_fold_axis_blind (t u : Twist) :
    t.toMatrix * t.conj.toMatrix = u.toMatrix * u.conj.toMatrix := by
  rw [hermitian_pair_folds_to_negI, hermitian_pair_folds_to_negI]

end QLF.LorentzSymbol
