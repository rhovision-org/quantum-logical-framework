import QLF_DiracWalk

set_option linter.unusedVariables false

/-!
# QLF_BoostCovariance — the Dirac walk's mass shell is boost-invariant in the large

[`QLF_RelativityScale`](QLF_RelativityScale.lean) and [`QLF_LorentzSymbol`](QLF_LorentzSymbol.lean)
left two obligations open: boost covariance (the unsigned census is only Euclidean-isotropic), and a
*derived* propagation law (reading the census symbol's zeros as a dispersion relation is an
assumption). This module discharges both for one dynamics the repo already has: the unitary Dirac
walk of [`QLF_DiracWalk`](QLF_DiracWalk.lean).

**The propagation law is derived there, not assumed.** The walk is unitary
(`diracWalk_unitary`), so its eigenvalues are phases `e^{iE}`, and `diracWalk_dispersion` proves
every one of them satisfies the exact mass shell

    cos E = cos m · cos k_y · cos k_x · cos k_z.

Here that shell is compared with the Lorentz-invariant one. No axioms.

* **`shell_taylor`** — with `S = E² + a² + b² + c² + m²`, each variable of size at most `1`,

      | cos m · cos a · cos b · cos c − cos E − (E² − a² − b² − c² − m²)/2 | ≤ S²/4.

  The shell function is the Minkowski form `E² − |k|² − m²` (order `S`) plus a remainder of order
  `S²`. So the walk's shell *is* `E² = |k|² + m²` up to a relative correction of order `S`, which
  is `(L_P/λ)²`: the energy–momentum relation of special relativity, with the lattice showing only
  at the next order.
* **`onShell_minkowski`** — on the shell, `|E² − a² − b² − c² − m²| ≤ S²/2`.
* **`shell_lorentz_invariant`** — let `(E, a, b, c)` be on the walk's shell and let
  `(E', a', b', c')` be any energy–momentum with the same Minkowski form,
  `E'² − a'² − b'² − c'² = E² − a² − b² − c²`. Then the transformed point satisfies the walk's
  shell equation up to `S²/4 + S'²/4`. This covers every Lorentz transformation at once (boosts
  in any direction and rotations), because all of them preserve the form.
* **`boost_form`** — the boost along `x` with `γ² − u² = 1` (`u = γv`) preserves the form, so
  **`shell_boost_invariant`**: the boosted energy–momentum of an on-shell mode is on-shell up to
  `S²/4 + S'²/4`.
* **`diracWalk_boost_covariant`** — stated on the walk itself: if `e^{iE}` is an eigenvalue at
  momentum `k`, and `e^{iE''}` is an eigenvalue at the boosted momentum `k'`, then the walk's
  actual energy there agrees with the boosted energy `E'`, `|cos E'' − cos E'| ≤ S²/4 + S'²/4`.

## What this is and is not

It is the relativity principle for **free propagation of the Dirac walk in the large**: an observer
boosted by any velocity finds the same energy–momentum law, to relative order `(L_P/λ)²` in *both*
frames (the bound needs `S'` small too, so a boost large enough to bring the mode to the Planck
scale is outside it). It is not exact: at order `S²` the lattice shows, consistently with
`QLF_RelativityScale.step_census_frame_dependent`. It says nothing yet about interactions, and it is
a statement about the Dirac walk, not about the census symbol of `QLF_LorentzSymbol`, whose kinetic
reading stays an assumption.
See [`Relativity_Principle.md`](../Relativity_Principle.md) §5b.
-/

namespace QLF.BoostCovariance

/-- `cos x = 1 − x²/2 + r` with `|r| ≤ (5/96) x⁴`, for `|x| ≤ 1`. -/
theorem cos_quad {x : ℝ} (hx : |x| ≤ 1) : |Real.cos x - (1 - x ^ 2 / 2)| ≤ 5 / 96 * x ^ 4 := by
  have h := Real.cos_bound hx
  have h4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h4] at h
  linarith

/-- One step of the product expansion: if `A ≈ 1 − α` and `B ≈ 1 − β`, then `AB ≈ 1 − α − β`,
    with the errors adding and the cross term `αβ`. -/
theorem prod_step {A B α β eA eB : ℝ} (hA : |A - (1 - α)| ≤ eA) (hB : |B - (1 - β)| ≤ eB)
    (hB1 : |B| ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) :
    |A * B - (1 - (α + β))| ≤ eA + eB + α * β := by
  have e : A * B - (1 - (α + β)) = (A - (1 - α)) * B + (1 - α) * (B - (1 - β)) + α * β := by ring
  rw [e]
  have h1 : |(A - (1 - α)) * B| ≤ eA := by
    rw [abs_mul]
    calc |A - (1 - α)| * |B| ≤ |A - (1 - α)| * 1 :=
          mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
      _ ≤ eA := by linarith
  have h2 : |(1 - α) * (B - (1 - β))| ≤ eB := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - α)]
    calc (1 - α) * |B - (1 - β)| ≤ 1 * |B - (1 - β)| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ eB := by linarith
  have h3 : |α * β| = α * β := abs_of_nonneg (mul_nonneg hα0 hβ0)
  calc |(A - (1 - α)) * B + (1 - α) * (B - (1 - β)) + α * β|
      ≤ |(A - (1 - α)) * B| + |(1 - α) * (B - (1 - β))| + |α * β| := abs_add_three _ _ _
    _ ≤ eA + eB + α * β := by linarith

/-- The sum of squares of an energy–momentum–mass point: its size against the Planck scale. -/
def size (E a b c m : ℝ) : ℝ := E ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 + m ^ 2

/-- The Minkowski form of an energy–momentum. -/
def form (E a b c : ℝ) : ℝ := E ^ 2 - a ^ 2 - b ^ 2 - c ^ 2

/-- The Dirac walk's shell function: zero exactly on the walk's mass shell
    (`DiracWalk.diracWalk_dispersion`). -/
noncomputable def shell (E a b c m : ℝ) : ℝ :=
  Real.cos m * (Real.cos a * Real.cos b * Real.cos c) - Real.cos E

private theorem abs_le_one_of_sq {x s : ℝ} (hx : x ^ 2 ≤ s) (hs : s ≤ 1) : |x| ≤ 1 := by
  rw [abs_le_one_iff_mul_self_le_one]
  nlinarith

/-- **The walk's shell is the Minkowski shell plus a higher-order remainder.** -/
theorem shell_taylor (E a b c m : ℝ) (h : size E a b c m ≤ 1) :
    |shell E a b c m - (form E a b c - m ^ 2) / 2| ≤ size E a b c m ^ 2 / 4 := by
  unfold size at h
  have hE : |E| ≤ 1 := abs_le_one_of_sq (by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg m]) h
  have ha : |a| ≤ 1 := abs_le_one_of_sq (by nlinarith [sq_nonneg E, sq_nonneg b, sq_nonneg c, sq_nonneg m]) h
  have hb : |b| ≤ 1 := abs_le_one_of_sq (by nlinarith [sq_nonneg E, sq_nonneg a, sq_nonneg c, sq_nonneg m]) h
  have hc : |c| ≤ 1 := abs_le_one_of_sq (by nlinarith [sq_nonneg E, sq_nonneg a, sq_nonneg b, sq_nonneg m]) h
  have hm : |m| ≤ 1 := abs_le_one_of_sq (by nlinarith [sq_nonneg E, sq_nonneg a, sq_nonneg b, sq_nonneg c]) h
  have qE := cos_quad hE
  have qa := cos_quad ha
  have qb := cos_quad hb
  have qc := cos_quad hc
  have qm := cos_quad hm
  have a0 := sq_nonneg a
  have b0 := sq_nonneg b
  have c0 := sq_nonneg c
  have m0 := sq_nonneg m
  have E0 := sq_nonneg E
  -- cos a · cos b
  have s1 := prod_step qa qb (Real.abs_cos_le_one b) (by positivity) (by nlinarith) (by positivity)
  -- (cos a cos b) · cos c
  have s2 := prod_step s1 qc (Real.abs_cos_le_one c) (by positivity) (by nlinarith) (by positivity)
  -- cos m · (cos a cos b cos c)
  have hP1 : |Real.cos a * Real.cos b * Real.cos c| ≤ 1 := by
    rw [abs_mul, abs_mul]
    have := Real.abs_cos_le_one a
    have := Real.abs_cos_le_one b
    have := Real.abs_cos_le_one c
    have h1 : |Real.cos a| * |Real.cos b| ≤ 1 := by
      nlinarith [abs_nonneg (Real.cos a), abs_nonneg (Real.cos b)]
    nlinarith [abs_nonneg (Real.cos a), abs_nonneg (Real.cos b), abs_nonneg (Real.cos c),
      mul_nonneg (abs_nonneg (Real.cos a)) (abs_nonneg (Real.cos b))]
  have s3 := prod_step qm s2 hP1 (by positivity) (by nlinarith) (by positivity)
  -- assemble
  have e : shell E a b c m - (form E a b c - m ^ 2) / 2 =
      (Real.cos m * (Real.cos a * Real.cos b * Real.cos c) -
        (1 - (m ^ 2 / 2 + (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2)))) -
      (Real.cos E - (1 - E ^ 2 / 2)) := by
    unfold shell form; ring
  rw [e]
  have habs := abs_sub (Real.cos m * (Real.cos a * Real.cos b * Real.cos c) -
        (1 - (m ^ 2 / 2 + (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2)))) (Real.cos E - (1 - E ^ 2 / 2))
  have p1 := mul_nonneg a0 b0
  have p2 := mul_nonneg a0 c0
  have p3 := mul_nonneg a0 m0
  have p4 := mul_nonneg b0 c0
  have p5 := mul_nonneg b0 m0
  have p6 := mul_nonneg c0 m0
  have p7 := mul_nonneg E0 a0
  have p8 := mul_nonneg E0 b0
  have p9 := mul_nonneg E0 c0
  have p10 := mul_nonneg E0 m0
  have t4 : ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
  rw [t4 E] at qE
  rw [t4 a, t4 b, t4 c, t4 m] at s3
  unfold size
  nlinarith [sq_nonneg (E ^ 2), sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (c ^ 2),
    sq_nonneg (m ^ 2)]

/-- **On the walk's shell the Minkowski relation holds to the next order**:
    `|E² − |k|² − m²| ≤ S²/2`. -/
theorem onShell_minkowski {E a b c m : ℝ} (h : size E a b c m ≤ 1) (hs : shell E a b c m = 0) :
    |form E a b c - m ^ 2| ≤ size E a b c m ^ 2 / 2 := by
  have ht := shell_taylor E a b c m h
  rw [hs, zero_sub, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  linarith [(div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp ht]

/-- **The walk's mass shell is Lorentz-invariant in the large.** If `(E, a, b, c)` is on the walk's
    shell and `(E', a', b', c')` has the same Minkowski form, then the transformed point satisfies
    the walk's shell equation up to `S²/4 + S'²/4`. -/
theorem shell_lorentz_invariant {E a b c E' a' b' c' m : ℝ}
    (h : size E a b c m ≤ 1) (h' : size E' a' b' c' m ≤ 1)
    (hform : form E' a' b' c' = form E a b c) (hs : shell E a b c m = 0) :
    |shell E' a' b' c' m| ≤ size E a b c m ^ 2 / 4 + size E' a' b' c' m ^ 2 / 4 := by
  have h1 := onShell_minkowski h hs
  have h2 := shell_taylor E' a' b' c' m h'
  rw [hform] at h2
  have e : shell E' a' b' c' m =
      (shell E' a' b' c' m - (form E a b c - m ^ 2) / 2) + (form E a b c - m ^ 2) / 2 := by ring
  rw [e]
  have h3 : |(form E a b c - m ^ 2) / 2| ≤ size E a b c m ^ 2 / 4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [(div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith : |form E a b c - m ^ 2| ≤ size E a b c m ^ 2 / 4 * 2)]
  calc |(shell E' a' b' c' m - (form E a b c - m ^ 2) / 2) + (form E a b c - m ^ 2) / 2|
      ≤ |shell E' a' b' c' m - (form E a b c - m ^ 2) / 2| + |(form E a b c - m ^ 2) / 2| :=
        abs_add_le _ _
    _ ≤ size E a b c m ^ 2 / 4 + size E' a' b' c' m ^ 2 / 4 := by linarith

/-- The boost along `x` with `γ² − u² = 1` (`u = γ v`) preserves the Minkowski form. -/
theorem boost_form (γ u E a b c : ℝ) (hγ : γ ^ 2 - u ^ 2 = 1) :
    form (γ * E + u * a) (u * E + γ * a) b c = form E a b c := by
  unfold form
  linear_combination (E ^ 2 - a ^ 2) * hγ

/-- **Boost invariance of the walk's mass shell in the large.** -/
theorem shell_boost_invariant {γ u E a b c m : ℝ} (hγ : γ ^ 2 - u ^ 2 = 1)
    (h : size E a b c m ≤ 1) (h' : size (γ * E + u * a) (u * E + γ * a) b c m ≤ 1)
    (hs : shell E a b c m = 0) :
    |shell (γ * E + u * a) (u * E + γ * a) b c m| ≤
      size E a b c m ^ 2 / 4 + size (γ * E + u * a) (u * E + γ * a) b c m ^ 2 / 4 :=
  shell_lorentz_invariant h h' (boost_form γ u E a b c hγ) hs

/-- **The Dirac walk's energies are boost-covariant in the large.** Let `e^{iE}` be an eigenvalue
    of the walk at momentum `(k_y, k_x, k_z)`. Boost along `x`: `E' = γE + u k_x`,
    `k_x' = uE + γ k_x`. If `e^{iE''}` is an eigenvalue of the walk at the boosted momentum, then
    the walk's actual energy there agrees with the boosted energy:
    `|cos E'' − cos E'| ≤ S²/4 + S'²/4`. -/
theorem diracWalk_boost_covariant {γ u ky kx kz m E E'' : ℝ} (hγ : γ ^ 2 - u ^ 2 = 1)
    (v v' : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hE : Matrix.mulVec (DiracWalk.diracWalk ky kx kz m) v = Complex.exp (E * Complex.I) • v)
    (hE'' : Matrix.mulVec (DiracWalk.diracWalk ky (u * E + γ * kx) kz m) v' =
      Complex.exp (E'' * Complex.I) • v')
    (h : size E kx ky kz m ≤ 1) (h' : size (γ * E + u * kx) (u * E + γ * kx) ky kz m ≤ 1) :
    |Real.cos E'' - Real.cos (γ * E + u * kx)| ≤
      size E kx ky kz m ^ 2 / 4 + size (γ * E + u * kx) (u * E + γ * kx) ky kz m ^ 2 / 4 := by
  have d := DiracWalk.diracWalk_dispersion ky kx kz m E v hv hE
  have d'' := DiracWalk.diracWalk_dispersion ky (u * E + γ * kx) kz m E'' v' hv' hE''
  have hs : shell E kx ky kz m = 0 := by unfold shell; rw [d]; ring
  have hb := shell_boost_invariant hγ h h' hs
  have e : Real.cos E'' - Real.cos (γ * E + u * kx) =
      shell (γ * E + u * kx) (u * E + γ * kx) ky kz m := by
    unfold shell; rw [d'']; ring
  rw [e]
  exact hb

end QLF.BoostCovariance
