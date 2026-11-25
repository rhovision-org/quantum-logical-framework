import QLF_InterferenceNoGo
import QLF_LoopClosure
import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# QLF_TimeDoubleSlit — the double slit in time

Companion: [`Double_Slit.md`](../Double_Slit.md) §6.

A spatial double slit lets one history through at two **places**; a time double slit lets it through
at two **instants** `t₁`, `t₂` (a mirror switched on twice, Tirole et al., *Nature Physics* 19, 999
(2023); an atom ionised in two optical half-cycles, Lindner et al., *PRL* 95, 040401 (2005)). The
fringes then appear in **frequency**, not in angle, with period `2π/Δt`.

QLF time is a count of ticks and frequency is phase per tick (`QLF.LoopClosure.phase`), so a time
slit is a set of ways distinguished by *when* along the history they pass, exactly as a space slit
is a set of ways distinguished by *where*. This module proves that the two experiments are one
theorem.

## What is proved

* **The pattern is one function of one phase.** `time_is_twoPath`, `space_is_twoPath`: both
  intensities equal `twoPath a₁ a₂ φ = |a₁ + a₂ e^{iφ}|²`, with `φ = ω·Δt` in time and `φ = k·Δx`
  in space. **`space_time_duality`**: equal phase gives equal intensity. The common factor
  `e^{iωt₁}` drops out (`normSq_expI`), so only the separation matters.
* **It is the Born weight of two disjoint ways** (`twoPath_eq_born`), and the fringe is that
  weight's interference term `I₂` from [`QLF_InterferenceNoGo`](QLF_InterferenceNoGo.lean)
  (`twoPath_fringe_term`, from `born_I₂`).
* **Fringe period** `2π/Δt` in frequency (`time_fringe_period`); with equal amplitudes the pattern
  is `2|a|²(1 + cos ωΔt)` (`twoPath_equal`), **dark** at `ωΔt = π` (`time_dark_fringe`, exactly
  zero) and **bright** at `ωΔt = 2πn` (`time_bright_fringe`, four times one slit). One time slit
  gives a flat spectrum (`single_time_slit_flat`).
* **Which-time information erases the fringes, by exactly the record overlap.** Tag each instant
  with a record vector `r₁`, `r₂` in any complex inner-product space. Identical records reproduce
  the coherent pattern (`marked_coherent`); orthogonal records give `|a₁|² + |a₂|²` at every
  frequency (`marked_orthogonal`); in general the fringe swing is at most
  `2|a₁||a₂|·|⟨r₁,r₂⟩|` (`marked_visibility_bound`).
* **On the substrate clock.** With `N` ticks per cycle and phase per tick `ζ`, `ζ^N = 1`, the
  amplitude at tick `n` depends only on the substrate phase `n mod N` (`tick_amp_phase`), and the
  fringes **redistribute** intensity over the `N` frequencies without creating any: the total is
  `N(|a₁|² + |a₂|²)` whenever `ζ^d ≠ 1` (`tick_conservation`). On the Pauli-scalar clock `ζ = i`
  (`N = 4`) with slits one tick apart the pattern is `4, 2, 0, 2` times `|a|²` (`mu4_pattern`): the
  dark fringe is `i² = −1`, a phase, which no unsigned count can produce
  (`unsigned_no_dark_fringe`).

## Scope

These are theorems of the two-path Born weight with a phase linear in the tick count. They assume
that phase; they do not derive the Born rule, `ℏ`, or a frequency in hertz, and they idealise each
time slit as an instant (Moshinsky's finite-width shutter, *Phys. Rev.* 88, 625 (1952), is not
treated). No axioms.
-/

namespace QLF.TimeDoubleSlit

open Complex
open scoped InnerProductSpace Real

/-! ## §1 One pattern, two readings -/

/-- A unit phase has weight one. -/
theorem normSq_expI (x : ℝ) : normSq (exp ((x : ℂ) * I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- The two-path pattern as a function of the relative phase `φ`. -/
noncomputable def twoPath (a₁ a₂ : ℂ) (φ : ℝ) : ℝ := normSq (a₁ + a₂ * exp ((φ : ℂ) * I))

/-- The amplitude at frequency `ω` behind two time slits at `t₁`, `t₂`. -/
noncomputable def timeAmp (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) : ℂ :=
  a₁ * exp (((ω * t₁ : ℝ) : ℂ) * I) + a₂ * exp (((ω * t₂ : ℝ) : ℂ) * I)

/-- The spectral intensity of the time double slit. -/
noncomputable def timeIntensity (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) : ℝ := normSq (timeAmp a₁ a₂ t₁ t₂ ω)

/-- The intensity at wavenumber `k` behind two space slits at `x₁`, `x₂`. -/
noncomputable def spaceIntensity (a₁ a₂ : ℂ) (x₁ x₂ k : ℝ) : ℝ :=
  normSq (a₁ * exp (((k * x₁ : ℝ) : ℂ) * I) + a₂ * exp (((k * x₂ : ℝ) : ℂ) * I))

private theorem factor_common (a₁ a₂ : ℂ) (u s₁ s₂ : ℝ) :
    a₁ * exp (((u * s₁ : ℝ) : ℂ) * I) + a₂ * exp (((u * s₂ : ℝ) : ℂ) * I) =
      exp (((u * s₁ : ℝ) : ℂ) * I) * (a₁ + a₂ * exp (((u * (s₂ - s₁) : ℝ) : ℂ) * I)) := by
  have he : exp (((u * s₂ : ℝ) : ℂ) * I) =
      exp (((u * s₁ : ℝ) : ℂ) * I) * exp (((u * (s₂ - s₁) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- **The time double slit is the two-path pattern at `φ = ω·Δt`.** -/
theorem time_is_twoPath (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) :
    timeIntensity a₁ a₂ t₁ t₂ ω = twoPath a₁ a₂ (ω * (t₂ - t₁)) := by
  unfold timeIntensity timeAmp twoPath
  rw [factor_common, Complex.normSq_mul, normSq_expI, one_mul]

/-- **The space double slit is the two-path pattern at `φ = k·Δx`.** -/
theorem space_is_twoPath (a₁ a₂ : ℂ) (x₁ x₂ k : ℝ) :
    spaceIntensity a₁ a₂ x₁ x₂ k = twoPath a₁ a₂ (k * (x₂ - x₁)) := by
  unfold spaceIntensity twoPath
  rw [factor_common, Complex.normSq_mul, normSq_expI, one_mul]

/-- **Space–time duality.** A time double slit and a space double slit with the same slit
amplitudes and the same accumulated relative phase give the same intensity. -/
theorem space_time_duality (a₁ a₂ : ℂ) (t₁ t₂ ω x₁ x₂ k : ℝ)
    (h : ω * (t₂ - t₁) = k * (x₂ - x₁)) :
    timeIntensity a₁ a₂ t₁ t₂ ω = spaceIntensity a₁ a₂ x₁ x₂ k := by
  rw [time_is_twoPath, space_is_twoPath, h]

/-! ## §2 The fringe is the Born interference term -/

/-- The two ways: slit one with amplitude `a₁`, slit two with `a₂` carrying the relative phase. -/
noncomputable def ways (a₁ a₂ : ℂ) (φ : ℝ) : Fin 2 → ℂ := ![a₁, a₂ * exp ((φ : ℂ) * I)]

/-- **The pattern is the Born weight of the event "either slit".** -/
theorem twoPath_eq_born (a₁ a₂ : ℂ) (φ : ℝ) :
    twoPath a₁ a₂ φ = QLF.InterferenceNoGo.born (ways a₁ a₂ φ) {0, 1} := by
  unfold twoPath QLF.InterferenceNoGo.born QLF.InterferenceNoGo.readout
    QLF.InterferenceNoGo.tally QLF.InterferenceNoGo.normSqΦ ways
  rw [Finset.sum_pair (by decide)]
  simp

/-- **The fringe is the interference term `I₂`** of the Born weight on the two disjoint slits. -/
theorem twoPath_fringe_term (a₁ a₂ : ℂ) (φ : ℝ) :
    QLF.InterferenceNoGo.I₂ (QLF.InterferenceNoGo.born (ways a₁ a₂ φ)) {0} {1} =
      2 * (a₁ * (starRingEnd ℂ) (a₂ * exp ((φ : ℂ) * I))).re := by
  rw [QLF.InterferenceNoGo.born_I₂ _ (by decide)]
  simp [QLF.InterferenceNoGo.tally, ways]

/-- The pattern: the two single-slit weights plus the fringe term. -/
theorem twoPath_expand (a₁ a₂ : ℂ) (φ : ℝ) :
    twoPath a₁ a₂ φ =
      normSq a₁ + normSq a₂ + 2 * (a₁ * (starRingEnd ℂ) (a₂ * exp ((φ : ℂ) * I))).re := by
  unfold twoPath
  rw [Complex.normSq_add, Complex.normSq_mul, normSq_expI, mul_one]

/-! ## §3 Fringes in frequency -/

/-- The pattern repeats every `2π` of relative phase. -/
theorem twoPath_periodic (a₁ a₂ : ℂ) (φ : ℝ) : twoPath a₁ a₂ (φ + 2 * π) = twoPath a₁ a₂ φ := by
  unfold twoPath
  have h : exp (((φ + 2 * π : ℝ) : ℂ) * I) = exp ((φ : ℂ) * I) := by
    rw [show (((φ + 2 * π : ℝ) : ℂ) * I) = (φ : ℂ) * I + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [h]

/-- **Fringe period in frequency.** Shifting the frequency by `2π/Δt` leaves the spectrum
unchanged: the further apart the time slits, the finer the spectral fringes. -/
theorem time_fringe_period (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) (ht : t₂ ≠ t₁) :
    timeIntensity a₁ a₂ t₁ t₂ (ω + 2 * π / (t₂ - t₁)) = timeIntensity a₁ a₂ t₁ t₂ ω := by
  rw [time_is_twoPath, time_is_twoPath]
  have hd : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr ht
  rw [add_mul, div_mul_cancel₀ _ hd, twoPath_periodic]

/-- **Equal amplitudes:** `2|a|²(1 + cos φ)`. -/
theorem twoPath_equal (a : ℂ) (φ : ℝ) : twoPath a a φ = 2 * normSq a * (1 + Real.cos φ) := by
  rw [twoPath_expand]
  have h : (a * (starRingEnd ℂ) (a * exp ((φ : ℂ) * I))).re = normSq a * Real.cos φ := by
    rw [map_mul, ← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.conj_re,
      Complex.exp_ofReal_mul_I_re]
  rw [h]
  ring

/-- **Dark fringe:** at `ω·Δt = π` the two instants cancel exactly. -/
theorem time_dark_fringe (a : ℂ) (t₁ t₂ ω : ℝ) (h : ω * (t₂ - t₁) = π) :
    timeIntensity a a t₁ t₂ ω = 0 := by
  rw [time_is_twoPath, h, twoPath_equal, Real.cos_pi]
  ring

/-- **Bright fringe:** at `ω·Δt = 2πn` the two instants give four times one slit. -/
theorem time_bright_fringe (a : ℂ) (t₁ t₂ ω : ℝ) (n : ℤ) (h : ω * (t₂ - t₁) = n * (2 * π)) :
    timeIntensity a a t₁ t₂ ω = 4 * normSq a := by
  rw [time_is_twoPath, h, twoPath_equal, Real.cos_int_mul_two_pi]
  ring

/-- **One time slit, no fringe:** the spectrum is flat. -/
theorem single_time_slit_flat (a : ℂ) (t₁ t₂ ω : ℝ) :
    timeIntensity a 0 t₁ t₂ ω = normSq a := by
  rw [time_is_twoPath]
  unfold twoPath
  simp

/-! ## §3a The two uncertainty relations, as fringe reciprocities

A time slit pair of separation `Δt` fixes the fringe spacing in frequency, and a space slit pair of
separation `Δx` fixes it in wavenumber. The spacing is exact, not a bound: a frequency shift `p` is a
symmetry of the spectrum **iff** `p·Δt ∈ 2πℤ` (`time_shift_iff`), so the least positive fringe
spacing is `2π/|Δt|` and every positive spacing obeys `p·|Δt| ≥ 2π` (`time_reciprocity`); the
same holds for `(k, x)` (`space_shift_iff`, `space_reciprocity`). With `E = ℏω` and `p = ℏk` these
are `ΔE·Δt = h` and `Δp·Δx = h` for the fringe spacing: the Fourier reciprocity of the two conjugate
pairs, which is what the uncertainty relations rest on. They are not the variance inequalities
`≥ ℏ/2` (those are `QLF_Uncertainty`'s and the entropic form in `UncertaintyPrinciple.md`). -/

private theorem twoPath_shift_iff (a : ℂ) (ha : a ≠ 0) (c s : ℝ) :
    (∀ u : ℝ, twoPath a a (u * c + s) = twoPath a a (u * c)) ↔
      ∃ n : ℤ, s = n * (2 * π) := by
  have hpos : 0 < normSq a := Complex.normSq_pos.mpr ha
  constructor
  · intro h
    have h0 := h 0
    rw [zero_mul, zero_add, twoPath_equal, twoPath_equal, Real.cos_zero] at h0
    have hc : Real.cos s = 1 := by nlinarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff s).mp hc
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩ u
    rw [twoPath_equal, twoPath_equal, Real.cos_add_int_mul_two_pi]

/-- **Time–frequency: the fringe spacing is exact.** A frequency shift `p` leaves the equal-slit
spectrum unchanged iff `p·Δt` is a whole number of turns. -/
theorem time_shift_iff (a : ℂ) (ha : a ≠ 0) (t₁ t₂ p : ℝ) :
    (∀ ω, timeIntensity a a t₁ t₂ (ω + p) = timeIntensity a a t₁ t₂ ω) ↔
      ∃ n : ℤ, p * (t₂ - t₁) = n * (2 * π) := by
  have key := twoPath_shift_iff a ha (t₂ - t₁) (p * (t₂ - t₁))
  simp only [time_is_twoPath, add_mul]
  exact key

/-- **Position–wavenumber: the same statement for the space slits.** -/
theorem space_shift_iff (a : ℂ) (ha : a ≠ 0) (x₁ x₂ q : ℝ) :
    (∀ k, spaceIntensity a a x₁ x₂ (k + q) = spaceIntensity a a x₁ x₂ k) ↔
      ∃ n : ℤ, q * (x₂ - x₁) = n * (2 * π) := by
  have key := twoPath_shift_iff a ha (x₂ - x₁) (q * (x₂ - x₁))
  simp only [space_is_twoPath, add_mul]
  exact key

private theorem reciprocity_of_shift (s p : ℝ) (hs : s ≠ 0) (hp : 0 < p)
    (h : ∃ n : ℤ, p * s = n * (2 * π)) : 2 * π ≤ p * |s| := by
  obtain ⟨n, hn⟩ := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
    rcases hn with h | h
    · linarith
    · exact hs h
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn0
  have habs : p * |s| = |(n : ℝ)| * (2 * π) := by
    rw [← abs_of_pos hp, ← abs_mul, hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [habs]
  nlinarith [Real.pi_pos]

/-- **The time–energy reciprocity.** The spacing `2π/|Δt|` is a fringe period, and every positive
fringe period `p` obeys `p·|Δt| ≥ 2π`. With `E = ℏω`: `ΔE·Δt = h` for the least spacing. -/
theorem time_reciprocity (a : ℂ) (ha : a ≠ 0) (t₁ t₂ : ℝ) (ht : t₂ ≠ t₁) :
    (∀ ω, timeIntensity a a t₁ t₂ (ω + 2 * π / |t₂ - t₁|) = timeIntensity a a t₁ t₂ ω) ∧
    (∀ p, 0 < p → (∀ ω, timeIntensity a a t₁ t₂ (ω + p) = timeIntensity a a t₁ t₂ ω) →
      2 * π ≤ p * |t₂ - t₁|) := by
  have hd : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr ht
  refine ⟨?_, fun p hp hper => reciprocity_of_shift _ p hd hp ((time_shift_iff a ha t₁ t₂ p).mp hper)⟩
  refine (time_shift_iff a ha t₁ t₂ _).mpr ?_
  rcases abs_choice (t₂ - t₁) with h | h
  · exact ⟨1, by rw [h, div_mul_cancel₀ _ hd]; simp⟩
  · refine ⟨-1, ?_⟩
    rw [h, div_mul_eq_mul_div, mul_comm, ← div_mul_eq_mul_div, div_neg, div_self hd]
    simp

/-- **The position–momentum reciprocity.** The same for the space slits: every positive fringe
spacing `q` in wavenumber obeys `q·|Δx| ≥ 2π`, so `Δp·Δx = h` for the least spacing. -/
theorem space_reciprocity (a : ℂ) (ha : a ≠ 0) (x₁ x₂ : ℝ) (hx : x₂ ≠ x₁) (q : ℝ) (hq : 0 < q)
    (hper : ∀ k, spaceIntensity a a x₁ x₂ (k + q) = spaceIntensity a a x₁ x₂ k) :
    2 * π ≤ q * |x₂ - x₁| :=
  reciprocity_of_shift _ q (sub_ne_zero.mpr hx) hq ((space_shift_iff a ha x₁ x₂ q).mp hper)

/-! ## §4 Which-time records -/

section Records

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The intensity when each instant leaves a record `r₁`, `r₂`: the squared length of the summed
recorded amplitude. -/
noncomputable def markedIntensity (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) (r₁ r₂ : E) : ℝ :=
  ‖(a₁ * exp (((ω * t₁ : ℝ) : ℂ) * I)) • r₁ + (a₂ * exp (((ω * t₂ : ℝ) : ℂ) * I)) • r₂‖ ^ 2

private theorem norm_phase (a : ℂ) (x : ℝ) : ‖a * exp ((x : ℂ) * I)‖ = ‖a‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **No record, full fringes:** identical unit records give the coherent pattern. -/
theorem marked_coherent (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) (r : E) (hr : ‖r‖ = 1) :
    markedIntensity a₁ a₂ t₁ t₂ ω r r = timeIntensity a₁ a₂ t₁ t₂ ω := by
  unfold markedIntensity timeIntensity timeAmp
  rw [← add_smul, norm_smul, hr, mul_one, Complex.normSq_eq_norm_sq]

/-- The recorded intensity: the two single-slit weights plus the fringe term scaled by the record
overlap. -/
theorem marked_expand (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) (r₁ r₂ : E) (h₁ : ‖r₁‖ = 1) (h₂ : ‖r₂‖ = 1) :
    markedIntensity a₁ a₂ t₁ t₂ ω r₁ r₂ =
      normSq a₁ + normSq a₂ +
        2 * ((starRingEnd ℂ) (a₁ * exp (((ω * t₁ : ℝ) : ℂ) * I)) *
          (a₂ * exp (((ω * t₂ : ℝ) : ℂ) * I)) * ⟪r₁, r₂⟫_ℂ).re := by
  unfold markedIntensity
  rw [@norm_add_sq ℂ, norm_smul, norm_smul, inner_smul_left, inner_smul_right, h₁, h₂,
    norm_phase, norm_phase, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  simp only [mul_one, RCLike.re_to_complex]
  ring_nf

/-- **Orthogonal records erase the fringes:** the spectrum is `|a₁|² + |a₂|²` at every
frequency. -/
theorem marked_orthogonal (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) (r₁ r₂ : E) (h₁ : ‖r₁‖ = 1) (h₂ : ‖r₂‖ = 1)
    (h : ⟪r₁, r₂⟫_ℂ = 0) :
    markedIntensity a₁ a₂ t₁ t₂ ω r₁ r₂ = normSq a₁ + normSq a₂ := by
  rw [marked_expand a₁ a₂ t₁ t₂ ω r₁ r₂ h₁ h₂, h]
  simp

/-- **Visibility is bounded by the record overlap.** The fringe swing about `|a₁|² + |a₂|²` is at
most `2|a₁||a₂|·|⟨r₁,r₂⟩|`: the more the records tell the instants apart, the weaker the fringe. -/
theorem marked_visibility_bound (a₁ a₂ : ℂ) (t₁ t₂ ω : ℝ) (r₁ r₂ : E) (h₁ : ‖r₁‖ = 1)
    (h₂ : ‖r₂‖ = 1) :
    |markedIntensity a₁ a₂ t₁ t₂ ω r₁ r₂ - (normSq a₁ + normSq a₂)| ≤
      2 * ‖a₁‖ * ‖a₂‖ * ‖⟪r₁, r₂⟫_ℂ‖ := by
  rw [marked_expand a₁ a₂ t₁ t₂ ω r₁ r₂ h₁ h₂]
  have hre := Complex.abs_re_le_norm
    ((starRingEnd ℂ) (a₁ * exp (((ω * t₁ : ℝ) : ℂ) * I)) *
      (a₂ * exp (((ω * t₂ : ℝ) : ℂ) * I)) * ⟪r₁, r₂⟫_ℂ)
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_phase, norm_phase] at hre
  have hsimp : normSq a₁ + normSq a₂ +
      2 * ((starRingEnd ℂ) (a₁ * exp (((ω * t₁ : ℝ) : ℂ) * I)) *
        (a₂ * exp (((ω * t₂ : ℝ) : ℂ) * I)) * ⟪r₁, r₂⟫_ℂ).re - (normSq a₁ + normSq a₂) =
      2 * ((starRingEnd ℂ) (a₁ * exp (((ω * t₁ : ℝ) : ℂ) * I)) *
        (a₂ * exp (((ω * t₂ : ℝ) : ℂ) * I)) * ⟪r₁, r₂⟫_ℂ).re := by ring
  rw [hsimp, abs_mul, abs_two]
  nlinarith [hre]

end Records

/-! ## §5 On the substrate clock -/

/-- The spectral intensity on an `N`-tick clock: phase per tick `ζ^k` at frequency index `k`,
time slits at ticks `t` and `t + d`. -/
noncomputable def tickIntensity (ζ a₁ a₂ : ℂ) (t d k : ℕ) : ℝ :=
  normSq (a₁ * (ζ ^ k) ^ t + a₂ * (ζ ^ k) ^ (t + d))

/-- **The tick amplitude reads only the substrate phase.** On a clock with `ζ^N = 1`, the phase
factor at tick `n` is fixed by `QLF.LoopClosure.phase n N = n mod N`. -/
theorem tick_amp_phase (ζ : ℂ) (N n : ℕ) (hζ : ζ ^ N = 1) :
    ζ ^ n = ζ ^ QLF.LoopClosure.phase n N := by
  unfold QLF.LoopClosure.phase
  exact pow_eq_pow_mod n hζ

private theorem tick_factor (ζ a₁ a₂ : ℂ) (N t d k : ℕ) (hN : 0 < N) (hζ : ζ ^ N = 1) :
    tickIntensity ζ a₁ a₂ t d k = normSq (a₁ + a₂ * (ζ ^ d) ^ k) := by
  have hn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hζ hN.ne'
  have h1 : normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hn]; norm_num
  unfold tickIntensity
  have he : a₁ * (ζ ^ k) ^ t + a₂ * (ζ ^ k) ^ (t + d) =
      (ζ ^ k) ^ t * (a₁ + a₂ * (ζ ^ d) ^ k) := by
    rw [pow_add, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  rw [he, Complex.normSq_mul, map_pow, map_pow, h1, one_pow, one_pow, one_mul]

/-- **Fringes redistribute, they do not create.** Summed over the `N` frequencies of the clock,
the intensity is `N(|a₁|² + |a₂|²)` whenever the slit separation is not a whole cycle
(`ζ^d ≠ 1`): the fringe term sums to zero. -/
theorem tick_conservation (ζ a₁ a₂ : ℂ) (N t d : ℕ) (hN : 0 < N) (hζ : ζ ^ N = 1)
    (hd : ζ ^ d ≠ 1) :
    ∑ k ∈ Finset.range N, tickIntensity ζ a₁ a₂ t d k = N * (normSq a₁ + normSq a₂) := by
  have hn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hζ hN.ne'
  have h1 : normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hn]; norm_num
  set w := ζ ^ d with hw
  have hwN : w ^ N = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hgeom : ∑ k ∈ Finset.range N, w ^ k = 0 := by
    rw [geom_sum_eq hd, hwN, sub_self, zero_div]
  have hterm : ∀ k, tickIntensity ζ a₁ a₂ t d k =
      normSq a₁ + normSq a₂ + 2 * (a₁ * (starRingEnd ℂ) a₂ * (starRingEnd ℂ) (w ^ k)).re := by
    intro k
    rw [tick_factor ζ a₁ a₂ N t d k hN hζ, Complex.normSq_add, Complex.normSq_mul, map_pow,
      map_pow, h1, one_pow, one_pow, mul_one, map_mul, ← mul_assoc]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum, ← map_sum, hgeom, map_zero,
    mul_zero, Complex.zero_re, mul_zero, add_zero]

/-- **The Pauli-scalar clock.** With phase per tick `i` (the `μ₄ = {±1, ±i}` of the Pauli scalars,
`N = 4`) and equal slits one tick apart, the four frequencies read `4, 2, 0, 2` times `|a|²`. The
dark fringe at `k = 2` is `i² = −1`. -/
theorem mu4_pattern (a : ℂ) :
    tickIntensity I a a 0 1 0 = 4 * normSq a ∧
    tickIntensity I a a 0 1 1 = 2 * normSq a ∧
    tickIntensity I a a 0 1 2 = 0 ∧
    tickIntensity I a a 0 1 3 = 2 * normSq a := by
  have hfac : ∀ k : ℕ, tickIntensity I a a 0 1 k = normSq a * normSq (1 + I ^ k) := by
    intro k
    unfold tickIntensity
    rw [← Complex.normSq_mul]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hfac]
  · norm_num [Complex.normSq_apply]
    ring
  · simp [Complex.normSq_apply]
    ring
  · simp [Complex.normSq_apply, pow_two]
  · simp [Complex.normSq_apply, pow_succ]
    ring

end QLF.TimeDoubleSlit
