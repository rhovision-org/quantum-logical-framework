import QLF_BoostCovariance

set_option linter.unusedVariables false

/-!
# QLF_InteractingKinematics — long-wavelength interacting kinematics is boost-covariant; elementary umklapp is not

[`QLF_BoostCovariance`](QLF_BoostCovariance.lean) proved that one free Dirac-walk mode, boosted, is
still on the walk's mass shell up to `S²/4 + S′²/4`, `S ≈ (L_P/λ)²`. Interactions add one thing
free propagation does not have: legs meet at a vertex, and the vertex has to conserve
energy–momentum. This module is the **kinematic layer** of interacting boost covariance: what a
vertex can conserve on the lattice, and when that conservation law is itself frame-independent.

On a translation-invariant lattice with a time-periodic step, an interacting process conserves
**lattice** energy–momentum: the incoming total minus the outgoing total is a reciprocal-lattice
vector, `2π·n` with `n ∈ ℤ⁴` (Bloch; quasi-energy is a phase `e^{iE}` too, so it is conserved
mod `2π` as well). Processes with `n ≠ 0` are **umklapp** processes. Here that conservation law is
taken as the definition of a lattice process (`Process.latticeConserving`); deriving it from a
specific interacting walk is not done here (see *Not here* below).

* **`no_umklapp`** — if every component's total `Σ|p|` over all legs is below `2π` (the
  long-wavelength condition, `Process.longWave`), the reciprocal vector is zero: the process
  conserves energy–momentum *exactly*, as in the continuum.
* **`umklapp_needs_short_wave`** — contrapositive: a genuine umklapp process has some component
  whose leg *total* reaches `2π`. That is a bound on the sum, not on any single leg.
* **`umklapp_leg_bound`, `soft_umklapp`** — the per-leg statement: with `N + M` legs, some leg has
  a component of size at least `2π/(N + M)`, and this cannot be improved to "a lattice-scale leg"
  without bounding the valence, because four legs of `π/2` already make an umklapp process.
* **`map_exactConserving`** — exact conservation is linear, so every Lorentz map
  (`Lorentz`: linear, preserves `E² − |k|²`) carries an exactly conserving process to an exactly
  conserving one.
* **`process_boost_covariant`** — the theorem of the module. A long-wavelength lattice process
  whose legs are on the walk's mass shell, seen by any Lorentz-transformed observer whose legs are
  still long-wavelength, is again an exactly conserving lattice process, and every leg is on the
  walk's mass shell up to `S²/4 + S′²/4` (from `shell_lorentz_invariant`). This covers any number
  of legs, so pair creation and annihilation *as kinematics* are included: a process may have
  different numbers of incoming and outgoing legs.
* **`boostX`, `boostXLorentz`** — the boost along `x` with `γ² − u² = 1` is a `Lorentz`.
* **`umklapp_x_not_covariant`, `umklapp_t_not_covariant`** — the converse side. The elementary
  umklapp vectors along the boost axis, `2π e_x` and `2π e_t`, are carried by any boost with
  `u ≠ 0` **off** the reciprocal lattice. So an observer boosted along `x` sees an elementary
  `x`- or `t`-umklapp as a process that conserves nothing, neither exactly nor mod `2π`. These
  are two vectors, not a classification: a boost with rational `γ`, `u` can carry other
  reciprocal vectors into the lattice.
* **`twoBody_translation_commute`, `twoBody_conserves_momentum`** — a two-body walk with any
  contact (relative-position) interaction commutes with moving both particles together, so it
  carries a state of definite total lattice momentum to one of the same total momentum: the
  translation invariance behind `latticeConserving`, for an actual interacting step.

## What this is and is not

It is **tree-level kinematics**: which processes are allowed, and whether the allowed set is the
same in every frame. In the long-wavelength sector it is, to the order of `QLF_BoostCovariance`.

It is **not** dynamical boost covariance. Amplitudes are not compared between frames, and loops are
not treated. A loop integrates over all intermediate momenta, including the lattice-scale ones
where neither `no_umklapp` nor the free shell bound applies; that region is where the Collins et
al. (2004) leakage would come from. Nothing here decomposes a loop into frame-dependent and
frame-independent parts: the finite-spacing shell corrections are frame dependence without any
umklapp. Bounding the lattice-scale contribution is an open obligation. The census-side
partial answer (axis-blind shared pairs keep the spread ratio at `1`) is
[`QLF_LorentzSymbol`](QLF_LorentzSymbol.lean) §5.

**Not here.** (i) For a two-body contact-interaction walk on `ℤ³` the conservation law is
derived (`twoBody_lattice_conservation`, `scattering_latticeConserving`, last two sections); for
more than two bodies, and for the full set of out-states of a given step (which total momenta
actually occur), it is still the definition of a process; (ii) the amplitude or S-matrix
comparison between frames; (iii) loops and the size of their umklapp contribution; (iv) pair
creation as a change in the number of census strands, which is a statement about the census, not
about kinematics. See [`Relativity_Principle.md`](../Relativity_Principle.md) §6a. No axioms.
-/

namespace QLF.InteractingKinematics

open QLF.BoostCovariance

/-- An energy–momentum `(E, k_x, k_y, k_z)`. -/
abbrev P4 := Fin 4 → ℝ

/-- The Minkowski form `E² − |k|²` of an energy–momentum. -/
def mform (p : P4) : ℝ := form (p 0) (p 1) (p 2) (p 3)

/-- The size `E² + |k|² + m²` of a leg of mass `m` against the Planck scale. -/
def msize (p : P4) (m : ℝ) : ℝ := size (p 0) (p 1) (p 2) (p 3) m

/-- The Dirac walk's shell function at a leg: zero exactly on the walk's mass shell. -/
noncomputable def mshell (p : P4) (m : ℝ) : ℝ := shell (p 0) (p 1) (p 2) (p 3) m

/-- A Lorentz map: linear on energy–momentum and preserving the Minkowski form. Boosts in any
    direction and rotations are all of this kind. -/
structure Lorentz where
  map : P4 →ₗ[ℝ] P4
  preserves : ∀ p, mform (map p) = mform p

/-- The reciprocal-lattice vector `2π·n`. -/
noncomputable def latticeVec (n : Fin 4 → ℤ) : P4 := fun c => 2 * Real.pi * (n c : ℝ)

/-- An interacting process: `N` incoming and `M` outgoing legs with their masses. `N ≠ M` is
    allowed, so pair creation and annihilation are processes too. -/
structure Process (N M : ℕ) where
  pin : Fin N → P4
  pout : Fin M → P4
  min : Fin N → ℝ
  mout : Fin M → ℝ

namespace Process

variable {N M : ℕ}

/-- Incoming total minus outgoing total. -/
def mismatch (P : Process N M) : P4 := ∑ i, P.pin i - ∑ j, P.pout j

/-- Lattice conservation: the mismatch is a reciprocal-lattice vector (umklapp allowed). -/
def latticeConserving (P : Process N M) : Prop := ∃ n : Fin 4 → ℤ, P.mismatch = latticeVec n

/-- Exact conservation, as in the continuum. -/
def exactConserving (P : Process N M) : Prop := P.mismatch = 0

/-- The long-wavelength condition: for every component, the legs' total magnitude is below `2π`. -/
def longWave (P : Process N M) : Prop :=
  ∀ c : Fin 4, ∑ i, |P.pin i c| + ∑ j, |P.pout j c| < 2 * Real.pi

/-- The same process seen by a Lorentz-transformed observer. -/
def map (P : Process N M) (Λ : Lorentz) : Process N M :=
  ⟨fun i => Λ.map (P.pin i), fun j => Λ.map (P.pout j), P.min, P.mout⟩

theorem mismatch_apply (P : Process N M) (c : Fin 4) :
    P.mismatch c = ∑ i, P.pin i c - ∑ j, P.pout j c := by
  unfold mismatch
  simp [Finset.sum_apply]

theorem abs_mismatch_le (P : Process N M) (c : Fin 4) :
    |P.mismatch c| ≤ ∑ i, |P.pin i c| + ∑ j, |P.pout j c| := by
  rw [mismatch_apply]
  calc |∑ i, P.pin i c - ∑ j, P.pout j c|
      ≤ |∑ i, P.pin i c| + |∑ j, P.pout j c| := abs_sub _ _
    _ ≤ ∑ i, |P.pin i c| + ∑ j, |P.pout j c| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)

end Process

/-- An integer whose `2π`-multiple is below `2π` in size is zero. -/
theorem int_eq_zero_of_small {n : ℤ} (h : |2 * Real.pi * (n : ℝ)| < 2 * Real.pi) : n = 0 := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_mul, abs_of_pos hp] at h
  have h1 : |(n : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [← Int.cast_abs] at h1
  have h2 : |n| < 1 := by exact_mod_cast h1
  rw [abs_lt] at h2
  omega

/-- **No umklapp at long wavelength.** A lattice-conserving process whose legs are long-wavelength
    conserves energy–momentum exactly. -/
theorem no_umklapp {N M : ℕ} (P : Process N M) (hl : P.latticeConserving) (hw : P.longWave) :
    P.exactConserving := by
  obtain ⟨n, hn⟩ := hl
  unfold Process.exactConserving
  funext c
  have hb := lt_of_le_of_lt (P.abs_mismatch_le c) (hw c)
  have hc : P.mismatch c = 2 * Real.pi * (n c : ℝ) := by rw [hn]; rfl
  rw [hc] at hb
  rw [hc, int_eq_zero_of_small hb]
  simp

/-- **Umklapp needs a short wavelength.** A lattice process that does not conserve exactly has a
    component whose legs' total magnitude reaches `2π`. -/
theorem umklapp_needs_short_wave {N M : ℕ} (P : Process N M) (hl : P.latticeConserving)
    (hu : ¬ P.exactConserving) :
    ∃ c : Fin 4, 2 * Real.pi ≤ ∑ i, |P.pin i c| + ∑ j, |P.pout j c| := by
  by_contra h
  push Not at h
  exact hu (no_umklapp P hl h)

/-- **The per-leg bound.** In an umklapp process with `N + M` legs, some leg has a component of
    magnitude at least `2π/(N + M)`. So a leg at the lattice scale is forced only at bounded
    valence: many soft legs can add up to a reciprocal vector (`soft_umklapp` below). -/
theorem umklapp_leg_bound {N M : ℕ} (P : Process N M) (hl : P.latticeConserving)
    (hu : ¬ P.exactConserving) :
    ∃ c : Fin 4, (∃ i, 2 * Real.pi ≤ ((N + M : ℕ) : ℝ) * |P.pin i c|) ∨
      (∃ j, 2 * Real.pi ≤ ((N + M : ℕ) : ℝ) * |P.pout j c|) := by
  obtain ⟨c, hc⟩ := umklapp_needs_short_wave P hl hu
  by_contra h
  push Not at h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  let f : Fin N ⊕ Fin M → ℝ := Sum.elim (fun i => |P.pin i c|) (fun j => |P.pout j c|)
  have hsum : ∑ a, f a = ∑ i, |P.pin i c| + ∑ j, |P.pout j c| := by
    simp [f, Fintype.sum_sum_type]
  have hlt : ∀ a, ((N + M : ℕ) : ℝ) * f a < 2 * Real.pi := by
    rintro (i | j)
    · exact (h c).1 i
    · exact (h c).2 j
  rw [← hsum] at hc
  by_cases hne : (Finset.univ : Finset (Fin N ⊕ Fin M)).Nonempty
  · have hs := Finset.sum_lt_sum_of_nonempty hne (fun a _ => hlt a)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul] at hs
    have hcard : 0 < (Finset.univ : Finset (Fin N ⊕ Fin M)).card := Finset.card_pos.mpr hne
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hcard
    have hK : (0 : ℝ) < ((N + M : ℕ) : ℝ) := by exact_mod_cast hcard
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hc
    linarith

/-- **Soft umklapp exists.** Four incoming legs, each carrying `π/2` along `x`, have mismatch
    `2π e_x`: a genuine umklapp process in which no single leg is at the lattice scale. With `n`
    legs of `2π/n` the same holds for any `n`, so umklapp does not by itself require a
    Planck-scale leg; `umklapp_leg_bound` is the sharp statement. -/
theorem soft_umklapp :
    ∃ P : Process 4 0, P.latticeConserving ∧ ¬ P.exactConserving ∧
      ∀ i c, |P.pin i c| ≤ Real.pi / 2 := by
  refine ⟨⟨fun _ => ![0, Real.pi / 2, 0, 0], Fin.elim0, fun _ => 0, Fin.elim0⟩, ⟨![0, 1, 0, 0], ?_⟩,
    ?_, ?_⟩
  · funext c
    fin_cases c <;> simp [Process.mismatch, latticeVec, Finset.sum_const] <;> ring
  · intro h
    have h1 := congrFun h 1
    simp [Process.mismatch, Finset.sum_const] at h1
  · intro i c
    have := Real.pi_pos
    fin_cases c <;> simp [abs_of_pos, this] <;> linarith

/-- Exact conservation is linear: a Lorentz map carries the mismatch to its image. -/
theorem map_mismatch {N M : ℕ} (P : Process N M) (Λ : Lorentz) :
    (P.map Λ).mismatch = Λ.map P.mismatch := by
  unfold Process.map Process.mismatch
  simp [map_sub, map_sum]

/-- A Lorentz map carries an exactly conserving process to an exactly conserving one. -/
theorem map_exactConserving {N M : ℕ} (P : Process N M) (Λ : Lorentz) (h : P.exactConserving) :
    (P.map Λ).exactConserving := by
  unfold Process.exactConserving at *
  rw [map_mismatch, h, map_zero]

/-- One leg: a Lorentz image of an on-shell leg is on the walk's shell to `S²/4 + S′²/4`. -/
theorem leg_covariant (Λ : Lorentz) {p : P4} {m : ℝ} (hs : mshell p m = 0)
    (h : msize p m ≤ 1) (h' : msize (Λ.map p) m ≤ 1) :
    |mshell (Λ.map p) m| ≤ msize p m ^ 2 / 4 + msize (Λ.map p) m ^ 2 / 4 :=
  shell_lorentz_invariant h h' (Λ.preserves p) hs

/-- **Interacting processes are boost-covariant in the large (kinematics).** Let `P` be a lattice
    process whose legs are long-wavelength and on the Dirac walk's mass shell. For any Lorentz map
    `Λ` that keeps every leg long-wavelength (`msize ≤ 1`), the transformed process conserves
    energy–momentum exactly (so it is again a lattice process, with no umklapp), and every
    transformed leg is on the walk's shell up to `S²/4 + S′²/4`. -/
theorem process_boost_covariant {N M : ℕ} (P : Process N M) (Λ : Lorentz)
    (hl : P.latticeConserving) (hw : P.longWave)
    (hin : ∀ i, mshell (P.pin i) (P.min i) = 0) (hout : ∀ j, mshell (P.pout j) (P.mout j) = 0)
    (hsin : ∀ i, msize (P.pin i) (P.min i) ≤ 1) (hsout : ∀ j, msize (P.pout j) (P.mout j) ≤ 1)
    (hsin' : ∀ i, msize (Λ.map (P.pin i)) (P.min i) ≤ 1)
    (hsout' : ∀ j, msize (Λ.map (P.pout j)) (P.mout j) ≤ 1) :
    (P.map Λ).exactConserving ∧ (P.map Λ).latticeConserving ∧
      (∀ i, |mshell (Λ.map (P.pin i)) (P.min i)| ≤
        msize (P.pin i) (P.min i) ^ 2 / 4 + msize (Λ.map (P.pin i)) (P.min i) ^ 2 / 4) ∧
      (∀ j, |mshell (Λ.map (P.pout j)) (P.mout j)| ≤
        msize (P.pout j) (P.mout j) ^ 2 / 4 + msize (Λ.map (P.pout j)) (P.mout j) ^ 2 / 4) := by
  have he := map_exactConserving P Λ (no_umklapp P hl hw)
  refine ⟨he, ⟨0, ?_⟩, fun i => leg_covariant Λ (hin i) (hsin i) (hsin' i),
    fun j => leg_covariant Λ (hout j) (hsout j) (hsout' j)⟩
  rw [he]
  funext c
  simp [latticeVec]

/-- A Dirac-walk eigenmode is on the walk's shell, so the leg hypotheses of
    `process_boost_covariant` are met by the walk's actual eigenmodes. -/
theorem walk_leg_onShell {E kx ky kz m : ℝ} (v : Fin 2 × Fin 2 → ℂ) (hv : v ≠ 0)
    (h : Matrix.mulVec (DiracWalk.diracWalk ky kx kz m) v = Complex.exp (E * Complex.I) • v) :
    mshell ![E, kx, ky, kz] m = 0 := by
  have d := DiracWalk.diracWalk_dispersion ky kx kz m E v hv h
  unfold mshell shell
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  rw [d]; ring

/-! ## The boost along `x`, and where the lattice frame enters -/

/-- The boost along `x` with rapidity parameters `γ`, `u = γv`. -/
def boostX (γ u : ℝ) (p : P4) : P4 := ![γ * p 0 + u * p 1, u * p 0 + γ * p 1, p 2, p 3]

/-- The boost along `x` as a linear map. -/
def boostXLin (γ u : ℝ) : P4 →ₗ[ℝ] P4 where
  toFun := boostX γ u
  map_add' p q := by
    funext c; fin_cases c <;> simp [boostX] <;> ring
  map_smul' r p := by
    funext c; fin_cases c <;> simp [boostX] <;> ring

/-- The boost along `x` with `γ² − u² = 1` is a Lorentz map. -/
def boostXLorentz {γ u : ℝ} (hγ : γ ^ 2 - u ^ 2 = 1) : Lorentz where
  map := boostXLin γ u
  preserves p := by
    show mform (boostX γ u p) = mform p
    unfold mform boostX
    simpa using boost_form γ u (p 0) (p 1) (p 2) (p 3) hγ

/-- Integers with `a² − b² = 1` have `b = 0`. -/
theorem int_hyperbola {a b : ℤ} (h : a ^ 2 - b ^ 2 = 1) : b = 0 := by
  have hm : (a - b) * (a + b) = 1 := by linear_combination h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The elementary umklapp vector `2π e_x` (along the boost axis). -/
noncomputable def umklappX : P4 := latticeVec ![0, 1, 0, 0]

/-- The elementary quasi-energy umklapp vector `2π e_t`. -/
noncomputable def umklappT : P4 := latticeVec ![1, 0, 0, 0]

/-- **A spatial umklapp along the boost axis is frame-dependent.** For every boost along `x` with
    `u ≠ 0`, the image of `2π e_x` is not a reciprocal-lattice vector. -/
theorem umklapp_x_not_covariant {γ u : ℝ} (hγ : γ ^ 2 - u ^ 2 = 1) (hu : u ≠ 0) :
    ¬ ∃ n : Fin 4 → ℤ, boostX γ u umklappX = latticeVec n := by
  rintro ⟨n, hn⟩
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  have h0 := congrFun hn 0
  have h1 := congrFun hn 1
  simp [boostX, umklappX, latticeVec] at h0 h1
  -- h0 : 2π·u = 2π·n 0   and   h1 : γ·2π = 2π·n 1  (up to normalisation by simp)
  have hu' : u = (n 0 : ℝ) := by
    have : (2 * Real.pi) * u = (2 * Real.pi) * (n 0 : ℝ) := by linarith
    exact mul_left_cancel₀ hp this
  have hγ' : γ = (n 1 : ℝ) := by
    have : (2 * Real.pi) * γ = (2 * Real.pi) * (n 1 : ℝ) := by linarith
    exact mul_left_cancel₀ hp this
  rw [hu', hγ'] at hγ
  have hz : (n 1) ^ 2 - (n 0) ^ 2 = 1 := by exact_mod_cast hγ
  have := int_hyperbola hz
  exact hu (by rw [hu', this]; simp)

/-- **A quasi-energy umklapp is frame-dependent too.** For every boost along `x` with `u ≠ 0`,
    the image of `2π e_t` is not a reciprocal-lattice vector. -/
theorem umklapp_t_not_covariant {γ u : ℝ} (hγ : γ ^ 2 - u ^ 2 = 1) (hu : u ≠ 0) :
    ¬ ∃ n : Fin 4 → ℤ, boostX γ u umklappT = latticeVec n := by
  rintro ⟨n, hn⟩
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  have h0 := congrFun hn 0
  have h1 := congrFun hn 1
  simp [boostX, umklappT, latticeVec] at h0 h1
  have hγ' : γ = (n 0 : ℝ) := by
    have : (2 * Real.pi) * γ = (2 * Real.pi) * (n 0 : ℝ) := by linarith
    exact mul_left_cancel₀ hp this
  have hu' : u = (n 1 : ℝ) := by
    have : (2 * Real.pi) * u = (2 * Real.pi) * (n 1 : ℝ) := by linarith
    exact mul_left_cancel₀ hp this
  rw [hu', hγ'] at hγ
  have hz : (n 0) ^ 2 - (n 1) ^ 2 = 1 := by exact_mod_cast hγ
  have := int_hyperbola hz
  exact hu (by rw [hu', this]; simp)

/-! ## Stage 3, the translation half: an interacting two-body walk conserves total lattice momentum

The definition `Process.latticeConserving` is what translation invariance gives. Here is the
translation invariance itself, for a general two-body walk with a contact interaction: each
particle hops by a coin-weighted shift, and the pair then picks up a phase that depends only on
its relative position. The step commutes with moving both particles together
(`twoBody_translation_commute`), so a state of definite total lattice momentum (an eigenstate of
every joint translation, with a character `χ`) is carried to a state of the same total momentum
(`twoBody_conserves_momentum`). Total momentum is a character of the lattice group, so it is
conserved exactly as a character, which for `ZMod N` is momentum mod `2π`, umklapp included. -/

section TwoBody

variable {S : Type*} [AddCommGroup S] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ι : Type*} [Fintype ι]

/-- Moving both particles by `a`. -/
def jointShift (a : S) (ψ : S × S → W) : S × S → W := fun x => ψ (x.1 - a, x.2 - a)

/-- A two-body walk step with a contact interaction: particle one hops by `e i`, particle two by
    `e j`, with coin `C i j` on the joint internal space, then the pair picks up the scalar
    `g (x₁ − x₂)`, a function of the relative position only. Any on-site or finite-range
    interaction has this form. -/
def twoBodyStep (e : ι → S) (C : ι → ι → W →ₗ[ℂ] W) (g : S → ℂ) (ψ : S × S → W) : S × S → W :=
  fun x => g (x.1 - x.2) • ∑ i, ∑ j, C i j (ψ (x.1 - e i, x.2 - e j))

/-- **The interacting step commutes with joint translation.** -/
theorem twoBody_translation_commute (e : ι → S) (C : ι → ι → W →ₗ[ℂ] W) (g : S → ℂ)
    (a : S) (ψ : S × S → W) :
    jointShift a (twoBodyStep e C g ψ) = twoBodyStep e C g (jointShift a ψ) := by
  funext x
  simp only [jointShift, twoBodyStep]
  have hrel : x.1 - a - (x.2 - a) = x.1 - x.2 := by abel
  rw [hrel]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  abel_nf

/-- **Total lattice momentum is conserved by the interacting step.** If every joint translation
    acts on `ψ` by the scalar `χ a` (definite total momentum), it acts on the stepped state by the
    same scalar. -/
theorem twoBody_conserves_momentum (e : ι → S) (C : ι → ι → W →ₗ[ℂ] W) (g : S → ℂ)
    (χ : S → ℂ) (ψ : S × S → W) (hψ : ∀ a, jointShift a ψ = χ a • ψ) (a : S) :
    jointShift a (twoBodyStep e C g ψ) = χ a • twoBodyStep e C g ψ := by
  rw [twoBody_translation_commute, hψ a]
  funext x
  simp only [twoBodyStep, Pi.smul_apply, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact smul_comm _ _ _

end TwoBody

/-! ## Stage 3, the reciprocal half: the conserved character is momentum mod `2π`

`twoBody_conserves_momentum` conserves a character. On the lattice `ℤ³` a two-body plane wave of
momenta `k₁`, `k₂` has the character of total momentum `k₁ + k₂` (`planeWave_jointShift`), a
non-zero state has only one character (`char_unique`), and two momenta give the same character
exactly when they differ by a reciprocal vector (`momChar_eq`). So if the interacting step sends
the plane wave to a non-zero state of total momentum `K'`, then `k₁ + k₂ − K' ∈ 2π ℤ³`
(`twoBody_lattice_conservation`): the spatial part of `Process.latticeConserving`, derived for
this walk instead of assumed. Quasi-energy is a phase, so it is conserved mod `2π` as well
(`quasiEnergy_mod`), and `scattering_latticeConserving` assembles the two into the `Process`
form for a two-to-two scattering. -/

section Reciprocal

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ι : Type*} [Fintype ι]

/-- A site of the spatial lattice `ℤ³`. -/
abbrev Site := Fin 3 → ℤ

/-- The translation character of total momentum `K`. -/
noncomputable def momChar (K : Fin 3 → ℝ) (a : Site) : ℂ :=
  Complex.exp (-(∑ c, (K c : ℂ) * (a c : ℂ)) * Complex.I)

/-- A two-body plane wave with momenta `k₁`, `k₂` and internal state `w`. -/
noncomputable def planeWave (k₁ k₂ : Fin 3 → ℝ) (w : W) : Site × Site → W :=
  fun x => Complex.exp ((∑ c, ((k₁ c : ℂ) * (x.1 c : ℂ) + (k₂ c : ℂ) * (x.2 c : ℂ))) *
    Complex.I) • w

/-- A two-body plane wave has the character of its total momentum. -/
theorem planeWave_jointShift (k₁ k₂ : Fin 3 → ℝ) (w : W) (a : Site) :
    jointShift a (planeWave k₁ k₂ w) = momChar (k₁ + k₂) a • planeWave k₁ k₂ w := by
  funext x
  simp only [jointShift, planeWave, momChar, Pi.smul_apply, smul_smul, ← Complex.exp_add]
  congr 2
  have h : ∑ c, ((k₁ c : ℂ) * ((x.1 - a) c : ℤ) + (k₂ c : ℂ) * ((x.2 - a) c : ℤ)) =
      ∑ c, ((k₁ c : ℂ) * (x.1 c : ℂ) + (k₂ c : ℂ) * (x.2 c : ℂ)) -
        ∑ c, (((k₁ + k₂) c : ℝ) : ℂ) * (a c : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Complex.ofReal_add]
    ring
  rw [h]
  ring

/-- A non-zero state has at most one translation character. -/
theorem char_unique {S : Type*} [AddCommGroup S] {ψ : S × S → W} (hψ : ψ ≠ 0) (χ χ' : S → ℂ)
    (h : ∀ a, jointShift a ψ = χ a • ψ) (h' : ∀ a, jointShift a ψ = χ' a • ψ) : χ = χ' := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hψ
  funext a
  have e : (χ a - χ' a) • ψ x = 0 := by
    rw [sub_smul]
    have := congrFun ((h a).symm.trans (h' a)) x
    simp only [Pi.smul_apply] at this
    rw [this, sub_self]
  rcases smul_eq_zero.mp e with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hx

/-- Two phases agree exactly when their angles differ by a multiple of `2π`. -/
theorem quasiEnergy_mod {E E' : ℝ}
    (h : Complex.exp (E * Complex.I) = Complex.exp (E' * Complex.I)) :
    ∃ n : ℤ, E - E' = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- Equal momentum characters differ by a reciprocal-lattice vector. -/
theorem momChar_eq {K K' : Fin 3 → ℝ} (h : momChar K = momChar K') (c : Fin 3) :
    ∃ n : ℤ, K c - K' c = 2 * Real.pi * n := by
  have hc := congrFun h (Pi.single c (-1))
  simp only [momChar, Pi.single_apply] at hc
  have e : ∀ L : Fin 3 → ℝ,
      -(∑ d, (L d : ℂ) * ((if d = c then (-1 : ℤ) else 0 : ℤ) : ℂ)) * Complex.I =
        (L c : ℂ) * Complex.I := by
    intro L
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  rw [e K, e K'] at hc
  exact quasiEnergy_mod hc

/-- **Lattice momentum conservation, derived.** If the interacting two-body step sends the plane
    wave of momenta `k₁`, `k₂` to a non-zero state of definite total momentum `K'`, then
    `k₁ + k₂ − K'` is a reciprocal-lattice vector. -/
theorem twoBody_lattice_conservation (e : ι → Site) (C : ι → ι → W →ₗ[ℂ] W) (g : Site → ℂ)
    (k₁ k₂ K' : Fin 3 → ℝ) (w : W)
    (hne : twoBodyStep e C g (planeWave k₁ k₂ w) ≠ 0)
    (hout : ∀ a, jointShift a (twoBodyStep e C g (planeWave k₁ k₂ w)) =
      momChar K' a • twoBodyStep e C g (planeWave k₁ k₂ w)) (c : Fin 3) :
    ∃ n : ℤ, k₁ c + k₂ c - K' c = 2 * Real.pi * n := by
  have hin := twoBody_conserves_momentum e C g (momChar (k₁ + k₂)) (planeWave k₁ k₂ w)
    (planeWave_jointShift k₁ k₂ w)
  have := momChar_eq (char_unique hne _ _ hin hout) c
  simpa using this

/-- **The `Process` form.** A two-to-two scattering whose quasi-energies agree mod `2π` and whose
    momenta agree mod the reciprocal lattice is a lattice-conserving `Process`: the definition of
    the first sections is met by the two-body walk. -/
theorem scattering_latticeConserving (E₁ E₂ E₃ E₄ : ℝ) (k₁ k₂ k₃ k₄ : Fin 3 → ℝ)
    (m : Fin 2 → ℝ) (m' : Fin 2 → ℝ)
    (hE : ∃ n : ℤ, E₁ + E₂ - (E₃ + E₄) = 2 * Real.pi * n)
    (hk : ∀ c, ∃ n : ℤ, k₁ c + k₂ c - (k₃ c + k₄ c) = 2 * Real.pi * n) :
    (Process.mk ![Fin.cons E₁ k₁, Fin.cons E₂ k₂] ![Fin.cons E₃ k₃, Fin.cons E₄ k₄]
      m m').latticeConserving := by
  obtain ⟨n0, h0⟩ := hE
  choose ns hns using hk
  refine ⟨Fin.cons n0 ns, ?_⟩
  funext c
  refine Fin.cases ?_ (fun d => ?_) c
  · simp [Process.mismatch, latticeVec, Fin.sum_univ_two]
    linarith
  · simp [Process.mismatch, latticeVec, Fin.sum_univ_two]
    linarith [hns d]

end Reciprocal

end QLF.InteractingKinematics
