/-
  QLF_QuantumComputer.lean — what QLF proves about the claim "the universe is a quantum
  computer", and where the proof stops.

  Write-up: Universe_Quantum_Computer.md.

  Thirteen results, no axioms.

  1. **Closure-preserving dynamics compute every Boolean function** (`fredkin_complete`).
     Every `f : (Fin n → Bool) → Bool` is the output of a tree of Fredkin gates on the
     inputs and constants (Shannon's 1949 expansion; each multiplexer is one controlled
     swap), with at most `2ⁿ − 1` gates, and every gate maps an admissible register to an
     admissible one (`QLF_Fredkin.fredkin_preserves_zfa`). This is stronger than
     `qlf_universality`, which shows that a circuit's code survives the ZFA filter: here the
     substrate's own gates *compute* `f`.

  2. **The twist layer alone is not a quantum computer** (`twist_folds_finite`). Every twist
     history folds to one of at most sixteen matrices, `{±1, ±i} · {I, σx, σy, σz}`
     (`nf_decomp`). A finite gate set closed under products generates a finite group, so
     single histories cannot approximate a generic rotation; the explicit witness is
     `twist_cannot_reach_rotation`.

  3. **Two Forms weighted by integer counts give a rotation of infinite order**
     (`rotation_is_form_product`, `rotation_powers_injective`). The product of the Forms
     `x̂` and `(3x̂ + 4ŷ)/5`, coefficients a Pythagorean triple of counts, is
     `diag((3+4i)/5, (3−4i)/5)`, and its powers are pairwise distinct: `(3+4i)ⁿ ≠ 5ⁿ` for
     `n ≥ 1`, since the real part of `(3+4i)ⁿ` is `3 mod 5`. That is exactly what the twist
     layer lacks. A rotation of infinite order about one axis together with one about a
     non-parallel axis generates a dense subgroup of SU(2), and dense single-qubit gates
     with one entangling gate are universal (Barenco et al. 1995). Those two steps are
     cited, not proved here; the entangling gate is §9.

  4. **A problem posed as a closure is solved without search** (`closing_cost_exact`,
     `completion_perm_closes`): the least closing continuation has length exactly the
     history's `ℓ¹` imbalance, and every order of the conjugate completion closes it.

  5. **Silver inflation is a discrete boost** (`silver_expands`, `silver_contracts`,
     `silver_unit`, `silver_boost_norm`, `projection_choice`): one projected dimension of the
     octagonal quasicrystal expands by `1 + √2` exactly as the other contracts by `1 − √2`,
     the indefinite norm `a² − 2b²` is preserved by two steps, and which projection is
     called physical is a choice.

  6. **Colour is finite, gluons are not** (`colour_transport_finite`, `gluonRotation_eq`,
     `gluonRotation_det`, `gluonRotation_powers_injective`): colour transport over `F₃` is a
     finite (qutrit Clifford-type) group, and the count-weighted rotation along the Cartan
     gluon `g3` is an `SU(3)` element of infinite order.

  7. **Two trits, not three bits** (`tritCode_injective`, `tritCode_surjective`,
     `closure_trits_zero`, `trits_weaker`): vacuum plus the eight twists is exactly `F₃²`, a
     closure sums to zero there, and the converse fails.

  8. **The past is an event trigger through its record** (`future_depends_only_on_record`,
     `completion_depends_only_on_record`, `minimal_future_is_completion`, `fabricated_past`):
     the futures a past admits depend only on its net signed action, so a different past with
     the same record triggers the same events, and the record fixes the content of the
     minimal future up to order.

  9. **A joint closure is an entangling gate** (`joint_closure_is_cz`, `interleaved_closes`,
     `cz_entangling`): interleaving two strands' closed pairs applies the controlled-Z phase
     `(−1)^{ab}`, which is not a product of single-qubit gates; and the Hadamard is a Form
     that exchanges twist axes (`hadamard_sq`, `hadamard_swaps`).

  10. **The boost acts on histories** (`silverDNA_closes`, `silverDNA_vec`, `silverDNA_int`):
     the silver twist DNA preserves closure, expands the physical octagonal vector by `1 + √2`
     and contracts the internal one by `1 − √2`.

  11. **Superposition is alternate histories** (`censusSum`, `censusSum_append`,
     `integer_form_is_census_sum`, `five_rotation_census`, `alternate_histories_cancel`): an
     amplitude is the sum of the folds of alternate histories; every integer Form is such a
     sum, and `5 · rotation` is the census sum of seven alternate histories, so the weights of
     §3 are counts of ways. The division by `5` is a ratio of alternatives to their mirror:
     `z = (2+i)/(2−i)` (`z_eq_ratio`), where `2 ± i` are census sums of three alternate
     histories (`gauss_census`, `gauss_census_mirror`) and `5 = |2+i|²` (`gauss_normSq`).

  12. **H·T has infinite order** (`hT_pow_ne_scalar`, `hadamard_t_infinite_order`): no
     positive power of the Clifford+T product is a scalar.

  13. **The rotation's angles are dense** (`arg_z_irrational`, `rotation_angles_dense`): the
     powers of the §3 rotation approach every phase about its axis. The remaining step to
     SU(2) density (two non-parallel axes) and Barenco universality stay cited.

  What this does NOT claim: that the universe *is* this construction (only that it is one
  model of a logical system that computes), and anything about complexity: an exact answer
  from a path sum costs the whole set of paths (`QLF_PossibilityGrowth`), and nothing here
  gives an NP oracle.
-/

import Mathlib
import QLF_Fredkin
import SpacetimeDynamics
import QLF_StrongAlgebra
import QLF_ColourFlux

namespace QLF.QuantumComputer

open QLF QLF.Fredkin

/-! ## 1. Classical universality: every Boolean function from controlled swaps -/

/-- A Shannon decision tree whose every internal node is one Fredkin gate. `mux i lo hi`
    feeds the register `(x i; lo, hi)` to a controlled swap and reads the first target line. -/
inductive MuxTree (n : ℕ) where
  | leaf (b : Bool)
  | mux (i : Fin n) (lo hi : MuxTree n)

namespace MuxTree

variable {n : ℕ}

/-- Run the network: each node is evaluated by the Fredkin gate itself. -/
def eval : MuxTree n → (Fin n → Bool) → Bool
  | leaf b, _ => b
  | mux i lo hi, x => (fredkin ⟨x i, lo.eval x, hi.eval x⟩).a

/-- Number of Fredkin gates in the network. -/
def gates : MuxTree n → ℕ
  | leaf _ => 0
  | mux _ lo hi => lo.gates + hi.gates + 1

/-- The registers the network feeds to its gates on input `x`. -/
def registers : MuxTree n → (Fin n → Bool) → List Reg
  | leaf _, _ => []
  | mux i lo hi, x => ⟨x i, lo.eval x, hi.eval x⟩ :: (lo.registers x ++ hi.registers x)

/-- Re-index a network on `n` inputs as one on `n + 1` inputs that ignores input `0`. -/
def lift : MuxTree n → MuxTree (n + 1)
  | leaf b => leaf b
  | mux i lo hi => mux i.succ lo.lift hi.lift

/-- **One controlled swap is a multiplexer**: the first target line of `fredkin (c; a, b)`
    is `b` when `c` is set and `a` otherwise. -/
theorem eval_mux (i : Fin n) (lo hi : MuxTree n) (x : Fin n → Bool) :
    (mux i lo hi).eval x = if x i then hi.eval x else lo.eval x := by
  simp only [eval]
  cases x i <;> rfl

theorem eval_lift (T : MuxTree n) (x : Fin (n + 1) → Bool) :
    T.lift.eval x = T.eval (Fin.tail x) := by
  induction T with
  | leaf b => rfl
  | mux i lo hi ihlo ihhi =>
      rw [lift, eval_mux, eval_mux, ihlo, ihhi]
      rfl

theorem gates_lift (T : MuxTree n) : T.lift.gates = T.gates := by
  induction T with
  | leaf b => rfl
  | mux i lo hi ihlo ihhi => simp only [lift, gates, ihlo, ihhi]

end MuxTree

open MuxTree

/-- **Every Boolean function is a Fredkin network** with at most `2ⁿ − 1` gates (Shannon
    expansion on the first input, then induction). -/
theorem fredkin_complete : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
    ∃ T : MuxTree n, T.gates + 1 ≤ 2 ^ n ∧ ∀ x, T.eval x = f x := by
  intro n
  induction n with
  | zero =>
      intro f
      refine ⟨leaf (f Fin.elim0), by simp [gates], fun x => ?_⟩
      have hx : x = Fin.elim0 := funext fun i => i.elim0
      simp [eval, hx]
  | succ n ih =>
      intro f
      obtain ⟨T0, hg0, h0⟩ := ih (fun y => f (Fin.cons false y))
      obtain ⟨T1, hg1, h1⟩ := ih (fun y => f (Fin.cons true y))
      refine ⟨mux 0 T0.lift T1.lift, ?_, fun x => ?_⟩
      · simp only [gates, gates_lift, pow_succ]
        omega
      · rw [eval_mux, eval_lift, eval_lift, h0, h1]
        have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
        cases hx0 : x 0
        · simp only [Bool.false_eq_true, ↓reduceIte]
          conv_rhs => rw [hx, hx0]
        · simp only [↓reduceIte]
          conv_rhs => rw [hx, hx0]

/-- **The substrate computes every Boolean function with admissible gates.** For every `f`
    there is a Fredkin network computing it, and on every input every register the network
    passes through a gate comes out as a ZFA-closed history (count-balanced and, by the
    keystone, Pauli-closed). -/
theorem substrate_computes (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ T : MuxTree n, T.gates + 1 ≤ 2 ^ n ∧ (∀ x, T.eval x = f x) ∧
      ∀ x, ∀ r ∈ T.registers x,
        ∃ p : PauliScalar, twistMatrixFold (encode (fredkin r)) = pauliScalarToMatrix p := by
  obtain ⟨T, hg, hT⟩ := fredkin_complete n f
  exact ⟨T, hg, hT, fun _ r _ => fredkin_preserves_zfa r⟩

/-! ## 2. The twist layer alone generates a finite group -/

instance : Finite PauliScalar :=
  Finite.of_surjective
    (fun i : Fin 4 => match i with
      | 0 => PauliScalar.one | 1 => PauliScalar.i | 2 => PauliScalar.negOne | 3 => PauliScalar.negI)
    (by intro p; cases p
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩)

instance : Finite Axis :=
  Finite.of_surjective
    (fun i : Fin 4 => match i with
      | 0 => Axis.I | 1 => Axis.X | 2 => Axis.Y | 3 => Axis.Z)
    (by intro a; cases a
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩)

/-- The sixteen matrices `{±1, ±i} · {I, σx, σy, σz}`. -/
noncomputable def pauliGroup : Set M :=
  Set.range (fun pa : PauliScalar × Axis => coePS pa.1 • axisMatrix pa.2)

theorem pauliGroup_finite : pauliGroup.Finite := Set.finite_range _

/-- **Every twist history folds into the sixteen-element Pauli group**, however long. -/
theorem twist_fold_mem (ts : List Twist) : twistMatrixFold ts ∈ pauliGroup := by
  obtain ⟨p, hp⟩ := nf_decomp ts
  exact ⟨(p, axisProd ts), hp.symm⟩

/-- **The twist layer reaches only finitely many gates.** -/
theorem twist_folds_finite : (Set.range twistMatrixFold).Finite :=
  pauliGroup_finite.subset (by rintro _ ⟨ts, rfl⟩; exact twist_fold_mem ts)

/-! ## 3. Integer-weighted Forms supply a rotation of infinite order -/

/-- `(3 + 4i)/5`, the unit Gaussian rational from the Pythagorean triple `3, 4, 5`. -/
noncomputable def z : ℂ := ⟨3 / 5, 4 / 5⟩

/-- Its conjugate `(3 − 4i)/5`. -/
noncomputable def zbar : ℂ := ⟨3 / 5, -4 / 5⟩

/-- The rotation `diag((3+4i)/5, (3−4i)/5)` about the `z` axis, by angle `2·arccos(3/5)`. -/
noncomputable def rotation : M := Matrix.diagonal ![z, zbar]

/-- The pure Form `x̂`. -/
noncomputable def xhat : Form := ⟨0, 1, 0, 0⟩

/-- The pure Form `(3x̂ + 4ŷ)/5`: three ways along `x`, four along `y`, normalized. -/
noncomputable def tilt : Form := ⟨0, 3 / 5, 4 / 5, 0⟩

/-- **The rotation is a product of two Forms** — `sequence (action x̂) (action tilt)` in
    RhoQuCalc. -/
theorem rotation_is_form_product : xhat.toMatrix * tilt.toMatrix = rotation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Form.toMatrix, xhat, tilt, rotation, z, zbar, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal] <;>
    apply Complex.ext <;> simp <;> ring

/-- **No twist history reaches the rotation.** The `(0,0)` entry of every fold has real
    part `0` or `±1`; the rotation's has real part `3/5`. -/
theorem twist_cannot_reach_rotation (ts : List Twist) : twistMatrixFold ts ≠ rotation := by
  intro h
  obtain ⟨p, hp⟩ := nf_decomp ts
  have h00 := congrArg (fun m : M => (m 0 0).re) (hp.symm.trans h)
  generalize axisProd ts = a at h00
  cases p <;> cases a <;>
    simp [coePS, axisMatrix, σx, σy, σz, rotation, z] at h00 <;> norm_num at h00

/-- Real and imaginary parts of `(3 + 4i)ⁿ`, by the recurrence of multiplication. -/
def gauss : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (gauss n).1 - 4 * (gauss n).2, 4 * (gauss n).1 + 3 * (gauss n).2)

theorem gauss_spec (n : ℕ) :
    ((3 : ℂ) + 4 * Complex.I) ^ n = ((gauss n).1 : ℂ) + ((gauss n).2 : ℂ) * Complex.I := by
  induction n with
  | zero => simp [gauss]
  | succ n ih =>
      rw [pow_succ, ih]
      apply Complex.ext <;> simp [gauss] <;> ring

/-- `(3 + 4i)ⁿ ≡ 3 + 4i (mod 5)` for `n ≥ 1`: the real part never becomes divisible by 5. -/
theorem gauss_mod (n : ℕ) (hn : 1 ≤ n) : (gauss n).1 % 5 = 3 ∧ (gauss n).2 % 5 = 4 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [gauss]
      omega

theorem five_z : (5 : ℂ) * z = 3 + 4 * Complex.I := by
  apply Complex.ext <;> simp [z] <;> norm_num

/-- **`(3 + 4i)/5` is not a root of unity.** -/
theorem z_pow_ne_one (n : ℕ) (hn : 1 ≤ n) : z ^ n ≠ 1 := by
  intro h
  have h5 : ((3 : ℂ) + 4 * Complex.I) ^ n = (5 : ℂ) ^ n := by
    rw [← five_z, mul_pow, h, mul_one]
  rw [gauss_spec] at h5
  have hre := congrArg Complex.re h5
  simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
  have hz : (gauss n).1 = 5 ^ n := by
    have : ((5 : ℂ) ^ n).re = (5 : ℝ) ^ n := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [this] at hre
    exact_mod_cast hre
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hdiv : (5 : ℤ) ^ (k + 1) % 5 = 0 := by
    rw [pow_succ]; exact Int.mul_emod_left _ _
  have := (gauss_mod (k + 1) hn).1
  omega

theorem z_ne_zero : z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [z] at this

theorem rotation_pow_entry (n : ℕ) : (rotation ^ n) 0 0 = z ^ n := by
  simp [rotation, Matrix.diagonal_pow]

/-- **The rotation has infinite order**: its powers are pairwise distinct gates, so one
    pair of count-weighted Forms already reaches infinitely many — what the twist layer,
    with sixteen, cannot. -/
theorem rotation_powers_injective : Function.Injective (fun n : ℕ => rotation ^ n) := by
  intro m n h
  have he : z ^ m = z ^ n := by
    have := congrArg (fun A : M => A 0 0) h
    simpa [rotation_pow_entry] using this
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : z ^ m * z ^ (n - m) = z ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, he]
    exact z_pow_ne_one (n - m) (by omega) (mul_left_cancel₀ (pow_ne_zero _ z_ne_zero) this)
  · have : z ^ n * z ^ (m - n) = z ^ n * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, he]
    exact z_pow_ne_one (m - n) (by omega) (mul_left_cancel₀ (pow_ne_zero _ z_ne_zero) this)

/-- **Quantum power needs weighted ways**, packaged: the twist folds are finite, the
    rotation's powers are infinite, the rotation is a product of two count-weighted Forms,
    and no single twist history reaches it. -/
theorem quantum_power_needs_weighted_ways :
    (Set.range twistMatrixFold).Finite ∧
    (Set.range (fun n : ℕ => rotation ^ n)).Infinite ∧
    xhat.toMatrix * tilt.toMatrix = rotation ∧
    ∀ ts, twistMatrixFold ts ≠ rotation :=
  ⟨twist_folds_finite, Set.infinite_range_of_injective rotation_powers_injective,
    rotation_is_form_product, twist_cannot_reach_rotation⟩

/-! ## 4. How the substrate solves a problem posed as a closure

    A history with net imbalance is an open problem; its solutions are the continuations that
    close it. The substrate does not search for one. The minimum cost of closing is exactly
    the `ℓ¹` imbalance of the signed action (`closing_cost_lower`), the conjugate completion
    attains it (`completion_closes`, `completion_length`), and every reordering of that
    completion closes too (`completion_perm_closes`), so the problem is solved in every
    order at once at the least possible cost. Contrast `QLF_PossibilityGrowth`: a property
    `X` that is not a closure condition must be queried, candidate by candidate. -/

/-- Twists needed to cancel one axis: the excess of one sign over the other. -/
def gap (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- **The imbalance** of a history: the `ℓ¹` norm of its signed action vector. -/
def imbalance (ts : List Twist) : ℕ :=
  gap (ts.count Twist.up) (ts.count Twist.down) +
  gap (ts.count Twist.left) (ts.count Twist.right) +
  gap (ts.count Twist.slash) (ts.count Twist.backslash) +
  gap (ts.count Twist.plus) (ts.count Twist.minus)

/-- **The conjugate completion**: for each axis, the excess, written in the opposite sign. -/
def completion (ts : List Twist) : List Twist :=
  List.replicate (ts.count Twist.up - ts.count Twist.down) Twist.down ++
  List.replicate (ts.count Twist.down - ts.count Twist.up) Twist.up ++
  List.replicate (ts.count Twist.left - ts.count Twist.right) Twist.right ++
  List.replicate (ts.count Twist.right - ts.count Twist.left) Twist.left ++
  List.replicate (ts.count Twist.slash - ts.count Twist.backslash) Twist.backslash ++
  List.replicate (ts.count Twist.backslash - ts.count Twist.slash) Twist.slash ++
  List.replicate (ts.count Twist.plus - ts.count Twist.minus) Twist.minus ++
  List.replicate (ts.count Twist.minus - ts.count Twist.plus) Twist.plus

/-- Counting a twist in a repeated twist (stated with the derived `BEq`, which is not lawful). -/
theorem count_replicate_twist (n : ℕ) (s t : Twist) :
    (List.replicate n s).count t = if (s == t) = true then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    split <;> simp_all

theorem completion_length (ts : List Twist) : (completion ts).length = imbalance ts := by
  simp only [completion, imbalance, gap, List.length_append, List.length_replicate]
  omega

/-- **The completion closes the history.** -/
theorem completion_closes (ts : List Twist) : countBalanced (ts ++ completion ts) := by
  simp only [countBalanced, completion, List.count_append]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true}) [count_replicate_twist] <;> omega

/-- **Closed in full ZFA**: by the keystone, the completed history folds to a Pauli scalar. -/
theorem completion_zfa (ts : List Twist) :
    ∃ p : PauliScalar, twistMatrixFold (ts ++ completion ts) = pauliScalarToMatrix p :=
  count_balanced_pauli_closed (completion_closes ts)

/-- **Every order of the completion closes**: the solution is reached every way at once. -/
theorem completion_perm_closes (ts c : List Twist) (hc : c.Perm (completion ts)) :
    countBalanced (ts ++ c) := by
  have h := completion_closes ts
  simp only [countBalanced, List.count_append] at h ⊢
  simp only [hc.count_eq]
  exact h

/-- The eight counts of a history add up to its length. -/
theorem count_sum (c : List Twist) :
    c.count Twist.up + c.count Twist.down + c.count Twist.left + c.count Twist.right +
    c.count Twist.slash + c.count Twist.backslash + c.count Twist.plus +
    c.count Twist.minus = c.length := by
  induction c with
  | nil => rfl
  | cons t c ih =>
      cases t <;> simp (config := {decide := true}) [List.count_cons] <;> omega

/-- **No continuation closes a history in fewer steps than its imbalance.** -/
theorem closing_cost_lower (ts c : List Twist) (h : countBalanced (ts ++ c)) :
    imbalance ts ≤ c.length := by
  simp only [countBalanced, List.count_append] at h
  have hs := count_sum c
  simp only [imbalance, gap]
  omega

/-- **The cost of closing is exactly the imbalance**: the least length of a closing
    continuation. -/
theorem closing_cost_exact (ts : List Twist) :
    IsLeast {k | ∃ c : List Twist, c.length = k ∧ countBalanced (ts ++ c)} (imbalance ts) :=
  ⟨⟨completion ts, completion_length ts, completion_closes ts⟩,
    fun _ ⟨c, hk, hc⟩ => hk ▸ closing_cost_lower ts c hc⟩

/-! ## 5. Expansion and contraction: silver inflation is a discrete boost

    The octagonal quasicrystal is the projection of `ℤ[ζ₈]`; its inflation acts on `ℤ[√2]`
    as multiplication by the silver ratio `λ = 1 + √2`. A lattice point `a + b√2` has two
    projections, the physical `x = a + b√2` and the internal `x* = a − b√2`. Inflation
    multiplies `x` by `λ > 1` and `x*` by `λ* = 1 − √2`, with `|λ*| < 1` and `λ·λ* = −1`
    (`silver_expands`, `silver_contracts`, `silver_unit`): one projected dimension expands
    exactly as the other contracts, and the product `x·x* = a² − 2b²` changes only by sign
    (`silver_norm`). Its square preserves that indefinite form exactly (`silver_boost_norm`),
    which is what a Lorentz boost does to `t² − z²` in light-cone coordinates
    (`QLF_LorentzCover.boostZ_action`: `t+z ↦ a²(t+z)`, `t−z ↦ b²(t−z)`, `ab = 1`).
    Which of the two directions is read as "the" dimension is the projection, chosen at
    readout: statically the lattice holds both, and expansion of one is contraction of the
    other. Compare the compact case of §3, `(3+4i)/5`, which preserves `a² + b²`: the
    rotation is the elliptic member of the pair, the silver unit the hyperbolic one. -/

/-- One silver inflation step on `ℤ[√2]`, `(a + b√2)(1 + √2) = (a + 2b) + (a + b)√2`. -/
def silverStep (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + 2 * p.2, p.1 + p.2)

/-- The norm `x·x* = a² − 2b²`, an indefinite quadratic form. -/
def silverNorm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - 2 * p.2 ^ 2

/-- **Inflation reverses the norm's sign**: `λ·λ* = −1`. -/
theorem silver_norm (p : ℤ × ℤ) : silverNorm (silverStep p) = - silverNorm p := by
  simp only [silverNorm, silverStep]; ring

/-- **Two inflations preserve the indefinite form exactly**: a discrete boost. -/
theorem silver_boost_norm (p : ℤ × ℤ) :
    silverNorm (silverStep (silverStep p)) = silverNorm p := by
  rw [silver_norm, silver_norm, neg_neg]

/-- The physical projection `x = a + b√2`. -/
noncomputable def physical (p : ℤ × ℤ) : ℝ := p.1 + p.2 * Real.sqrt 2

/-- The internal projection `x* = a − b√2`. -/
noncomputable def internal (p : ℤ × ℤ) : ℝ := p.1 - p.2 * Real.sqrt 2

theorem sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- **The physical dimension expands** by the silver ratio. -/
theorem silver_expands (p : ℤ × ℤ) :
    physical (silverStep p) = (1 + Real.sqrt 2) * physical p := by
  simp only [physical, silverStep]; push_cast
  linear_combination (-(p.2 : ℝ)) * sqrt2_sq

/-- **The internal dimension contracts** by the conjugate `1 − √2`. -/
theorem silver_contracts (p : ℤ × ℤ) :
    internal (silverStep p) = (1 - Real.sqrt 2) * internal p := by
  simp only [internal, silverStep]; push_cast
  linear_combination (-(p.2 : ℝ)) * sqrt2_sq

/-- **Expansion times contraction is a unit**: `(1 + √2)(1 − √2) = −1`, with the expanding
    factor above `1` and the contracting one below `1` in size. -/
theorem silver_unit :
    (1 + Real.sqrt 2) * (1 - Real.sqrt 2) = -1 ∧ 1 < 1 + Real.sqrt 2 ∧
      |1 - Real.sqrt 2| < 1 := by
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h3 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨by linear_combination (-1 : ℝ) * sqrt2_sq, by linarith, ?_⟩
  rw [abs_lt]; constructor <;> linarith

/-- Galois conjugation `a + b√2 ↦ a − b√2`: the choice of which projection to call physical. -/
def galois (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)

/-- **The two projections are one projection read two ways**: the internal projection of a
    point is the physical projection of its conjugate. Which dimension expands and which
    contracts under the same inflation is fixed by that choice, not by the lattice. -/
theorem projection_choice (p : ℤ × ℤ) : internal p = physical (galois p) := by
  simp only [internal, physical, galois]; push_cast; ring

/-! ## 6. Quarks and gluons: colour is a qutrit Clifford structure; gluon directions add the rest

    `QLF_ColourFlux` makes colour the Weyl qutrit over `F₃²`: the eight twists are the eight
    nonzero vectors of `F₃²`, the transport group is `SL(2, 3)`, and the colour flux is the
    Heisenberg commutator phase `ω`. In quantum-computing terms that is the qutrit Pauli
    (Weyl) group and its symplectic (Clifford) action. Like the twist layer of §2, it is
    finite: every colour-transport matrix lies in the 81 matrices over `F₃`
    (`colour_transport_finite`). A finite transport group cannot be universal.

    The gluons are the continuous part. Along the Cartan gluon `g3` of `QLF_StrongAlgebra`,
    the same count-weighted rotation as §3 gives the `SU(3)` element
    `exp(iθ g3) = (1 − g3²) + (3/5) g3² + (4/5) i g3` (`gluonRotation_eq`), with determinant
    `1` (`gluonRotation_det`) and pairwise distinct powers (`gluonRotation_powers_injective`).
    So the split of §2–§3 recurs for colour: discrete colour transport is Clifford-type and
    finite, and count-weighted gluon directions supply infinite order. -/

instance : Finite QLF.ColourFlux.MatF3 :=
  Finite.of_injective (fun m : QLF.ColourFlux.MatF3 => (m.a, m.b, m.c, m.d))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl)

/-- **Colour transport is finite**: any set of `F₃` transport matrices, in particular the
    group generated by the twists `qMat` and the axis cycle `cycM`, is finite. -/
theorem colour_transport_finite (S : Set QLF.ColourFlux.MatF3) : S.Finite := Set.toFinite S

/-- The count-weighted rotation along the Cartan gluon direction `g3`. -/
noncomputable def gluonRotation : QLF.M3 := Matrix.diagonal ![z, zbar, 1]

/-- **It is `exp(iθ g3)` with `cos θ = 3/5`, `sin θ = 4/5`**, written in the gluon generator. -/
theorem gluonRotation_eq :
    gluonRotation = (1 - QLF.g3 * QLF.g3) + (3 / 5 : ℂ) • (QLF.g3 * QLF.g3) +
      ((4 / 5 : ℂ) * Complex.I) • QLF.g3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gluonRotation, QLF.g3, z, zbar, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal, Matrix.one_apply] <;>
    apply Complex.ext <;> simp <;> norm_num

theorem z_mul_zbar : z * zbar = 1 := by
  apply Complex.ext <;> simp [z, zbar] <;> norm_num

/-- **It is in `SU(3)`**: determinant `1`. -/
theorem gluonRotation_det : gluonRotation.det = 1 := by
  rw [gluonRotation, Matrix.det_diagonal, Fin.prod_univ_three]
  simp [z_mul_zbar]

/-- **It has infinite order**: its powers are pairwise distinct colour rotations. -/
theorem gluonRotation_powers_injective :
    Function.Injective (fun n : ℕ => gluonRotation ^ n) := by
  intro m n h
  have he : z ^ m = z ^ n := by
    have := congrArg (fun A : QLF.M3 => A 0 0) h
    simpa [gluonRotation, Matrix.diagonal_pow] using this
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : z ^ m * z ^ (n - m) = z ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, he]
    exact z_pow_ne_one (n - m) (by omega) (mul_left_cancel₀ (pow_ne_zero _ z_ne_zero) this)
  · have : z ^ n * z ^ (m - n) = z ^ n * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, he]
    exact z_pow_ne_one (m - n) (by omega) (mul_left_cancel₀ (pow_ne_zero _ z_ne_zero) this)


/-! ## 7. Two trits, not three bits

    The eight twists are usually counted as three bits, `2³ = 8`. That count is an
    abstraction: it carries no algebra. The colour code counts them as two trits, the eight
    nonzero vectors of `F₃²` (`3² − 1 = 8`, also the number of gluons, `dim su(3)`), with the
    vacuum as `0`. Conjugate twists are opposite vectors, the four axes are the four lines
    through the origin (the projective line over `F₃`), and a closure sums to zero. -/

section Trits

open QLF.ColourFlux

/-- **Two trits, not three bits.** The vacuum (no twist) is `0 ∈ F₃²` and each twist is its
    colour vector; this is a bijection between `Option Twist` and `F₃²`, so the alphabet is
    `3² − 1 = 8` nonzero two-trit words. The three-bit count `2³ = 8` is the same number but
    carries no algebra; the two-trit code carries the colour flux (`QLF_ColourFlux`). -/
def tritCode : Option Twist → V
  | none => (0, 0)
  | some t => colVec t

theorem tritCode_injective : Function.Injective tritCode := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some u => exact absurd h.symm (colVec_ne_zero u)
  | some t => cases b with
    | none => exact absurd h (colVec_ne_zero t)
    | some u => rw [colVec_injective t u h]

theorem tritCode_surjective : Function.Surjective tritCode := by
  intro v
  by_cases hv : v = (0, 0)
  · exact ⟨none, hv.symm⟩
  · obtain ⟨t, -, ht⟩ := List.mem_map.mp (colVec_surjective v hv)
    exact ⟨some t, ht⟩

/-- The colour sum of a history, letter by letter. -/
theorem colSum_eq (ts : List Twist) : (ts.map colVec).sum =
    ts.count Twist.up • colVec Twist.up + ts.count Twist.down • colVec Twist.down +
    ts.count Twist.left • colVec Twist.left + ts.count Twist.right • colVec Twist.right +
    ts.count Twist.slash • colVec Twist.slash + ts.count Twist.backslash • colVec Twist.backslash +
    ts.count Twist.plus • colVec Twist.plus + ts.count Twist.minus • colVec Twist.minus := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases t <;> simp (config := {decide := true}) [List.count_cons, add_smul] <;> abel

/-- **A closure sums to zero in `F₃²`**: conjugate twists are opposite vectors. -/
theorem closure_trits_zero (ts : List Twist) (h : countBalanced ts) :
    (ts.map colVec).sum = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [colSum_eq, h1, h2, h3, h4]
  have e1 : colVec Twist.up = - colVec Twist.down := by decide
  have e2 : colVec Twist.left = - colVec Twist.right := by decide
  have e3 : colVec Twist.slash = - colVec Twist.backslash := by decide
  have e4 : colVec Twist.plus = - colVec Twist.minus := by decide
  rw [e1, e2, e3, e4]
  simp only [smul_neg]
  abel

/-- **The converse fails**: `^^^` sums to zero mod 3 but is not a closure. The two-trit sum is a
    necessary condition, coarser than count balance. -/
theorem trits_weaker : ([Twist.up, Twist.up, Twist.up].map colVec).sum = 0 ∧
    ¬ countBalanced [Twist.up, Twist.up, Twist.up] := by
  refine ⟨by decide, ?_⟩
  intro h; exact absurd h.1 (by decide)

end Trits


/-! ## 8. The past as an event trigger

    Jim (2026-11-25): selection of a past history as a fabrication determining the future;
    "it is event triggers". An open history is a trigger: it fires an event (a closure) when
    a continuation supplies the conjugates of its excess. The theorems below show the trigger
    is the **record**, the net signed action, not the history. Any two pasts with the same
    record close under exactly the same continuations, have the same minimal completion, and
    so trigger the same events; a different past with the same record (a fabricated one) is
    indistinguishable to every future. And the record fixes *what* the minimal future
    contains, leaving only the order open, which is the runtime part. -/

section Triggers


/-- **Two pasts with the same record**: the same net signed action on every axis. -/
def sameRecord (p q : List Twist) : Prop :=
  ((p.count Twist.up : ℤ) - p.count Twist.down = (q.count Twist.up : ℤ) - q.count Twist.down) ∧
  ((p.count Twist.left : ℤ) - p.count Twist.right = (q.count Twist.left : ℤ) - q.count Twist.right) ∧
  ((p.count Twist.slash : ℤ) - p.count Twist.backslash =
    (q.count Twist.slash : ℤ) - q.count Twist.backslash) ∧
  ((p.count Twist.plus : ℤ) - p.count Twist.minus = (q.count Twist.plus : ℤ) - q.count Twist.minus)

/-- **The future depends on the past only through its record.** Any continuation closes one
    past iff it closes the other. -/
theorem future_depends_only_on_record (p q : List Twist) (h : sameRecord p q) (c : List Twist) :
    countBalanced (p ++ c) ↔ countBalanced (q ++ c) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [countBalanced, List.count_append]
  constructor <;> rintro ⟨e1, e2, e3, e4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **The same record triggers the same minimal future.** -/
theorem completion_depends_only_on_record (p q : List Twist) (h : sameRecord p q) :
    completion p = completion q := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have a1 : p.count Twist.up - p.count Twist.down = q.count Twist.up - q.count Twist.down := by omega
  have a2 : p.count Twist.down - p.count Twist.up = q.count Twist.down - q.count Twist.up := by omega
  have a3 : p.count Twist.left - p.count Twist.right = q.count Twist.left - q.count Twist.right := by omega
  have a4 : p.count Twist.right - p.count Twist.left = q.count Twist.right - q.count Twist.left := by omega
  have a5 : p.count Twist.slash - p.count Twist.backslash =
      q.count Twist.slash - q.count Twist.backslash := by omega
  have a6 : p.count Twist.backslash - p.count Twist.slash =
      q.count Twist.backslash - q.count Twist.slash := by omega
  have a7 : p.count Twist.plus - p.count Twist.minus = q.count Twist.plus - q.count Twist.minus := by omega
  have a8 : p.count Twist.minus - p.count Twist.plus = q.count Twist.minus - q.count Twist.plus := by omega
  simp only [completion, a1, a2, a3, a4, a5, a6, a7, a8]

/-- What the conjugate completion contains, twist by twist. -/
theorem completion_counts (ts : List Twist) :
    (completion ts).count Twist.up = ts.count Twist.down - ts.count Twist.up ∧
    (completion ts).count Twist.down = ts.count Twist.up - ts.count Twist.down ∧
    (completion ts).count Twist.left = ts.count Twist.right - ts.count Twist.left ∧
    (completion ts).count Twist.right = ts.count Twist.left - ts.count Twist.right ∧
    (completion ts).count Twist.slash = ts.count Twist.backslash - ts.count Twist.slash ∧
    (completion ts).count Twist.backslash = ts.count Twist.slash - ts.count Twist.backslash ∧
    (completion ts).count Twist.plus = ts.count Twist.minus - ts.count Twist.plus ∧
    (completion ts).count Twist.minus = ts.count Twist.plus - ts.count Twist.minus := by
  simp only [completion, List.count_append, count_replicate_twist]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true})

/-- One axis cannot be closed in fewer twists than its gap. -/
theorem gap_le (a b x y : ℕ) (h : a + x = b + y) : gap a b ≤ x + y := by
  simp only [gap]; omega

/-- At the minimum, the axis is closed by conjugates only. -/
theorem gap_eq_split (a b x y : ℕ) (h : a + x = b + y) (he : gap a b = x + y) :
    x = b - a ∧ y = a - b := by
  simp only [gap] at he; omega

/-- **The record fixes the content of the minimal future.** Every shortest closing continuation
    contains exactly the twists of the conjugate completion; only their order is open. -/
theorem minimal_future_is_completion (ts c : List Twist) (h : countBalanced (ts ++ c))
    (hlen : c.length = imbalance ts) (t : Twist) : c.count t = (completion ts).count t := by
  simp only [countBalanced, List.count_append] at h
  obtain ⟨b1, b2, b3, b4⟩ := h
  have hs := count_sum c
  have l1 := gap_le _ _ _ _ b1
  have l2 := gap_le _ _ _ _ b2
  have l3 := gap_le _ _ _ _ b3
  have l4 := gap_le _ _ _ _ b4
  simp only [imbalance] at hlen
  obtain ⟨u1, d1⟩ := gap_eq_split _ _ _ _ b1 (by omega)
  obtain ⟨u2, d2⟩ := gap_eq_split _ _ _ _ b2 (by omega)
  obtain ⟨u3, d3⟩ := gap_eq_split _ _ _ _ b3 (by omega)
  obtain ⟨u4, d4⟩ := gap_eq_split _ _ _ _ b4 (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := completion_counts ts
  cases t
  · rw [c1, u1]
  · rw [c2, d1]
  · rw [c3, u2]
  · rw [c4, d2]
  · rw [c5, u3]
  · rw [c6, d3]
  · rw [c7, u4]
  · rw [c8, d4]

/-- **A fabricated past works as well as the real one**: `^` and `^<>` are different histories with
    the same record, so they trigger the same futures. -/
theorem fabricated_past :
    sameRecord [Twist.up] [Twist.up, Twist.left, Twist.right] ∧
    [Twist.up] ≠ [Twist.up, Twist.left, Twist.right] := by
  refine ⟨?_, by decide⟩
  simp (config := {decide := true}) [sameRecord]

end Triggers


/-! ## 9. An entangling gate from a joint closure, and the Hadamard as a Form

    Each strand is a qubit whose basis states are "carries a closed pair" (`1`) or "carries
    nothing" (`0`), as a Fredkin line carries a ball or not. Strand A's pair is `> <`, strand
    B's is `^ v`. Closing them jointly (interleaved) rather than separately multiplies the fold
    by `(−1)^{ab}` (`joint_closure_is_cz`): the controlled-Z phase, which is entangling
    (`cz_entangling`). With the Hadamard, itself a Form (`hadamardForm`, `hadamard_sq`,
    `hadamard_swaps`), controlled-Z gives CNOT, and CNOT with dense single-qubit rotations is
    universal (Barenco et al. 1995, cited). -/

section JointGate

/-- Strand A carries the x-pair `> <` when `a`; strand B carries the y-pair `^ v` when `b`. -/
def separated (a b : Bool) : List Twist :=
  (if a then [Twist.right, Twist.left] else []) ++ (if b then [Twist.up, Twist.down] else [])

/-- The joint history: the two strands' pairs interleaved, `> ^ < v` when both are present. -/
def interleaved (a b : Bool) : List Twist :=
  (if a then [Twist.right] else []) ++ (if b then [Twist.up] else []) ++
  (if a then [Twist.left] else []) ++ (if b then [Twist.down] else [])

/-- **A joint closure applies the controlled-Z phase.** Interleaving the strands multiplies the fold
    by `−1` exactly when both carry a pair, because `σx` and `σy` anticommute: the relative phase
    between joint and separate closure is `(−1)^{ab}`. -/
theorem joint_closure_is_cz (a b : Bool) :
    twistMatrixFold (interleaved a b) =
      (if a && b then (-1 : ℂ) else 1) • twistMatrixFold (separated a b) := by
  cases a <;> cases b <;>
    simp [interleaved, separated, twistMatrixFold, Twist.toMatrix] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σx, σy, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every joint history is a closure, whatever the strands carry. -/
theorem interleaved_closes (a b : Bool) : countBalanced (interleaved a b) := by
  cases a <;> cases b <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Two-qubit operators on the basis `|ab⟩`. -/
abbrev M4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The controlled-Z gate, `diag(1, 1, 1, −1)`. -/
noncomputable def cz : M4 := Matrix.diagonal fun p => if p = (1, 1) then -1 else 1

/-- **Controlled-Z is entangling**: it is not a tensor product of single-qubit operators, since
    `(A₀₀B₀₀)(A₁₁B₁₁) = (A₀₀B₁₁)(A₁₁B₀₀)` would force `−1 = 1`. -/
theorem cz_entangling (A B : M) : Matrix.kroneckerMap (· * ·) A B ≠ cz := by
  intro h
  have e1 := congrFun (congrFun h (0, 0)) (0, 0)
  have e2 := congrFun (congrFun h (0, 1)) (0, 1)
  have e3 := congrFun (congrFun h (1, 0)) (1, 0)
  have e4 := congrFun (congrFun h (1, 1)) (1, 1)
  simp [cz, Matrix.kroneckerMap_apply, Matrix.diagonal] at e1 e2 e3 e4
  have : (A 0 0 * B 0 0) * (A 1 1 * B 1 1) = (A 0 0 * B 1 1) * (A 1 1 * B 0 0) := by ring
  rw [e1, e2, e3, e4] at this
  norm_num at this

/-- **The Hadamard is a Form**: `(σx + σz)/√2`, an equal superposition of two twist axes. -/
noncomputable def hadamardForm : Form := ⟨0, 1 / Real.sqrt 2, 0, 1 / Real.sqrt 2⟩

/-- It is its own inverse (a unitary reflection). -/
theorem hadamard_sq : hadamardForm.toMatrix * hadamardForm.toMatrix = 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardForm, Form.toMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp <;> field_simp <;> linarith

/-- **It is a Clifford gate**: it exchanges the `z` and `x` twist axes, `H σz H = σx`. -/
theorem hadamard_swaps : hadamardForm.toMatrix * σz * hadamardForm.toMatrix = σx := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardForm, Form.toMatrix, σz, σx, Matrix.mul_apply, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp <;> field_simp <;> linarith

end JointGate


/-! ## 10. The boost on twist histories: the silver DNA

    §5 put the silver boost on the ring `ℤ[√2]`. Here it acts on twist histories themselves.
    Lay the twists on the octagon `^ > / + v < \ −` and replace each by itself flanked by its
    neighbours (`silverSub`, from `ZFA_DNA.md` §12). The substitution preserves closure
    (`silverDNA_closes`), multiplies a history's physical octagonal vector `Σ ζ₈^p` by
    `1 + √2` (`silverDNA_vec`) and its internal vector `Σ ζ₈^{3p}` by `1 − √2`
    (`silverDNA_int`). So one closure-preserving operation on histories expands one projected
    dimension and contracts the other: the boost is a substrate operation. -/

section SilverDNA


/-- Octagon position, order `^ > / + v < \ −`. -/
def octPos : Twist → ℕ
  | Twist.up => 0 | Twist.right => 1 | Twist.slash => 2 | Twist.plus => 3
  | Twist.down => 4 | Twist.left => 5 | Twist.backslash => 6 | Twist.minus => 7

/-- **The silver twist DNA**: each twist becomes itself flanked by its octagon neighbours. -/
def silverSub : Twist → List Twist
  | Twist.up => [Twist.minus, Twist.up, Twist.right]
  | Twist.right => [Twist.up, Twist.right, Twist.slash]
  | Twist.slash => [Twist.right, Twist.slash, Twist.plus]
  | Twist.plus => [Twist.slash, Twist.plus, Twist.down]
  | Twist.down => [Twist.plus, Twist.down, Twist.left]
  | Twist.left => [Twist.down, Twist.left, Twist.backslash]
  | Twist.backslash => [Twist.left, Twist.backslash, Twist.minus]
  | Twist.minus => [Twist.backslash, Twist.minus, Twist.up]

def silverDNA (h : List Twist) : List Twist := h.flatMap silverSub

/-- How the substitution moves counts. -/
theorem silverDNA_counts (h : List Twist) :
    (silverDNA h).count Twist.up = h.count Twist.minus + h.count Twist.up + h.count Twist.right ∧
    (silverDNA h).count Twist.down = h.count Twist.plus + h.count Twist.down + h.count Twist.left ∧
    (silverDNA h).count Twist.right = h.count Twist.up + h.count Twist.right + h.count Twist.slash ∧
    (silverDNA h).count Twist.left = h.count Twist.down + h.count Twist.left + h.count Twist.backslash ∧
    (silverDNA h).count Twist.slash = h.count Twist.right + h.count Twist.slash + h.count Twist.plus ∧
    (silverDNA h).count Twist.backslash = h.count Twist.left + h.count Twist.backslash + h.count Twist.minus ∧
    (silverDNA h).count Twist.plus = h.count Twist.slash + h.count Twist.plus + h.count Twist.down ∧
    (silverDNA h).count Twist.minus = h.count Twist.backslash + h.count Twist.minus + h.count Twist.up := by
  induction h with
  | nil => simp [silverDNA]
  | cons t h ih =>
    simp only [silverDNA, List.flatMap_cons, List.count_append] at ih ⊢
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih
    rw [i1, i2, i3, i4, i5, i6, i7, i8]
    cases t <;> simp (config := {decide := true}) [silverSub, List.count_cons] <;> omega

/-- **It preserves closure**: the neighbours of a conjugate are the conjugates of the neighbours. -/
theorem silverDNA_closes (h : List Twist) (hb : countBalanced h) : countBalanced (silverDNA h) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := silverDNA_counts h
  obtain ⟨b1, b2, b3, b4⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- `ζ₈ = e^{iπ/4}`, the `T`-gate phase. -/
noncomputable def zeta8 : ℂ := ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩

theorem zeta8_sq : zeta8 ^ 2 = Complex.I := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · simp [zeta8, pow_two]
  · simp [zeta8, pow_two]; nlinarith

/-- The physical octagonal vector of a twist, `ζ₈^p`. -/
noncomputable def octVec (t : Twist) : ℂ := zeta8 ^ octPos t

noncomputable def vecSum (h : List Twist) : ℂ := (h.map octVec).sum

theorem zeta8_add_inv : zeta8 + zeta8 ^ 7 = (Real.sqrt 2 : ℂ) := by
  have h7 : zeta8 ^ 7 = - Complex.I * zeta8 := by
    rw [show 7 = 2 * 3 + 1 by rfl, pow_succ, pow_mul, zeta8_sq]; simp [Complex.I_pow_three]
  rw [h7]; apply Complex.ext <;> simp [zeta8]

/-- One twist's image scales its physical vector by the silver ratio. -/
theorem silverSub_vec (t : Twist) :
    ((silverSub t).map octVec).sum = (1 + Real.sqrt 2) * octVec t := by
  have h8 : zeta8 ^ 8 = 1 := by rw [show 8 = 2 * 4 by rfl, pow_mul, zeta8_sq, Complex.I_pow_four]
  rw [← zeta8_add_inv]
  cases t <;> simp only [silverSub, octVec, octPos, List.map, List.sum_cons, List.sum_nil, add_zero]
  · linear_combination (0 : ℂ) * h8
  · linear_combination (-zeta8 ^ 3) * h8
  · linear_combination (-zeta8 ^ 4) * h8
  · linear_combination (-zeta8 ^ 0) * h8
  · linear_combination (-zeta8 ^ 1) * h8
  · linear_combination (-zeta8 ^ 5) * h8
  · linear_combination (-zeta8 ^ 2) * h8
  · linear_combination (-(zeta8 ^ 6 + 1)) * h8

/-- **The silver DNA scales the octagonal vector by the silver ratio.** -/
theorem silverDNA_vec (h : List Twist) : vecSum (silverDNA h) = (1 + Real.sqrt 2) * vecSum h := by
  induction h with
  | nil => simp [silverDNA, vecSum]
  | cons t h ih =>
    simp only [silverDNA, vecSum, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [silverSub_vec, ih]; ring

/-- Internal position `3p mod 8`: the octagon read through `zeta8 ↦ zeta8³`. -/
def intExp : Twist → ℕ
  | Twist.up => 0 | Twist.right => 3 | Twist.slash => 6 | Twist.plus => 1
  | Twist.down => 4 | Twist.left => 7 | Twist.backslash => 2 | Twist.minus => 5

noncomputable def intVec (t : Twist) : ℂ := zeta8 ^ intExp t

noncomputable def intSum (h : List Twist) : ℂ := (h.map intVec).sum

theorem zeta8_35 : zeta8 ^ 3 + zeta8 ^ 5 = -(Real.sqrt 2 : ℂ) := by
  have h4 : zeta8 ^ 4 = -1 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, zeta8_sq, Complex.I_sq]
  linear_combination (zeta8 ^ 3 + zeta8) * h4 + (-1 : ℂ) * zeta8_add_inv

/-- One twist's image scales its internal vector by `1 − √2`. -/
theorem silverSub_int (t : Twist) :
    ((silverSub t).map intVec).sum = (1 - Real.sqrt 2) * intVec t := by
  have h8 : zeta8 ^ 8 = 1 := by rw [show 8 = 2 * 4 by rfl, pow_mul, zeta8_sq, Complex.I_pow_four]
  have hc : (1 : ℂ) - (Real.sqrt 2 : ℂ) = 1 + zeta8 ^ 3 + zeta8 ^ 5 := by rw [add_assoc, zeta8_35]; ring
  rw [hc]
  cases t <;> simp only [silverSub, intVec, intExp, List.map, List.sum_cons, List.sum_nil, add_zero]
  · linear_combination (0 : ℂ) * h8
  · linear_combination (-zeta8) * h8
  · linear_combination (-zeta8 ^ 4 - zeta8 ^ 2) * h8
  · linear_combination (-1 : ℂ) * h8
  · linear_combination (-zeta8 ^ 3 - zeta8) * h8
  · linear_combination (0 : ℂ) * h8
  · linear_combination (0 : ℂ) * h8
  · linear_combination (-zeta8 ^ 2 - 1) * h8

/-- **The same substitution contracts the internal vector** by `1 − √2`. -/
theorem silverDNA_int (h : List Twist) : intSum (silverDNA h) = (1 - Real.sqrt 2) * intSum h := by
  induction h with
  | nil => simp [silverDNA, intSum]
  | cons t h ih =>
    simp only [silverDNA, intSum, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [silverSub_int, ih]; ring

end SilverDNA

-- ==========================================
-- 11. Superposition is alternate histories
-- ==========================================

/-! A superposition is a sum over alternate histories: each history contributes its fold,
and the amplitude is the census sum. Integer Form weights are signed counts of one-twist
histories, and the infinite-order rotation of §3 is the census sum of seven alternate
histories (three empty, four `>^`) divided by the census norm `5`. -/

section Superposition

noncomputable def censusSum (hs : List (List Twist)) : M := (hs.map twistMatrixFold).sum

theorem censusSum_append (a b : List (List Twist)) :
    censusSum (a ++ b) = censusSum a + censusSum b := by
  simp [censusSum]

theorem censusSum_replicate (k : ℕ) (h : List Twist) :
    censusSum (List.replicate k h) = (k : ℂ) • twistMatrixFold h := by
  simp [censusSum, List.map_replicate, List.sum_replicate, Nat.cast_smul_eq_nsmul]

theorem fold_single (t : Twist) : twistMatrixFold [t] = t.toMatrix := by
  simp [twistMatrixFold]

theorem fold_nil : twistMatrixFold [] = 1 := by simp [twistMatrixFold]

def signed (n : ℤ) (pos neg : Twist) : List (List Twist) :=
  if 0 ≤ n then List.replicate n.toNat [pos] else List.replicate (-n).toNat [neg]

theorem censusSum_signed (n : ℤ) (pos neg : Twist) (h : neg.toMatrix = -pos.toMatrix) :
    censusSum (signed n pos neg) = (n : ℂ) • pos.toMatrix := by
  unfold signed
  split_ifs with hn
  · rw [censusSum_replicate, fold_single]
    congr 1
    have h2 : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn
    conv_rhs => rw [← h2]
    norm_cast
  · rw [censusSum_replicate, fold_single, h, smul_neg, ← neg_smul]
    congr 1
    have : (((-n).toNat : ℤ) : ℂ) = ((-n : ℤ) : ℂ) := by rw [Int.toNat_of_nonneg (by omega)]
    push_cast at this ⊢
    rw [this]; ring

theorem integer_form_is_census_sum (t x y z : ℤ) :
    censusSum (signed t Twist.plus Twist.minus ++ signed x Twist.right Twist.left ++
      signed y Twist.up Twist.down ++ signed z Twist.slash Twist.backslash) =
      (Form.toMatrix ⟨t, x, y, z⟩) := by
  simp only [censusSum_append]
  rw [censusSum_signed _ _ _ (by simp [Twist.toMatrix]), censusSum_signed _ _ _ (by simp [Twist.toMatrix]),
    censusSum_signed _ _ _ (by simp [Twist.toMatrix]), censusSum_signed _ _ _ (by simp [Twist.toMatrix])]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Twist.toMatrix, σx, σy, σz, Form.toMatrix] <;> ring

theorem five_rotation_census :
    censusSum (List.replicate 3 [] ++ List.replicate 4 [Twist.right, Twist.up]) =
      (5 : ℂ) • rotation := by
  rw [censusSum_append, censusSum_replicate, censusSum_replicate, fold_nil]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [twistMatrixFold, Twist.toMatrix, σx, σy, rotation, z, zbar] <;> apply Complex.ext <;> simp <;> norm_num

theorem alternate_histories_cancel :
    censusSum [[Twist.plus], [Twist.minus]] = 0 := by
  simp [censusSum, twistMatrixFold, Twist.toMatrix]

/-- Three alternate histories, two empty and one folding to `iI`, sum to `(2 + i)·I`. -/
theorem gauss_census :
    censusSum [[], [], [Twist.right, Twist.up, Twist.slash]] = (2 + Complex.I) • (1 : M) := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [censusSum, twistMatrixFold, Twist.toMatrix, σx, σy, σz] <;> ring

/-- Its mirror: flip one twist, and the same three alternatives sum to `(2 − i)·I`. -/
theorem gauss_census_mirror :
    censusSum [[], [], [Twist.left, Twist.up, Twist.slash]] = (2 - Complex.I) • (1 : M) := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [censusSum, twistMatrixFold, Twist.toMatrix, σx, σy, σz] <;> ring

/-- **The 5 is a ratio of alternatives to their mirror**: `(3+4i)/5 = (2+i)/(2−i)`. -/
theorem z_eq_ratio : z = (2 + Complex.I) / (2 - Complex.I) := by
  have h : (2 - Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [eq_div_iff h]
  apply Complex.ext <;> simp [z] <;> norm_num

/-- The 5 is the Born weight of the three alternatives: `|2 + i|² = 5`. -/
theorem gauss_normSq : Complex.normSq (2 + Complex.I) = 5 := by
  rw [Complex.normSq_apply]; simp; norm_num

end Superposition


-- ==========================================
-- 12. Clifford+T: H·T has infinite order
-- ==========================================

/-! The Hadamard and the `T = diag(1, ζ₈)` gate both have entries in `ℤ[ζ₈, 1/√2]`, the
octagonal ring of §6. Their product has infinite order. Proof: if `(HT)ⁿ` were scalar, the
ratio `ρ` of its eigenvalues would be a root of unity, so `ρ + ρ⁻¹` would be an algebraic
integer; but `ρ + ρ⁻¹ = −1 − √2/2`, and then `1/2 = (√2/2)²` would be an algebraic integer. -/

section CliffordT

/-- The Hadamard gate. -/
noncomputable def hadamard : M := (1 / (Real.sqrt 2 : ℂ)) • !![1, 1; 1, -1]

/-- The T gate, `diag(1, ζ₈)`. -/
noncomputable def tGate : M := !![1, 0; 0, zeta8]

/-- `√2 · H · T`, entries in `ℤ[ζ₈]`. -/
noncomputable def hT : M := !![1, zeta8; 1, -zeta8]

theorem hadamard_tGate : hadamard * tGate = (1 / (Real.sqrt 2 : ℂ)) • hT := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, tGate, hT, Matrix.mul_apply, Fin.sum_univ_two]

/-- Cayley–Hamilton powers of a 2×2 matrix through its eigenvalues. -/
theorem pow_two_by_two (A : M) (l1 l2 : ℂ) (htr : A 0 0 + A 1 1 = l1 + l2)
    (hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = l1 * l2) (n : ℕ) :
    (l1 - l2) • A ^ n = (l1 ^ n - l2 ^ n) • A + (l1 * l2 ^ n - l2 * l1 ^ n) • (1 : M) := by
  have ch : A * A = (l1 + l2) • A - (l1 * l2) • (1 : M) := by
    rw [← htr, ← hdet]
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← smul_mul_assoc, ih, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ch]
    module

theorem half_not_integral : ¬ IsIntegral ℤ ((1 : ℂ) / 2) := by
  intro h
  have h1 : ((1 : ℂ) / 2) = algebraMap ℚ ℂ (1 / 2) := by simp
  rw [h1, isIntegral_algebraMap_iff,
    IsIntegrallyClosed.isIntegral_iff] at h
  obtain ⟨y, hy⟩ := h
  have : (2 * y : ℚ) = 1 := by
    have : (algebraMap ℤ ℚ y) = (y : ℚ) := rfl
    rw [this] at hy; rw [hy]; norm_num
  have : 2 * y = 1 := by exact_mod_cast this
  omega

theorem rootOfUnity_integral (r : ℂ) (n : ℕ) (hn : 0 < n) (h : r ^ n = 1) : IsIntegral ℤ r :=
  IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)

theorem zeta8_ne_zero : zeta8 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [zeta8] at this

theorem sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'

theorem sqrt2_mul_zeta8 : (Real.sqrt 2 : ℂ) * zeta8 = 1 + Complex.I := by
  apply Complex.ext <;> simp [zeta8] <;> nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- **`H·T` has infinite order**: no positive power is a scalar. -/
theorem hT_pow_ne_scalar (n : ℕ) (hn : 1 ≤ n) (c : ℂ) : hT ^ n ≠ c • (1 : M) := by
  intro hc
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((1 - zeta8) ^ 2 - 4 * (-2 * zeta8))
    (by norm_num : 0 < 2)
  have hz2 := zeta8_sq
  have hsq := sqrt2_mul_zeta8
  have r2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  set l1 := (1 - zeta8 + s) / 2
  set l2 := (1 - zeta8 - s) / 2
  have htr : hT 0 0 + hT 1 1 = l1 + l2 := by simp [hT, l1, l2]; ring
  have hdet : hT 0 0 * hT 1 1 - hT 0 1 * hT 1 0 = l1 * l2 := by
    simp only [hT, l1, l2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (1/4 : ℂ) * hs
  have key := congrArg (fun A : M => A 0 1) (pow_two_by_two hT l1 l2 htr hdet n)
  simp only [hc, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply] at key
  simp [hT] at key
  -- key : (l1 ^ n - l2 ^ n) * zeta8 = 0 (up to form)
  have hpow : l1 ^ n = l2 ^ n := by
    rcases key with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h zeta8_ne_zero
  have hprod : l1 * l2 = -2 * zeta8 := by
    simp only [l1, l2]; linear_combination (-1/4 : ℂ) * hs
  have hδ : -2 * zeta8 ≠ 0 := by simp [zeta8_ne_zero]
  have hl2 : l2 ≠ 0 := by intro h; rw [h, mul_zero] at hprod; exact hδ hprod.symm
  have hl1 : l1 ≠ 0 := by intro h; rw [h, zero_mul] at hprod; exact hδ hprod.symm
  set ρ := l1 / l2
  have hρ : ρ ^ n = 1 := by simp [ρ, div_pow, hpow, pow_ne_zero n hl2]
  have hρi : ρ⁻¹ ^ n = 1 := by rw [inv_pow, hρ, inv_one]
  have hint : IsIntegral ℤ (ρ + ρ⁻¹) :=
    (rootOfUnity_integral ρ n (by omega) hρ).add (rootOfUnity_integral ρ⁻¹ n (by omega) hρi)
  have hval : ρ + ρ⁻¹ = -1 - (Real.sqrt 2 : ℂ) / 2 := by
    have e1 : ρ + ρ⁻¹ = (l1 + l2) ^ 2 / (l1 * l2) - 2 := by
      simp only [ρ]; field_simp; ring
    rw [e1, hprod]
    have : l1 + l2 = 1 - zeta8 := by simp only [l1, l2]; ring
    rw [this]
    have hz := zeta8_ne_zero
    field_simp
    linear_combination (-1 : ℂ) * hz2 + hsq
  rw [hval] at hint
  have h2 : IsIntegral ℤ ((Real.sqrt 2 : ℂ) / 2) := by
    have e : (Real.sqrt 2 : ℂ) / 2 = -1 - (-1 - (Real.sqrt 2 : ℂ) / 2) := by ring
    rw [e]; exact (isIntegral_one (R := ℤ) (B := ℂ)).neg.sub hint
  have h3 : IsIntegral ℤ ((1 : ℂ) / 2) := by
    have := h2.mul h2
    rwa [div_mul_div_comm, r2, show (2:ℂ) * 2 = 4 by norm_num,
      show (2:ℂ) / 4 = 1 / 2 by norm_num] at this
  exact half_not_integral h3

/-- **`H·T` has infinite order** on the qubit itself: no positive power is a scalar. -/
theorem hadamard_t_infinite_order (n : ℕ) (hn : 1 ≤ n) (c : ℂ) :
    (hadamard * tGate) ^ n ≠ c • (1 : M) := by
  intro h
  rw [hadamard_tGate, smul_pow] at h
  apply hT_pow_ne_scalar n hn ((Real.sqrt 2 : ℂ) ^ n * c)
  calc hT ^ n = ((Real.sqrt 2 : ℂ) ^ n) • ((1 / (Real.sqrt 2 : ℂ)) ^ n • hT ^ n) := by
        rw [smul_smul, ← mul_pow, mul_one_div_cancel sqrt2_ne, one_pow, one_smul]
    _ = ((Real.sqrt 2 : ℂ) ^ n * c) • (1 : M) := by rw [h, smul_smul]

end CliffordT

-- ==========================================
-- 13. Dense angles
-- ==========================================

/-! The rotation of §3 is `diag(z, z̄)` with `z = (3+4i)/5 = exp(iθ)`. Since no power of `z`
is `1`, `θ/2π` is irrational, so the angles `kθ` are dense on the circle (Mathlib's
`AddCircle.denseRange_zsmul_coe_iff`): count-weighted ways reach every phase about one axis
to any precision. -/

theorem norm_z : ‖z‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp [z]; norm_num

theorem z_exp : z = Complex.exp (Complex.arg z * Complex.I) := by
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [norm_z] at this; simpa using this.symm

theorem arg_z_irrational : Irrational (Complex.arg z / (2 * Real.pi)) := by
  rintro ⟨q, hq⟩
  have hpos : 0 < q.den := q.den_pos
  have hθ : (q.den : ℝ) * Complex.arg z = 2 * Real.pi * q.num := by
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    have : Complex.arg z = 2 * Real.pi * (q : ℝ) := by rw [hq]; field_simp
    rw [this, Rat.cast_def]
    field_simp
  apply z_pow_ne_one q.den hpos
  rw [z_exp, ← Complex.exp_nat_mul]
  have : (q.den : ℂ) * (Complex.arg z * Complex.I) = q.num * (2 * Real.pi * Complex.I) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hθ; push_cast at this
    linear_combination Complex.I * this
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- **The angles of the count-weighted rotation's powers are dense on the circle.** -/
theorem rotation_angles_dense :
    DenseRange (fun k : ℤ => k • (Complex.arg z : AddCircle (2 * Real.pi))) :=
  AddCircle.denseRange_zsmul_coe_iff.mpr arg_z_irrational


end QLF.QuantumComputer
