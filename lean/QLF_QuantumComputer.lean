/-
  QLF_QuantumComputer.lean — what QLF proves about the claim "the universe is a quantum
  computer", and where the proof stops.

  Write-up: Universe_Quantum_Computer.md.

  Eight results, no axioms.

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
     cited, not proved here, and the entangling gate is the open bridge (see the doc §4).

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

end QLF.QuantumComputer
