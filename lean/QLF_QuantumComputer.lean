/-
  QLF_QuantumComputer.lean — what QLF proves about the claim "the universe is a quantum
  computer", and where the proof stops.

  Write-up: Universe_Quantum_Computer.md.

  Nineteen results, no axioms.

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
     with one entangling gate are universal (Barenco et al. 1995). Density is §19; universality is
     proved in `QLF_Barenco`. The entangling gate on the substrate is §9.

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

  9. **A joint closure carries the controlled-Z sign table** (`joint_closure_is_cz`,
     `interleaved_closes`, `cz_entangling`): interleaving two strands' closed pairs multiplies
     the fold by `(−1)^{ab}`, the diagonal of controlled-Z, and controlled-Z as a matrix is not
     a product of single-qubit gates. That interleaving acts as a gate on superposed presence
     states is not shown. The Hadamard is a Form exchanging twist axes (`hadamard_sq`,
     `hadamard_swaps`); it acts on the spinor, not on the presence bit.

  10. **The boost acts on histories** (`silverDNA_closes`, `silverDNA_vec`, `silverDNA_int`):
     the silver twist DNA preserves closure, expands the physical octagonal vector by `1 + √2`
     and contracts the internal one by `1 − √2`.

  11. **Superposition is alternate histories** (`censusSum`, `censusSum_append`,
     `integer_form_is_census_sum`, `five_rotation_census`, `alternate_histories_cancel`): an
     amplitude is the sum of the folds of alternate histories; every integer Form is such a
     sum, and `5 · rotation` is the census sum of seven alternate histories, so the weights of
     §3 are counts of alternate histories. These are open histories: a closure folds to `±I`,
     so a census sum over closures alone is an integer times `I`. The division by `5` is a ratio of alternatives to their mirror:
     `z = (2+i)/(2−i)` (`z_eq_ratio`), where `2 ± i` are census sums of three alternate
     histories (`gauss_census`, `gauss_census_mirror`) and `5 = |2+i|²` (`gauss_normSq`). Without
     phase diversity the ratio is the identity (`mirror_ratio_eq_one_iff`).

  12. **H·T has infinite order** (`hT_pow_ne_scalar`, `hadamard_t_infinite_order`): no
     positive power of the Clifford+T product is a scalar.

  13. **The rotation's angles are dense** (`arg_z_irrational`, `rotation_angles_dense`): the
     powers of the §3 rotation approach every phase about its axis. Two-axis SU(2) density is
     §19; Barenco universality is `QLF_Barenco`.

  14. **No choice fixed in advance** (`ks_orthogonal`, `ks_each_twice`, `ks_double_count`,
     `no_choice_fixed_in_advance`): the Kochen–Specker theorem in Cabello's eighteen-direction
     form. No assignment of outcomes fixed beforehand, independent of context, exists.

  15. **Readings made theorems** (`presence_bit_is_fold_sign`, `presence_states_distinct`,
     `record_blind_to_phase`): the presence bit of a closed pair is its fold sign, and two
     histories with the same twists in a different order fold to opposite phases.

  16. **The halting theorem, restated** (`no_computable_superdeterministic_theory`): no
     computable predictor decides halting. This is Mathlib's theorem under another name; it is
     not a result about superdeterminism (see the write-up, §6f).

  17. **Every rational phase is alternatives over their mirror** (`rational_phase_is_mirror_ratio`):
     `(p + qi)/r` with `p² + q² = r²` equals `(a + bi)/(a − bi)` (Hilbert's Theorem 90 for `ℚ(i)`).

  18. **Memes transmit the choice, not the phase** (`copy_keeps_record`, `meme_transmits_choice`,
     `meme_does_not_transmit_phase`).

  19. **SU(2) density** (`su2_euler`, `E_mem_closure`, `euler_continuous`, `su2_dense`,
     `D_z_pow`, `D_z_inv_pow`, `rotation_mul_D_inv`): every `SU(2)` matrix is a limit of
     products of powers of the count-weighted rotation, its inverse, and the Hadamard.

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
    by `(−1)^{ab}` (`joint_closure_is_cz`): the sign table of controlled-Z, which as a matrix
    is entangling (`cz_entangling`). This compares the folds of two classical histories for
    each fixed `(a, b)`; a linear action on superposed presence states is not defined here.
    The Hadamard is a Form (`hadamardForm`, `hadamard_sq`, `hadamard_swaps`) acting on the
    spinor, not on the presence bit. -/

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

/-- **Diversity enables choice.** A set of alternatives with in-phase weight `a` and
quarter-turn weight `b`, divided by its mirror, is the identity exactly when `b = 0`. -/
theorem mirror_ratio_eq_one_iff (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    ((a : ℂ) + b * Complex.I) / ((a : ℂ) - b * Complex.I) = 1 ↔ b = 0 := by
  have hne : ((a : ℂ) - b * Complex.I) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0; have h2 := congrArg Complex.im h0
    simp at h1 h2
    rcases h with h | h
    · exact h h1
    · exact h (by linarith)
  rw [div_eq_one_iff_eq hne]
  constructor
  · intro e; have := congrArg Complex.im e; simp at this; linarith
  · intro hb; simp [hb]

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


-- ==========================================
-- 14. No choice fixed in advance (Kochen–Specker)
-- ==========================================

/-! Eighteen directions in four dimensions, in nine orthogonal bases, each direction in
exactly two bases. A choice fixed in advance would give each direction a value regardless
of which basis is measured and exactly one "yes" per basis. Counting the yeses basis by
basis gives `9`; counting direction by direction gives an even number. So no such choice
exists: in a quantum logic, choice is made in context, at the event. -/

section KochenSpecker

def ksVec : Fin 18 → Fin 4 → ℤ := ![![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![1, 1, 0, 0],
    ![1, -1, 0, 0],
    ![0, 1, 0, 0],
    ![1, 0, 1, 0],
    ![1, 0, -1, 0],
    ![1, -1, 1, -1],
    ![1, -1, -1, 1],
    ![0, 0, 1, 1],
    ![1, 1, 1, 1],
    ![0, 1, 0, -1],
    ![1, 0, 0, 1],
    ![1, 0, 0, -1],
    ![0, 1, -1, 0],
    ![1, 1, -1, 1],
    ![1, 1, 1, -1],
    ![-1, 1, 1, 1]]
def ksBasis : Fin 9 → Fin 4 → Fin 18 := ![![0, 1, 2, 3],
    ![0, 4, 5, 6],
    ![7, 8, 2, 9],
    ![7, 10, 6, 11],
    ![1, 4, 12, 13],
    ![8, 10, 13, 14],
    ![15, 16, 3, 9],
    ![15, 17, 5, 11],
    ![16, 17, 12, 14]]

/-- The nine bases are orthogonal: distinct members have zero inner product. -/
theorem ks_orthogonal : ∀ b : Fin 9, ∀ i j : Fin 4, i ≠ j →
    ∑ k : Fin 4, ksVec (ksBasis b i) k * ksVec (ksBasis b j) k = 0 := by
  decide

/-- Each of the eighteen directions lies in exactly two of the nine bases. -/
theorem ks_each_twice : ∀ v : Fin 18,
    (Finset.univ.filter (fun p : Fin 9 × Fin 4 => ksBasis p.1 p.2 = v)).card = 2 := by
  decide

/-- Double counting over the nine bases. -/
theorem ks_double_count (g : Fin 18 → ℕ) :
    ∑ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 2 * ∑ v : Fin 18, g v := by
  simp [Fin.sum_univ_succ, ksBasis]
  ring

/-- **Kochen–Specker** (Cabello, Estebaranz and García-Alcaine 1996): no assignment of
values to the eighteen directions, fixed in advance and independent of which basis is
measured, gives exactly one "yes" in every basis. -/
theorem no_choice_fixed_in_advance :
    ¬ ∃ g : Fin 18 → ℕ, ∀ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 1 := by
  rintro ⟨g, hg⟩
  have h := ks_double_count g
  simp only [hg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at h
  omega

end KochenSpecker

-- ==========================================
-- 15. Readings made theorems
-- ==========================================

/-! Two readings of the write-up, stated and proved: the presence bit of §9 is the fold
sign, and a record of counts is blind to phase. -/

section Readings

/-- **The presence bit is the fold sign.** A strand carrying the closed pair `> <` folds to
`−1`, an empty strand to `1`: presence is read off the phase, `(−1)^a`. -/
theorem presence_bit_is_fold_sign (a : Bool) :
    twistMatrixFold (if a then [Twist.right, Twist.left] else []) =
      (if a then (-1 : ℂ) else 1) • (1 : M) := by
  cases a
  · simp [twistMatrixFold]
  · apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [twistMatrixFold, Twist.toMatrix, σx, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two presence states are distinguishable by phase alone. -/
theorem presence_states_distinct :
    twistMatrixFold [Twist.right, Twist.left] ≠ twistMatrixFold [] := by
  have h1 := presence_bit_is_fold_sign true
  simp only [if_true] at h1
  rw [h1]
  simp only [twistMatrixFold, List.foldr_nil]
  intro h
  have := congrArg (fun A : M => A 0 0) h
  norm_num at this

/-- **Counts are shared, phase is private.** Two histories with exactly the same twists, a
permutation of one another, so the same record of every kind, fold to opposite phases. -/
theorem record_blind_to_phase :
    [Twist.up, Twist.left, Twist.down, Twist.right].Perm
        [Twist.up, Twist.down, Twist.left, Twist.right] ∧
      twistMatrixFold [Twist.up, Twist.left, Twist.down, Twist.right] = -1 ∧
      twistMatrixFold [Twist.up, Twist.down, Twist.left, Twist.right] = 1 := by
  refine ⟨by decide, ?_, ?_⟩ <;>
  · apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [twistMatrixFold, Twist.toMatrix, σx, σy, Matrix.mul_apply, Fin.sum_univ_two]

end Readings

-- ==========================================
-- 16. No computable superdeterministic theory
-- ==========================================

/-! Mathlib's halting theorem, restated as a predictor. It is kept because the write-up
discusses it; it does not bear on superdeterminism. A detector cannot be set by whether a
program halts (that setting is never fixed at a finite time), and the same argument would
rule out every deterministic theory. -/

section Superdeterminism

open Nat.Partrec (Code)

/-- The halting theorem as a predictor: no computable `Code → Bool` decides halting on
input `n`. The name is historical; this is not a theorem about superdeterminism. -/
theorem no_computable_superdeterministic_theory (n : ℕ) :
    ¬ ∃ predict : Code → Bool, Computable predict ∧
      ∀ c, predict c = true ↔ (Code.eval c n).Dom := by
  rintro ⟨f, hf, hiff⟩
  apply ComputablePred.halting_problem n
  rw [ComputablePred.computable_iff]
  exact ⟨f, hf, funext fun c => propext (hiff c).symm⟩

end Superdeterminism

-- ==========================================
-- 17. Normalization: every rational phase is alternatives over their mirror
-- ==========================================

section Normalization

/-- **Every rational phase is a set of alternatives over its mirror** (Hilbert 90 for
`ℚ(i)/ℚ`): a Pythagorean phase `(p + qi)/r` equals `(a + bi)/(a − bi)` for integers `a, b`. -/
theorem rational_phase_is_mirror_ratio (p q r : ℤ) (hr : r ≠ 0) (h : p ^ 2 + q ^ 2 = r ^ 2) :
    ∃ a b : ℤ, ((a : ℂ) - b * Complex.I) ≠ 0 ∧
      ((p : ℂ) + q * Complex.I) / r = ((a : ℂ) + b * Complex.I) / ((a : ℂ) - b * Complex.I) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hC : (p : ℂ) ^ 2 + (q : ℂ) ^ 2 = (r : ℂ) ^ 2 := by exact_mod_cast h
  by_cases hp : r + p = 0
  · have hp' : p = -r := by omega
    have hq : q = 0 := by
      subst hp'; have : q ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    · subst hq; rw [hp']; push_cast
      rw [div_eq_div_iff hrC (by simp)]
      ring_nf
  · refine ⟨r + p, q, ?_, ?_⟩
    · intro h0
      have := congrArg Complex.re h0
      simp at this
      exact hp (by exact_mod_cast this)
    · have hd : ((↑(r + p) : ℂ) - (q : ℂ) * Complex.I) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this
        exact hp (by exact_mod_cast this)
      rw [div_eq_div_iff hrC hd]
      push_cast
      linear_combination hC + (-(q:ℂ) ^ 2) * Complex.I_sq

end Normalization

-- ==========================================
-- 18. Memes transmit the choice, not the phase
-- ==========================================

/-! A meme is a closure's record held by more than one party (`Memetics_QLF.md` §5;
`Quantum_Knowledge_Base.md`'s redundancy `R`). A copy keeps the record, so it admits exactly
the futures the original selection admits; a copy with the same twists can still carry the
opposite phase. -/

section Memes

/-- A copy of a record, in any order, keeps the record. -/
theorem copy_keeps_record (p q : List Twist) (h : p.Perm q) : sameRecord p q := by
  simp [sameRecord, h.count_eq]

/-- **A meme transmits the choice.** A copy of a closed selection's record admits exactly the
same futures as the original. -/
theorem meme_transmits_choice (p q : List Twist) (h : p.Perm q) (c : List Twist) :
    countBalanced (p ++ c) ↔ countBalanced (q ++ c) :=
  future_depends_only_on_record p q (copy_keeps_record p q h) c

/-- **A meme does not transmit the phase.** A copy with the same twists can fold to the
opposite phase. -/
theorem meme_does_not_transmit_phase :
    ∃ p q : List Twist, p.Perm q ∧ twistMatrixFold p ≠ twistMatrixFold q := by
  obtain ⟨hperm, h1, h2⟩ := record_blind_to_phase
  refine ⟨_, _, hperm, ?_⟩
  rw [h1, h2]
  intro h
  have := congrArg (fun A : M => A 0 0) h
  norm_num at this

end Memes

-- ==========================================
-- 19. SU(2) density from the count-weighted rotation and the Hadamard
-- ==========================================

/-! Every `SU(2)` matrix has Euler angles in the form `D(e^{iα}) · H · D(e^{iβ}) · H · D(e^{iγ})`
(`su2_euler`), with `D(w) = diag(w, w̄)`. The powers of `z = (3+4i)/5` come arbitrarily close
to every phase (`E_mem_closure`), and the Euler product is continuous, so every `SU(2)` matrix
is a limit of products of powers of `rotation = D(z)`, its inverse, and the Hadamard
(`su2_dense`). This is the two-axis density step that §3 previously cited. -/

section Density

/-- A phase `e^{ix}`. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp (x * Complex.I)

theorem E_add (x y : ℝ) : E (x + y) = E x * E y := by
  simp only [E]; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem E_star (x : ℝ) : star (E x) = E (-x) := by
  simp only [E]
  rw [show (star (Complex.exp (↑x * Complex.I))) = (starRingEnd ℂ) (Complex.exp (↑x * Complex.I))
    from rfl, ← Complex.exp_conj]
  congr 1; simp [Complex.conj_ofReal]

theorem E_plus (x : ℝ) : E x + E (-x) = 2 * (Real.cos x : ℂ) := by
  simp only [E]; rw [Complex.ofReal_cos, Complex.two_cos]; push_cast; ring_nf

theorem E_minus (x : ℝ) : E x - E (-x) = 2 * (Real.sin x : ℂ) * Complex.I := by
  simp only [E]
  rw [← Complex.cos_add_sin_I, show ((-x : ℝ) : ℂ) * Complex.I = -(↑x * Complex.I) by push_cast; ring,
    ← neg_mul, ← Complex.cos_sub_sin_I]
  push_cast; ring

theorem E_pi_div_two : E (Real.pi / 2) = Complex.I := by
  simp only [E]
  rw [← Complex.cos_add_sin_I]
  push_cast
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring

theorem polar (a : ℂ) : a = (‖a‖ : ℂ) * E (Complex.arg a) := by
  simp only [E]; exact (Complex.norm_mul_exp_arg_mul_I a).symm

/-- The diagonal phase gate `diag(w, w̄)`. -/
noncomputable def D (w : ℂ) : M := Matrix.diagonal ![w, star w]

/-- The Euler product `D u · H · D v · H · D t`. -/
@[irreducible] noncomputable def euler (u v t : ℂ) : M := D u * hadamard * D v * hadamard * D t

theorem euler_eq (u v t : ℂ) : euler u v t =
    !![u * t * ((v + star v) / 2), u * star t * ((v - star v) / 2);
       star u * t * ((v - star v) / 2), star u * star t * ((v + star v) / 2)] := by
  have r2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := sqrt2_ne
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [euler, D, hadamard, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;>
    field_simp <;> rw [pow_two, r2] <;> ring


/-- **Powers of the count-weighted phase reach every phase.** -/
theorem E_mem_closure (x : ℝ) : E x ∈ closure (Set.range fun k : ℤ => z ^ k) := by
  set θ : AddCircle (2 * Real.pi) := ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))
  have hd : DenseRange (fun k : ℤ => k • θ) := rotation_angles_dense
  let g : AddCircle (2 * Real.pi) → ℂ := fun y => ((AddCircle.toCircle y : Circle) : ℂ)
  have hg : Continuous g := continuous_induced_dom.comp AddCircle.continuous_toCircle
  have h2π : ∀ y : ℝ, 2 * Real.pi / (2 * Real.pi) * y = y := by
    intro y; rw [div_self (by positivity), one_mul]
  have hθ : g θ = z := by
    simp only [g, θ, AddCircle.toCircle_apply_mk, Circle.coe_exp, h2π]
    exact z_exp.symm
  have hgk : ∀ k : ℤ, g (k • θ) = z ^ k := by
    intro k; simp only [g, AddCircle.toCircle_zsmul, Circle.coe_zpow]
    rw [← hθ]
  have hgx : g (x : AddCircle (2 * Real.pi)) = E x := by
    simp only [g, AddCircle.toCircle_apply_mk, Circle.coe_exp, E, h2π]
  have hx : (x : AddCircle (2 * Real.pi)) ∈ closure (Set.range fun k : ℤ => k • θ) := by
    rw [hd.closure_eq]; trivial
  rw [← hgx]
  exact map_mem_closure hg hx (by rintro _ ⟨k, rfl⟩; exact ⟨k, (hgk k).symm⟩)

/-- The shape of an `SU(2)` matrix: `[[a, −b̄], [b, ā]]` with `|a|² + |b|² = 1`. -/
theorem su2_shape (U : M) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U 1 1 = star (U 0 0) ∧ U 0 1 = -star (U 1 0) ∧
      Complex.normSq (U 0 0) + Complex.normSq (U 1 0) = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hU
  obtain ⟨hu, hdet⟩ := hU
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hsU
  have hadj : star U = Matrix.adjugate U := by
    rw [← hinv, Matrix.inv_def, hdet]; simp
  rw [Matrix.adjugate_fin_two] at hadj
  have e00 := congrArg (fun A : M => A 0 0) hadj
  have e01 := congrArg (fun A : M => A 1 0) hadj
  have n00 := congrArg (fun A : M => A 0 0) hsU
  simp [Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 n00
  refine ⟨e00.symm, ?_, ?_⟩
  · have := congrArg star e01; simp at this; rw [this]; simp
  · apply Complex.ofReal_injective
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    exact n00

theorem E_neg_pi_div_two : E (-(Real.pi / 2)) = -Complex.I := by
  rw [← E_star, E_pi_div_two]; simp

/-- **Euler angles.** Every `SU(2)` matrix is `D(e^{iα}) · H · D(e^{iβ}) · H · D(e^{iγ})`. -/
theorem su2_euler (U : M) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ α β γ : ℝ, U = euler (E α) (E β) (E γ) := by
  obtain ⟨h11, h01, hn⟩ := su2_shape U hU
  set a := U 0 0 with ha_def
  set b := U 1 0 with hb_def
  have hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; exact hn
  set A := Complex.arg a
  set B := Complex.arg b
  set φ := Real.arccos ‖a‖
  have ha1 : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
  have hc : Real.cos φ = ‖a‖ := Real.cos_arccos (by linarith [norm_nonneg a]) ha1
  have hs : Real.sin φ = ‖b‖ := by
    rw [Real.sin_arccos, show 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg b)
  refine ⟨(A - B + Real.pi / 2) / 2, φ, (A + B - Real.pi / 2) / 2, ?_⟩
  set u := E ((A - B + Real.pi / 2) / 2) with hu_def
  set t := E ((A + B - Real.pi / 2) / 2) with ht_def
  have h1 : u * t = E A := by rw [hu_def, ht_def, ← E_add]; congr 1; ring
  have h2 : star u * t = E B * (-Complex.I) := by
    rw [hu_def, ht_def, E_star, ← E_add,
      show -((A - B + Real.pi / 2) / 2) + (A + B - Real.pi / 2) / 2 = B + -(Real.pi / 2) by ring,
      E_add, E_neg_pi_div_two]
  have h3 : u * star t = E (-B) * Complex.I := by
    have := congrArg star h2
    simp only [star_mul', star_star, star_neg, E_star] at this
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    rw [hI] at this
    linear_combination this
  have h4 : star u * star t = E (-A) := by
    have := congrArg star h1
    simp only [star_mul', E_star] at this
    exact this
  have hpa : a = (‖a‖ : ℂ) * E A := polar a
  have hpb : b = (‖b‖ : ℂ) * E B := polar b
  have hplus : E φ + star (E φ) = 2 * (‖a‖ : ℂ) := by rw [E_star, E_plus, hc]
  have hminus : E φ - star (E φ) = 2 * (‖b‖ : ℂ) * Complex.I := by rw [E_star, E_minus, hs]
  have hsb : star b = (‖b‖ : ℂ) * E (-B) := by
    conv_lhs => rw [hpb]
    rw [star_mul', E_star]; simp
  have hsa : star a = (‖a‖ : ℂ) * E (-A) := by
    conv_lhs => rw [hpa]
    rw [star_mul', E_star]; simp
  rw [euler_eq]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j
  · change a = u * t * ((E φ + star (E φ)) / 2)
    rw [hplus, h1]; conv_lhs => rw [hpa]
    ring
  · change U 0 1 = u * star t * ((E φ - star (E φ)) / 2)
    rw [h01, hsb, hminus, h3]
    linear_combination (-(‖b‖ : ℂ) * E (-B)) * Complex.I_sq
  · change b = star u * t * ((E φ - star (E φ)) / 2)
    rw [hminus, h2]; conv_lhs => rw [hpb]
    linear_combination ((‖b‖ : ℂ) * E B) * Complex.I_sq
  · change U 1 1 = star u * star t * ((E φ + star (E φ)) / 2)
    rw [h11, hsa, hplus, h4]; ring

theorem euler_continuous : Continuous fun q : ℂ × ℂ × ℂ => euler q.1 q.2.1 q.2.2 := by
  unfold euler D
  have hD : ∀ f : ℂ × ℂ × ℂ → ℂ, Continuous f →
      Continuous fun q => (Matrix.diagonal ![f q, star (f q)] : M) := by
    intro f hf
    apply Continuous.matrix_diagonal
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hf.star
  refine ((((hD _ continuous_fst).matrix_mul continuous_const).matrix_mul
    (hD _ (continuous_fst.comp continuous_snd))).matrix_mul continuous_const).matrix_mul
    (hD _ (continuous_snd.comp continuous_snd))

/-- **SU(2) density.** Every `SU(2)` matrix is a limit of products
`D(z^j) · H · D(z^k) · H · D(z^l)` of powers of the count-weighted rotation and the Hadamard. -/
theorem su2_dense (U : M) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U ∈ closure (Set.range fun p : ℤ × ℤ × ℤ => euler (z ^ p.1) (z ^ p.2.1) (z ^ p.2.2)) := by
  obtain ⟨α, β, γ, hE⟩ := su2_euler U hU
  rw [hE]
  have hp : ((E α, E β, E γ) : ℂ × ℂ × ℂ) ∈ closure
      ((Set.range fun k : ℤ => z ^ k) ×ˢ ((Set.range fun k : ℤ => z ^ k) ×ˢ
        (Set.range fun k : ℤ => z ^ k))) := by
    rw [closure_prod_eq, closure_prod_eq]
    exact ⟨E_mem_closure α, E_mem_closure β, E_mem_closure γ⟩
  have hmaps : Set.MapsTo (fun q : ℂ × ℂ × ℂ => euler q.1 q.2.1 q.2.2)
      ((Set.range fun k : ℤ => z ^ k) ×ˢ ((Set.range fun k : ℤ => z ^ k) ×ˢ
        (Set.range fun k : ℤ => z ^ k)))
      (Set.range fun p : ℤ × ℤ × ℤ => euler (z ^ p.1) (z ^ p.2.1) (z ^ p.2.2)) := by
    intro q hq
    obtain ⟨⟨j, hj⟩, ⟨k, hk⟩, ⟨l, hl⟩⟩ := hq
    exact ⟨(j, k, l), by simp only [hj, hk, hl]⟩
  exact map_mem_closure (f := fun q : ℂ × ℂ × ℂ => euler q.1 q.2.1 q.2.2)
    (x := (E α, E β, E γ)) euler_continuous hp hmaps

/-- The diagonal gates are the rotation's powers: `D(z) = rotation`. -/
theorem D_z : D z = rotation := by
  simp only [D, rotation]
  congr 1
  ext i; fin_cases i
  · rfl
  · show star z = zbar
    apply Complex.ext <;> simp [z, zbar]; ring

theorem D_mul (u w : ℂ) : D (u * w) = D u * D w := by
  simp only [D, Matrix.diagonal_mul_diagonal]
  congr 1; ext i; fin_cases i <;> simp

theorem D_one : D 1 = 1 := by
  simp only [D]; rw [← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp

/-- `D(z^k)` is `rotation^k` for `k ≥ 0` and the `k`-th power of `rotation`'s inverse
`D(z⁻¹)` for `k < 0`. -/
theorem D_z_pow (n : ℕ) : D (z ^ n) = rotation ^ n := by
  induction n with
  | zero => simp [D_one]
  | succ n ih => rw [pow_succ, D_mul, ih, D_z, pow_succ]

theorem D_z_inv_pow (n : ℕ) : D (z ^ (-(n : ℤ))) = (D z⁻¹) ^ n := by
  induction n with
  | zero => simp [D_one]
  | succ n ih =>
    rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) + -1 by push_cast; ring, zpow_add₀ z_ne_zero, D_mul, ih,
      zpow_neg_one, pow_succ]

theorem rotation_mul_D_inv : rotation * D z⁻¹ = 1 := by
  rw [← D_z, ← D_mul, mul_inv_cancel₀ z_ne_zero, D_one]

end Density

end QLF.QuantumComputer
