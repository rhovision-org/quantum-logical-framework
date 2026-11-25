/-
  QLF_QuantumComputer.lean — what QLF proves about the claim "the universe is a quantum
  computer", and where the proof stops.

  Write-up: Universe_Quantum_Computer.md.

  Four results, no axioms.

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

  What this does NOT claim: that the universe *is* this construction (only that it is one
  model of a logical system that computes), and anything about complexity: an exact answer
  from a path sum costs the whole set of paths (`QLF_PossibilityGrowth`), and nothing here
  gives an NP oracle.
-/

import Mathlib
import QLF_Fredkin
import SpacetimeDynamics

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

end QLF.QuantumComputer
