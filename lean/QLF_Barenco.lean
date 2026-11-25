import QLF_ControlledUnitary
import QLF_TwoLevelUnitary

/-!
# QLF_Barenco — one-qubit gates and CNOT are universal

Stage 3 of Barenco et al. (1995), *Elementary gates for quantum computation*, Phys. Rev. A
**52**, 3457: on `n ≥ 1` qubits, every unitary is a finite product of one-qubit unitaries and
CNOTs (`universality`, `universality_list`). Exact, not approximate.

The route:

1. **Gates on one target.** A gate acting on qubit `t`, with a `2 × 2` block that may depend on
   the other qubits, is `lift t F`. Gates on the same target multiply blockwise (`lift_mul`).
2. **Multi-controlled gates** (`ctrl_mem`): `ctrl S t U` applies `U ∈ U(2)` to qubit `t` when
   every qubit in `S` is `1`. One control is the `A·X·B·X·C` network of
   [`QLF_ControlledUnitary`](QLF_ControlledUnitary.lean). More controls split `S = {c} ∪ S'`
   and use a group commutator: `C^S([V, V']) = [C^{c}(V), C^{S'}(V')]` (`ctrl_comm`), with
   every `SU(2)` matrix a product of three commutators (`su2_three_commutators`). The phase
   `e^{iδ}` under the controls `S` is the gate `diag(1, e^{iδ})` on a control qubit `c`,
   controlled by `S \ {c}` (`ctrl_phase_switch`). This replaces Barenco's square-root recursion
   (Lemma 7.5) and needs no ancilla.
3. **Routing** (`twoLevel_mem`): a two-level unitary on basis states `s ≠ s'` is moved by CNOTs
   (`cnot_isPerm`) onto a pair that differs in one qubit `t`, then by `X` gates (`flip_isPerm`)
   onto the pair whose other qubits are all `1`. There it is a fully controlled gate on `t`.
4. **Two-level decomposition** ([`QLF_TwoLevelUnitary`](QLF_TwoLevelUnitary.lean)) finishes it.

No axioms beyond Lean's own. Part of the [Quantum Logical Framework (QLF)](../README.md);
write-up in [`Barenco_Universality.md`](../Barenco_Universality.md).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QLF.Barenco

open Matrix QLF.ControlledUnitary QLF.TwoLevelUnitary

variable {n : ℕ}

/-- Basis states of `n` qubits. -/
abbrev St (n : ℕ) := Fin n → Fin 2

/-- Operators on `n` qubits. -/
abbrev Mat (n : ℕ) := Matrix (St n) (St n) ℂ

/-- A state split into the bit at `t` and the other bits. -/
def split (t : Fin n) : St n ≃ Fin 2 × ({j // j ≠ t} → Fin 2) := Equiv.funSplitAt t (Fin 2)

/-- A gate on qubit `t` whose `2 × 2` block `F x` may depend on the other qubits of `x`
(the bit at `t` is read as `0`). -/
def lift (t : Fin n) (F : St n → M2) : Mat n :=
  (Matrix.blockDiagonal fun r => F ((split t).symm (0, r))).submatrix (split t) (split t)

theorem lift_mul (t : Fin n) (F G : St n → M2) :
    lift t F * lift t G = lift t (fun x => F x * G x) := by
  rw [lift, lift, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]; rfl

theorem lift_star (t : Fin n) (F : St n → M2) :
    star (lift t F) = lift t (fun x => star (F x)) := by
  rw [lift, lift, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.blockDiagonal_conjTranspose]; rfl

theorem lift_one (t : Fin n) : lift t (fun _ => 1) = 1 := by
  rw [lift]
  have : (Matrix.blockDiagonal fun r : ({j // j ≠ t} → Fin 2) => (1 : M2)) = 1 :=
    Matrix.blockDiagonal_one
  rw [this, Matrix.submatrix_one_equiv]

theorem split_symm_zero (t : Fin n) (x : St n) :
    (split t).symm (0, fun j => x j) = Function.update x t 0 := by
  funext i
  by_cases hi : i = t
  · subst hi; simp [split, Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [split, Equiv.funSplitAt, Equiv.piSplitAt, hi]

theorem lift_apply (t : Fin n) (F : St n → M2) (x y : St n) :
    lift t F x y = if (∀ i, i ≠ t → x i = y i) then F (Function.update x t 0) (x t) (y t)
      else 0 := by
  have hx : (split t x) = (x t, fun j : {j // j ≠ t} => x j) := rfl
  have hy : (split t y) = (y t, fun j : {j // j ≠ t} => y j) := rfl
  rw [lift, Matrix.submatrix_apply, hx, hy, Matrix.blockDiagonal_apply']
  have hiff : ((fun j : {j // j ≠ t} => x j) = fun j : {j // j ≠ t} => y j) ↔ ∀ i, i ≠ t → x i = y i := by
    constructor
    · intro h i hi; exact congrFun h ⟨i, hi⟩
    · intro h; funext j; exact h j j.2
  by_cases h : ∀ i, i ≠ t → x i = y i
  · rw [if_pos (hiff.mpr h), if_pos h, split_symm_zero]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-! ## Controlled gates -/

/-- `ctrl S t U`: the gate `U` on qubit `t`, applied when every qubit in `S` is `1`. -/
def ctrl (S : Finset (Fin n)) (t : Fin n) (U : M2) : Mat n :=
  lift t (fun x => if ∀ i ∈ S, x i = 1 then U else 1)

/-- A one-qubit gate `A` on qubit `t`. -/
def onQubit (t : Fin n) (A : M2) : Mat n := ctrl ∅ t A

/-- CNOT with control `c` and target `t`. -/
def cnot (c t : Fin n) : Mat n := ctrl {c} t X

/-- The elementary gates: one-qubit unitaries and CNOTs. -/
def gates (n : ℕ) : Set (Mat n) :=
  {M | (∃ t A, A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ M = onQubit t A) ∨
       (∃ c t, c ≠ t ∧ M = cnot c t)}

/-- The circuits: finite products of elementary gates. -/
def circuits (n : ℕ) : Submonoid (Mat n) := Submonoid.closure (gates n)

theorem onQubit_mem (t : Fin n) {A : M2} (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    onQubit t A ∈ circuits n :=
  Submonoid.subset_closure (Or.inl ⟨t, A, hA, rfl⟩)

theorem cnot_mem {c t : Fin n} (h : c ≠ t) : cnot c t ∈ circuits n :=
  Submonoid.subset_closure (Or.inr ⟨c, t, h, rfl⟩)

theorem ctrl_apply {S : Finset (Fin n)} {t : Fin n} (ht : t ∉ S) (U : M2) (x y : St n) :
    ctrl S t U x y = if (∀ i, i ≠ t → x i = y i) then
      (if ∀ i ∈ S, x i = 1 then U else 1) (x t) (y t) else 0 := by
  rw [ctrl, lift_apply]
  have h : (∀ i ∈ S, Function.update x t 0 i = 1) ↔ ∀ i ∈ S, x i = 1 := by
    constructor
    · intro h i hi; have := h i hi; rwa [Function.update_of_ne (by rintro rfl; exact ht hi)] at this
    · intro h i hi; rw [Function.update_of_ne (by rintro rfl; exact ht hi)]; exact h i hi
  simp only [h]

/-- `onQubit t A` is `A` on qubit `t` and the identity on the others. -/
theorem onQubit_apply (t : Fin n) (A : M2) (x y : St n) :
    onQubit t A x y = if (∀ i, i ≠ t → x i = y i) then A (x t) (y t) else 0 := by
  rw [onQubit, ctrl_apply (Finset.notMem_empty t)]
  simp

/-- `cnot c t` flips qubit `t` when qubit `c` is `1`, and is the identity otherwise. -/
theorem cnot_apply {c t : Fin n} (hct : c ≠ t) (x y : St n) :
    cnot c t x y = if (∀ i, i ≠ t → x i = y i) then
      (if x c = 1 then X else 1) (x t) (y t) else 0 := by
  rw [cnot, ctrl_apply (by simp [Ne.symm hct])]
  simp

theorem ctrl_mul (S : Finset (Fin n)) (t : Fin n) (A B : M2) :
    ctrl S t A * ctrl S t B = ctrl S t (A * B) := by
  rw [ctrl, ctrl, ctrl, lift_mul]; congr 1; funext x; split_ifs <;> simp

theorem ctrl_star (S : Finset (Fin n)) (t : Fin n) (A : M2) :
    star (ctrl S t A) = ctrl S t (star A) := by
  rw [ctrl, ctrl, lift_star]; congr 1; funext x; split_ifs <;> simp

theorem ctrl_unitary (S : Finset (Fin n)) (t : Fin n) {U : M2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ctrl S t U ∈ Matrix.unitaryGroup (St n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ctrl_star, ctrl_mul, Matrix.mem_unitaryGroup_iff.mp hU, ctrl,
    ← lift_one t]
  congr 1; funext x; split_ifs <;> rfl

theorem star_X : star X = X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.star_apply]

theorem X_mem : X ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_X, X_mul_X]

theorem circuits_le_unitary : circuits n ≤ Matrix.unitaryGroup (St n) ℂ := by
  rw [circuits, Submonoid.closure_le]
  rintro M (⟨t, A, hA, rfl⟩ | ⟨c, t, _, rfl⟩)
  · exact ctrl_unitary _ _ hA
  · exact ctrl_unitary _ _ X_mem

theorem star_mem_circuits {M : Mat n} (h : M ∈ circuits n) : star M ∈ circuits n := by
  induction h using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨t, A, hA, rfl⟩ | ⟨c, t, hct, rfl⟩
    · rw [onQubit, ctrl_star]; exact onQubit_mem t (Unitary.star_mem hA)
    · rw [cnot, ctrl_star, star_X]; exact cnot_mem hct
  | one => rw [star_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [star_mul]; exact Submonoid.mul_mem _ hy hx

/-! ## Multi-controlled gates -/

/-- **Commutators add controls.** If `S`'s condition is `S₁`'s and `S₂`'s, the controlled
commutator is the commutator of the controlled gates. -/
theorem ctrl_comm (S S₁ S₂ : Finset (Fin n)) (t : Fin n)
    (hS : ∀ x : St n, (∀ i ∈ S, x i = 1) ↔ (∀ i ∈ S₁, x i = 1) ∧ (∀ i ∈ S₂, x i = 1))
    (V V' : M2) (hV : V * star V = 1) (hV' : V' * star V' = 1) :
    ctrl S t (comm V V') =
      ctrl S₁ t V * ctrl S₂ t V' * ctrl S₁ t (star V) * ctrl S₂ t (star V') := by
  simp only [ctrl, lift_mul]
  congr 1; funext x
  simp only [hS x]
  by_cases h1 : ∀ i ∈ S₁, x i = 1 <;> by_cases h2 : ∀ i ∈ S₂, x i = 1
  · simp only [if_pos (And.intro h1 h2), if_pos h1, if_pos h2, ControlledUnitary.comm]
  · simp only [if_neg (fun h : _ ∧ _ => h2 h.2), if_pos h1, if_neg h2, mul_one]; exact hV.symm
  · simp only [if_neg (fun h : _ ∧ _ => h1 h.1), if_neg h1, if_pos h2, one_mul, mul_one]
    rw [hV']
  · simp only [if_neg (fun h : _ ∧ _ => h1 h.1), if_neg h1, if_neg h2, one_mul]

/-- **One control from two CNOTs** (Barenco Corollary 5.3): for `W ∈ SU(2)`, controlled-`W` is
`A · CNOT · B · CNOT · C` on the target. -/
theorem ctrl_single_su2 {c t : Fin n} (hct : c ≠ t) {W : M2}
    (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) : ctrl {c} t W ∈ circuits n := by
  obtain ⟨A, B, C, hA, hB, hC, h1, h2⟩ := abc_decomposition W hW
  have e : ctrl {c} t W = onQubit t A * cnot c t * onQubit t B * cnot c t * onQubit t C := by
    simp only [onQubit, cnot, ctrl, lift_mul]
    congr 1; funext x
    have h1' : A * (B * C) = 1 := by rw [← mul_assoc]; exact h1
    have h2' : A * (X * (B * (X * C))) = W := by simp only [← mul_assoc]; exact h2
    by_cases hx : x c = 1
    · simp [hx, h2', mul_assoc]
    · simp [hx, h1', mul_assoc]
  rw [e]
  have hu : ∀ {A : M2}, A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ := fun h => (Matrix.mem_specialUnitaryGroup_iff.mp h).1
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
    (onQubit_mem t (hu hA)) (cnot_mem hct)) (onQubit_mem t (hu hB))) (cnot_mem hct))
    (onQubit_mem t (hu hC))

/-- The phase gate `diag(1, e^{iδ})`. -/
noncomputable def phase2 (δ : ℝ) : M2 := !![1, 0; 0, E δ]

theorem phase2_mem (δ : ℝ) : phase2 δ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [phase2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  exact E_mul_star δ

theorem eq_of_agree {t : Fin n} {x y : St n} (h : ∀ i, i ≠ t → x i = y i) (ht : x t = y t) :
    x = y := by
  funext i; by_cases hi : i = t
  · subst hi; exact ht
  · exact h i hi

/-- **Phases move to a control.** `e^{iδ}` on qubit `t` under the controls `S` equals
`diag(1, e^{iδ})` on a control `c ∈ S`, under the controls `S \ {c}`. -/
theorem ctrl_phase_switch {S : Finset (Fin n)} {c t : Fin n} (hc : c ∈ S) (ht : t ∉ S)
    (δ : ℝ) : ctrl S t (E δ • (1 : M2)) = ctrl (S.erase c) c (phase2 δ) := by
  have hc' : c ∉ S.erase c := Finset.notMem_erase c S
  have hS : ∀ x : St n, (∀ i ∈ S, x i = 1) ↔ (∀ i ∈ S.erase c, x i = 1) ∧ x c = 1 := by
    intro x; constructor
    · intro h; exact ⟨fun i hi => h i (Finset.mem_of_mem_erase hi), h c hc⟩
    · intro h i hi
      by_cases hic : i = c
      · rw [hic]; exact h.2
      · exact h.1 i (Finset.mem_erase.mpr ⟨hic, hi⟩)
  ext x y
  rw [ctrl_apply ht, ctrl_apply hc']
  by_cases hxy : x = y
  · subst hxy
    simp only [ne_eq, implies_true, if_true, hS x]
    by_cases h1 : ∀ i ∈ S.erase c, x i = 1 <;> by_cases h2 : x c = 1
    · simp only [if_pos (And.intro h1 h2), if_pos h1]; rw [h2]; simp [phase2]
    · have h2' : x c = 0 := by omega
      simp only [if_neg (fun h : _ ∧ _ => h2 h.2), if_pos h1]; rw [h2']; simp [phase2]
    · simp only [if_neg (fun h : _ ∧ _ => h1 h.1), if_neg h1]; simp
    · simp only [if_neg (fun h : _ ∧ _ => h1 h.1), if_neg h1]; simp
  · have off : ∀ (M : M2) (a b : Fin 2), M 0 1 = 0 → M 1 0 = 0 → a ≠ b → M a b = 0 := by
      intro M a b h01 h10 hab
      fin_cases a <;> fin_cases b <;> simp_all
    have hL := off (if ∀ i ∈ S, x i = 1 then E δ • (1 : M2) else 1) (x t) (y t)
      (by split_ifs <;> simp) (by split_ifs <;> simp)
    have hR := off (if ∀ i ∈ S.erase c, x i = 1 then phase2 δ else 1) (x c) (y c)
      (by split_ifs <;> simp [phase2]) (by split_ifs <;> simp [phase2])
    by_cases ha : ∀ i, i ≠ t → x i = y i
    · rw [if_pos ha, hL (fun e => hxy (eq_of_agree ha e))]
      by_cases hb : ∀ i, i ≠ c → x i = y i
      · rw [if_pos hb, hR (fun e => hxy (eq_of_agree hb e))]
      · rw [if_neg hb]
    · rw [if_neg ha]
      by_cases hb : ∀ i, i ≠ c → x i = y i
      · rw [if_pos hb, hR (fun e => hxy (eq_of_agree hb e))]
      · rw [if_neg hb]

/-- **Every multi-controlled one-qubit unitary is a circuit** (no ancilla). -/
theorem ctrl_mem : ∀ (k : ℕ) (S : Finset (Fin n)), S.card = k → ∀ t, t ∉ S →
    ∀ U : M2, U ∈ Matrix.unitaryGroup (Fin 2) ℂ → ctrl S t U ∈ circuits n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk t ht U hU
  by_cases hS0 : S = ∅
  · subst hS0; exact onQubit_mem t hU
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hS0
  have hct : c ≠ t := fun e => ht (e ▸ hc)
  have hcard : (S.erase c).card < k := by
    rw [← hk]; exact Finset.card_erase_lt_of_mem hc
  have hu : ∀ {A : M2}, A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ := fun h => (Matrix.mem_specialUnitaryGroup_iff.mp h).1
  obtain ⟨δ, W, hW, rfl⟩ := unitary_eq_phase_smul_su2 U hU
  have hsplit : ctrl S t (E δ • W) = ctrl S t (E δ • (1 : M2)) * ctrl S t W := by
    rw [ctrl_mul, smul_mul_assoc, one_mul]
  rw [hsplit]
  refine Submonoid.mul_mem _ ?_ ?_
  · rw [ctrl_phase_switch hc ht]
    exact ih _ hcard _ rfl c (Finset.notMem_erase c S) _ (phase2_mem δ)
  · by_cases h1 : S = {c}
    · subst h1; exact ctrl_single_su2 hct hW
    · have hcard1 : ({c} : Finset (Fin n)).card < k := by
        rw [← hk, Finset.card_singleton]
        obtain ⟨d, hd, hdc⟩ : ∃ d ∈ S, d ≠ c := by
          by_contra hh
          simp only [not_exists, not_and, not_not] at hh
          exact h1 (Finset.eq_singleton_iff_unique_mem.mpr ⟨hc, hh⟩)
        exact Finset.one_lt_card.mpr ⟨d, hd, c, hc, hdc⟩
      have hS : ∀ x : St n, (∀ i ∈ S, x i = 1) ↔
          (∀ i ∈ ({c} : Finset (Fin n)), x i = 1) ∧ (∀ i ∈ S.erase c, x i = 1) := by
        intro x; constructor
        · intro h
          exact ⟨fun i hi => h i (by rw [Finset.mem_singleton.mp hi]; exact hc),
            fun i hi => h i (Finset.mem_of_mem_erase hi)⟩
        · intro h i hi
          by_cases hic : i = c
          · exact h.1 i (Finset.mem_singleton.mpr hic)
          · exact h.2 i (Finset.mem_erase.mpr ⟨hic, hi⟩)
      have hct1 : t ∉ ({c} : Finset (Fin n)) := by simp [Ne.symm hct]
      have hte : t ∉ S.erase c := fun h => ht (Finset.mem_of_mem_erase h)
      obtain ⟨V₁, V₁', V₂, V₂', V₃, V₃', h1m, h1m', h2m, h2m', h3m, h3m', rfl⟩ :=
        su2_three_commutators W hW
      have hc1 : ∀ {V V' : M2}, V ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
          V' ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ → ctrl S t (comm V V') ∈ circuits n := by
        intro V V' hV hV'
        have hVu := hu hV
        have hVu' := hu hV'
        rw [ctrl_comm S {c} (S.erase c) t hS V V' (Matrix.mem_unitaryGroup_iff.mp hVu)
          (Matrix.mem_unitaryGroup_iff.mp hVu')]
        exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
          (ih _ hcard1 _ rfl t hct1 V hVu) (ih _ hcard _ rfl t hte V' hVu'))
          (ih _ hcard1 _ rfl t hct1 _ (Unitary.star_mem hVu)))
          (ih _ hcard _ rfl t hte _ (Unitary.star_mem hVu'))
      rw [← ctrl_mul, ← ctrl_mul]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hc1 h1m h1m') (hc1 h2m h2m'))
        (hc1 h3m h3m')

/-! ## Permutation gates -/

/-- `P` is the permutation matrix of `σ`: `P e_y = e_{σ y}`. -/
def IsPerm (P : Mat n) (σ : Equiv.Perm (St n)) : Prop := ∀ x y, P x y = if x = σ y then 1 else 0

theorem conj_apply {P : Mat n} {σ : Equiv.Perm (St n)} (hP : IsPerm P σ) (V : Mat n)
    (x y : St n) : (P * V * star P) x y = V (σ.symm x) (σ.symm y) := by
  have h1 : ∀ z, (P * V) x z = V (σ.symm x) z := by
    intro z; rw [mul_apply, Finset.sum_eq_single (σ.symm x)]
    · rw [hP, if_pos (σ.apply_symm_apply x).symm, one_mul]
    · intro w _ hw
      rw [hP, if_neg (fun e => hw (by rw [e, σ.symm_apply_apply])), zero_mul]
    · simp
  rw [mul_apply, Finset.sum_eq_single (σ.symm y)]
  · rw [h1, Matrix.star_apply, hP, if_pos (σ.apply_symm_apply y).symm, star_one, mul_one]
  · intro w _ hw
    rw [Matrix.star_apply, hP, if_neg (fun e => hw (by rw [e, σ.symm_apply_apply])), star_zero,
      mul_zero]
  · simp

theorem conj_supported {P : Mat n} {σ : Equiv.Perm (St n)} (hP : IsPerm P σ) {V : Mat n}
    {s s' : St n} (hV : SupportedOn {s, s'} V) : SupportedOn {σ s, σ s'} (P * V * star P) := by
  intro k l h
  have hmem : ∀ m, σ.symm m ∈ ({s, s'} : Finset (St n)) → m ∈ ({σ s, σ s'} : Finset (St n)) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.symm_apply_eq] at hm ⊢
    exact hm
  rw [conj_apply hP, hV _ _ (h.imp (fun hk hk' => hk (hmem k hk')) (fun hl hl' => hl (hmem l hl'))),
    Matrix.one_apply, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem conj_mem {P : Mat n} (hPc : P ∈ circuits n)
    {V : Mat n} (hV : P * V * star P ∈ circuits n) : V ∈ circuits n := by
  have h1 : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp (circuits_le_unitary hPc)
  have e : V = star P * (P * V * star P) * P := by
    calc V = (star P * P) * V * (star P * P) := by rw [h1, one_mul, mul_one]
      _ = star P * (P * V * star P) * P := by simp only [mul_assoc]
  rw [e]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (star_mem_circuits hPc) hV) hPc

theorem conj_unitary {P V : Mat n} (hPc : P ∈ circuits n) (hV : V ∈ Matrix.unitaryGroup (St n) ℂ) :
    P * V * star P ∈ Matrix.unitaryGroup (St n) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (circuits_le_unitary hPc) hV)
    (Unitary.star_mem (circuits_le_unitary hPc))

theorem fin2_add_one_add_one : ∀ a : Fin 2, a + 1 + 1 = a := by decide

theorem fin2_add_add : ∀ a b : Fin 2, a + b + b = a := by decide

theorem fin2_ne_add_one : ∀ a b : Fin 2, a ≠ b → a + 1 = b := by decide

theorem X_apply (a b : Fin 2) : X a b = if a = b + 1 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [X]

theorem ctrlX_apply (a b c : Fin 2) :
    (if c = 1 then X else 1) a b = if a = b + c then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [X]

/-- Flipping bit `f`. -/
def flipFun (f : Fin n) (x : St n) : St n := Function.update x f (x f + 1)

theorem flipFun_invol (f : Fin n) : Function.Involutive (flipFun f) := by
  intro x; funext i
  by_cases hi : i = f
  · subst hi; simp [flipFun, fin2_add_one_add_one]
  · simp [flipFun, hi]

/-- The `X` gate on qubit `f`, as a permutation of basis states. -/
def flipPerm (f : Fin n) : Equiv.Perm (St n) := (flipFun_invol f).toPerm

theorem flip_isPerm (f : Fin n) : IsPerm (onQubit f X) (flipPerm f) := by
  intro x y
  rw [onQubit, ctrl_apply (Finset.notMem_empty f)]
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true]
  change _ = if x = flipFun f y then 1 else 0
  by_cases h : ∀ i, i ≠ f → x i = y i
  · have e : x = flipFun f y ↔ x f = y f + 1 := by
      constructor
      · intro e; rw [e]; simp [flipFun]
      · intro e; funext i
        by_cases hi : i = f
        · subst hi; simp [flipFun, e]
        · simp [flipFun, hi, h i hi]
    rw [if_pos h, X_apply]; simp only [e]
  · rw [if_neg h, if_neg]
    intro e; apply h; intro i hi; rw [e]; simp [flipFun, hi]

/-- CNOT with control `c`, target `t`, as a map on basis states. -/
def cnotFun (c t : Fin n) (x : St n) : St n := Function.update x t (x t + x c)

theorem cnotFun_invol {c t : Fin n} (hct : c ≠ t) : Function.Involutive (cnotFun c t) := by
  intro x; funext i
  by_cases hi : i = t
  · subst hi; simp [cnotFun, Function.update_of_ne hct, fin2_add_add]
  · simp [cnotFun, hi]

/-- CNOT as a permutation of basis states. -/
def cnotPerm {c t : Fin n} (hct : c ≠ t) : Equiv.Perm (St n) := (cnotFun_invol hct).toPerm

theorem cnot_isPerm {c t : Fin n} (hct : c ≠ t) : IsPerm (cnot c t) (cnotPerm hct) := by
  intro x y
  have ht : t ∉ ({c} : Finset (Fin n)) := by simp [Ne.symm hct]
  rw [cnot, ctrl_apply ht]
  simp only [Finset.mem_singleton, forall_eq]
  change _ = if x = cnotFun c t y then 1 else 0
  by_cases h : ∀ i, i ≠ t → x i = y i
  · have e : x = cnotFun c t y ↔ x t = y t + y c := by
      constructor
      · intro e; rw [e]; simp [cnotFun]
      · intro e; funext i
        by_cases hi : i = t
        · subst hi; simp [cnotFun, e]
        · simp [cnotFun, hi, h i hi]
    rw [if_pos h, h c hct, ctrlX_apply]; simp only [e]
  · rw [if_neg h, if_neg]
    intro e; apply h; intro i hi; rw [e]; simp [cnotFun, hi]

/-! ## Routing two-level unitaries -/

/-- **The fully controlled pair.** A unitary that is the identity outside the two states
whose qubits other than `t` are all `1` is a fully controlled gate on `t`. -/
theorem pair_allOnes_mem (t : Fin n) (s : St n) (hs : ∀ i, i ≠ t → s i = 1) (V : Mat n)
    (hV : V ∈ Matrix.unitaryGroup (St n) ℂ)
    (hsup : SupportedOn {Function.update s t 0, Function.update s t 1} V) : V ∈ circuits n := by
  set p : Fin 2 → St n := fun b => Function.update s t b with hp
  have ht : t ∉ Finset.univ.erase t := Finset.notMem_erase t _
  have hpmem : ∀ x : St n, x ∈ ({p 0, p 1} : Finset (St n)) ↔ ∀ i, i ≠ t → x i = 1 := by
    intro x; constructor
    · intro hx i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [p, hi, hs i hi]
    · intro hx
      have : x = p (x t) := by
        funext i; by_cases hi : i = t
        · subst hi; simp [p]
        · simp [p, hi, hx i hi, hs i hi]
      rw [this]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      generalize x t = b; fin_cases b <;> simp
  set U2 : M2 := Matrix.of fun b b' => V (p b) (p b') with hU2
  have hpt : ∀ b, p b t = b := fun b => by simp [p]
  have hpinj : ∀ b b', p b = p b' ↔ b = b' := by
    intro b b'; constructor
    · intro e; have := congrFun e t; rwa [hpt, hpt] at this
    · rintro rfl; rfl
  have hfix : ∀ x : St n, (∀ i, i ≠ t → x i = 1) → p (x t) = x := by
    intro x hx; funext i; by_cases hi : i = t
    · subst hi; simp [p]
    · simp [p, hi, hx i hi, hs i hi]
  have hVeq : V = ctrl (Finset.univ.erase t) t U2 := by
    ext x y
    rw [ctrl_apply ht]
    have hact : (∀ i ∈ Finset.univ.erase t, x i = 1) ↔ ∀ i, i ≠ t → x i = 1 := by
      simp [Finset.mem_erase]
    by_cases hxy : ∀ i, i ≠ t → x i = y i
    · rw [if_pos hxy]
      by_cases hA : ∀ i, i ≠ t → x i = 1
      · have hAy : ∀ i, i ≠ t → y i = 1 := fun i hi => (hxy i hi) ▸ hA i hi
        rw [if_pos (hact.mpr hA), hU2, Matrix.of_apply, hfix x hA, hfix y hAy]
      · rw [if_neg (fun h => hA (hact.mp h)), hsup x y (Or.inl (fun h => hA ((hpmem x).mp h))),
          Matrix.one_apply, Matrix.one_apply]
        by_cases he : x = y
        · subst he; simp
        · rw [if_neg he, if_neg (fun e => he (eq_of_agree hxy e))]
    · rw [if_neg hxy]
      have hne : x ≠ y := fun e => hxy (fun i _ => by rw [e])
      by_cases hA : ∀ i, i ≠ t → x i = 1
      · have hAy : ¬ ∀ i, i ≠ t → y i = 1 := fun hy => hxy (fun i hi => by rw [hA i hi, hy i hi])
        rw [hsup x y (Or.inr (fun h => hAy ((hpmem y).mp h))), Matrix.one_apply, if_neg hne]
      · rw [hsup x y (Or.inl (fun h => hA ((hpmem x).mp h))), Matrix.one_apply, if_neg hne]
  have hU2u : U2 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have h1 := Matrix.mem_unitaryGroup_iff.mp hV
    rw [hVeq, ctrl_star, ctrl_mul] at h1
    ext b b'
    have h2 : ctrl (Finset.univ.erase t) t (U2 * star U2) (p b) (p b') = (1 : Mat n) (p b) (p b') :=
      by rw [h1]
    rw [ctrl_apply ht, if_pos (fun i hi => by simp [p, hi]),
      if_pos (by simp [Finset.mem_erase, p]; intro i hi; simp [hi, hs i hi]), hpt, hpt,
      Matrix.one_apply] at h2
    rw [h2, Matrix.one_apply]
    exact if_congr (hpinj b b') rfl rfl
  rw [hVeq]
  exact ctrl_mem _ _ rfl t ht U2 hU2u

/-- **`X` gates fix the control pattern.** A unitary that is the identity outside a pair of
states differing only at qubit `t` is a circuit. -/
theorem pair_mem (t : Fin n) (F : Finset (Fin n)) : ∀ (s : St n) (V : Mat n),
    V ∈ Matrix.unitaryGroup (St n) ℂ → (∀ i, i ≠ t → i ∉ F → s i = 1) →
    SupportedOn {Function.update s t 0, Function.update s t 1} V → V ∈ circuits n := by
  induction F using Finset.induction_on with
  | empty =>
    intro s V hV hs hsup
    exact pair_allOnes_mem t s (fun i hi => hs i hi (Finset.notMem_empty i)) V hV hsup
  | @insert f F' hf ih =>
    intro s V hV hs hsup
    by_cases hsf : f = t ∨ s f = 1
    · refine ih s V hV (fun i hi hiF => ?_) hsup
      by_cases hif : i = f
      · subst hif; exact hsf.resolve_left hi
      · exact hs i hi (by simp [hif, hiF])
    · simp only [not_or] at hsf
      obtain ⟨hft, hsf1⟩ := hsf
      have hP := flip_isPerm (n := n) f
      have hPc : onQubit f X ∈ circuits n := onQubit_mem f X_mem
      have hmove : ∀ b, flipPerm f (Function.update s t b) =
          Function.update (flipFun f s) t b := by
        intro b; funext i
        change flipFun f (Function.update s t b) i = _
        by_cases hit : i = t
        · subst hit; simp [flipFun, Ne.symm hft]
        · by_cases hif : i = f
          · subst hif; simp [flipFun, hit, hft]
          · simp [flipFun, hit, hif]
      have hsup' := conj_supported hP hsup
      rw [hmove, hmove] at hsup'
      refine conj_mem hPc (ih (flipFun f s) _ (conj_unitary hPc hV) (fun i hi hiF => ?_) hsup')
      by_cases hif : i = f
      · subst hif
        have : s i = 0 := by omega
        simp [flipFun, this]
      · simp only [flipFun, Function.update_of_ne hif]
        exact hs i hi (by simp [hif, hiF])

/-- **CNOTs bring the pair together.** For `w t = 0` and `u t = 1`, a unitary that is the
identity outside `{w, u}` is a circuit. -/
theorem pair_cnot_mem (t : Fin n) (w : St n) (hw : w t = 0) (D : Finset (Fin n)) :
    ∀ (u : St n) (V : Mat n), V ∈ Matrix.unitaryGroup (St n) ℂ → u t = 1 →
    (∀ i, i ≠ t → i ∉ D → u i = w i) → SupportedOn {w, u} V → V ∈ circuits n := by
  induction D using Finset.induction_on with
  | empty =>
    intro u V hV hu hD hsup
    have hw0 : Function.update w t 0 = w := by rw [← hw]; exact Function.update_eq_self t w
    have hu1 : Function.update w t 1 = u := by
      funext i; by_cases hi : i = t
      · subst hi; simp [hu]
      · simp [hi, hD i hi (Finset.notMem_empty i)]
    refine pair_mem t Finset.univ w V hV (fun i _ h => absurd (Finset.mem_univ i) h) ?_
    rw [hw0, hu1]; exact hsup
  | @insert i D' hi ih =>
    intro u V hV hu hD hsup
    by_cases hskip : i = t ∨ u i = w i
    · refine ih u V hV hu (fun j hj hjD => ?_) hsup
      by_cases hji : j = i
      · subst hji; exact hskip.resolve_left hj
      · exact hD j hj (by simp [hji, hjD])
    · simp only [not_or] at hskip
      obtain ⟨hit, hne⟩ := hskip
      have hti : t ≠ i := Ne.symm hit
      have hP := cnot_isPerm hti
      have hPc : cnot t i ∈ circuits n := cnot_mem hti
      have hσw : cnotPerm hti w = w := by
        change cnotFun t i w = w
        simp [cnotFun, hw]
      have hsup' := conj_supported hP hsup
      rw [hσw] at hsup'
      refine conj_mem hPc (ih _ _ (conj_unitary hPc hV) ?_ (fun j hj hjD => ?_) hsup')
      · change cnotFun t i u t = 1
        simp only [cnotFun]; rw [Function.update_of_ne hti]; exact hu
      · change cnotFun t i u j = w j
        by_cases hji : j = i
        · subst hji; simp [cnotFun, hu, fin2_ne_add_one _ _ hne]
        · simp only [cnotFun, Function.update_of_ne hji]
          exact hD j hj (by simp [hji, hjD])

/-- **Every two-level unitary on `n ≥ 1` qubits is a circuit.** -/
theorem twoLevel_mem_circuits {n : ℕ} {V : Mat (n + 1)} (h : TwoLevel V) :
    V ∈ circuits (n + 1) := by
  obtain ⟨hV, i, j, hsup⟩ := h
  -- make the two states distinct
  obtain ⟨j', hij', hsup'⟩ : ∃ j', i ≠ j' ∧ SupportedOn {i, j'} V := by
    by_cases hij : i = j
    · refine ⟨flipFun 0 i, fun e => ?_, hsup.mono (by subst hij; simp)⟩
      have := congrFun e 0
      simp [flipFun] at this
    · exact ⟨j, hij, hsup⟩
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hij'
  have h01 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  rcases h01 _ _ ht with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
  · exact pair_cnot_mem t i hi0 Finset.univ j' V hV hj1
      (fun k _ h => absurd (Finset.mem_univ k) h) hsup'
  · rw [Finset.pair_comm] at hsup'
    exact pair_cnot_mem t j' hj0 Finset.univ i V hV hi1
      (fun k _ h => absurd (Finset.mem_univ k) h) hsup'

/-! ## Universality -/

/-- **Barenco universality.** On `n ≥ 1` qubits, every unitary lies in the monoid generated by
one-qubit unitaries and CNOTs. -/
theorem universality {n : ℕ} (U : Mat (n + 1)) (hU : U ∈ Matrix.unitaryGroup (St (n + 1)) ℂ) :
    U ∈ circuits (n + 1) :=
  (Submonoid.closure_le.mpr (fun _ hV => twoLevel_mem_circuits hV))
    (unitary_mem_closure_twoLevel U hU)

/-- **Barenco universality, as a list of gates.** Every unitary on `n ≥ 1` qubits is a finite
product of one-qubit unitaries and CNOTs. -/
theorem universality_list {n : ℕ} (U : Mat (n + 1))
    (hU : U ∈ Matrix.unitaryGroup (St (n + 1)) ℂ) :
    ∃ l : List (Mat (n + 1)), (∀ g ∈ l, g ∈ gates (n + 1)) ∧ l.prod = U :=
  Submonoid.exists_list_of_mem_closure (universality U hU)

/-- The converse: every circuit is unitary, so the circuits are exactly the unitaries. -/
theorem circuits_eq_unitary {n : ℕ} :
    (circuits (n + 1) : Set (Mat (n + 1))) = Matrix.unitaryGroup (St (n + 1)) ℂ := by
  ext U; exact ⟨fun h => circuits_le_unitary h, fun h => universality U h⟩

end QLF.Barenco
