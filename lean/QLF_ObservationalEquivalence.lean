import QLF_TensorConservativeReturn
import Mathlib

/-!
# QLF_ObservationalEquivalence — the tensor quotient is what joint closures can tell apart

`QLF_TensorConservativeReturn` proved a conservative return on closure classes, but it
**defined** the class relation as "same tensor image". With that definition `R ∘ F = id`
is close to true by construction, and its own scope note says so: it does not show that the
quotient is the *physically selected* closure equivalence.

This file supplies the relation from the other side. Two two-body histories are
**observationally equivalent** when no continuation can tell them apart by joint closure:
for every context history `c` and every phase `z`, `w ++ c` closes jointly with phase `z`
exactly when `w' ++ c` does. Nothing about tensors enters that definition. Then:

* `obsEquiv_iff_pairEquiv` — observational equivalence **is** the tensor-image relation, so
  the quotient of `QLF_TensorConservativeReturn` is the one that joint closure selects.
* `separating_test_is_zfa` — the context that separates two inequivalent histories can be
  taken to be a genuine ZFA closure: on each body it is the history's dagger completion, which
  is count-balanced (`countBalanced_append_dagger`). The tests are events, not just Pauli folds.
* `bareEquiv_iff_projective` — if the test reads only *whether* a joint closure happens and
  not its phase, the relation is strictly coarser: the tensor image up to a non-zero scalar.
* `phase_is_needed` — the gauge twist `−` on one body is invisible to every phase-blind test
  but is separated by a phased one. A global sign of one body is observable only through the
  phase of a joint closure (compare the `4π` spinor sign seen in neutron interferometry,
  Rauch et al. 1975 and Werner et al. 1975).
* `obsTrigger` — the quotient strange-loop trigger rebuilt on the observational classes, so its
  `coreEquiv` is no longer chosen by definition.
* `obsEquiv_iff_exists_bisim` (§7) — observational equivalence is the **greatest bisimulation**
  of the append system: every relation that agrees on the joint closure now and survives every
  one-token extension is contained in it (`bisim_le_obsEquiv`, `bisim_le_pairEquiv`). The
  equivalence a bridge must state is therefore the coarsest one compatible with continuation and
  closure outcomes ([`Bridge_Tools.md`](../Bridge_Tools.md) §2).

**Scope.** The premises are those of `QLF_TensorFromClosure`: two independent bodies, each
acting through its own fold, a multiplicative joint fold, and no relative order between the
bodies' events. The observable is the joint closure phase of appended contexts. What stays
open: that this is the *only* physical observable (an apparatus/detector map), the entangled
sector (shared pairs, `QLF_EntanglementPrimacy` rung 6), and the `N`-body version. The bridge
records remain `B-OPEN`. No axioms.

Target and status: [`tensor_return_target.md`](../verification/strange-loop/tensor_return_target.md);
the strange-loop reading is in [`Strange_Loops.md`](../Strange_Loops.md) and
[`Map_Is_Territory.md`](../Map_Is_Territory.md).
-/

noncomputable section

open QLF QLF.TensorFromClosure QLF.TensorConservativeReturn QLF.ConservativeReturn
open QLF.ClosureUnitarity
open scoped TensorProduct

namespace QLF.ObservationalEquivalence

-- ==========================================
-- §1. Projections and the joint fold are monoid maps
-- ==========================================

theorem projA_append (w c : PairHistory) : projA (w ++ c) = projA w ++ projA c := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨b, t⟩ := x
    cases b <;> simp [ih]

theorem projB_append (w c : PairHistory) : projB (w ++ c) = projB w ++ projB c := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨b, t⟩ := x
    cases b <;> simp [ih]

/-- The joint fold is multiplicative under concatenation. -/
theorem foldPair_append (w c : PairHistory) :
    foldPair (w ++ c) = foldPair w * foldPair c := by
  simp only [foldPair, projA_append, projB_append, fold_append,
    Algebra.TensorProduct.tmul_mul_tmul]

theorem foldPair_nil : foldPair [] = 1 := by
  simp [foldPair, twistMatrixFold, Algebra.TensorProduct.one_def]

-- ==========================================
-- §2. The joint closure test
-- ==========================================

/-- **The joint closure test.** History `w` followed by context `c` closes jointly with phase
    `z`: the joint fold is the scalar `z`. -/
def ClosesWith (w c : PairHistory) (z : ℂ) : Prop :=
  foldPair (w ++ c) = z • (1 : M ⊗[ℂ] M)

/-- **Observational equivalence:** no context separates `w` from `w'` by joint closure, phase
    included. Defined without reference to tensors. -/
def ObsEquiv (w w' : PairHistory) : Prop :=
  ∀ (c : PairHistory) (z : ℂ), ClosesWith w c z ↔ ClosesWith w' c z

/-- **Phase-blind equivalence:** no context separates `w` from `w'` by *whether* a joint closure
    happens. -/
def BareEquiv (w w' : PairHistory) : Prop :=
  ∀ c : PairHistory, (∃ z : ℂ, ClosesWith w c z) ↔ (∃ z : ℂ, ClosesWith w' c z)

-- ==========================================
-- §3. The dagger completion: a test that is a genuine ZFA closure
-- ==========================================

private lemma conj_conj' (t : Twist) : t.conj.conj = t := by cases t <;> rfl

private lemma dagger_dagger' (ts : List Twist) : ClosureUnitarity.dagger (ClosureUnitarity.dagger ts) = ts := by
  unfold ClosureUnitarity.dagger
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  conv_rhs => rw [← List.map_id ts]
  congr 1
  funext t
  exact conj_conj' t

private lemma length_dagger' (ts : List Twist) : (ClosureUnitarity.dagger ts).length = ts.length := by
  simp [ClosureUnitarity.dagger]

/-- The dagger also closes from the left. -/
theorem dagger_mul_fold (ts : List Twist) :
    twistMatrixFold (ClosureUnitarity.dagger ts) * twistMatrixFold ts = (-1 : ℂ) ^ ts.length • (1 : M) := by
  have h := closure_by_dagger (ClosureUnitarity.dagger ts)
  rw [dagger_dagger', length_dagger', fold_append] at h
  exact h

/-- The **completion** of a two-body history: each body's dagger, body `A` first. -/
def completion (w : PairHistory) : PairHistory :=
  tagA (ClosureUnitarity.dagger (projA w)) ++ tagB (ClosureUnitarity.dagger (projB w))

/-- The sign with which a history closes against its completion. -/
def completionSign (w : PairHistory) : ℂ :=
  (-1 : ℂ) ^ ((projA w).length + (projB w).length)

theorem completionSign_ne_zero (w : PairHistory) : completionSign w ≠ 0 := by
  simp [completionSign]

theorem projA_completion (w : PairHistory) : projA (completion w) = ClosureUnitarity.dagger (projA w) :=
  projA_normal _ _

theorem projB_completion (w : PairHistory) : projB (completion w) = ClosureUnitarity.dagger (projB w) :=
  projB_normal _ _

private lemma smul_one_tmul_smul_one (a b : ℂ) :
    (a • (1 : M)) ⊗ₜ[ℂ] (b • (1 : M)) = (a * b) • (1 : M ⊗[ℂ] M) := by
  rw [TensorProduct.smul_tmul_smul, Algebra.TensorProduct.one_def]

theorem fold_mul_completion (w : PairHistory) :
    foldPair w * foldPair (completion w) = completionSign w • (1 : M ⊗[ℂ] M) := by
  simp only [foldPair, projA_completion, projB_completion,
    Algebra.TensorProduct.tmul_mul_tmul]
  rw [← fold_append, ← fold_append, closure_by_dagger, closure_by_dagger,
    smul_one_tmul_smul_one, completionSign, pow_add]

theorem completion_mul_fold (w : PairHistory) :
    foldPair (completion w) * foldPair w = completionSign w • (1 : M ⊗[ℂ] M) := by
  simp only [foldPair, projA_completion, projB_completion,
    Algebra.TensorProduct.tmul_mul_tmul]
  rw [dagger_mul_fold, dagger_mul_fold, smul_one_tmul_smul_one, completionSign, pow_add]

/-- Every history closes jointly against its own completion. -/
theorem closesWith_completion (w : PairHistory) :
    ClosesWith w (completion w) (completionSign w) := by
  unfold ClosesWith
  rw [foldPair_append, fold_mul_completion]

/-- **The separating test is a ZFA closure.** On each body, history-then-completion is
    count-balanced. -/
theorem separating_test_is_zfa (w : PairHistory) :
    countBalanced (projA (w ++ completion w)) ∧ countBalanced (projB (w ++ completion w)) := by
  rw [projA_append, projB_append, projA_completion, projB_completion]
  exact ⟨countBalanced_append_dagger _, countBalanced_append_dagger _⟩

-- ==========================================
-- §4. Observational equivalence is the tensor quotient
-- ==========================================

/-- One test suffices: if `w'` closes against `w`'s completion with `w`'s sign, the two have the
    same tensor image. -/
theorem pairEquiv_of_completion_test {w w' : PairHistory}
    (h : ClosesWith w' (completion w) (completionSign w)) : PairEquiv w w' := by
  unfold ClosesWith at h
  rw [foldPair_append] at h
  have key : completionSign w • foldPair w' = completionSign w • foldPair w := by
    calc completionSign w • foldPair w'
        = foldPair w' * (completionSign w • (1 : M ⊗[ℂ] M)) := by rw [mul_smul_comm, mul_one]
      _ = foldPair w' * (foldPair (completion w) * foldPair w) := by rw [completion_mul_fold]
      _ = (foldPair w' * foldPair (completion w)) * foldPair w := by rw [mul_assoc]
      _ = completionSign w • foldPair w := by rw [h, smul_mul_assoc, one_mul]
  have := congrArg (fun x => (completionSign w)⁻¹ • x) key
  simp only [smul_smul, inv_mul_cancel₀ (completionSign_ne_zero w), one_smul] at this
  exact this.symm

/-- **Observational equivalence is the tensor-image relation.** The quotient that
    `QLF_TensorConservativeReturn` chose by definition is the one joint closure selects. -/
theorem obsEquiv_iff_pairEquiv (w w' : PairHistory) : ObsEquiv w w' ↔ PairEquiv w w' := by
  constructor
  · intro h
    exact pairEquiv_of_completion_test ((h _ _).1 (closesWith_completion w))
  · intro h c z
    unfold ClosesWith
    rw [foldPair_append, foldPair_append]
    unfold PairEquiv at h
    rw [h]

/-- The observational relation, as a function, equals the tensor-image relation. -/
theorem obsEquiv_eq : ObsEquiv = PairEquiv :=
  funext fun w => funext fun w' => propext (obsEquiv_iff_pairEquiv w w')

-- ==========================================
-- §5. Without the phase: the projective quotient, strictly coarser
-- ==========================================

/-- The joint fold of any history is non-zero (it has an inverse). -/
theorem foldPair_ne_zero (w : PairHistory) : foldPair w ≠ 0 := by
  intro h0
  have h := fold_mul_completion w
  rw [h0, zero_mul] at h
  have h1 := congrArg kronLift h
  rw [map_zero, map_smul, map_one] at h1
  have h2 := congrFun (congrFun h1 (0, 0)) (0, 0)
  simp [completionSign] at h2
  exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0) h2.symm

/-- **Phase-blind tests see the tensor image only up to a non-zero scalar.** -/
theorem bareEquiv_iff_projective (w w' : PairHistory) :
    BareEquiv w w' ↔ ∃ u : ℂ, u ≠ 0 ∧ foldPair w' = u • foldPair w := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (h (completion w)).1 ⟨_, closesWith_completion w⟩
    unfold ClosesWith at hz
    rw [foldPair_append] at hz
    have key : completionSign w • foldPair w' = z • foldPair w := by
      calc completionSign w • foldPair w'
          = foldPair w' * (completionSign w • (1 : M ⊗[ℂ] M)) := by rw [mul_smul_comm, mul_one]
        _ = foldPair w' * (foldPair (completion w) * foldPair w) := by rw [completion_mul_fold]
        _ = (foldPair w' * foldPair (completion w)) * foldPair w := by rw [mul_assoc]
        _ = z • foldPair w := by rw [hz, smul_mul_assoc, one_mul]
    have hw' : foldPair w' = ((completionSign w)⁻¹ * z) • foldPair w := by
      have := congrArg (fun x => (completionSign w)⁻¹ • x) key
      simp only [smul_smul, inv_mul_cancel₀ (completionSign_ne_zero w), one_smul] at this
      exact this
    refine ⟨(completionSign w)⁻¹ * z, ?_, hw'⟩
    rintro h0
    rw [h0, zero_smul] at hw'
    exact foldPair_ne_zero w' hw'
  · rintro ⟨u, hu, hw'⟩ c
    unfold ClosesWith
    rw [foldPair_append, foldPair_append, hw', smul_mul_assoc]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨u * z, ?_⟩
      rw [hz, smul_smul]
    · rintro ⟨z, hz⟩
      refine ⟨u⁻¹ * z, ?_⟩
      have := congrArg (fun x => u⁻¹ • x) hz
      simp only [smul_smul, inv_mul_cancel₀ hu, one_smul] at this
      exact this

/-- Observational equivalence refines phase-blind equivalence. -/
theorem bareEquiv_of_obsEquiv {w w' : PairHistory} (h : ObsEquiv w w') : BareEquiv w w' :=
  fun c => ⟨fun ⟨z, hz⟩ => ⟨z, (h c z).1 hz⟩, fun ⟨z, hz⟩ => ⟨z, (h c z).2 hz⟩⟩

/-- The gauge twist `−` on body `A`. -/
def gaugeFlip : PairHistory := [(false, Twist.minus)]

theorem foldPair_gaugeFlip : foldPair gaugeFlip = (-1 : ℂ) • (1 : M ⊗[ℂ] M) := by
  have hm : twistMatrixFold [Twist.minus] = (-1 : ℂ) • (1 : M) := by
    rw [fold_singleton]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Twist.toMatrix]
  have : foldPair gaugeFlip = twistMatrixFold [Twist.minus] ⊗ₜ[ℂ] twistMatrixFold [] := rfl
  rw [this, hm, show twistMatrixFold ([] : List Twist) = (1 : M) from rfl,
    ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

/-- **The phase is needed.** The gauge flip `−` on one body passes every phase-blind test but
    is separated from the empty history by a phased one. -/
theorem phase_is_needed :
    BareEquiv gaugeFlip [] ∧ ¬ ObsEquiv gaugeFlip [] := by
  refine ⟨?_, ?_⟩
  · refine (bareEquiv_iff_projective _ _).2 ⟨-1, by norm_num, ?_⟩
    rw [foldPair_gaugeFlip, foldPair_nil, smul_smul]
    norm_num
  · intro h
    have hp := (obsEquiv_iff_pairEquiv _ _).1 h
    unfold PairEquiv at hp
    rw [foldPair_gaugeFlip, foldPair_nil] at hp
    have h1 := congrArg kronLift hp
    rw [map_smul, map_one] at h1
    have h2 := congrFun (congrFun h1 (0, 0)) (0, 0)
    norm_num at h2

-- ==========================================
-- §6. The trigger on observational classes
-- ==========================================

/-- Classes of two-body histories under observational equivalence. -/
def ObsClass : Type := Quot ObsEquiv

/-- Observational classes are the tensor closure classes. -/
def obsClassEquiv : ObsClass ≃ ClosureClass :=
  Quot.congr (Equiv.refl _) (fun a b => obsEquiv_iff_pairEquiv a b)

/-- **The quotient trigger on observational classes.** Same tensor side as `tensorTrigger`; the
    finite side is now quotiented by what joint closures can distinguish. -/
def obsTrigger : QuotientStrangeLoopTrigger where
  Core := ObsClass
  Tensor := TensorImage
  coreEquiv := Eq
  equiv_refl := fun _ => rfl
  equiv_symm := fun h => h.symm
  equiv_trans := fun h₁ h₂ => h₁.trans h₂
  forward := fun c => forwardImage (obsClassEquiv c)
  ret := fun x => obsClassEquiv.symm (R x)
  forward_respects := by
    intro c c' h
    rw [h]
  composite_id_on_quotient := by
    intro c
    show obsClassEquiv.symm (R (forwardImage (obsClassEquiv c))) = c
    rw [R_forward, Equiv.symm_apply_apply]

theorem obsTrigger_exists : Nonempty QuotientStrangeLoopTrigger :=
  ⟨obsTrigger⟩

/-- The composite identity on observational classes. -/
theorem obs_conservative_return (c : ObsClass) :
    obsClassEquiv.symm (R (forwardImage (obsClassEquiv c))) = c := by
  rw [R_forward, Equiv.symm_apply_apply]

-- ==========================================
-- §7. Observational equivalence is the greatest bisimulation
-- ==========================================

/-! The relation above quantifies over whole contexts. The same relation arises
step by step, which is the form a bridge specification needs: a relation on histories
that (i) agrees on the observable *now* (does the history close jointly, and with which
phase) and (ii) is preserved by every one-token extension is a **bisimulation** of the
append transition system (Park 1981; Milner 1989). Every such relation is contained in
`ObsEquiv`, and `ObsEquiv` is one. So the equivalence is not a choice among many: it is
the unique coarsest relation compatible with continuation and closure outcomes, and any
bridge that preserves those two things can use only a refinement of it. This is the
Myhill–Nerode right congruence (Nerode 1958) of the joint-closure observable, read as a
bisimulation; the content particular to QLF is `obsEquiv_iff_pairEquiv` above. -/

/-- The observable of a history now: whether it closes jointly with phase `z`. -/
def ObsNow (w : PairHistory) (z : ℂ) : Prop :=
  ClosesWith w [] z

/-- **Bisimulation** of the append transition system for the joint-closure observable. -/
def IsBisim (R : PairHistory → PairHistory → Prop) : Prop :=
  ∀ w w', R w w' →
    (∀ z : ℂ, ObsNow w z ↔ ObsNow w' z) ∧ ∀ x : Tok, R (w ++ [x]) (w' ++ [x])

/-- A bisimulation is preserved by any appended context, not just one token. -/
theorem IsBisim.append {R : PairHistory → PairHistory → Prop} (hR : IsBisim R) :
    ∀ (c w w' : PairHistory), R w w' → R (w ++ c) (w' ++ c) := by
  intro c
  induction c with
  | nil => intro w w' h; simpa using h
  | cons x c ih =>
    intro w w' h
    have h1 := (hR w w' h).2 x
    have h2 := ih _ _ h1
    simpa [List.append_assoc] using h2

/-- **Every bisimulation is contained in observational equivalence.** -/
theorem bisim_le_obsEquiv {R : PairHistory → PairHistory → Prop} (hR : IsBisim R)
    {w w' : PairHistory} (h : R w w') : ObsEquiv w w' := by
  intro c z
  have hc := hR.append c w w' h
  have := (hR _ _ hc).1 z
  simpa [ObsNow, ClosesWith] using this

/-- **Observational equivalence is a bisimulation.** -/
theorem obsEquiv_isBisim : IsBisim ObsEquiv := by
  intro w w' h
  refine ⟨fun z => by simpa [ObsNow] using h [] z, fun x c z => ?_⟩
  have := h ([x] ++ c) z
  simpa [ClosesWith, List.append_assoc] using this

/-- **The greatest bisimulation.** Two histories are observationally equivalent exactly
    when some bisimulation relates them. -/
theorem obsEquiv_iff_exists_bisim (w w' : PairHistory) :
    ObsEquiv w w' ↔ ∃ R : PairHistory → PairHistory → Prop, IsBisim R ∧ R w w' :=
  ⟨fun h => ⟨ObsEquiv, obsEquiv_isBisim, h⟩, fun ⟨_, hR, h⟩ => bisim_le_obsEquiv hR h⟩

/-- The tensor relation is therefore the greatest bisimulation too: any relation on
    two-body histories that respects one-token continuation and joint-closure outcomes
    (phase included) identifies only histories with the same tensor image. -/
theorem bisim_le_pairEquiv {R : PairHistory → PairHistory → Prop} (hR : IsBisim R)
    {w w' : PairHistory} (h : R w w') : PairEquiv w w' :=
  (obsEquiv_iff_pairEquiv w w').1 (bisim_le_obsEquiv hR h)

/-- `PairEquiv` is itself a bisimulation. -/
theorem pairEquiv_isBisim : IsBisim PairEquiv := by
  intro w w' h
  have h' := (obsEquiv_iff_pairEquiv w w').2 h
  refine ⟨(obsEquiv_isBisim w w' h').1, fun x => ?_⟩
  exact (obsEquiv_iff_pairEquiv _ _).1 ((obsEquiv_isBisim w w' h').2 x)

/-- Observational equivalence is an equivalence relation. -/
theorem obsEquiv_equivalence : Equivalence ObsEquiv :=
  ⟨fun _ _ _ => Iff.rfl, fun h c z => (h c z).symm,
    fun h₁ h₂ c z => (h₁ c z).trans (h₂ c z)⟩

end QLF.ObservationalEquivalence
