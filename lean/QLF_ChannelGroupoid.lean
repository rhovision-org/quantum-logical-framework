import QLF_ClosureUnitarity
import QLF_BalancedPhaseReal
import QLF_KraftMeasure

/-!
# QLF_ChannelGroupoid — the boundary-labeled dagger category of histories (U2)

Issue #207, target **U2**. Objects are boundary labels `v ∈ ℤ⁴`, the signed action vector of a
channel, one coordinate per conjugate pair of twists. A morphism `v ⟶ w` is a finite twist history
whose signed action carries `v` to `w`. This is the full channel space: every label, every history.

* **`act_append`, `act_dagger`, `act_eq_zero_iff`.** The signed action is additive under
  concatenation, negated by the dagger (conjugate every twist and reverse), and zero exactly on
  count-balanced histories.
* **Category.** `idH`, `comp` (concatenation), `comp_assoc`, `id_comp`, `comp_id`.
* **Dagger.** `dag : (v ⟶ w) → (w ⟶ v)`, with `dag_dag`, `dag_comp` (order reverses), `dag_id`.
* **`hol_comp`, `hol_dag`, `hol_id`.** The ordered fold (holonomy) is a functor to `2 × 2` matrices,
  and a dagger functor up to the central sign: `hol(h†) = (−1)^|h| hol(h)ᴴ`.
* **`hol_comp_dag`.** `h ≫ h†` is an endomorphism with holonomy `(−1)^|h|`: modulo the centre
  `{±1}` every morphism is invertible, so the holonomy image is a groupoid.
* **`endo_closure`.** Every endomorphism `v ⟶ v` is a closure: count balanced, with holonomy
  `+1` or `−1` (`balanced_phase_is_real`), at every boundary label.
* **`kernel_compose`.** The channel kernel `K_L(v, w)`, the sum of folds over all histories of
  length `L` from `v` to `w`, composes over intermediate channels:
  `K_{L₁+L₂}(v, w) = Σ_u K_{L₁}(v, u) K_{L₂}(u, w)`. This is the full-channel-space form of the
  light-cone `shellKernel_compose` (#210).
* **`kernel_dagger`.** `K_L(w, v) = (−1)^L K_L(v, w)ᴴ`.

No axioms. The label `v` is the net displacement of the closed walk of
[Closure_Walk.md](../Closure_Walk.md); closures are the walks that return.
Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.ChannelGroupoid

open QLF QLF.ClosureUnitarity Matrix

/-- The positive twist of each conjugate pair. -/
def pos : Fin 4 → Twist
  | 0 => .up
  | 1 => .right
  | 2 => .slash
  | 3 => .plus

/-- **The signed action vector**: for each pair, positive count minus conjugate count. -/
def act (ts : List Twist) : Fin 4 → ℤ := fun a => (ts.count (pos a) : ℤ) - ts.count (pos a).conj

theorem act_append (a b : List Twist) : act (a ++ b) = act a + act b := by
  funext k; simp only [act, List.count_append, Pi.add_apply]; push_cast; ring

theorem act_nil : act [] = 0 := by funext k; simp [act]

lemma conj_conj (t : Twist) : t.conj.conj = t := by cases t <;> rfl

theorem act_dagger (ts : List Twist) : act (dagger ts) = -act ts := by
  funext k; simp only [act, count_dagger, conj_conj, Pi.neg_apply]; ring

theorem act_eq_zero_iff (ts : List Twist) : act ts = 0 ↔ countBalanced ts := by
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp only [act, pos, Twist.conj, Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at h0 h1 h2 h3
    exact ⟨h0, h1.symm, h2, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext k
    fin_cases k <;> simp [act, pos, Twist.conj, h0, h1, h2, h3]

/-! ## The category -/

/-- **Morphisms `v ⟶ w`**: histories whose signed action carries `v` to `w`. -/
def Hom (v w : Fin 4 → ℤ) := {ts : List Twist // v + act ts = w}

def idH (v : Fin 4 → ℤ) : Hom v v := ⟨[], by rw [act_nil, add_zero]⟩

def comp {u v w : Fin 4 → ℤ} (f : Hom u v) (g : Hom v w) : Hom u w :=
  ⟨f.1 ++ g.1, by rw [act_append, ← add_assoc, f.2, g.2]⟩

theorem comp_assoc {u v w x : Fin 4 → ℤ} (f : Hom u v) (g : Hom v w) (h : Hom w x) :
    comp (comp f g) h = comp f (comp g h) := Subtype.ext (List.append_assoc _ _ _)

theorem id_comp {v w : Fin 4 → ℤ} (f : Hom v w) : comp (idH v) f = f := Subtype.ext rfl

theorem comp_id {v w : Fin 4 → ℤ} (f : Hom v w) : comp f (idH w) = f :=
  Subtype.ext (List.append_nil _)

/-- **The dagger**: conjugate every twist and reverse, `v ⟶ w` to `w ⟶ v`. -/
def dag {v w : Fin 4 → ℤ} (f : Hom v w) : Hom w v :=
  ⟨dagger f.1, by
    rw [act_dagger, ← sub_eq_add_neg, sub_eq_iff_eq_add]; exact f.2.symm⟩

theorem dagger_dagger (ts : List Twist) : dagger (dagger ts) = ts := by
  unfold dagger
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  conv_rhs => rw [← List.map_id ts]
  congr 1; funext t; exact conj_conj t

theorem dagger_append (a b : List Twist) : dagger (a ++ b) = dagger b ++ dagger a := by
  unfold dagger; rw [List.map_append, List.reverse_append]

theorem dag_dag {v w : Fin 4 → ℤ} (f : Hom v w) : dag (dag f) = f :=
  Subtype.ext (dagger_dagger f.1)

theorem dag_comp {u v w : Fin 4 → ℤ} (f : Hom u v) (g : Hom v w) :
    dag (comp f g) = comp (dag g) (dag f) := Subtype.ext (dagger_append _ _)

theorem dag_id (v : Fin 4 → ℤ) : dag (idH v) = idH v := Subtype.ext rfl

/-! ## The holonomy functor -/

/-- The holonomy of a morphism: its ordered fold. -/
noncomputable def hol {v w : Fin 4 → ℤ} (f : Hom v w) : Matrix (Fin 2) (Fin 2) ℂ :=
  twistMatrixFold f.1

theorem hol_id (v : Fin 4 → ℤ) : hol (idH v) = 1 := by simp [hol, idH, twistMatrixFold]

theorem hol_comp {u v w : Fin 4 → ℤ} (f : Hom u v) (g : Hom v w) :
    hol (comp f g) = hol f * hol g := fold_append _ _

theorem hol_dag {v w : Fin 4 → ℤ} (f : Hom v w) :
    hol (dag f) = (-1 : ℂ) ^ f.1.length • (hol f)ᴴ := fold_dagger _

/-- **Inverse modulo the centre**: `h ≫ h†` has holonomy `(−1)^|h|`. -/
theorem hol_comp_dag {v w : Fin 4 → ℤ} (f : Hom v w) :
    hol (comp f (dag f)) = (-1 : ℂ) ^ f.1.length • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  closure_by_dagger _

/-- **Every endomorphism is a closure**: count balanced, with holonomy `±1`. -/
theorem endo_closure {v : Fin 4 → ℤ} (f : Hom v v) :
    countBalanced f.1 ∧ (hol f = 1 ∨ hol f = -1) := by
  have h : act f.1 = 0 := by
    have := f.2
    exact add_eq_left.mp this
  have hb := (act_eq_zero_iff f.1).mp h
  exact ⟨hb, QLF.BalancedPhaseReal.balanced_phase_is_real hb⟩

/-! ## The channel kernel on the full channel space -/

/-- The fold of a length-`L` history given as a function. -/
noncomputable def foldF {L : ℕ} (h : Fin L → Twist) : Matrix (Fin 2) (Fin 2) ℂ :=
  twistMatrixFold (List.ofFn h)

/-- **The channel kernel**: the sum of folds over all length-`L` histories from `v` to `w`. -/
noncomputable def kernel (L : ℕ) (v w : Fin 4 → ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ h : Fin L → Twist, if v + act (List.ofFn h) = w then foldF h else 0

/-- The labels reachable from `v` in `L` steps. -/
noncomputable def reach (L : ℕ) (v : Fin 4 → ℤ) : Finset (Fin 4 → ℤ) :=
  Finset.univ.image (fun h : Fin L → Twist => v + act (List.ofFn h))

/-- **Composition over intermediate channels**:
    `K_{L₁+L₂}(v, w) = Σ_u K_{L₁}(v, u) K_{L₂}(u, w)`. -/
theorem kernel_compose (L₁ L₂ : ℕ) (v w : Fin 4 → ℤ) :
    kernel (L₁ + L₂) v w = ∑ u ∈ reach L₁ v, kernel L₁ v u * kernel L₂ u w := by
  have lhs : kernel (L₁ + L₂) v w = ∑ p : (Fin L₁ → Twist) × (Fin L₂ → Twist),
      if v + act (List.ofFn p.1) + act (List.ofFn p.2) = w then foldF p.1 * foldF p.2 else 0 := by
    unfold kernel
    refine Fintype.sum_equiv (Fin.appendEquiv L₁ L₂).symm _ _ fun h => ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b, h = Fin.append a b :=
      ⟨_, _, ((Fin.appendEquiv L₁ L₂).apply_symm_apply h).symm⟩
    have hs : (Fin.appendEquiv L₁ L₂).symm (Fin.append a b) = (a, b) :=
      (Fin.appendEquiv L₁ L₂).symm_apply_apply (a, b)
    simp only [hs, List.ofFn_fin_append, act_append, foldF, fold_append, add_assoc]
  rw [lhs, Fintype.sum_prod_type]
  symm
  calc ∑ u ∈ reach L₁ v, kernel L₁ v u * kernel L₂ u w
      = ∑ u ∈ reach L₁ v, ∑ a : Fin L₁ → Twist, ∑ b : Fin L₂ → Twist,
          if v + act (List.ofFn a) = u then
            (if u + act (List.ofFn b) = w then foldF a * foldF b else 0) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        unfold kernel
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
    _ = ∑ a : Fin L₁ → Twist, ∑ u ∈ reach L₁ v, ∑ b : Fin L₂ → Twist,
          if v + act (List.ofFn a) = u then
            (if u + act (List.ofFn b) = w then foldF a * foldF b else 0) else 0 :=
        Finset.sum_comm
    _ = ∑ a : Fin L₁ → Twist, ∑ b : Fin L₂ → Twist,
          if v + act (List.ofFn a) + act (List.ofFn b) = w then foldF a * foldF b else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        have hmem : v + act (List.ofFn a) ∈ reach L₁ v :=
          Finset.mem_image_of_mem _ (Finset.mem_univ a)
        rw [Finset.sum_eq_single (v + act (List.ofFn a))]
        · simp only [↓reduceIte]
        · intro u _ hu
          have : ¬ (v + act (List.ofFn a) = u) := Ne.symm hu
          simp only [this, ↓reduceIte, Finset.sum_const_zero]
        · intro h; exact absurd hmem h

/-- The dagger on length-`L` histories. -/
def dagF {L : ℕ} (h : Fin L → Twist) : Fin L → Twist := fun i => (h (Fin.rev i)).conj

lemma ofFn_dagF {L : ℕ} (h : Fin L → Twist) : List.ofFn (dagF h) = dagger (List.ofFn h) := by
  unfold dagger dagF
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.map_map, ← List.map_reverse,
    List.finRange_reverse, List.map_map]
  rfl

lemma dagF_dagF {L : ℕ} (h : Fin L → Twist) : dagF (dagF h) = h := by
  funext i; simp [dagF, conj_conj]

/-- **The kernel's dagger**: `K_L(w, v) = (−1)^L K_L(v, w)ᴴ`. -/
theorem kernel_dagger (L : ℕ) (v w : Fin 4 → ℤ) :
    kernel L w v = (-1 : ℂ) ^ L • (kernel L v w)ᴴ := by
  unfold kernel
  rw [conjTranspose_sum, Finset.smul_sum]
  let e : (Fin L → Twist) ≃ (Fin L → Twist) := ⟨dagF, dagF, dagF_dagF, dagF_dagF⟩
  refine Fintype.sum_equiv e _ _ fun h => ?_
  show _ = (-1 : ℂ) ^ L • (if v + act (List.ofFn (dagF h)) = w then foldF (dagF h) else 0)ᴴ
  rw [ofFn_dagF, act_dagger]
  have hiff : (v + -act (List.ofFn h) = w) ↔ (w + act (List.ofFn h) = v) := by
    constructor <;> intro hh <;> rw [← hh] <;> abel
  by_cases hc : w + act (List.ofFn h) = v
  · simp only [hc, hiff.mpr hc, ↓reduceIte]
    unfold foldF
    rw [ofFn_dagF, fold_dagger, conjTranspose_smul, conjTranspose_conjTranspose, smul_smul,
      List.length_ofFn]
    simp [← mul_pow]
  · have hc' : ¬ (v + -act (List.ofFn h) = w) := fun hh => hc (hiff.mp hh)
    simp only [hc, hc', ↓reduceIte]
    simp

end QLF.ChannelGroupoid
