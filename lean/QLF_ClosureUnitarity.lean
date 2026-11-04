import QLF_PhaseRule
import Mathlib

set_option linter.unusedVariables false

/-!
# QLF_ClosureUnitarity — **a closure is a point on a unitary path; a zero is either empty or cancelled**

First milestone of the closure-algebra programme of issue #207
([`Closure_Unitarity.md`](../Closure_Unitarity.md)). Three things are packaged here, all without axioms.

## U1 — every finite history is unitary

Each of the eight twists maps to `±σ` or `±I`: Hermitian and squaring to `I`, hence unitary
(`twist_unitary`). The ordered fold of **any** history, open or closed, is therefore in the unitary
group (`history_unitary`). Closure adds nothing here; unitarity is the ground on which closure is a
distinguished point.

## U1b — closure is the central point of that path

A count-balanced history is unitary **and** central-real: it folds to `+I` or `−I`
(`closure_on_unitary_path`, from `phase_rule_real`). The inclusion is strict — the single twist `^`
is a unitary history whose fold `σy` is neither (`unitary_history_not_closure`). So

    unitary history  ⊋  ZFA closure.

## U2 seed — the dagger completes every history to a closure

The conjugate-reverse history `dagger h = reverse (map conj h)` folds to `(−1)^|h| · U(h)†`
(`fold_dagger`): reversal gives the Hermitian adjoint (`fold_reverse`, each twist being Hermitian),
and each conjugation costs one sign. Hence **every** history, followed by its dagger, is a ZFA closure
with central sign `(−1)^|h|` (`closure_by_dagger`, `countBalanced_append_dagger`) — the general form
of the Hermitian-pair closure `t · t† = −I`. Unitarity `U U† = I` is exactly what makes `h ++ h†`
close.

## PZ3 — the zero taxonomy

For a seed `s` and continuation length `L`, the closure family is the set of length-`L`
continuations `c` with `s ++ c` balanced; the signed amplitude is the sum of their phases
(`predictedPhase`, an integer read off the word). The amplitude **is** the coherent matrix sum
(`matrix_amplitude`: `Σ U(s ++ c) = A · I`), so it is not the normalized event weight of
[`QLF_InterferenceNoGo`](QLF_InterferenceNoGo.lean). Two ways to be zero:

* **structural zero** — no admissible closure exists (`StructuralZero`);
* **interference zero** — closures exist, but their signed sum is exactly `0` (`InterferenceZero`).

They are exclusive and exhaust `A = 0` (`zero_taxonomy`, `zero_exclusive`).

## PZ3b — the `^<` cancellation, promoted to all orders

[`Perturbation_Theory_QLF.md`](../Perturbation_Theory_QLF.md) reported, from the registry, that the
seed `^<` has `W = 2, 72, 2820` ways at `L = 2, 4, 6` with `A_L = 0` throughout. That was a finite
observation. Here it is a theorem at **every** order, with its mechanism:

> **`antiHermitian_seed_forbidden`** — if a seed's fold is anti-Hermitian (`U(s)† = −U(s)`), its
> signed amplitude vanishes at every continuation length.

Reversing the continuation (`c ↦ c.reverse`) maps the closure family to itself and replaces
`U(c)` by `U(c)†`; when `U(s)† = −U(s)`, that flips the closing phase (`phase_reverse_flip`). So the
family splits into `±` pairs and cancels exactly — and no balanced continuation can be a palindrome.
`U(^<) = σy·(−σx) = iσz` is anti-Hermitian (`upLeft_antiHermitian`), so `^<` is forbidden to all
orders (`upLeft_forbidden_all_orders`) while having closures (`upLeft_interference_zero`): the zero is
**destructive interference driven by time reversal**, not an absence of histories. The registry counts
are re-derived as a cross-check (`upLeft_ways_two/four/six`). A Hermitian seed such as `^` has no such
pairing and a nonzero amplitude (`up_amplitude_one`); `^^^^` at `L = 2` is a structural zero
(`upFour_structural_zero_two`).

## Scope

Finite and exact. Not here: complete-channel unitarity `S†S = I` (U3) — `QLF_PolyaTransience`
proves the non-closing mass is positive, so closed channels alone cannot be normalized to one; poles
and the closure resolvent (PZ1–PZ2); any gluon kernel (G1–G4).
-/

namespace QLF.ClosureUnitarity

open QLF QLF.PhaseRule
open scoped Matrix

-- ==========================================
-- §1  U1 — every twist, and every history, is unitary
-- ==========================================

theorem sigma_x_herm : σxᴴ = σx := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σx, Matrix.conjTranspose_apply]

theorem sigma_y_herm : σyᴴ = σy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σy, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_I]

theorem sigma_z_herm : σzᴴ = σz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σz, Matrix.conjTranspose_apply]

/-- Every twist matrix is Hermitian. -/
theorem twist_herm (t : Twist) : (t.toMatrix)ᴴ = t.toMatrix := by
  cases t <;>
    simp [Twist.toMatrix, Matrix.conjTranspose_neg, sigma_x_herm, sigma_y_herm, sigma_z_herm]

/-- Every twist matrix squares to the identity. -/
theorem twist_sq (t : Twist) : t.toMatrix * t.toMatrix = 1 := by
  cases t <;> simp [Twist.toMatrix, sigma_x_sq, sigma_y_sq, sigma_z_sq]

/-- **Each twist is unitary**: Hermitian and an involution. -/
theorem twist_unitary (t : Twist) : t.toMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, twist_herm, twist_sq]

/-- **U1 — finite-history unitarity.** The ordered fold of every twist history, closed or open, is
    unitary. -/
theorem history_unitary (ts : List Twist) :
    twistMatrixFold ts ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  induction ts with
  | nil =>
    show (1 : M) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    exact one_mem _
  | cons t rest ih =>
    show t.toMatrix * twistMatrixFold rest ∈ Matrix.unitaryGroup (Fin 2) ℂ
    exact mul_mem (twist_unitary t) ih

/-- U1, written out: `U(h)† U(h) = I`. -/
theorem history_conjTranspose_mul (ts : List Twist) :
    (twistMatrixFold ts)ᴴ * twistMatrixFold ts = 1 := by
  have h := history_unitary ts
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

/-- U1, the other side: `U(h) U(h)† = I`. -/
theorem history_mul_conjTranspose (ts : List Twist) :
    twistMatrixFold ts * (twistMatrixFold ts)ᴴ = 1 := by
  have h := history_unitary ts
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
  exact h

-- ==========================================
-- §2  U1b — closure is the central-real point of the unitary path
-- ==========================================

/-- **U1b — closure on the unitary path.** A count-balanced history is unitary and folds to the
    real centre `{+I, −I}`. -/
theorem closure_on_unitary_path {ts : List Twist} (h : countBalanced ts) :
    twistMatrixFold ts ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (twistMatrixFold ts = 1 ∨ twistMatrixFold ts = -1) :=
  ⟨history_unitary ts, phase_rule_real h⟩

/-- **The inclusion is strict.** The one-twist history `^` is unitary, not balanced, and folds to
    `σy`, which is neither `+I` nor `−I`. -/
theorem unitary_history_not_closure :
    twistMatrixFold [Twist.up] ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ¬ countBalanced [Twist.up] ∧
      twistMatrixFold [Twist.up] ≠ 1 ∧ twistMatrixFold [Twist.up] ≠ -1 := by
  refine ⟨history_unitary _, ?_, ?_, ?_⟩
  · unfold countBalanced; decide
  · intro h
    have h00 := congrArg (fun A : M => A 0 0) h
    simp [twistMatrixFold, Twist.toMatrix, σy] at h00
  · intro h
    have h00 := congrArg (fun A : M => A 0 0) h
    simp [twistMatrixFold, Twist.toMatrix, σy] at h00

-- ==========================================
-- §3  U2 seed — reversal is the adjoint; the dagger completes every history
-- ==========================================

/-- The ordered fold is a monoid homomorphism `(List Twist, ++) → (M, *)`. -/
theorem fold_append (a b : List Twist) :
    twistMatrixFold (a ++ b) = twistMatrixFold a * twistMatrixFold b := by
  induction a with
  | nil => simp [twistMatrixFold]
  | cons t rest ih =>
    simp only [twistMatrixFold, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, Matrix.mul_assoc]

theorem fold_singleton (t : Twist) : twistMatrixFold [t] = t.toMatrix := by
  simp [twistMatrixFold]

/-- **Reversal is the adjoint.** Because every twist is Hermitian, reading a history backwards
    gives exactly the conjugate transpose of its fold. -/
theorem fold_reverse (ts : List Twist) :
    (twistMatrixFold ts)ᴴ = twistMatrixFold ts.reverse := by
  induction ts with
  | nil => simp [twistMatrixFold]
  | cons t rest ih =>
    rw [List.reverse_cons, fold_append, fold_singleton]
    show (t.toMatrix * twistMatrixFold rest)ᴴ = _
    rw [Matrix.conjTranspose_mul, ih, twist_herm]

/-- Conjugating a twist negates its matrix. -/
theorem conj_toMatrix (t : Twist) : t.conj.toMatrix = -t.toMatrix := by
  cases t <;> simp [Twist.conj, Twist.toMatrix]

/-- Conjugating every twist of a history costs one sign per twist. -/
theorem fold_map_conj (ts : List Twist) :
    twistMatrixFold (ts.map Twist.conj) = (-1 : ℂ) ^ ts.length • twistMatrixFold ts := by
  induction ts with
  | nil => simp [twistMatrixFold]
  | cons t rest ih =>
    show t.conj.toMatrix * twistMatrixFold (rest.map Twist.conj)
        = (-1 : ℂ) ^ (rest.length + 1) • (t.toMatrix * twistMatrixFold rest)
    rw [conj_toMatrix, ih, mul_smul_comm, pow_succ, mul_neg_one, neg_smul, neg_mul, smul_neg]

/-- The **dagger** of a history: conjugate every twist and reverse the order. -/
def dagger (ts : List Twist) : List Twist := (ts.map Twist.conj).reverse

/-- **The dagger folds to the adjoint**, up to the sign `(−1)^|h|`. -/
theorem fold_dagger (ts : List Twist) :
    twistMatrixFold (dagger ts) = (-1 : ℂ) ^ ts.length • (twistMatrixFold ts)ᴴ := by
  unfold dagger
  rw [← fold_reverse, fold_map_conj, Matrix.conjTranspose_smul]
  simp

/-- **Every history closes against its dagger**, with central sign `(−1)^|h|`. This is unitarity
    `U U† = I` read as a closure, and the general form of `t · t† = −I`. -/
theorem closure_by_dagger (ts : List Twist) :
    twistMatrixFold (ts ++ dagger ts) = (-1 : ℂ) ^ ts.length • (1 : M) := by
  rw [fold_append, fold_dagger, mul_smul_comm, history_mul_conjTranspose]

theorem count_map_conj (l : List Twist) (a : Twist) :
    (l.map Twist.conj).count a = l.count a.conj := by
  induction l with
  | nil => rfl
  | cons t rest ih =>
    cases t <;> cases a <;>
      simp (config := { decide := true }) [List.map_cons, List.count_cons, ih, Twist.conj]

theorem count_dagger (l : List Twist) (a : Twist) :
    (dagger l).count a = l.count a.conj := by
  unfold dagger
  rw [(List.reverse_perm _).count_eq, count_map_conj]

/-- **…and it is a ZFA closure in the counting sense too**: `h ++ dagger h` is count-balanced. -/
theorem countBalanced_append_dagger (ts : List Twist) : countBalanced (ts ++ dagger ts) := by
  unfold countBalanced
  simp only [List.count_append, count_dagger, Twist.conj]
  exact ⟨by omega, by omega, by omega, by omega⟩

-- ==========================================
-- §4  PZ3 — closure families, signed amplitudes, and the two kinds of zero
-- ==========================================

instance decBalanced : DecidablePred countBalanced := fun ts => by
  unfold countBalanced; infer_instance

/-- The eight twists, listed. -/
def allTwists : List Twist :=
  [Twist.up, Twist.down, Twist.left, Twist.right,
   Twist.slash, Twist.backslash, Twist.plus, Twist.minus]

theorem mem_allTwists (t : Twist) : t ∈ allTwists := by
  cases t <;> simp [allTwists]

/-- Every twist word of length `n` (the `8^n` continuations). -/
def words : ℕ → List (List Twist)
  | 0 => [[]]
  | n + 1 => allTwists.flatMap (fun t => (words n).map (List.cons t))

theorem mem_words : ∀ (n : ℕ) (c : List Twist), c ∈ words n ↔ c.length = n
  | 0, c => by cases c <;> simp [words]
  | n + 1, c => by
    cases c with
    | nil => simp [words]
    | cons t d =>
      simp only [words, List.mem_flatMap, List.mem_map, List.length_cons, mem_words n]
      constructor
      · rintro ⟨a, _, b, hb, hab⟩
        cases hab
        omega
      · intro h
        exact ⟨t, mem_allTwists t, d, by omega, rfl⟩

/-- **The closure family** of a seed at continuation length `L`: every length-`L` continuation
    that completes the seed to a count-balanced (hence ZFA-closed) history. -/
def closureFamily (seed : List Twist) (L : ℕ) : Finset (List Twist) :=
  ((words L).filter (fun c => decide (countBalanced (seed ++ c)))).toFinset

theorem mem_closureFamily (seed : List Twist) (L : ℕ) (c : List Twist) :
    c ∈ closureFamily seed L ↔ c.length = L ∧ countBalanced (seed ++ c) := by
  simp [closureFamily, List.mem_filter, mem_words]

/-- The multiplicity `W_L`: how many ways the seed closes at length `L`. -/
def ways (seed : List Twist) (L : ℕ) : ℕ := (closureFamily seed L).card

/-- The signed amplitude `A_L`: the sum of the closing phases (`±1`, from the phase rule). -/
def signedAmplitude (seed : List Twist) (L : ℕ) : ℤ :=
  ∑ c ∈ closureFamily seed L, predictedPhase (seed ++ c)

/-- **The signed amplitude is the coherent matrix amplitude.** Summing the actual `2×2` folds of
    the closing histories gives `A_L · I`. So `A_L` is an amplitude, not a normalized weight. -/
theorem matrix_amplitude (seed : List Twist) (L : ℕ) :
    ∑ c ∈ closureFamily seed L, twistMatrixFold (seed ++ c)
      = ((signedAmplitude seed L : ℤ) : ℂ) • (1 : M) := by
  unfold signedAmplitude
  rw [Int.cast_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro c hc
  exact fold_eq_predictedPhase ((mem_closureFamily seed L c).1 hc).2

/-- **Structural zero**: no admissible closure exists. -/
def StructuralZero (seed : List Twist) (L : ℕ) : Prop := closureFamily seed L = ∅

/-- **Interference zero**: closures exist, and their signed sum is exactly zero. -/
def InterferenceZero (seed : List Twist) (L : ℕ) : Prop :=
  (closureFamily seed L).Nonempty ∧ signedAmplitude seed L = 0

theorem structuralZero_amplitude {seed : List Twist} {L : ℕ} (h : StructuralZero seed L) :
    signedAmplitude seed L = 0 := by
  unfold StructuralZero at h
  simp [signedAmplitude, h]

/-- **The taxonomy is exhaustive**: a zero amplitude is structural or interference. -/
theorem zero_taxonomy (seed : List Twist) (L : ℕ) :
    signedAmplitude seed L = 0 ↔ StructuralZero seed L ∨ InterferenceZero seed L := by
  unfold StructuralZero InterferenceZero
  constructor
  · intro h
    rcases (closureFamily seed L).eq_empty_or_nonempty with he | hne
    · exact Or.inl he
    · exact Or.inr ⟨hne, h⟩
  · rintro (he | ⟨_, h⟩)
    · simp [signedAmplitude, he]
    · exact h

/-- **…and exclusive**: no zero is both. -/
theorem zero_exclusive (seed : List Twist) (L : ℕ) :
    ¬ (StructuralZero seed L ∧ InterferenceZero seed L) := by
  unfold StructuralZero InterferenceZero
  rintro ⟨he, hne, _⟩
  rw [he] at hne
  exact Finset.not_nonempty_empty hne

-- ==========================================
-- §5  PZ3b — anti-Hermitian seeds are forbidden at every order
-- ==========================================

/-- Reversing the continuation preserves balance. -/
theorem countBalanced_perm {a b : List Twist} (p : a.Perm b) (h : countBalanced b) :
    countBalanced a := by
  unfold countBalanced at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p.count_eq Twist.up, p.count_eq Twist.down]; exact h1
  · rw [p.count_eq Twist.left, p.count_eq Twist.right]; exact h2
  · rw [p.count_eq Twist.slash, p.count_eq Twist.backslash]; exact h3
  · rw [p.count_eq Twist.plus, p.count_eq Twist.minus]; exact h4

theorem balanced_reverse {seed c : List Twist} (h : countBalanced (seed ++ c)) :
    countBalanced (seed ++ c.reverse) :=
  countBalanced_perm (List.Perm.append_left seed (List.reverse_perm c)) h

/-- The matrix core of the flip: if `S† = −S`, `S² = −I`, `S F = φ I` and `S F† = ψ I` with `φ`
    real, then `ψ = −φ`. -/
theorem flip_core (S F : M) (φ ψ : ℂ) (hφ : star φ = φ) (hS : Sᴴ = -S)
    (hSS : S * S = -1) (e1 : S * F = φ • (1 : M)) (e2 : S * Fᴴ = ψ • (1 : M)) : ψ = -φ := by
  have e3 : Fᴴ * S = -(φ • (1 : M)) := by
    have h := congrArg Matrix.conjTranspose e1
    rw [Matrix.conjTranspose_mul, hS, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hφ,
      mul_neg] at h
    rw [← h, neg_neg]
  have e4 : S * Fᴴ = -(φ • (1 : M)) := by
    calc S * Fᴴ = S * Fᴴ * (S * -S) := by simp only [mul_neg, hSS, neg_neg, mul_one]
      _ = S * (Fᴴ * S) * -S := by simp only [mul_assoc]
      _ = -(φ • (1 : M)) := by
        rw [e3]
        simp only [mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_mul_assoc, mul_one, hSS,
          smul_neg]
  have h := e2.symm.trans e4
  have h00 := congrArg (fun A : M => A 0 0) h
  simpa using h00

/-- **The reversal flip.** For an anti-Hermitian seed, reversing a closing continuation reverses
    the sign of the closure. -/
theorem phase_reverse_flip (seed c : List Twist)
    (hS : (twistMatrixFold seed)ᴴ = -(twistMatrixFold seed))
    (hb : countBalanced (seed ++ c)) :
    predictedPhase (seed ++ c.reverse) = -predictedPhase (seed ++ c) := by
  have hU := history_conjTranspose_mul seed
  rw [hS, neg_mul] at hU
  have hSS : twistMatrixFold seed * twistMatrixFold seed = -1 := by
    have h := congrArg Neg.neg hU
    rwa [neg_neg] at h
  have e1 : twistMatrixFold seed * twistMatrixFold c
      = ((predictedPhase (seed ++ c) : ℤ) : ℂ) • (1 : M) := by
    rw [← fold_eq_predictedPhase hb, fold_append]
  have e2 : twistMatrixFold seed * (twistMatrixFold c)ᴴ
      = ((predictedPhase (seed ++ c.reverse) : ℤ) : ℂ) • (1 : M) := by
    rw [← fold_eq_predictedPhase (balanced_reverse hb), fold_append, fold_reverse]
  have hφ : star ((predictedPhase (seed ++ c) : ℤ) : ℂ) = ((predictedPhase (seed ++ c) : ℤ) : ℂ) := by
    simp
  have key := flip_core _ _ _ _ hφ hS hSS e1 e2
  exact_mod_cast key

/-- **PZ3b — anti-Hermitian seeds are forbidden at every order.** If a seed's fold satisfies
    `U(s)† = −U(s)`, then reversing the continuation pairs every closure with one of opposite sign,
    and the signed amplitude vanishes at every continuation length. -/
theorem antiHermitian_seed_forbidden (seed : List Twist)
    (hS : (twistMatrixFold seed)ᴴ = -(twistMatrixFold seed)) (L : ℕ) :
    signedAmplitude seed L = 0 := by
  unfold signedAmplitude
  have hflip : ∀ c ∈ closureFamily seed L,
      predictedPhase (seed ++ c.reverse) = -predictedPhase (seed ++ c) := fun c hc =>
    phase_reverse_flip seed c hS ((mem_closureFamily seed L c).1 hc).2
  have hmem : ∀ c ∈ closureFamily seed L, c.reverse ∈ closureFamily seed L := by
    intro c hc
    rw [mem_closureFamily] at hc ⊢
    exact ⟨by rw [List.length_reverse]; exact hc.1, balanced_reverse hc.2⟩
  refine Finset.sum_involution (fun c _ => c.reverse) ?_ ?_ ?_ ?_
  · intro c hc
    show predictedPhase (seed ++ c) + predictedPhase (seed ++ c.reverse) = 0
    rw [hflip c hc]
    ring
  · intro c hc hne heq
    have hne' : predictedPhase (seed ++ c) ≠ 0 := hne
    have heq' : c.reverse = c := heq
    have h := hflip c hc
    rw [heq'] at h
    omega
  · intro c hc
    exact hmem c hc
  · intro c hc
    exact List.reverse_reverse c

/-- **Corollary: no palindrome closes an anti-Hermitian seed.** -/
theorem antiHermitian_no_palindrome (seed c : List Twist)
    (hS : (twistMatrixFold seed)ᴴ = -(twistMatrixFold seed)) (hb : countBalanced (seed ++ c)) :
    c.reverse ≠ c := by
  intro heq
  have h := phase_reverse_flip seed c hS hb
  rw [heq] at h
  have h1 : predictedPhase (seed ++ c) = 1 ∨ predictedPhase (seed ++ c) = -1 := by
    unfold predictedPhase
    rcases neg_one_pow_eq_or ℤ (negCount (seed ++ c) + invCount (axisWord (seed ++ c))) with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  omega

-- ==========================================
-- §6  The seed `^<`, and two contrasts
-- ==========================================

/-- `U(^<) = σy · (−σx) = iσz` is anti-Hermitian. -/
theorem upLeft_antiHermitian :
    (twistMatrixFold [Twist.up, Twist.left])ᴴ = -(twistMatrixFold [Twist.up, Twist.left]) := by
  rw [fold_reverse]
  show Twist.left.toMatrix * (Twist.up.toMatrix * 1)
      = -(Twist.up.toMatrix * (Twist.left.toMatrix * 1))
  simp only [Twist.toMatrix, mul_one, neg_mul, mul_neg, neg_neg, anti_yx]

/-- **`^<` is forbidden at every order** — the registry's `A_L = 0` for `L = 2, 4, 6`, now for
    all `L`. -/
theorem upLeft_forbidden_all_orders (L : ℕ) :
    signedAmplitude [Twist.up, Twist.left] L = 0 :=
  antiHermitian_seed_forbidden _ upLeft_antiHermitian L

/-- **…and the zero is interference, not absence**: at `L = 2` the closures `v>` and `>v` exist. -/
theorem upLeft_interference_zero : InterferenceZero [Twist.up, Twist.left] 2 := by
  unfold InterferenceZero
  refine ⟨⟨[Twist.down, Twist.right], ?_⟩, upLeft_forbidden_all_orders 2⟩
  rw [mem_closureFamily]
  exact ⟨rfl, by unfold countBalanced; decide⟩

/-- Registry cross-check: `W_2 = 2`. -/
theorem upLeft_ways_two : ways [Twist.up, Twist.left] 2 = 2 := by native_decide

/-- Registry cross-check: `W_4 = 72`. -/
theorem upLeft_ways_four : ways [Twist.up, Twist.left] 4 = 72 := by native_decide

/-- Registry cross-check: `W_6 = 2820`. -/
theorem upLeft_ways_six : ways [Twist.up, Twist.left] 6 = 2820 := by native_decide

/-- **Contrast — a Hermitian seed is not forbidden.** `^` (fold `σy`, Hermitian) closes at `L = 1`
    only through `v`, with phase `−1`: amplitude `−1`, no cancellation. -/
theorem up_amplitude_one : signedAmplitude [Twist.up] 1 = -1 := by native_decide

/-- **Contrast — a structural zero.** `^^^^` cannot close in two more twists: it needs four `v`. -/
theorem upFour_structural_zero_two :
    StructuralZero [Twist.up, Twist.up, Twist.up, Twist.up] 2 := by
  unfold StructuralZero; native_decide

/-- The same seed is no longer structurally zero at `L = 4` (`vvvv`), so a structural zero is a
    statement about capacity, not a selection rule. -/
theorem upFour_ways_four : ways [Twist.up, Twist.up, Twist.up, Twist.up] 4 = 1 := by
  native_decide

theorem closure_unitarity_summary : True := trivial

end QLF.ClosureUnitarity
