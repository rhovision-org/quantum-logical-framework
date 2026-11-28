import Mathlib
import QLF_ModelTesting

/-!
# QLF_AnthropicEquivalence — **every computable model has an equivalent closure encoding**

Obligation O2 of [`Framing.md`](../Framing.md) §6: the theorem `Correct(M) ⟹ ∃ E_M, O_QLF ∘ E_M = O_M`
of §3a. The anthropic argument says any solution need only account for what can be observed, and an
observation is a finite record (A10: no measurement yields a real number). So a model is given here by
what it can be checked against:

* `Model S` — a state space `S`, a **computable** admissibility test `allowed : S → Bool` (Deutsch's
  physical Church–Turing premise, stated as a premise), and the **finite record** `observe : S → List
  Bool` each state leaves.

**Results** (no axioms):

* `decode` is **one observable map for every model**: it reads a twist history back as the record it
  carries (`decode_recordWord_append`). Nothing about `M` enters it.
* `anthropic_equivalence` — for every model `M` there is an encoding `E_M` with
  `Admissible E_M s ↔ M.allowed s` and `decode ∘ E_M = M.observe`: **`O_QLF ∘ E_M = O_M`**.
* `encodeModel_canFail_iff` — and the test is not vacuous: the encoding can fail exactly when the model
  forbids something (contrast `pairEncoding_cannot_fail`).
* `verdicts_transfer` — every verdict about the model's observations (necessary, possible, impossible)
  is the same verdict about closures.
* `frequencies_transfer` — the probability side: in any finite ensemble, the number of allowed states
  with a given record equals the number of closing histories that decode to it (A10: probabilities are
  counts).
* `same_observations_equivalent` — two models that allow the same states and record the same things
  are `Equivalent` through their encodings, hence get the same verdicts (`equivalent_same_verdicts`).

**The non-circular case.** The encoding above reads `allowed` to decide where to fail, so for an
arbitrary model the content is in the premise, not the construction. For the models whose selection
rule is a **conservation law**, the equal-and-opposite form itself, the encoding is built part by part
from the charges and never consults admissibility:

* `ChargeModel` — each state is a list of parts carrying integer charges; `conservation_equivalence`:
  the part-by-part encoding closes **iff the total charge is zero**, decodes to the record, and can fail
  iff some state violates conservation. Here closure *computes* the model's selection rule.

**Scope.** Dynamics enter by taking trajectories as states. What is not claimed: that a given model is
correct (that is the premise `Correct(M)`, which only experiment decides), nor anything about models
using uncomputable resources, which fall outside the premise. This is equivalence at the level of
records; the finer question of which joint closures distinguish histories is `ObsEquiv`
([`QLF_ObservationalEquivalence`](QLF_ObservationalEquivalence.lean)).
-/

namespace QLF.AnthropicEquivalence

open QLF QLF.ModelTesting

private instance decCB : DecidablePred countBalanced := fun ts => by
  unfold countBalanced; infer_instance

/-! ## Records as closures, and the universal decoder -/

/-- A record bit as a closed pair: `0 ↦ > <`, `1 ↦ / \`. -/
def bitWord : Bool → List Twist
  | false => [Twist.right, Twist.left]
  | true => [Twist.slash, Twist.backslash]

/-- A record as a closure. -/
def recordWord (r : List Bool) : List Twist := r.flatMap bitWord

/-- **The universal observable map `O_QLF`**: read closed pairs back as bits, stop at anything else. -/
def decode : List Twist → List Bool
  | Twist.slash :: Twist.backslash :: rest => true :: decode rest
  | Twist.right :: Twist.left :: rest => false :: decode rest
  | _ => []

theorem decode_recordWord_append (r : List Bool) (tail : List Twist)
    (ht : ∀ rest, tail ≠ Twist.slash :: Twist.backslash :: rest)
    (ht' : ∀ rest, tail ≠ Twist.right :: Twist.left :: rest) :
    decode (recordWord r ++ tail) = r ++ decode tail := by
  induction r with
  | nil => simp [recordWord]
  | cons b r ih =>
    cases b <;> simp only [recordWord, List.flatMap_cons, bitWord, List.cons_append,
      List.nil_append, decode] at ih ⊢ <;> rw [ih] <;> rfl

theorem decode_recordWord (r : List Bool) : decode (recordWord r) = r := by
  have := decode_recordWord_append r [] (fun _ h => by simp at h) (fun _ h => by simp at h)
  simpa [decode] using this

theorem count_recordWord (r : List Bool) :
    (recordWord r).count Twist.up = 0 ∧ (recordWord r).count Twist.down = 0 ∧
    (recordWord r).count Twist.plus = 0 ∧ (recordWord r).count Twist.minus = 0 ∧
    (recordWord r).count Twist.left = (recordWord r).count Twist.right ∧
    (recordWord r).count Twist.slash = (recordWord r).count Twist.backslash := by
  induction r with
  | nil => simp [recordWord]
  | cons b r ih =>
    simp only [recordWord, List.flatMap_cons, List.count_append] at ih ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    cases b <;> simp only [bitWord] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true }) [List.count_cons] <;>
      omega

theorem recordWord_closes (r : List Bool) : countBalanced (recordWord r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := count_recordWord r
  exact ⟨by rw [h1, h2], h5, h6, by rw [h3, h4]⟩

theorem recordWord_plus_open (r : List Bool) : ¬ countBalanced (recordWord r ++ [Twist.plus]) := by
  obtain ⟨_, _, h3, h4, _, _⟩ := count_recordWord r
  rintro ⟨_, _, _, h⟩
  simp only [List.count_append, h3, h4] at h
  simp (config := { decide := true }) at h

/-! ## Every computable model -/

/-- A model: a computable admissibility test and the finite record each state leaves. -/
structure Model (S : Type) where
  allowed : S → Bool
  observe : S → List Bool

variable {S : Type}

/-- The encoding of a model: the record as a closure, left open by one gauge twist where the model
    forbids the state. -/
def encodeModel (M : Model S) : Encoding S :=
  ⟨fun s => if M.allowed s then recordWord (M.observe s) else recordWord (M.observe s) ++ [Twist.plus]⟩

theorem admissible_iff (M : Model S) (s : S) :
    Admissible (encodeModel M) s ↔ M.allowed s = true := by
  unfold Admissible encodeModel
  cases h : M.allowed s
  · simp only [h, Bool.false_eq_true, ↓reduceIte, iff_false]; exact recordWord_plus_open _
  · simp only [h, ↓reduceIte, iff_true]; exact recordWord_closes _

theorem decode_encode (M : Model S) (s : S) : decode ((encodeModel M).encode s) = M.observe s := by
  unfold encodeModel
  cases h : M.allowed s
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [decode_recordWord_append _ _ (fun _ h => by simp at h) (fun _ h => by simp at h)]
    simp [decode]
  · simp only [h, ↓reduceIte]; exact decode_recordWord _

/-- **The anthropic equivalence theorem.** For every computable model with finite records there is an
    encoding `E_M` that admits exactly the model's allowed states and whose decoding is the model's
    observable: `O_QLF ∘ E_M = O_M`, with one `O_QLF` for all models. -/
theorem anthropic_equivalence (M : Model S) :
    ∃ E : Encoding S, (∀ s, Admissible E s ↔ M.allowed s = true) ∧
      (fun s => decode (E.encode s)) = M.observe :=
  ⟨encodeModel M, admissible_iff M, funext (decode_encode M)⟩

/-- **Not vacuous**: the encoding can fail exactly when the model forbids a state. -/
theorem encodeModel_canFail_iff (M : Model S) :
    CanFail (encodeModel M) ↔ ∃ s, M.allowed s = false := by
  unfold CanFail
  simp only [admissible_iff, Bool.not_eq_true]

/-- **Verdicts transfer**: every verdict about the model's observations is the same verdict about
    closures. -/
theorem verdicts_transfer (M : Model S) (Q : List Bool → Prop) :
    (Necessary (encodeModel M) (fun s => Q (decode ((encodeModel M).encode s))) ↔
        ∀ s, M.allowed s = true → Q (M.observe s)) ∧
      (Possible (encodeModel M) (fun s => Q (decode ((encodeModel M).encode s))) ↔
        ∃ s, M.allowed s = true ∧ Q (M.observe s)) ∧
      (Impossible (encodeModel M) (fun s => Q (decode ((encodeModel M).encode s))) ↔
        ∀ s, M.allowed s = true → ¬ Q (M.observe s)) := by
  simp [Necessary, Possible, Impossible, admissible_iff, decode_encode]

/-- **Frequencies transfer**: in a finite ensemble, allowed states with a given kind of record are as
    many as closing histories that decode to it. -/
theorem frequencies_transfer (M : Model S) (q : List Bool → Bool) (l : List S) :
    l.countP (fun s => M.allowed s && q (M.observe s)) =
      l.countP (fun s => decide (countBalanced ((encodeModel M).encode s)) &&
        q (decode ((encodeModel M).encode s))) := by
  congr 1; funext s
  have h := admissible_iff M s
  unfold Admissible at h
  rw [decode_encode]
  cases ha : M.allowed s <;> simp_all

/-- **Models with the same observations are equivalent** through their encodings. -/
theorem same_observations_equivalent (M₁ M₂ : Model S) (ha : ∀ s, M₁.allowed s = M₂.allowed s)
    (ho : ∀ s, M₁.allowed s = true → M₁.observe s = M₂.observe s) :
    Equivalent (encodeModel M₁) (encodeModel M₂) (fun s => decode ((encodeModel M₁).encode s))
      (fun s => decode ((encodeModel M₂).encode s)) := by
  intro s
  refine ⟨by rw [admissible_iff, admissible_iff, ha], fun h => ?_⟩
  dsimp only
  rw [decode_encode, decode_encode]
  exact ho s ((admissible_iff M₁ s).mp h)

/-! ## The non-circular case: conservation laws -/

/-- A charge as a one-axis word: `q` ups or `−q` downs. -/
def chargeWord (q : ℤ) : List Twist :=
  if 0 ≤ q then List.replicate q.toNat Twist.up else List.replicate (-q).toNat Twist.down

theorem count_rep (a b : Twist) (k : ℕ) :
    (List.replicate k b).count a = if a = b then k else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    cases a <;> cases b <;> simp (config := { decide := true })

theorem chargeWord_counts (q : ℤ) :
    ((chargeWord q).count Twist.up : ℤ) - (chargeWord q).count Twist.down = q ∧
      (chargeWord q).count Twist.left = 0 ∧ (chargeWord q).count Twist.right = 0 ∧
      (chargeWord q).count Twist.slash = 0 ∧ (chargeWord q).count Twist.backslash = 0 ∧
      (chargeWord q).count Twist.plus = 0 ∧ (chargeWord q).count Twist.minus = 0 := by
  unfold chargeWord
  split_ifs with h
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) [count_rep] <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) [count_rep] <;> omega

theorem charges_counts (qs : List ℤ) :
    ((qs.flatMap chargeWord).count Twist.up : ℤ) - (qs.flatMap chargeWord).count Twist.down =
        qs.sum ∧
      (qs.flatMap chargeWord).count Twist.left = 0 ∧ (qs.flatMap chargeWord).count Twist.right = 0 ∧
      (qs.flatMap chargeWord).count Twist.slash = 0 ∧
      (qs.flatMap chargeWord).count Twist.backslash = 0 ∧
      (qs.flatMap chargeWord).count Twist.plus = 0 ∧ (qs.flatMap chargeWord).count Twist.minus = 0 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := chargeWord_counts q
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := ih
    simp only [List.flatMap_cons, List.count_append, List.sum_cons, c2, c3, c4, c5, c6, c7,
      i2, i3, i4, i5, i6, i7, add_zero, and_true]
    push_cast
    linear_combination c1 + i1

/-- A model whose selection rule is a conservation law: each state is a list of charged parts. -/
structure ChargeModel (S : Type) where
  parts : S → List ℤ
  observe : S → List Bool

/-- The part-by-part encoding: the record, then each part's charge. It never consults admissibility. -/
def encodeCharge (M : ChargeModel S) : Encoding S :=
  ⟨fun s => recordWord (M.observe s) ++ (M.parts s).flatMap chargeWord⟩

theorem mem_charges (qs : List ℤ) (t : Twist) (h : t ∈ qs.flatMap chargeWord) :
    t = Twist.up ∨ t = Twist.down := by
  obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp h
  unfold chargeWord at hq
  split_ifs at hq
  · exact Or.inl (List.eq_of_mem_replicate hq)
  · exact Or.inr (List.eq_of_mem_replicate hq)

theorem decode_of_head (t : Twist) (w : List Twist) (h : t = Twist.up ∨ t = Twist.down) :
    decode (t :: w) = [] := by
  rcases h with rfl | rfl <;> cases w <;> rfl

theorem decode_charges (qs : List ℤ) : decode (qs.flatMap chargeWord) = [] := by
  cases hw : qs.flatMap chargeWord with
  | nil => rfl
  | cons t w => exact decode_of_head t w (mem_charges qs t (by rw [hw]; exact List.mem_cons_self))

theorem decode_charge_tail (qs : List ℤ) :
    (∀ rest, qs.flatMap chargeWord ≠ Twist.slash :: Twist.backslash :: rest) ∧
      (∀ rest, qs.flatMap chargeWord ≠ Twist.right :: Twist.left :: rest) := by
  constructor
  · intro rest h
    rcases mem_charges qs Twist.slash (by rw [h]; exact List.mem_cons_self) with h' | h' <;> cases h'
  · intro rest h
    rcases mem_charges qs Twist.right (by rw [h]; exact List.mem_cons_self) with h' | h' <;> cases h'

/-- **Conservation laws are computed by closure.** The part-by-part encoding closes exactly when the
    total charge vanishes, decodes to the record, and can fail exactly when some state violates
    conservation. -/
theorem conservation_equivalence (M : ChargeModel S) :
    (∀ s, Admissible (encodeCharge M) s ↔ (M.parts s).sum = 0) ∧
      (∀ s, decode ((encodeCharge M).encode s) = M.observe s) ∧
      (CanFail (encodeCharge M) ↔ ∃ s, (M.parts s).sum ≠ 0) := by
  have hadm : ∀ s, Admissible (encodeCharge M) s ↔ (M.parts s).sum = 0 := by
    intro s
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := count_recordWord (M.observe s)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := charges_counts (M.parts s)
    unfold Admissible encodeCharge countBalanced
    simp only [List.count_append, r1, r2, r3, r4, c2, c3, c4, c5, c6, c7, add_zero, zero_add]
    constructor
    · rintro ⟨h, _, _, _⟩
      rw [← c1, h, sub_self]
    · intro h
      refine ⟨?_, r5, r6, trivial⟩
      have : ((M.parts s).flatMap chargeWord).count Twist.up =
          ((M.parts s).flatMap chargeWord).count Twist.down := by
        have := c1.trans h; omega
      exact this
  refine ⟨hadm, fun s => ?_, ?_⟩
  · obtain ⟨t1, t2⟩ := decode_charge_tail (M.parts s)
    unfold encodeCharge
    rw [decode_recordWord_append _ _ t1 t2]
    have hd := decode_charges (M.parts s)
    rw [hd, List.append_nil]
  · unfold CanFail; simp only [hadm]

end QLF.AnthropicEquivalence
