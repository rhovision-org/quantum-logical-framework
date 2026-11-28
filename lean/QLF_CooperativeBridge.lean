import Mathlib
import QLF_TwistAlphabet

/-!
# QLF_CooperativeBridge — gates CC4, CC7, CC9 and competing listeners

Write-up: [`Cooperative_Intelligence.md`](../Cooperative_Intelligence.md) §5. Part of
[Quantum Logical Framework (QLF)](../README.md).

## CC4: a semantic-to-ZFA encoding, on a declared domain

The domain is **needs and offers on four kinds**. A cooperative history is a list of acts, each a
`need k` or an `offer k` with `k : Fin 4`. The encoding is fixed before any verdict: a need of kind `k`
is the twist on axis `k` and an offer is its conjugate, act by act (`encode`). On this domain:

* **`encode_closes_iff_met`**: the encoded history is count balanced (so ZFA closed, both conjuncts,
  by `count_balanced_pauli_closed`) **iff, for every kind, needs and offers are equal in number**.
  Sound and complete for exact one-for-one balance. **`surplus_offer_not_met`**: this is not
  fulfilment; a surplus offer answers every need and still does not close.
* **`encode_append`**: the encoding is a homomorphism, so it cannot see the verdict it produces.

Two limits, both proved:

* **`any_verdict_encodes`**: for any decidable predicate there is an encoding whose closure is that
  predicate. So the *existence* of an encoding is no evidence. An encoding counts only when it is fixed
  per act, as `encode` is.
* **`no_act_encoding_sees_order`**: no fixed, context-free per-act encoding into twist words, checked
  by count balance, can represent a
  semantics that distinguishes `[need, offer]` from `[offer, need]`. Count balance is order blind.
  "Answered after it was asked" is outside every structural encoding of this kind.

## CC7: first closure relative to a schedule

A schedule is an order of the same acts. `IsFirst h k`: the prefix of length `k` closes, and no
shorter nonempty prefix does.

* **`final_verdict_schedule_invariant`**: whether the whole history closes does not depend on the
  schedule.
* **`first_closure_schedule_dependent`**: when it first closes does.
* **`no_schedule_free_first_closure`**: no permutation-invariant function returns the first balanced
  prefix. This is about the schedule, not about whether a physical global clock exists.
* **`isFirst_append`**: a first closure stays first in every extension. It is a fact about a past
  prefix, not the current closure state.

## Competing listeners

A listener hears only the acts whose kind it attends to. `listenerFirst K h k` is its first closure
on the stream.

* **`race_schedule_dependent`**: which of two listeners closes first depends on the schedule.
* **`whole_met_listener_met`**: if the whole history is met, every listener's view is met. A met view
  is not a closure: **`vacuous_listener_never_closes`** (a listener that hears nothing) and
  **`partial_listener_views`** (views of an unbalanced whole can differ).
* **`listeners_cover_met`**: conversely, listeners whose kinds together cover all four, each met,
  make the whole history met.

## CC9: certificate verification

A certificate is a twist history with a claimed verdict.

* **`verifiers_agree`**: any two procedures that decide count balance are the same function. The
  verdict depends on the certificate, not on who checks it.
* **`verify_sound`**, **`verify_true_pauli`**: an accepted positive certificate is a Pauli receipt.
* **`verdict_certificate_is_the_bit`**: a certificate built from an external verifier's Boolean
  verifies exactly when the Boolean is true. It carries that bit and nothing more, which is the kill
  condition "a certificate restates an external verdict", proved.

**Kinds.** Everything here is derived. CC9's `verifiers_agree` is bookkeeping for any decidable
checker. CC4 is a bridge on the declared domain only; whether a real cooperative task *is* a
needs-and-offers history is a reading, and the order-blindness limit says which tasks it cannot be.
No axiom.
-/

namespace QLF.CooperativeBridge

open QLF

instance decCB : DecidablePred countBalanced := fun ts => by
  unfold countBalanced; infer_instance

/-! ## CC4 -/

/-- A cooperative act: a need or an offer of one of four kinds. -/
inductive Act
  | need (k : Fin 4)
  | offer (k : Fin 4)
  deriving DecidableEq, Repr

/-- The kind of an act. -/
def Act.kind : Act → Fin 4
  | need k => k
  | offer k => k

/-- Kind `k` is axis `k`: `^`, `<`, `/`, `+`. -/
def axisTwist : Fin 4 → Twist
  | 0 => Twist.up
  | 1 => Twist.left
  | 2 => Twist.slash
  | 3 => Twist.plus

/-- The per-act encoding: a need is its axis twist, an offer the conjugate. -/
def enc : Act → Twist
  | Act.need k => axisTwist k
  | Act.offer k => (axisTwist k).conj

/-- The encoding of a history, fixed act by act before any verdict. -/
def encode (h : List Act) : List Twist := h.map enc

/-- The intended semantics: every need is matched by an offer of the same kind. -/
def Met (h : List Act) : Prop := ∀ k : Fin 4, h.count (Act.need k) = h.count (Act.offer k)

instance (h : List Act) : Decidable (Met h) := by unfold Met; infer_instance

private theorem count_encode (h : List Act) (k : Fin 4) :
    (encode h).count (axisTwist k) = h.count (Act.need k) ∧
      (encode h).count (axisTwist k).conj = h.count (Act.offer k) := by
  induction h with
  | nil => simp [encode]
  | cons a h ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [encode, List.map_cons, List.count_cons] at ih1 ih2 ⊢
    rw [ih1, ih2]
    cases a with
    | need j =>
      fin_cases k <;> fin_cases j <;> simp (config := { decide := true })
    | offer j =>
      fin_cases k <;> fin_cases j <;> simp (config := { decide := true })

/-- **CC4 on the declared domain, sound and complete.** The encoded history closes iff every need is
matched by an offer of the same kind. -/
theorem encode_closes_iff_met (h : List Act) : countBalanced (encode h) ↔ Met h := by
  have h0 := count_encode h 0
  have h1 := count_encode h 1
  have h2 := count_encode h 2
  have h3 := count_encode h 3
  simp only [axisTwist, Twist.conj] at h0 h1 h2 h3
  unfold countBalanced Met
  constructor
  · rintro ⟨a, b, c, d⟩ k
    fin_cases k
    · simpa [h0.1, h0.2] using a
    · simpa [h1.1, h1.2] using b
    · simpa [h2.1, h2.2] using c
    · simpa [h3.1, h3.2] using d
  · intro hm
    exact ⟨by rw [h0.1, h0.2]; exact hm 0, by rw [h1.1, h1.2]; exact hm 1,
      by rw [h2.1, h2.2]; exact hm 2, by rw [h3.1, h3.2]; exact hm 3⟩

/-- A met history is a full ZFA closure: its fold is a Pauli scalar. -/
theorem met_pauli_closed {h : List Act} (hm : Met h) :
    ∃ p : PauliScalar, twistMatrixFold (encode h) = pauliScalarToMatrix p :=
  count_balanced_pauli_closed ((encode_closes_iff_met h).mpr hm)

/-- The encoding is a homomorphism of histories. -/
theorem encode_append (h h' : List Act) : encode (h ++ h') = encode h ++ encode h' := by
  simp [encode]

/-- **Limit: existence of an encoding is no evidence.** Any decidable predicate has an encoding
whose closure is exactly that predicate. -/
theorem any_verdict_encodes {α : Type*} (P : α → Prop) [DecidablePred P] :
    ∃ e : α → List Twist, ∀ a, countBalanced (e a) ↔ P a := by
  refine ⟨fun a => if P a then [] else [Twist.up], fun a => ?_⟩
  by_cases hp : P a
  · simp only [hp, ↓reduceIte, iff_true]; unfold countBalanced; decide
  · simp only [hp, ↓reduceIte, iff_false]; unfold countBalanced; decide

/-- **Limit: no per-act encoding sees order.** If a semantics `S` tells `[need k, offer k]` from
`[offer k, need k]`, no encoding of acts into twist words represents it by closure. -/
theorem no_act_encoding_sees_order (S : List Act → Prop) (k : Fin 4)
    (hS : S [Act.need k, Act.offer k] ∧ ¬ S [Act.offer k, Act.need k]) :
    ¬ ∃ f : Act → List Twist, ∀ h, countBalanced (h.map f).flatten ↔ S h := by
  rintro ⟨f, hf⟩
  have e1 := hf [Act.need k, Act.offer k]
  have e2 := hf [Act.offer k, Act.need k]
  have swap : countBalanced ([Act.need k, Act.offer k].map f).flatten ↔
      countBalanced ([Act.offer k, Act.need k].map f).flatten := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    unfold countBalanced
    simp only [List.count_append]
    constructor <;> rintro ⟨a, b, c, d⟩ <;> exact ⟨by omega, by omega, by omega, by omega⟩
  exact hS.2 (e2.mp (swap.mp (e1.mpr hS.1)))

/-- The worked instance of the order limit: offering before asking closes just as asking before
offering does. -/
theorem order_blind :
    Met [Act.need 0, Act.offer 0] ∧ Met [Act.offer 0, Act.need 0] := by
  decide

/-- **The domain is exact conservation, not fulfilment.** A surplus offer leaves every need answered
yet the history is not met and does not close. -/
theorem surplus_offer_not_met : ¬ Met [Act.need 0, Act.offer 0, Act.offer 0] := by
  decide

/-! ## CC7 -/

/-- The prefix of length `k` is nonempty and closes. -/
def ClosesAt (h : List Act) (k : ℕ) : Prop := 0 < k ∧ k ≤ h.length ∧ Met (h.take k)

instance (h : List Act) (k : ℕ) : Decidable (ClosesAt h k) := by
  unfold ClosesAt; infer_instance

/-- `k` is the first closure of the schedule `h`. -/
def IsFirst (h : List Act) (k : ℕ) : Prop := ClosesAt h k ∧ ∀ j < k, ¬ ClosesAt h j

instance (h : List Act) (k : ℕ) : Decidable (IsFirst h k) := by
  unfold IsFirst; infer_instance

/-- **The final verdict does not depend on the schedule.** -/
theorem final_verdict_schedule_invariant {h h' : List Act} (hp : h.Perm h') : Met h ↔ Met h' := by
  unfold Met
  simp only [hp.count_eq]

/-- Two schedules of the same acts. -/
def schedA : List Act := [Act.need 0, Act.offer 0, Act.need 1, Act.offer 1]
/-- The same acts, needs first. -/
def schedB : List Act := [Act.need 0, Act.need 1, Act.offer 0, Act.offer 1]

/-- **The first closure depends on the schedule.** Same acts, first closure at 2 in one schedule
and 4 in the other. -/
theorem first_closure_schedule_dependent :
    schedA.Perm schedB ∧ IsFirst schedA 2 ∧ IsFirst schedB 4 := by
  decide

/-- **No global now.** No function of the multiset of acts gives the first closure. -/
theorem no_schedule_free_first_closure :
    ¬ ∃ F : List Act → ℕ, (∀ h h', h.Perm h' → F h = F h') ∧ ∀ h k, IsFirst h k → F h = k := by
  rintro ⟨F, hinv, hF⟩
  obtain ⟨hp, ha, hb⟩ := first_closure_schedule_dependent
  have := hinv _ _ hp
  rw [hF _ _ ha, hF _ _ hb] at this
  omega

/-- **A first closure is a record.** Later acts never move it. -/
theorem isFirst_append {h : List Act} {k : ℕ} (e : List Act) (hk : IsFirst h k) :
    IsFirst (h ++ e) k := by
  obtain ⟨⟨hpos, hle, hm⟩, hmin⟩ := hk
  refine ⟨⟨hpos, by simp; omega, by rwa [List.take_append_of_le_length hle]⟩, ?_⟩
  rintro j hj ⟨hjpos, _, hjm⟩
  exact hmin j hj ⟨hjpos, by omega, by rwa [List.take_append_of_le_length (by omega)] at hjm⟩

/-! ## Competing listeners -/

/-- What a listener attending to the kinds `K` hears of a history. -/
def heard (K : Fin 4 → Bool) (h : List Act) : List Act := h.filter (fun a => K a.kind)

/-- The listener closes at stream position `k`: it has heard something by then, and what it heard
is met. -/
def ListenerCloses (K : Fin 4 → Bool) (h : List Act) (k : ℕ) : Prop :=
  0 < k ∧ k ≤ h.length ∧ heard K (h.take k) ≠ [] ∧ Met (heard K (h.take k))

instance (K : Fin 4 → Bool) (h : List Act) (k : ℕ) : Decidable (ListenerCloses K h k) := by
  unfold ListenerCloses; infer_instance

/-- The listener's first closure on the stream. -/
def ListenerFirst (K : Fin 4 → Bool) (h : List Act) (k : ℕ) : Prop :=
  ListenerCloses K h k ∧ ∀ j < k, ¬ ListenerCloses K h j

instance (K : Fin 4 → Bool) (h : List Act) (k : ℕ) : Decidable (ListenerFirst K h k) := by
  unfold ListenerFirst; infer_instance

/-- A listener for kind `0`. -/
def L0 : Fin 4 → Bool := fun k => k = 0
/-- A listener for kind `1`. -/
def L1 : Fin 4 → Bool := fun k => k = 1

/-- `schedA` with its two pairs swapped. -/
def schedC : List Act := [Act.need 1, Act.offer 1, Act.need 0, Act.offer 0]

/-- **Which listener closes first depends on the schedule.** -/
theorem race_schedule_dependent :
    schedA.Perm schedC ∧
      (ListenerFirst L0 schedA 2 ∧ ListenerFirst L1 schedA 4) ∧
      (ListenerFirst L1 schedC 2 ∧ ListenerFirst L0 schedC 4) := by
  decide

/-- **A met projection is not a closure.** One listener's view can be met while another's is not,
and a listener that hears nothing is vacuously met yet never closes. -/
theorem partial_listener_views :
    Met (heard L0 [Act.need 0, Act.offer 0, Act.need 1]) ∧
      ¬ Met (heard L1 [Act.need 0, Act.offer 0, Act.need 1]) := by
  decide

/-- A listener that hears nothing is vacuously met and never closes. -/
theorem vacuous_listener_never_closes :
    Met (heard L1 [Act.need 0, Act.offer 0]) ∧
      ∀ k, ¬ ListenerCloses L1 [Act.need 0, Act.offer 0] k := by
  refine ⟨by decide, ?_⟩
  rintro k ⟨_, hk, hne, _⟩
  apply hne
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k <;> decide

private theorem count_heard (K : Fin 4 → Bool) (h : List Act) (a : Act) :
    (heard K h).count a = if K a.kind then h.count a else 0 := by
  unfold heard
  split
  · rename_i hk
    exact List.count_filter (by simpa using hk)
  · rename_i hk
    apply List.count_eq_zero_of_not_mem
    intro hm
    exact hk (by simpa using (List.mem_filter.mp hm).2)

/-- **Agreement on whether.** If the whole history is met, every listener's view is met. -/
theorem whole_met_listener_met (K : Fin 4 → Bool) {h : List Act} (hm : Met h) :
    Met (heard K h) := by
  intro k
  rw [count_heard, count_heard]
  simp only [Act.kind]
  by_cases hk : K k = true <;> simp [hk, hm k]

/-- **Listeners that cover every kind, each met, make the whole met.** -/
theorem listeners_cover_met (Ks : List (Fin 4 → Bool)) (h : List Act)
    (hcov : ∀ k, ∃ K ∈ Ks, K k = true) (hm : ∀ K ∈ Ks, Met (heard K h)) : Met h := by
  intro k
  obtain ⟨K, hK, hk⟩ := hcov k
  have := hm K hK k
  rw [count_heard, count_heard] at this
  simpa [Act.kind, hk] using this

/-! ## CC9 -/

/-- A certificate: a twist history and the verdict claimed for it. -/
structure Cert where
  hist : List Twist
  claim : Bool

/-- Verification: recompute the verdict and compare it with the claim. -/
def verify (c : Cert) : Bool := decide (countBalanced c.hist) == c.claim

/-- **Verifiers agree.** Two procedures that each decide count balance are one function, so the
verdict depends on the certificate and not on who checks it. Bookkeeping for any decidable checker. -/
theorem verifiers_agree (v w : List Twist → Bool)
    (hv : ∀ ts, v ts = true ↔ countBalanced ts) (hw : ∀ ts, w ts = true ↔ countBalanced ts) :
    v = w := by
  funext ts
  exact Bool.eq_iff_iff.mpr ((hv ts).trans (hw ts).symm)

/-- An accepted certificate's claim is the true verdict. -/
theorem verify_sound {c : Cert} (hc : verify c = true) : (c.claim = true ↔ countBalanced c.hist) := by
  unfold verify at hc
  cases hcl : c.claim <;> simp_all

/-- An accepted positive certificate is a Pauli receipt. -/
theorem verify_true_pauli {c : Cert} (hc : verify c = true) (hpos : c.claim = true) :
    ∃ p : PauliScalar, twistMatrixFold c.hist = pauliScalarToMatrix p :=
  count_balanced_pauli_closed ((verify_sound hc).mp hpos)

/-- A certificate built from an external verifier's Boolean. -/
def Cert.ofVerdict (b : Bool) : Cert := ⟨if b then [] else [Twist.up], true⟩

/-- **A restated verdict is the bit.** The certificate verifies exactly when the external Boolean was
true, and carries nothing else. -/
theorem verdict_certificate_is_the_bit (b : Bool) : verify (Cert.ofVerdict b) = b := by
  cases b <;> decide

end QLF.CooperativeBridge
