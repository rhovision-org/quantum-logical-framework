import QLF_TwistAlphabet

/-!
# QLF_ModelTesting — **the model-encoding interface and its verdicts**

Obligation O3 of [`Framing.md`](../Framing.md) §6: a typed interface for "encode a model as closures",
whose verdicts are the ones of [`Framing.md`](../Framing.md) §4, and a theorem that says when such a
test tells us nothing.

A **model** is a type `S` of states (or processes) with an **encoding** `encode : S → List Twist`. A
state is **admissible** when its encoding closes (count balance, which entails Pauli closure by
`count_balanced_pauli_closed`). For a proposition `P` about states:

* `Necessary E P` — every admissible state satisfies `P`;
* `Possible E P` — some admissible state satisfies `P`;
* `Impossible E P` — no admissible state satisfies `P`;
* `Equivalent E₁ E₂ O₁ O₂` — two models over one state space whose admissible states and observables
  agree.

*Undetermined* is not a proposition: it is the record that none of the above has been proved, and it
stays the default.

**Results** (no axioms):

* `possible_iff_not_impossible` — the two refutation-side verdicts are complementary.
* `necessary_and_possible` — with at least one admissible state, necessity gives possibility.
* `CanFail` — an encoding can fail when some state does not close. `vacuous_of_cannot_fail`: if it
  cannot, every verdict about `P` is a verdict about the model alone, and the substrate contributed
  nothing. This is the formal content of "an oracle must be one the construction could fail", and the
  reason `qlf_universality` is bookkeeping ([`Principles.md`](../Principles.md) P10):
  `pairEncoding_cannot_fail` is its encoding pattern (each element becomes a cancelling pair), and it
  cannot fail.
* `identity_can_fail` — the identity encoding of histories can fail, so tests through it have content.
* `impossible_of_never_closes`, `possible_of_witness` — the two ways a verdict is established: a
  theorem over all states, or a witness.
* `equivalent_same_verdicts` — observationally equivalent models receive the same verdict on every
  observable proposition: the proved step of the anthropic argument (obligation O2 is the rest).
-/

namespace QLF.ModelTesting

open QLF

/-- A model with an encoding of its states as twist histories. -/
structure Encoding (S : Type) where
  encode : S → List Twist

variable {S : Type}

/-- A state is admissible when its encoding closes. -/
def Admissible (E : Encoding S) (s : S) : Prop := countBalanced (E.encode s)

def Necessary (E : Encoding S) (P : S → Prop) : Prop := ∀ s, Admissible E s → P s
def Possible (E : Encoding S) (P : S → Prop) : Prop := ∃ s, Admissible E s ∧ P s
def Impossible (E : Encoding S) (P : S → Prop) : Prop := ∀ s, Admissible E s → ¬ P s

/-- Two encodings of one state space are equivalent for observables `O₁`, `O₂` when they admit the
    same states and those states look the same. -/
def Equivalent {α : Type} (E₁ E₂ : Encoding S) (O₁ O₂ : S → α) : Prop :=
  ∀ s, (Admissible E₁ s ↔ Admissible E₂ s) ∧ (Admissible E₁ s → O₁ s = O₂ s)

/-- An encoding can fail when some state does not close. -/
def CanFail (E : Encoding S) : Prop := ∃ s, ¬ Admissible E s

theorem possible_iff_not_impossible (E : Encoding S) (P : S → Prop) :
    Possible E P ↔ ¬ Impossible E P := by
  unfold Possible Impossible
  constructor
  · rintro ⟨s, hs, hp⟩ h
    exact h s hs hp
  · intro h
    by_contra hn
    exact h fun s hs hp => hn ⟨s, hs, hp⟩

theorem necessary_and_possible (E : Encoding S) (P : S → Prop) (h : Necessary E P)
    (hne : ∃ s, Admissible E s) : Possible E P := by
  obtain ⟨s, hs⟩ := hne
  exact ⟨s, hs, h s hs⟩

theorem possible_of_witness (E : Encoding S) (P : S → Prop) (s : S) (hs : Admissible E s)
    (hp : P s) : Possible E P := ⟨s, hs, hp⟩

theorem impossible_of_never_closes (E : Encoding S) (P : S → Prop)
    (h : ∀ s, P s → ¬ Admissible E s) : Impossible E P :=
  fun s hs hp => h s hp hs

/-- **A test through an encoding that cannot fail tells us nothing**: every verdict reduces to a
    statement about the model alone. -/
theorem vacuous_of_cannot_fail (E : Encoding S) (h : ¬ CanFail E) (P : S → Prop) :
    (Necessary E P ↔ ∀ s, P s) ∧ (Possible E P ↔ ∃ s, P s) ∧
      (Impossible E P ↔ ∀ s, ¬ P s) := by
  have hall : ∀ s, Admissible E s := fun s => by
    by_contra hn
    exact h ⟨s, hn⟩
  refine ⟨⟨fun hn s => hn s (hall s), fun hp s _ => hp s⟩,
    ⟨fun ⟨s, _, hp⟩ => ⟨s, hp⟩, fun ⟨s, hp⟩ => ⟨s, hall s, hp⟩⟩,
    ⟨fun hi s => hi s (hall s), fun hp s _ => hp s⟩⟩

/-- The encoding pattern of `qlf_universality`: each element becomes a cancelling pair. -/
def pairEncoding (S : Type) : Encoding (List S) :=
  ⟨fun l => l.flatMap fun _ => [Twist.right, Twist.left]⟩

theorem pairEncoding_closes (l : List S) : Admissible (pairEncoding S) l := by
  unfold Admissible pairEncoding countBalanced
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.count_append] at ih ⊢
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true }) [List.count_cons] <;> omega

/-- **The pair encoding cannot fail**, so tests through it are vacuous. -/
theorem pairEncoding_cannot_fail : ¬ CanFail (pairEncoding S) :=
  fun ⟨l, hl⟩ => hl (pairEncoding_closes l)

/-- The identity encoding of histories. -/
def idEncoding : Encoding (List Twist) := ⟨id⟩

/-- **The identity encoding can fail**: `^` alone does not close. -/
theorem identity_can_fail : CanFail idEncoding := by
  refine ⟨[Twist.up], ?_⟩
  unfold Admissible idEncoding countBalanced
  decide

/-- **Observationally equivalent models get the same verdicts** on every observable proposition
    (one that depends on the state only through what is observed). This is the formal step of the
    anthropic argument that is proved: no test of what can be observed separates equivalent models.
    That a correct model *is* equivalent to QLF is obligation O2, not this theorem. -/
theorem equivalent_same_verdicts {α : Type} (E₁ E₂ : Encoding S) (O₁ O₂ : S → α)
    (h : Equivalent E₁ E₂ O₁ O₂) (Q : α → Prop) :
    (Necessary E₁ (fun s => Q (O₁ s)) ↔ Necessary E₂ (fun s => Q (O₂ s))) ∧
      (Possible E₁ (fun s => Q (O₁ s)) ↔ Possible E₂ (fun s => Q (O₂ s))) ∧
      (Impossible E₁ (fun s => Q (O₁ s)) ↔ Impossible E₂ (fun s => Q (O₂ s))) := by
  have key : ∀ s, Admissible E₂ s → (Q (O₁ s) ↔ Q (O₂ s)) := fun s hs => by
    rw [(h s).2 ((h s).1.mpr hs)]
  refine ⟨⟨fun hn s hs => (key s hs).mp (hn s ((h s).1.mpr hs)),
      fun hn s hs => (key s ((h s).1.mp hs)).mpr (hn s ((h s).1.mp hs))⟩,
    ⟨fun ⟨s, hs, hq⟩ => ⟨s, (h s).1.mp hs, (key s ((h s).1.mp hs)).mp hq⟩,
      fun ⟨s, hs, hq⟩ => ⟨s, (h s).1.mpr hs, (key s hs).mpr hq⟩⟩,
    ⟨fun hi s hs hq => hi s ((h s).1.mpr hs) ((key s hs).mpr hq),
      fun hi s hs hq => hi s ((h s).1.mp hs) ((key s ((h s).1.mp hs)).mp hq)⟩⟩

end QLF.ModelTesting
