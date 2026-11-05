import QLF_Discoveries2026
import QLF_FirstReturn
import QLF_ClosureEquivalence
import QLF_IndexedFactors

set_option linter.unusedVariables false

/-!
# QLF_Polarons — polarons as irreducible shared ZFA closures

This module formalizes the substrate part of `Polarons_QLF.md`. It does **not** derive the
Fröhlich Hamiltonian, Landau–Pekar effective mass, or Bose-polaron spectroscopy. It proves the
QLF statements that precede those continuum bridges:

1. an open impurity plus a bath can form one joint ZFA closure;
2. if the impurity is open and the joint history closes, the bath is forced to be open too;
3. joint closure means exact opposite signed action on all four twist axes;
4. count balance already implies Pauli closure, so no second closure postulate is required;
5. adding `FirstReturn.IsPrime` makes the joint closure irreducible: no earlier nonempty prefix
   closes, and the full joint history is its unique prime first closure;
6. closure classes are the existing `ClosureEquiv` quotient, so microscopic histories with the
   same ledger and fold are one reportable class;
7. a concrete prime, genuinely non-factorizable witness exists: `^ | v`.

No axioms.
-/

namespace QLF.Polarons

open QLF

/-- Minimal polaron substrate predicate: the impurity does not close on its own, but the impurity
    followed by the bath does close. Bath openness is *derived* below, not assumed. -/
def IsPolaron (impurity bath : List Twist) : Prop :=
  ¬ countBalanced impurity ∧ countBalanced (impurity ++ bath)

/-- Expanded coupled-sector form: neither factor closes alone, while the pair closes jointly. -/
def CoupledPolaron (impurity bath : List Twist) : Prop :=
  ¬ countBalanced impurity ∧ ¬ countBalanced bath ∧ countBalanced (impurity ++ bath)

/-- An irreducible polaron: the joint history itself is a prime/first closure. -/
def PrimePolaron (impurity bath : List Twist) : Prop :=
  IsPolaron impurity bath ∧ QLF.FirstReturn.IsPrime (impurity ++ bath)

-- ============================================================================
-- 1. Shared closure is forced, not postulated twice
-- ============================================================================

/-- If an open impurity closes only after the bath is appended, the bath cannot already be a
    closure. This is `forced_sharing` specialized to the polaron predicate. -/
theorem polaron_bath_open {impurity bath : List Twist} (h : IsPolaron impurity bath) :
    ¬ countBalanced bath :=
  QLF.Discoveries2026.forced_sharing h.2 h.1

/-- The minimal definition and the explicit coupled-sector definition are equivalent. The bath-open
    conjunct is therefore a theorem, not an independent assumption. -/
theorem isPolaron_iff_coupled {impurity bath : List Twist} :
    IsPolaron impurity bath ↔ CoupledPolaron impurity bath := by
  constructor
  · intro h
    exact ⟨h.1, polaron_bath_open h, h.2⟩
  · intro h
    exact ⟨h.1, h.2.2⟩

/-- **Exact dressing condition.** Joint closure is equivalent to the bath carrying the exact
    opposite signed action of the impurity on all four QLF axes. -/
theorem polaron_actions_compensate {impurity bath : List Twist} (h : IsPolaron impurity bath) :
    QLF.Discoveries2026.net impurity Twist.up Twist.down =
        - QLF.Discoveries2026.net bath Twist.up Twist.down ∧
    QLF.Discoveries2026.net impurity Twist.left Twist.right =
        - QLF.Discoveries2026.net bath Twist.left Twist.right ∧
    QLF.Discoveries2026.net impurity Twist.slash Twist.backslash =
        - QLF.Discoveries2026.net bath Twist.slash Twist.backslash ∧
    QLF.Discoveries2026.net impurity Twist.plus Twist.minus =
        - QLF.Discoveries2026.net bath Twist.plus Twist.minus :=
  (QLF.Discoveries2026.countBalanced_append_iff impurity bath).mp h.2

/-- **Pauli closure is downstream of ZFA balance.** The joint polaron history folds to a Pauli
    scalar automatically; it need not be added to the polaron definition. -/
theorem polaron_pauli_closed {impurity bath : List Twist} (h : IsPolaron impurity bath) :
    ∃ p : PauliScalar,
      twistMatrixFold (impurity ++ bath) = pauliScalarToMatrix p :=
  count_balanced_pauli_closed h.2

-- ============================================================================
-- 2. First closure / irreducibility
-- ============================================================================

/-- A prime polaron is jointly balanced. -/
theorem prime_polaron_balanced {impurity bath : List Twist} (h : PrimePolaron impurity bath) :
    countBalanced (impurity ++ bath) :=
  h.1.2

/-- A prime polaron has no earlier nonempty balanced prefix. This is the exact formal content of
    calling the dressed history **irreducible**. -/
theorem prime_polaron_no_early_closure {impurity bath : List Twist}
    (h : PrimePolaron impurity bath) {k : ℕ}
    (hk : k < (impurity ++ bath).length) (hk0 : 0 < k) :
    ¬ countBalanced ((impurity ++ bath).take k) :=
  h.2.2.2 k hk hk0

/-- If any prime prefix of a prime-polaron history is exhibited, its length must be the full joint
    length. Thus the full impurity+bath event is the unique prime first closure. -/
theorem prime_polaron_first_closure_unique {impurity bath : List Twist}
    (h : PrimePolaron impurity bath) {ℓ : ℕ}
    (hℓ : ℓ ≤ (impurity ++ bath).length)
    (hp : QLF.FirstReturn.IsPrime ((impurity ++ bath).take ℓ)) :
    ℓ = (impurity ++ bath).length := by
  apply QLF.FirstReturn.prime_prefix_unique (impurity ++ bath) ℓ (impurity ++ bath).length
  · exact hℓ
  · exact le_rfl
  · exact hp
  · rw [List.take_length]; exact h.2

/-- Every minimal polaron has a unique prime first closure somewhere in its closing joint history.
    **Scope:** that prefix can end before the bath begins (a balanced prefix of the impurity alone,
    e.g. impurity `^v^`), so this theorem does not by itself give a first closure that involves both
    impurity and bath. `PrimePolaron` is the stronger condition: there the first closure is the full
    joint history, so it necessarily spans both. -/
theorem polaron_has_prime_prefix {impurity bath : List Twist} (h : IsPolaron impurity bath) :
    ∃ ℓ, ℓ ≤ (impurity ++ bath).length ∧
      QLF.FirstReturn.IsPrime ((impurity ++ bath).take ℓ) := by
  have hi_ne : impurity ≠ [] := by
    intro hi
    apply h.1
    subst impurity
    unfold countBalanced
    simp
  have hlen : 0 < (impurity ++ bath).length := by
    rw [List.length_append]
    have hi_pos : 0 < impurity.length := List.length_pos_of_ne_nil hi_ne
    omega
  exact QLF.FirstReturn.prime_prefix_exists (impurity ++ bath) h.2 hlen

-- ============================================================================
-- 3. Physical closure classes
-- ============================================================================

/-- The reportable class of a joint polaron history, using QLF's existing ledger+fold quotient.
    **This is a history-level equivalence by design.** It keeps the combined ledger and fold of
    `impurity ++ bath` and forgets where the impurity ends and the bath begins, so different
    partitions of one history give the same class. Before these classes are used to label physical
    branches, it is open whether the partition, the coupling or a boundary state must be kept too. -/
noncomputable def polaronClass (impurity bath : List Twist) :
    QLF.ClosureEquivalence.ClosureClass :=
  Quotient.mk QLF.ClosureEquivalence.closureSetoid (impurity ++ bath)

/-- Equal closure tokens give the same polaron class. This is the formal basis for grouping many
    microscopic bath histories into one branch/state only after the ledger **and** fold agree. -/
theorem polaronClass_eq_of_equiv
    {impurity₁ bath₁ impurity₂ bath₂ : List Twist}
    (h : QLF.ClosureEquivalence.ClosureEquiv
      (impurity₁ ++ bath₁) (impurity₂ ++ bath₂)) :
    polaronClass impurity₁ bath₁ = polaronClass impurity₂ bath₂ :=
  Quotient.sound h

-- ============================================================================
-- 4. Constructive witness: a genuinely coupled prime closure exists
-- ============================================================================

/-- Minimal open impurity witness. -/
def demoImpurity : List Twist := [Twist.up]

/-- Its complementary bath response. -/
def demoBath : List Twist := [Twist.down]

/-- `^ | v` is an actual prime polaron-shaped closure: neither side is balanced, their pair closes,
    and no earlier nonempty prefix closes. -/
theorem demo_prime_polaron : PrimePolaron demoImpurity demoBath := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold demoImpurity countBalanced; decide
  · unfold demoImpurity demoBath countBalanced; decide
  · unfold demoImpurity demoBath; decide

/-- The same witness is genuinely in the coupled sector: neither factor's fold is a scalar on its
    own, even though the joint history closes. This rules out reinterpreting the witness as two
    already-independent closed bodies. -/
theorem demo_nonfactorizable :
    (∀ c : ℂ, twistMatrixFold demoImpurity ≠ c • (1 : M)) ∧
    (∀ c : ℂ, twistMatrixFold demoBath ≠ c • (1 : M)) := by
  simpa [demoImpurity, demoBath] using
    QLF.IndexedFactors.shared_closure_not_factorizable.2

/-- There exists at least one irreducible, genuinely coupled composite closure of the form required
    by the polaron substrate model. This proves **possibility**, not the physical identification of
    any particular laboratory polaron with this minimal witness. -/
theorem prime_polaron_exists :
    ∃ impurity bath : List Twist,
      PrimePolaron impurity bath ∧
      (∀ c : ℂ, twistMatrixFold impurity ≠ c • (1 : M)) ∧
      (∀ c : ℂ, twistMatrixFold bath ≠ c • (1 : M)) := by
  exact ⟨demoImpurity, demoBath, demo_prime_polaron,
    demo_nonfactorizable.1, demo_nonfactorizable.2⟩

/-- Bundle the proved substrate content in one theorem. -/
theorem polaron_substrate_summary {impurity bath : List Twist} (h : PrimePolaron impurity bath) :
    ¬ countBalanced impurity ∧
    ¬ countBalanced bath ∧
    countBalanced (impurity ++ bath) ∧
    (∃ p : PauliScalar, twistMatrixFold (impurity ++ bath) = pauliScalarToMatrix p) ∧
    (∀ k, k < (impurity ++ bath).length → 0 < k →
      ¬ countBalanced ((impurity ++ bath).take k)) := by
  refine ⟨h.1.1, polaron_bath_open h.1, h.1.2, polaron_pauli_closed h.1, ?_⟩
  intro k hk hk0
  exact prime_polaron_no_early_closure h hk hk0

end QLF.Polarons
