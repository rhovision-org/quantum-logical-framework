import QLF_TwistAlphabet

/-!
# Finite accessible clock-domain records

Companion: Time_Reversed_Clock_Domains.md, issue #236.

A deliberately weak, closure-only model. The accessible record retains the
local word and counterpart length, but not counterpart order. Explicit balanced
histories witness non-identifiability for this interface. A stricter pairing
class may remove the witnesses. No physical time reversal, antimatter label,
horizon, causal noninterference, tick normalization or age map is derived.
-/

namespace QLF.ClockDomains

abbrev History := List Twist × List Twist
abbrev Record := List Twist × Nat

/-- Joint count balance is the only admissibility condition in this toy class. -/
def admissible (h : History) : Prop := countBalanced (h.1 ++ h.2)

/-- Accessible local word plus aggregate counterpart length. -/
def accessible (h : History) : Record := (h.1, h.2.length)

def canonical : History := ([Twist.up], [Twist.down])
def extendedLeft : History := ([Twist.up], [Twist.down, Twist.left, Twist.right])
def extendedRight : History := ([Twist.up], [Twist.down, Twist.right, Twist.left])

theorem canonical_admissible : admissible canonical := by
  unfold admissible canonical countBalanced
  decide

theorem extendedLeft_admissible : admissible extendedLeft := by
  unfold admissible extendedLeft countBalanced
  decide

theorem extendedRight_admissible : admissible extendedRight := by
  unfold admissible extendedRight countBalanced
  decide

/-- Fixing our local word does not select a unique count-balanced completion. -/
theorem alternative_completions :
    canonical.1 = extendedLeft.1 ∧ canonical.2 ≠ extendedLeft.2 ∧
      admissible canonical ∧ admissible extendedLeft := by
  exact ⟨rfl, by decide, canonical_admissible, extendedLeft_admissible⟩

theorem counterparts_distinct : extendedLeft.2 ≠ extendedRight.2 := by decide

theorem records_equal : accessible extendedLeft = accessible extendedRight := rfl

/-- Our interface distinguishes some admissible completions, so is not constant. -/
theorem records_distinct : accessible canonical ≠ accessible extendedLeft := by
  unfold accessible canonical extendedLeft
  decide

theorem accessible_nonconstant :
    ∃ h k : History, admissible h ∧ admissible k ∧ accessible h ≠ accessible k :=
  ⟨canonical, extendedLeft, canonical_admissible, extendedLeft_admissible,
    records_distinct⟩

/-- Two different counterpart words in one record fiber obstruct exact recovery
    on the stated admissible class. This asserts no causal invariance. -/
theorem collision_blocks_reconstruction (h k : History)
    (hh : admissible h) (hk : admissible k)
    (hsame : accessible h = accessible k) (hdiff : h.2 ≠ k.2) :
    ¬ ∃ R : Record → List Twist, ∀ x : History, admissible x → R (accessible x) = x.2 := by
  intro hex
  obtain ⟨R, hR⟩ := hex
  exact hdiff ((hR h hh).symm.trans ((congrArg R hsame).trans (hR k hk)))

/-- Concrete finite non-identifiability, rather than an assumed collision. -/
theorem no_exact_reconstruction :
    ¬ ∃ R : Record → List Twist, ∀ h : History, admissible h → R (accessible h) = h.2 :=
  collision_blocks_reconstruction extendedLeft extendedRight
    extendedLeft_admissible extendedRight_admissible records_equal counterparts_distinct

/-- More restrictive classes need not inherit the obstruction: if the
    counterpart is prescribed from the local word, it can be recovered. -/
theorem prescribed_counterpart_reconstructible (partner : List Twist → List Twist) :
    ∃ R : Record → List Twist, ∀ h : History,
      h.2 = partner h.1 → R (accessible h) = h.2 := by
  refine ⟨fun record => partner record.1, ?_⟩
  intro h hp
  exact hp.symm

end QLF.ClockDomains
