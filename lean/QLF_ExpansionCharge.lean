import QLF_Handedness
/-!
# QLF_ExpansionCharge — a net expand/contract is a charge effect, and charge alone

`Lumina_QLF.md` §10 pre-registers a prediction: the cosmic expand/contract imbalance tracks the
**ionization** (charge-separation) field, not the neutral-matter density. This module anchors the one
part of that claim ZFA actually forces — that the net expand/contract of a history lives on the **gauge
(charge) axis and nowhere else** — so the prediction is not a free choice but the only handedness-covariant
possibility.

**The physical identification is established elsewhere, not here.** That *expansion/contraction is
temporal* (the future/present faces of an event, `event_duality_balanced`, `QLF_CosmicInflation`) and that
*time is synthesized from the gauge axis* — only the two gauge twists `+ −` carry temporal binding, the six
spatial twists carry spatial extension (the 6+2 split of `QLF_CosmologicalConstant.gauge_axis_fraction`,
and the time-from-gauge synthesis of `ZFAEventDynamics`) — are the substrate facts that make the gauge axis
the expansion axis. Taking that as given, this module proves, over `QLF_Handedness`, the handedness-level
consequences that complete the chain:

* **`netExpansion_eq_charge`** — the net expand/contract (the gauge handedness) *is* the chiral charge.
* **`closed_no_net_expansion`** / **`neutral_pair_no_net_expansion`** — a ZFA-closed event, and any
  concatenation of neutral (charge-balanced) events, has zero net expand/contract: a **neutral atom
  sources none**, its `+` and `−` locked together. This is the "cancels locally" step of §10.
* **`spatial_imbalance_sources_nothing`** — a purely spatial handedness imbalance (a net spin on `X`, `Y`
  or `Z`) sources **zero** net expansion. This is the content: expansion tracks charge *specifically*, not
  handedness in general. Had expansion read the spatial components too, the §10 prediction would attach to
  the density/spin field, not the ionization field — so this lemma is the one that could have come out
  otherwise, and does not (method rule 4).
* **`charge_sources_net_expansion`** — a charged (ionized) configuration sources a nonzero net expansion.

So the gap in the §10 prediction is exactly its *amplitude* (the ZFA `+`/`−` interaction rate, still
underived); its *location* — on the charge axis, zero for neutral matter — is forced. No new axiom; all
over `QLF_Handedness`.
-/
namespace QLF

open QLF.Spin

/-- The net expand/contract of a history: its handedness on the gauge axis. `+` (right-handed gauge)
    contracts, `−` (left-handed gauge) expands, so this signed count is the net of the two faces. The
    identification of the gauge axis as the *temporal* (expansion) axis is the 6+2 split of
    `QLF_CosmologicalConstant` / the time-from-gauge synthesis of `ZFAEventDynamics`, used here as given. -/
def netExpansion (ts : List Twist) : Int := handednessOn Axis.I ts

/-- **The net expand/contract is the chiral charge.** Not analogous to it — equal to it, because both are
    the one primitive (handedness) read on the gauge axis (`chiralCharge_eq_handednessOn_gauge`). -/
theorem netExpansion_eq_charge (ts : List Twist) : netExpansion ts = chiralCharge ts :=
  (chiralCharge_eq_handednessOn_gauge ts).symm

/-- **A ZFA-closed event sources no net expand/contract.** Closure is handedness balance on every axis
    (`zfa_iff_handedness_balanced`), the gauge axis included. -/
theorem closed_no_net_expansion (ts : List Twist) (h : countBalanced ts) :
    netExpansion ts = 0 :=
  (zfa_iff_handedness_balanced ts).mp h Axis.I

/-- **Neutral matter cancels it locally.** Two charge-balanced events, concatenated, still source zero —
    the `+` and `−` stay locked. (A neutral atom is such an event; a gas of them is such a concatenation.) -/
theorem neutral_pair_no_net_expansion (h₁ h₂ : List Twist)
    (hc₁ : countBalanced h₁) (hc₂ : countBalanced h₂) :
    netExpansion (h₁ ++ h₂) = 0 := by
  have e₁ := (zfa_iff_handedness_balanced h₁).mp hc₁ Axis.I
  have e₂ := (zfa_iff_handedness_balanced h₂).mp hc₂ Axis.I
  unfold netExpansion
  rw [handednessOn_append]
  omega

/-- **A purely spatial imbalance sources nothing.** A single right-handed `X`-twist carries a net spatial
    handedness (`handednessOn Axis.X = 1`) yet its net expansion is `0`: expansion reads the **charge**
    component, not spin. This is the lemma that distinguishes the §10 prediction (ionization-tracking)
    from a density/spin-tracking one — and it could have been false. -/
theorem spatial_imbalance_sources_nothing :
    handednessOn Axis.X [rightTwist Axis.X] = 1 ∧ netExpansion [rightTwist Axis.X] = 0 := by
  decide

/-- **A charged (ionized) configuration sources a nonzero net expansion.** The lone gauge twist `+` has
    `netExpansion = 1`: break a neutral closure — ionize — and the expand/contract term switches on. -/
theorem charge_sources_net_expansion :
    netExpansion [rightTwist Axis.I] = 1 := by
  decide

/-- **Summary.** Net expand/contract equals charge, vanishes for every neutral/closed configuration, is
    untouched by spatial (spin) imbalance, and is switched on only by net charge. The §10 prediction's
    *location* on the ionization field is forced; only its amplitude is open. -/
theorem expansion_is_charge_not_spin :
    (∀ ts : List Twist, netExpansion ts = chiralCharge ts) ∧
      (∀ ts : List Twist, countBalanced ts → netExpansion ts = 0) ∧
      netExpansion [rightTwist Axis.X] = 0 ∧
      netExpansion [rightTwist Axis.I] = 1 :=
  ⟨netExpansion_eq_charge, closed_no_net_expansion,
    (spatial_imbalance_sources_nothing).2, charge_sources_net_expansion⟩

-- ==========================================
-- The sign is the arrow, not a count (anchors Lumina_QLF.md §11 K1)
-- ==========================================

/-- Gauge conjugation (`reflect Axis.I`: swap `+ ↔ −`, leave the spatial twists) negates net expansion,
    because handedness on the gauge axis is negated when its two twists are swapped. The spatial twists
    the reflection also touches do not enter `netExpansion` at all. -/
theorem handednessOn_I_map_reflect_I (ts : List Twist) :
    handednessOn Axis.I (ts.map (reflect Axis.I)) = - handednessOn Axis.I ts := by
  induction ts with
  | nil => simp [handednessOn]
  | cons t rest ih =>
    rw [List.map_cons, handednessOn_cons, handednessOn_cons, ih, reflect_twistAxis]
    by_cases h : twistAxis t = Axis.I
    · rw [if_pos h, if_pos h]
      have hr : reflect Axis.I t = Twist.conj t := by unfold reflect; rw [if_pos h]
      rw [hr, handedness_conj]; ring
    · rw [if_neg h, if_neg h]; ring

/-- `reflect Axis.I` is an involution on twists: conjugating the gauge twists twice is the identity. -/
theorem reflect_I_involutive (t : Twist) : reflect Axis.I (reflect Axis.I t) = t := by
  cases t <;> decide

/-- …and hence on histories. So gauge conjugation pairs each history with a unique partner. -/
theorem map_reflect_I_involutive (ts : List Twist) :
    (ts.map (reflect Axis.I)).map (reflect Axis.I) = ts := by
  induction ts with
  | nil => rfl
  | cons t rest ih => rw [List.map_cons, List.map_cons, reflect_I_involutive, ih]

/-- **Gauge conjugation sends closures to closures.** It negates the gauge handedness (which was zero)
    and leaves every spatial handedness untouched, so count balance is preserved. -/
theorem gauge_conjugate_closure (ts : List Twist) (h : countBalanced ts) :
    countBalanced (ts.map (reflect Axis.I)) := by
  rw [zfa_iff_handedness_balanced] at h ⊢
  intro a
  by_cases ha : a = Axis.I
  · subst ha
    have := h Axis.I
    rw [handednessOn_I_map_reflect_I]
    omega
  · rw [handednessOn_map_reflect_other ha ts]
    exact h a

/-- **The sign of the expand/contract term is the arrow, not a count** (Lumina_QLF.md §11 K1, proved).
    Gauge conjugation is an involution that sends every ZFA closure to a ZFA closure while *negating* net
    expansion. So the closures carrying net expansion `+n` are in exact bijection with those carrying
    `−n`: **no count distinguishes expansion from contraction.** The universe's net expansion therefore
    cannot come from a multiplicity bias between `+` and `−`; it is carried entirely by the irreversible
    time arrow (`QLF_ClosureDepthLaw.closedAtHorizon_mono` — `−` closes into not-yet-synthesized future
    time, `+` within already-synthesized present time). The census (`expansion_rate_qlf.py`) confirms the
    bijection numerically: the `+`-seed and `−`-seed first-closure multiplicities match to the integer. -/
theorem expansion_sign_not_a_count :
    (∀ ts : List Twist, countBalanced ts → countBalanced (ts.map (reflect Axis.I))) ∧
      (∀ ts : List Twist, netExpansion (ts.map (reflect Axis.I)) = - netExpansion ts) ∧
      (∀ ts : List Twist, (ts.map (reflect Axis.I)).map (reflect Axis.I) = ts) :=
  ⟨gauge_conjugate_closure, handednessOn_I_map_reflect_I, map_reflect_I_involutive⟩

end QLF
