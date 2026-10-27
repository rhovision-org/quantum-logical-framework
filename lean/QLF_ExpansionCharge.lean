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

end QLF
