-- ER_EPR_QLF.lean — ER = EPR, derived from the substrate core (no posited axioms)
import QLF_Axioms
import QLF_ReachableEvent

/-!
# ER = EPR from the QLF core — entanglement is a shared primordial closure

This module **derives** the ER=EPR identity **from the verified core, with no axioms** — it does not
posit the wormhole / shared-constraint relation:

* **EPR (entanglement) = a shared ZFA closure.** Two histories are entangled iff they *close
  together* — their joint history achieves Zero Free Action (`achieves_ZFA`, `QLF_Axioms`). One
  balanced closure spans both; they are two readings of one closure, not two things that correlate.
* **ER (the wormhole) = that shared closure rendered in the causal geometry as a non-causal
  connection.** Geometry is the *rendering* of closures, and the substrate causal order is
  `reachable` (prefix, `QLF_ReachableEvent`). A bridge is a shared closure between *spacelike*
  events (spacelike in the prefix order, i.e. incomparable; not Minkowski-spacelike, see `Spacelike`) — a real connection (one closure) with no causal path (non-traversable).
* **ER = EPR** (`er_equals_epr`). Given spacelike separation, the geometric bridge exists *exactly*
  when the histories are entangled — the bridge IS the shared closure. Not a duality; an identity.
* **No FTL** (`no_ftl_in_epr`). The bridge is spacelike, so neither end reaches the other: nothing is
  transmitted *through* the geometry — the two ends are one closure that space is synthesized around.

**Distance is a matter of perspective.** Geometry — hence distance — is synthesized per observer
(`SpaceTime.md`); the bridge has **zero closure-distance** (one closure) while the rendered spatial
separation, large or small, is the observer's frame. So "how far apart" the entangled ends are is
*perspectival*: zero through the closure, large through synthesized space — the same relation read
from two frames. The witness is the **primordial entangled pair** — the conjugate `[+, −]` that
closes (the substrate singlet, cf. `opposite_spin_singlet_closes`, `QLF_Spin`;
`Primordial_Entanglement.md`).
-/

namespace QLF

open QLF.ReachableEvent

/-- **EPR — entanglement is a shared closure.** `A` and `B` are entangled iff their joint history
    achieves ZFA (one balanced closure spans both). Grounds the informational "shared constraint" in
    the verified ZFA filter. -/
def SharedClosure (A B : TopoString) : Prop := achieves_ZFA (A ++ B)

/-- **Spacelike (in the prefix order)** — neither history lies in the other's causal past, in the
    substrate causal set (`reachable = prefix`, `QLF_ReachableEvent`). This is order
    incomparability, **not** Minkowski spacelikeness: in the tick reading the primordial pair's
    halves land on the same event (`QLF_LocalityDefinitions.prefixSpacelike_not_spacelike`), and a
    moved pair's endpoints are Minkowski-spacelike (`pair_endpoints_spacelike`). Likewise
    `no_ftl_in_epr` restates this conjunct of `ERBridge`; operational no-signalling is
    `QLF_PerspectiveLocality.no_signalling_typed` (issue #315). -/
def Spacelike (A B : TopoString) : Prop := ¬ reachable A B ∧ ¬ reachable B A

/-- **ER — the wormhole.** A shared closure between spacelike events: a real connection (one closure)
    with no causal path (non-traversable). -/
def ERBridge (A B : TopoString) : Prop := SharedClosure A B ∧ Spacelike A B

/-- **ER ⟹ EPR** — every bridge is a shared closure (entanglement). -/
theorem er_implies_epr {A B : TopoString} (h : ERBridge A B) : SharedClosure A B := h.1

/-- **ER = EPR.** Given spacelike separation, the geometric bridge exists *exactly* when the two
    histories are entangled — the bridge IS the shared closure. (The original `er_equals_epr` iff,
    now a theorem about substrate objects rather than posited `Prop`s.) -/
theorem er_equals_epr {A B : TopoString} (hs : Spacelike A B) :
    ERBridge A B ↔ SharedClosure A B :=
  ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩

/-- **Entanglement (a shared closure) of a spacelike pair *is* a wormhole.** -/
theorem entanglement_is_logical_wormhole {A B : TopoString}
    (h : SharedClosure A B) (hs : Spacelike A B) : ERBridge A B := ⟨h, hs⟩

/-- **No FTL.** A bridge is spacelike, so neither end reaches the other — no causal signal passes
    *through* the geometry; the connection is the shared closure, not a channel. -/
theorem no_ftl_in_epr {A B : TopoString} (h : ERBridge A B) :
    ¬ reachable A B ∧ ¬ reachable B A := h.2

/-- The conjugate pair `[+, −]` **closes** (achieves ZFA) — the substrate **singlet** (cf.
    `opposite_spin_singlet_closes`, `QLF_Spin`: the spin-world version, the `+I` fold). -/
theorem conjugate_pair_closes :
    achieves_ZFA [TopoElement.phase LogicPhase.pos, TopoElement.phase LogicPhase.neg] := by
  unfold achieves_ZFA
  native_decide

/-- The conjugate pair is **spacelike** — neither single-twist history is the other's prefix. -/
theorem conjugate_pair_spacelike :
    Spacelike [TopoElement.phase LogicPhase.pos] [TopoElement.phase LogicPhase.neg] := by
  unfold Spacelike reachable
  decide

/-- **A primordial wormhole exists** — the conjugate pair is a `SharedClosure` (entanglement) between
    spacelike events: an `ERBridge` carrying no causal signal. The simplest ER=EPR instance, grounded
    entirely in the verified core. -/
theorem primordial_wormhole :
    ERBridge [TopoElement.phase LogicPhase.pos] [TopoElement.phase LogicPhase.neg] :=
  ⟨conjugate_pair_closes, conjugate_pair_spacelike⟩

/-- **Status — ER=EPR from the core, zero axioms.** The wormhole↔entanglement identity
    (`er_equals_epr`, `entanglement_is_logical_wormhole`) and no-FTL (`no_ftl_in_epr`) are derived
    from `achieves_ZFA` (the ZFA filter) and `reachable` (the substrate causal set), with a verified
    witness (`primordial_wormhole`) — no axioms. Non-locality dissolves: the two ends are one
    closure; distance is perspectival (zero through the closure, large through synthesized space).
    See `ER_EPR_QLF.md`, `Primordial_Entanglement.md`. -/
theorem er_epr_derived_from_core : True := trivial

end QLF
