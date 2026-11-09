# Holography Audit — what QLF proves about bulk and boundary

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

**Status labels** follow [`ScientificApproach.md`](ScientificApproach.md): *proved*, *exact computational*, *definition*, *cited*, *prose only*, *incorrect*.
**Lean anchors:** [`lean/QLF_HolographicBoundary.lean`](lean/QLF_HolographicBoundary.lean) and [`lean/QLF_HolographicArea.lean`](lean/QLF_HolographicArea.lean) (no axioms). §5 records the follow-up pass that resolved two of the gaps.

## 0. Verdict

The holographic principle comes up throughout QLF's prose. [`CLAUDE.md`](CLAUDE.md) calls it "a topological necessity of closure". Before this audit, the Lean held **no theorem relating a bulk to a boundary**. What the Lean did hold was:

* an **area law by definition**: `holographic_event_count R := 4πR²` ([`QLF_GravityFromDelay`](lean/QLF_GravityFromDelay.lean)) and `holographic_event_count_blanket v := 20v²` ([`QLF_PrimordialMarkovBlanket`](lean/QLF_PrimordialMarkovBlanket.lean)). `holographic_entropy_eq` is `ring` over that definition, so the `R²` is an input and not a result;
* exact bookkeeping *on top of* the definition: `holographic_bh_ratio = 4 log 2` ([`QLF_HolographicDensity`](lean/QLF_HolographicDensity.lean)), `lqg_horizon_is_holographic` (`rfl`), `bh_entropy_first_law`.

This audit adds three proved statements. Together they are the precise content that "the boundary determines the bulk" can carry, and they also show where it carries nothing:

| # | Statement | Lean | What it carries |
|---|---|---|---|
| 1 | **Closure is a boundary property.** A twist history is count-balanced iff its `ℤ⁴` walk sends zero net flux through the boundary of *every* region. The one-cell boundary around the start already suffices | `outFlux_eq`, `closed_iff_zero_flux_everywhere`, `closure_iff_boundary_silent` | **Bookkeeping** (method rule 4). The flux identity telescopes and holds for every walk. The only ZFA content is the endpoint condition |
| 2 | **The bulk is the prefix closure of the boundary**, because every prefix extends to a closure (append its conjugate) | `every_prefix_closes`, `bulk_eq_prefixes_of_boundary` | The boundary determines the bulk only because the bulk is **all** of possibility. No finite path is pruned. Selection works on *measure* (≥ ¼ of possibility never closes, [`QLF_FirstReturn`](lean/QLF_FirstReturn.lean); numerically 80.7 %, [`Closure_Walk.md`](Closure_Walk.md)) and not on existence |
| 3 | **Area law from locality.** If each shared pair (one `log 2` bit) joins adjacent sites, the entropy a region shares with its outside is `≤ |∂A| · log 2` | `area_law_of_local_pairs`, `cutEntropy_le_area` | **A real area law, derived from one premise: locality.** `nonlocal_pairs_break_area_law` shows the premise is needed. Three nonlocal pairs cross a two-edge boundary, which is a volume law |

**The finding that matters:** an area law does not follow from closure. It follows from the **locality of shared closures**, and QLF has not derived that. The tensor-product work (`QLF_TensorFromClosure`, PR #219, open) derives *that* a shared pair entangles two bodies, with one half on each body. Nothing yet says the two bodies must be neighbours. That premise is where holography's content lives, and it is now the named open gap (§3).

## 1. Inventory: every holographic claim, classified

### Lean

| Item | Module | Status |
|---|---|---|
| `holographic_event_count R = 4πR²` | `QLF_GravityFromDelay` | **definition** (the area law is an input) |
| `holographic_entropy_eq : S = 4πR² log 2` | `QLF_GravityFromDelay` | proved, but `ring` over the definition |
| `holographic_event_count_blanket v = 20v²` | `QLF_PrimordialMarkovBlanket` | **definition** (`rfl`). The face count of the geodesic icosahedron is real geometry, but "one event per face" is an identification |
| `holographic_bh_ratio = 4 log 2`, `residual_is_quarter_times_quantum` | `QLF_HolographicDensity` | proved. It measures the gap between `N log 2` and Bekenstein–Hawking `N/4` exactly. Does not close it |
| `lqg_horizon_is_holographic` | `QLF_LoopQuantumGravity` | `rfl` (naming) |
| `bh_entropy_first_law`, `bhEntropyOfMass_eq_area` | `QLF_HorizonFirstLaw` | proved (continuum Bekenstein–Hawking algebra) |
| `hadron_horizon_entropy_eq` | `QLF_QuantumBlackHole` | re-export of `holographic_entropy_eq` |
| `blanket_doubling_doubles_information` | `QLF_NoFreeDuplication` | proved over the definitional `20v²` |
| `info_synthesis_disjunctive`, `no_free_duplication_summary` | `QLF_InfoSynthesis`, `QLF_NoFreeDuplication` | `: True := trivial`. Summary markers that anchor nothing |
| **New:** flux theorem, bulk-from-boundary, area law from locality | `QLF_HolographicBoundary` | **proved**, no axioms (table in §0) |

### Prose

| Claim | Where | Status |
|---|---|---|
| "The AdS/CFT identity … is machine-verified in `RhoQuCalc.lean` and `ZFAEventDynamics.lean`" | [`Holographic.md`](Holographic.md) | **incorrect.** Neither file mentions a bulk, a boundary, AdS or holography. Corrected in place; the provable content is §0 row 2 |
| "The entire bulk is mathematically identical to the sum of its boundary states" | [`Holographic.md`](Holographic.md), [`CLAUDE.md`](CLAUDE.md) | **now proved in a precise form** (rows 1–2), and the precise form shows it is weak. The sum identity telescopes, and the bulk is the prefix closure of the boundary because every prefix closes |
| `holographic.py`: the action vector "encoded faithfully as a 2-component logical state", giving a "3D bulk observable" and a "1D boundary encoding" | [`Holographic.md`](Holographic.md) §2–§6 | **incorrect as stated** (§2 below). The map is many-to-one and cannot tell a closure from an open history |
| "The factor ¼ … is the minimal number of gauge twists needed for ZFA closure" | [`Entropy.md`](Entropy.md) §3 | **incorrect.** `QLF_HolographicDensity` proves QLF's count exceeds Bekenstein–Hawking by `4 log 2`. The ¼ is an open residual, not derived |
| "A Pauli-closed history of length `2k` carries `log C(2k,k)` nats … recovering the area law in the large-`k` asymptotic" | [`Entropy.md`](Entropy.md) §1 | **incorrect.** `log C(2k,k) = 2k log 2 − ½ log(πk) + o(1)` is linear in length. That is extensive (volume-like) in the history, not an area law |
| Ryu–Takayanagi "is the area law applied to the same per-atom quantum" | [`Quantum_Gravity.md`](Quantum_Gravity.md) §4 | **prose only.** Row 3 is the honest discrete form: RT-type counting holds *when* shared pairs are local |
| de Sitter = replication, AdS = interlocking closures | [`Holographic.md`](Holographic.md), [`Curvature.md`](Curvature.md) | **prose only** (no Lean) |
| Holographic QEC: `full_zeno_prune` "is the machine-verified boundary decoder" | [`CLAUDE.md`](CLAUDE.md) | **prose only.** `full_zeno_prune` is verified as a filter, and no code property (distance, recovery) is proved |
| [`QLF_Holographic_Computational_Universe.md`](QLF_Holographic_Computational_Universe.md) cites `ER_EPR_QLF.lean` as "formal Lean proof that ER = EPR" | that file | **overstated.** `er_equals_epr` unpacks a conjunction (naming) |

## 2. The `holographic.py` bridge, checked

[`holographic.py`](holographic.py) maps a prefix's action `(v,h,d,l)` to `ψ = (v+ih, d+il)/‖·‖` and reads off the Bloch vector `(X,Y,Z)` and `φ = arg β − arg α`. The algebra is correct: `X²+Y²+Z² = 1`, and `ψ → −ψ` leaves `(X,Y,Z)` fixed. The readings in `Holographic.md` do not hold up. Running the module's own functions:

| action `(v,h,d,l)` | `(X,Y,Z)` | `φ` |
|---|---|---|
| `(0,0,0,0)` *closed* | `(0,0,+1)` | 0 |
| `(1,0,0,0)` `^` | `(0,0,+1)` | 0 |
| `(−1,0,0,0)` `v` | `(0,0,+1)` | 0 |
| `(0,1,0,0)` `>` | `(0,0,+1)` | 0 |
| `(5,0,0,0)` `^^^^^` | `(0,0,+1)` | 0 |
| `(0,0,1,0)` `/` and `(0,0,0,1)` `+` | `(0,0,−1)` | 0 |

* **Not faithful.** A closure and five different open histories land on the same point. The projection cannot tell ZFA from non-ZFA, so it cannot be the carrier of a holographic *encoding* of closure.
* **The dimension goes down, not up.** `ℤ⁴ → ℂ² (ℝ⁴) → S³ → S²` is normalization followed by the Hopf map. The "3D" observable is a point on a 2-sphere, which is fewer real parameters than the 4-component action it came from. "Lower-dimensional logic generates higher-dimensional observables" inverts what the map does.
* **`φ` is not a separate boundary.** It is the Hopf fibre coordinate of the same `ψ`, and the code returns `0` whenever either component vanishes.

What survives is the standard spinor fact that a 2-component state carries a 3-vector by bilinears, with the `SU(2) → SO(3)` double cover. That is real but not holography. The verified version of that fact is [`QLF_Spin`](lean/QLF_Spin.lean).

## 3. Open gaps, named

1. **Locality of shared closures.** This is the premise of the derived area law (row 3). A route: shared pairs come from interleaving histories whose causal diamonds intersect ([`MultiParticle.md`](MultiParticle.md)). If a pair can only form between histories within one step of each other on the walk lattice, `area_law_of_local_pairs` applies with the lattice adjacency. That needs a theorem tying the joint-closure condition to walk distance. Until it exists, holography is **a conditional result**: area law ⇐ locality.
2. **From cut pairs to von Neumann entropy.** `cutEntropy` counts `log 2` per cut pair. Identifying this with the entanglement entropy of the reduced state is standard for a product of singlets and is cited here. The tensor-product module (`QLF_TensorFromClosure`, PR #219) supplies the pieces for a Lean proof.
3. **`R²` from the substrate, not by definition.** The capacity-`R` horizon of the twist walk is an `ℓ¹` ball. Its boundary in the three spatial axes has `4R²+2` sites (checked by enumeration for `R ≤ 6`, not proved in Lean). Proving that count would replace `holographic_event_count := 4πR²` with a derived quadratic. The `4` vs `4π` (ℓ¹ vs Euclidean sphere) would then be an honest substrate→continuum factor next to the `4 log 2` residual. *Caveat:* in Lean, `maxExcursion` / `closedAtHorizon_iff_maxExcursion_le` are stated for the 1-D phase string (`TopoString`), not for the `ℓ¹` ball on `ℤ⁴` that [`Closure_Walk.md`](Closure_Walk.md) §1 attributes to them. The `ℤ⁴` version is a further target.
4. **The Bekenstein–Hawking ¼.** It is still the `4 log 2` residual of [`QLF_HolographicDensity`](lean/QLF_HolographicDensity.lean), and is not derived.
5. **A bulk reconstruction theorem** (entanglement wedge, QEC distance) is absent. Row 2 shows that the generator-tree reading cannot supply one, since it constrains nothing at finite length.

## 5. Resolution pass: which overclaims could be made true

| Overclaim | Resolved? | How |
|---|---|---|
| Area law `∝ R²` (was `holographic_event_count := 4πR²`, a definition) | **Yes, proved** | `horizon_area_law`: the capacity-`R` horizon (the spatial `ℓ¹` sphere) has between `(⌊R/2⌋+1)²` and `2(2R+1)²` sites. Enumeration gives exactly `4R²+2`. The `R²` is now a theorem; `4` vs `4π` is the ℓ¹-vs-Euclidean geometric factor of the continuum rendering, a named factor next to `4 log 2` |
| Locality of shared closures (the premise of the area law) | **Yes, conditionally** | `light_cone`: `L` twists move the walker at most `ℓ¹` distance `L`. `pair_range_le` / `pair_local_of_age`: two halves of a pair that leave one event and are each carried `k` steps end within `2k`. So `area_law_of_local_pairs` applies with adjacency "within `2k`", giving an area law with a boundary layer of width `2k`. This is the light-cone argument for area laws (the Lieb–Robinson route), here on the substrate. **Still posited:** that a shared pair is born at one event (the open item of `QLF_TensorFromClosure`, PR #219) |
| "The bulk is identical to the sum of its boundary states" | **Yes, in its precise form** (§0 rows 1–2) | The stronger reading, that the boundary *constrains* the bulk, is false at finite length (`every_prefix_closes`), so it should not be restated |
| `holographic.py` as a faithful encoding | **Yes, by switching the carrier** | The faithful carrier is the unnormalized `Form` of the open half: `countBalanced_iff_strandForm_zero` ([`QLF_EntanglementPrimacy`](lean/QLF_EntanglementPrimacy.lean)) proves it is zero **exactly** on closures. The normalized Bloch reading is a lossy view of it, and is documented as such in `holographic.py` |
| Bekenstein–Hawking ¼ "derived" | **No** | Still the measured `4 log 2` residual. The new geometric factor (`4` vs `4π`) does not remove it: `4R²·log 2` vs `πR²` per Planck patch is a ratio `(4/π)·log 2·…` that depends on how a lattice site maps to a Planck area, which nothing fixes yet |
| "`log C(2k,k)` gives the area law" | **No; it is false** | `log C(2k,k) ≈ 2k log 2` is extensive in a history's length. It cannot be repaired, only withdrawn |
| "AdS/CFT is a provable identity / machine-verified" | **No** | The provable content is §0 rows 1–2. de Sitter / AdS readings stay prose |
| Holographic QEC: "`full_zeno_prune` is the machine-verified boundary decoder" | **Not attempted** | Would need a code property (distance, recovery map). Open |

## 4. How to talk about holography in QLF now

* Say: **closure is a boundary property** (`closure_iff_boundary_silent`); **the horizon has `Θ(R²)` sites** (`horizon_area_law`); **shared pairs born at one event stay within the light cone** (`pair_range_le`), so **the area law follows** (`cutEntropy_le_area`). All proved; the one premise left is that a shared pair is born at one event.
* Say: `4πR²` is the continuum rendering of the substrate's `4R²+2`, and the `4 log 2` gap to Bekenstein–Hawking is measured exactly, not derived.
* Do not say: AdS/CFT is "a provable identity", "machine-verified", or "the area law follows automatically". The first two are false as citations, and the third needs the locality premise.

See also: [`Holographic.md`](Holographic.md), [`Entropy.md`](Entropy.md), [`Quantum_Gravity.md`](Quantum_Gravity.md), [`Open_Problems.md`](Open_Problems.md), [`Closure_Walk.md`](Closure_Walk.md).
