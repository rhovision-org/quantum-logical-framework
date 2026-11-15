# Holography Audit — what QLF proves about bulk and boundary

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

**Status labels** follow [`ScientificApproach.md`](ScientificApproach.md): *proved*, *exact computational*, *definition*, *cited*, *prose only*, *incorrect*.
**Lean anchors:** [`lean/QLF_HolographicBoundary.lean`](lean/QLF_HolographicBoundary.lean) and [`lean/QLF_HolographicArea.lean`](lean/QLF_HolographicArea.lean) (no axioms). §4 records the follow-up pass that resolved two of the gaps.

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

**The finding that matters:** an area law does not follow from closure. It follows from the **locality of shared closures**, and QLF has not derived that. The tensor-product work (`QLF_TensorFromClosure`, PR #219, merged) derives *that* a shared pair entangles two bodies, with one half on each body; `QLF_TensorConservativeReturn` proves the quotient return on tensor-image classes. Nothing yet says the two bodies must be neighbours, and nothing yet selects the physical closure equivalence. That locality/shared-pair-birth premise is where holography's content lives, and it is the named open gap (§3). The open item is not tensor-product composition.

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
2. **From cut pairs to von Neumann entropy.** `cutEntropy` counts `log 2` per cut pair. Identifying this with the entanglement entropy of the reduced state is standard for a product of singlets and is cited here. The tensor-product module (`QLF_TensorFromClosure`, merged) supplies the derived algebra, and `QLF_TensorConservativeReturn` supplies the quotient coherence; the locality/shared-pair-birth and entropy identification remain open.
3. **`R²` from the substrate, not by definition.** The capacity-`R` horizon of the twist walk is an `ℓ¹` ball. Its boundary in the three spatial axes has `4R²+2` sites (checked by enumeration for `R ≤ 6`, not proved in Lean). Proving that count would replace `holographic_event_count := 4πR²` with a derived quadratic. The `4` vs `4π` (ℓ¹ vs Euclidean sphere) would then be an honest substrate→continuum factor next to the `4 log 2` residual. *Caveat:* in Lean, `maxExcursion` / `closedAtHorizon_iff_maxExcursion_le` are stated for the 1-D phase string (`TopoString`), not for the `ℓ¹` ball on `ℤ⁴` that [`Closure_Walk.md`](Closure_Walk.md) §1 attributes to them. The `ℤ⁴` version is a further target.
4. **The Bekenstein–Hawking ¼.** It is still the `4 log 2` residual of [`QLF_HolographicDensity`](lean/QLF_HolographicDensity.lean), and is not derived.
5. **A bulk reconstruction theorem** (entanglement wedge, QEC distance) is absent. Row 2 shows that the generator-tree reading cannot supply one, since it constrains nothing at finite length.

## 4. Resolution pass: which overclaims could be made true

| Overclaim | Resolved? | How |
|---|---|---|
| Area law `∝ R²` (was `holographic_event_count := 4πR²`, a definition) | **Yes for the lattice sphere; the horizon identification is a bridge** | `horizon_area_law`: the spatial `ℓ¹` sphere `sphere3 R` has between `(⌊R/2⌋+1)²` and `2(2R+1)²` sites. Enumeration gives exactly `4R²+2`. The `R²` is now a theorem; `4` vs `4π` is the ℓ¹-vs-Euclidean geometric factor of the continuum rendering, a named factor next to `4 log 2`. **Not proved:** that `sphere3 R` is the horizon QLF's capacity semantics (`closedAtHorizon`) selects, or that it renders as the continuum `4πR²`. Those are a geometric/physical bridge. `holographic_event_count := 4πR²` stays a definition and is not reclassified as a derived count |
| Locality of shared closures (the premise of the area law) | **Yes, from the locality principle** | The premise is Jim's principle *only local information has any effect*: every shared pair links sites within a fixed **step distance** `d`. Nothing here is time; `d` counts steps of history. [`QLF_LocalAreaLaw`](lean/QLF_LocalAreaLaw.lean) `local_area_law` proves that then the pairs cut by the boundary of the `ℓ¹` ball of radius `R` number at most `4d(2d+1)³(2R+1)²`: `O(R²)` with a coefficient fixed by `d` alone, not by the region (`local_entropy_law` at `log 2` per pair). The pairs form a `Finset`, so the bound is for a *simple* pair graph: reading it as entropy assumes a local capacity of one shared pair per site pair (`M` singlets on one link would carry `M · log 2` and escape the bound), and the step from `log 2` per cut pair to von Neumann entropy stays open. `light_cone` / `pair_range_le` / `pair_local_of_steps` connect it to histories: halves related to a shared event through `k` steps each lie within `2k`, so `d = 2k`. If the step distance were allowed to grow with `R`, the coefficient would grow too; the principle is what forbids that. This is the light-cone argument for area laws (the Lieb–Robinson route), here on the substrate. **Still posited:** that a shared pair is born at one event. What remains open is locality/shared-pair birth, not tensor-product composition; PR #219 is merged and `tensor_conservative_return` proves the quotient return. |
| "The bulk is identical to the sum of its boundary states" | **Yes, in its precise form** (§0 rows 1–2) | The stronger reading, that the boundary *constrains* the bulk, is false at finite length (`every_prefix_closes`), so it should not be restated |
| `holographic.py` as a faithful encoding | **Only as faithful closure *detection*** | The unnormalized `Form` of the open half detects the closure predicate exactly: `countBalanced_iff_strandForm_zero` ([`QLF_EntanglementPrimacy`](lean/QLF_EntanglementPrimacy.lean)) proves it is zero **exactly** on closures. It is **not** a faithful encoding of histories: it keeps only net counts, so it is not injective (`[up, down]` and `[down, up]` both give `0`). The normalized Bloch reading loses even the detection, and is documented as lossy in `holographic.py` |
| Bekenstein–Hawking ¼ "derived" | **No** | Still the measured `4 log 2` residual. The new geometric factor (`4` vs `4π`) does not remove it: `4R²·log 2` vs `πR²` per Planck patch is a ratio `(4/π)·log 2·…` that depends on how a lattice site maps to a Planck area, which nothing fixes yet |
| "`log C(2k,k)` gives the area law" | **No; it is false** | `log C(2k,k) ≈ 2k log 2` is extensive in a history's length. It cannot be repaired, only withdrawn |
| "AdS/CFT is a provable identity / machine-verified" | **No** | The provable content is §0 rows 1–2. de Sitter / AdS readings stay prose |
| Holographic QEC: "`full_zeno_prune` is the machine-verified boundary decoder" | **Not attempted** | Would need a code property (distance, recovery map). Open |

### 4a. What a closure carries across a boundary: one π-flux quantum per plaquette

Jim asked (2026-11-09) whether an up/down entanglement teams with a left/right one to make a
closure. It does, and the team carries a quantity neither pair has on its own: enclosed area.
[`QLF_PlaquetteArea`](lean/QLF_PlaquetteArea.lean) proves the lattice Green's theorem for the
edge-sign connection of [`QLF_EdgeSign`](lean/QLF_EdgeSign.lean). For any history with no `Z`
twist, the holonomy is the enclosed area mod 2 (`holonomy_eq_area_parity`). So the phase is
`(−1)^{#neg} · (−1)^{area}`, and for a balanced history that scalar is the Pauli fold
(`fold_eq_area_phase`). A single-axis closure encloses nothing (`area_zero_of_no_X`). The decided
squares explain the `QLF_EdgeSign` examples: `^>v<` has area `−1`, `^><v` has area `0`, and twice
round has area `−2`. The same four twists in a different order give a different sign *because*
they bound a different area. Numerically: 0 mismatches over the 68,844 planar closures of
length ≤ 10.

For holography this is the precise sense in which a closure's phase is a **boundary** quantity: it
is a flux, read entirely off the loop: one π-flux quantum per plaquette of the surface the loop
bounds, summed mod 2. It is a single ℤ₂ value for the whole loop: areas that differ by two give the
same holonomy, so it records neither the enclosed geometry nor one recoverable bit per cell, and it is
not an entropy density. That is Stokes' theorem, which is bookkeeping in the method's sense (rule 4): it holds for
every loop. What it settles is *where* the phase lives (on the enclosed surface, as the parity of
the flux through it), not a new count.

**Three dimensions are encoded in two.** The same module proves the general case
(`holonomy_eq_projected_areas`): for *every* history, in any axes and closed or not, the holonomy
is the parity of the sum of its three shadows, the areas it projects on the `XY`, `XZ` and `YZ`
planes. For a closure each shadow is an integer area (`shoelace_eq_two_projArea`), and the sum
fixes the fold's sign (`fold_eq_projected_phase`). A skew hexagon `^>/v<\` round a cube's corner
lies in no plane, but its shadows are `−1`, `1`, `1`, so it carries one π quantum. So the phase of a
3-D closure is entirely a 2-D quantity: what its loop casts on the coordinate planes. Before the
proof this was checked on all 299,593 histories of length ≤ 6 (gauge twists included) with 0
mismatches.

## 5. How to talk about holography in QLF now

* Say: **closure is a boundary property** (`closure_iff_boundary_silent`); **the horizon has `Θ(R²)` sites** (`horizon_area_law`); **shared pairs born at one event stay within the light cone** (`pair_range_le`), so, **given that only local information has effect** (shared pairs within a fixed step distance `d`), **the area law follows with a coefficient fixed by `d`** (`local_area_law`). The premise is a stated logical principle, not a hidden assumption. The `ℓ¹` sphere's `Θ(R²)` count is proved; that it is the physical horizon is a bridge.
* Say: `4πR²` is, by a geometric bridge, the continuum rendering of the substrate's `4R²+2`, and the `4 log 2` gap to Bekenstein–Hawking is measured exactly, not derived.
* Do not say: AdS/CFT is "a provable identity", "machine-verified", or "the area law follows automatically". The first two are false as citations, and the third needs the locality premise.

See also: [`Holographic.md`](Holographic.md), [`Entropy.md`](Entropy.md), [`Quantum_Gravity.md`](Quantum_Gravity.md), [`Open_Problems.md`](Open_Problems.md), [`Closure_Walk.md`](Closure_Walk.md).
