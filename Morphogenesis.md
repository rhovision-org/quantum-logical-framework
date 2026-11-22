# Morphogenesis in QLF: what closure alone can differentiate

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

**Question.** Can a diverse, patternless population of histories become spatially differentiated through closure alone, with no rule that mentions the pattern? And if it can, which rungs of an emergence ladder from closure to organised form are proved, which are measured, and which are open?

Classical morphogenesis has two reference mechanisms. Turing (1952) showed that local activation with longer-range inhibition can make a uniform state unstable to a pattern of fixed wavelength. Ovchinnikov and Zeldovich (1978) and Toussaint and Wilczek (1983) showed that diffusion-limited annihilation `A + B → 0` segregates an initially uniform mixture into growing domains, because the difference `n_A − n_B` is conserved and its initial fluctuations survive. This page asks which of the two the substrate supplies and proves the part that is pure bookkeeping in [`QLF_Morphogenesis`](lean/QLF_Morphogenesis.lean). The lattice test is [`morphogenesis_census.py`](morphogenesis_census.py).

Grades used below: **F** formal (Lean, no axioms), **N** numerical (pre-registered run), **E** empirical, **B-OPEN** a bridge not yet built ([claim_records/README.md](claim_records/README.md)).

---

## 1. Three quantities that must not be conflated

QLF uses "frequency" in two senses, and morphogenesis needs a third quantity.

| Symbol | Meaning | Where it lives |
|---|---|---|
| `f = 1/R` | the repetition rate of a closure of period `R` | [`QLF_HarmonicClosure`](lean/QLF_HarmonicClosure.lean) `component_freq` |
| `M` | multiplicity: the number of ways a closure occurs, which is its frequency of occurrence | [Philosophy.md](Philosophy.md) §3a, [census_inventory.py](census_inventory.py) |
| `n(x, t)` | the local population of a species of history at site `x` | this page |

Promotion and demotion in a pattern are statements about `n`. The binding inequality is a statement about `f`. A morphogen rule that moves `n` must say so, and a rule stated in terms of `f` does not by itself move `n`.

## 2. What the cited ingredients actually say

Every name in the input texts was checked against the tree. All exist. Two of them carry less than their names suggest.

- **`binding_raises_harmonic`** and **`freq_bind_ge_left`/`_right`** are true by definition. [`QLF_Consciousness`](lean/QLF_Consciousness.lean) defines `bind a b := min a b`, so "the bound closure has frequency at least that of each part" restates `min a b ≤ a`. They are a convention for the period of a phase-locked composite, not a derived promotion mechanism. A morphogen rule cannot rest on them.
- **`QLF_ClosureBinding.Bind A B`** is `countBalanced (A ++ B)`. On closures that predicate is always true (§3), so a compatibility graph `K(i, j) = [h_i ∘ h_j is ZFA]` over closures is the complete graph.

The ingredients that do carry content here are the boundary state `disp h ∈ ℤ⁴` with `balanced_iff_disp` and `disp_append` ([`QLF_ClosureChannels`](lean/QLF_ClosureChannels.lean)), and `balanced_append` / `balanced_of_append` ([`QLF_ClosureKernel`](lean/QLF_ClosureKernel.lean)).

## 3. The ladder

Each rung names its grade. The proved rungs are bookkeeping: conservation laws and their consequences. They are what any closure-only morphogen rule must respect, not evidence that a pattern forms.

### Rung 0. Diversity is generated (F)

The path integral generates `4ⁿ` histories and only `C(2n, n)` of them close ([`QLF_Firebreak`](lean/QLF_Firebreak.lean) `generated_count`, `not_all_paths_close`). Diversity is the open strands that are generated and have not closed.

### Rung 1. Compatibility is a charge rule on open strands (F)

[`QLF_Morphogenesis`](lean/QLF_Morphogenesis.lean) §1:

- `closures_always_compatible`: two closures always bind. Closure–closure compatibility cannot differentiate anything, so a differentiating rule must act on open strands.
- `bind_iff_opposite`: two histories bind iff `disp A + disp B = 0`. On open strands compatibility is an opposite-charge rule in `ℤ⁴`, one charge per axis.
- `identical_open_blocked`: an open strand never binds with a copy of itself. This is the count-level analogue of `identical_channel_blocked` in [`QLF_ClosureBinding`](lean/QLF_ClosureBinding.lean).

Pauli closure adds nothing to these rules, because count balance entails it (`count_balanced_pauli_closed`).

### Rung 2. Promotion and demotion are conserved (F)

A region is a list of histories and its ledger is the sum of their boundary states. The local events are promote (join two histories), demote (split one), emit (a closure leaves as a receipt carrying `ΔF = −log 2`, [`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)) and reorder. This is the conserved demotion both input texts asked for first.

- `event_conserves_ledger`, `events_conserve_ledger`: every local event and every finite sequence of them conserves the ledger.
- `demotion_leaves_closures`: demoting a closure along a closed prefix leaves two closures, so no receipt is lost by unbinding.

### Rung 3. Local closure erases exactly the balanced part (F)

- `region_closes_iff`: a region can be closed away completely by local events iff its ledger is zero.
- `imbalance_persists`: a region with non-zero ledger keeps an open strand under every sequence of local events.
- `excess_species_persists`: for any additive reading of the ledger, such as the `up − down` count, a positive regional excess leaves a surviving strand with a positive reading. The locally excess species cannot be closed away; only transport removes it.
- `hop_flux`: moving a history between regions shifts their ledgers by exactly its boundary state. This is the continuity equation, with closure contributing zero.

Together these are the substrate form of the Ovchinnikov–Zeldovich–Toussaint–Wilczek mechanism: closure removes the balanced part, the ledger's initial fluctuation is conserved, and that residue is what is left to form domains.

### Rung 4. Differentiation on a lattice (N, pre-registered, §4, passed)

Whether the residue actually forms domains, and whether it does so only because of the algebra, is a numerical question. §4 is the test and §5 the result: it does, in `d = 1` and `d = 2`, and it disappears when the ledger is broken.

### Rung 5. Persistent pattern with a preferred scale (B-OPEN)

Segregation by a conserved charge coarsens forever. It has no wavelength and no steady state. A Turing pattern needs a second length scale, an inhibition that acts farther than activation. Nothing in rungs 0 to 3 supplies one. Suggestions are in §6.

### Rung 6 and up. Chemistry, folding, life, collectives (existing, mixed grades)

- Bonds as shared closures: [Chemistry.md](Chemistry.md), [`QLF_Unsaturation`](lean/QLF_Unsaturation.lean) (F for the closure count, a structural reading for the bond).
- Folds as closure inventories: [Protein_Folding.md](Protein_Folding.md), [`QLF_Folding`](lean/QLF_Folding.lean). Its kinetic prediction was tested and failed (§5e there), and that failure stands.
- Evolution as generate-and-select: [Evolution.md](Evolution.md) (a structural reading).
- Nested control: [Hierarchical_Control.md](Hierarchical_Control.md), [Emergent_Markov_Blankets.md](Emergent_Markov_Blankets.md).

None of these is yet connected to rung 4 by a theorem. Each connection is B-OPEN.

---

## 4. Pre-registration: the lattice differentiation test

Fixed in the commit that adds this section and [`morphogenesis_census.py`](morphogenesis_census.py), before any run.

**Model.** A periodic lattice: `d = 1` with 2048 sites for 4096 steps, and `d = 2` with 128×128 sites for 1024 steps. Initially every site holds an independent Poisson number of each of the eight single-twist strands, mean `1/8` each, for one strand per site in all. Every step every strand hops to a uniformly random nearest neighbour, then the closure rule acts at every site. Eight seeds per configuration. The variants differ only in the closure rule:

- **G**, the algebra: two strands close iff their joint history is ZFA, which for single twists means iff they are conjugate (`bind_iff_opposite`). By `region_closes_iff` each site keeps exactly its ledger.
- **R_all**, complete compatibility, which is what closure-level compatibility gives (`closures_always_compatible`): any two strands at a site close. This breaks ledger conservation.
- **D**, no closure.

A randomized matching of the eight types is **not** used as a control. A random perfect matching without self-pairs is a relabeling of G and gives the same statistics, so it tests nothing about the algebra. The content-bearing control is breaking the conserved ledger, which R_all does.

**Statistics.**
- `S(t)`, axis segregation. For each axis, `φ(x) = n₊(x) − n₋(x)`. Among nearest-neighbour bonds with both ends non-zero, the fraction with equal sign, minus `p₊² + p₋²` from the site sign frequencies. Averaged over the four axes. `0` means no organisation and `0.5` complete segregation.
- `Q(t)`, dominant-type agreement on bonds between occupied sites, minus `Σ p_type²`. Reported, not graded.
- `ρ(t)`, strand density.

**Predictions and kill conditions.**
- **P1 (the test).** At the final time, `S_G ≥ 0.2` in both `d = 1` and `d = 2`, and `S_G − max(S_R_all, S_D)` exceeds 3 combined standard errors. **Kill:** `S_G < 0.1`, or the gap to the controls is within 3 standard errors, in either dimension. Then closure does not differentiate this population and rung 4 fails as posed.
- **P2 (simulator check against the classical result).** The late-time density exponent of G, fitted over `t ∈ [T/16, T]`, lies in `[−0.32, −0.18]` for `d = 1` (theory `−1/4`) and `[−0.60, −0.40]` for `d = 2` (theory `−1/2`). R_all in `d = 1` lies in `[−0.60, −0.40]` (theory `−1/2` for `A + A → 0`). A failure here means the simulator or the reduction is wrong, not that QLF is.
- **P4 (persistence).** With pair creation, which places a conjugate pair across a site and a random neighbour with probability `0.002` per site per step and conserves the ledger, G's `S` averaged over the last three sample times is `≥ 0.1` and above 3 standard errors. Expected outcome: **fail**. Pair creation seeds adjacent opposite charges, which push `S` toward zero or below. A pass would mean the substrate supplies persistent differentiation without a second scale.

**Amendments, 2026-11-22, after a smoke run on a 256-site and a 32×32 lattice that is not graded.** Thresholds, sizes, seeds and statistics are unchanged.
- **A1.** With every strand hopping every step, strands on the two sublattices of a bipartite lattice never share a site, so the lattice splits into two independent populations and every nearest-neighbour bond compares them. That defeats `S` and `Q` for every variant. The walk is now lazy: each strand stays with probability `1/2`, otherwise hops. This changes the time unit by a factor of two and no exponent.
- **A2.** R_all leaves at most one strand per site, so in the smoke run no bond had both ends non-zero on one axis and `S_R_all` was undefined. A control whose `S` is undefined at every seed is reported as not measurable, and P1 uses the other control.

What the test can and cannot show. P1 passing would show that the algebra's conserved ledger alone differentiates a diverse population, and that this vanishes when the ledger is broken. This is the method's rule 4 test: the claim would be false for a closure rule without a conserved charge (R_all), and the run measures that. It would not show anything beyond the classical `A + B → 0` result. QLF's contribution is the derivation of the charge rule and its conservation from closure (rungs 1 to 3), with no species, rates or forces put in.

## 4b. Pre-registration: the graded large-lattice run and the lower bound

Fixed 2026-11-22, after §5 and the two exploratory `d = 2` runs reported there, and before this run. Because those runs informed it, this is a second registered test, not a blind one.

**Model.** Variant G only, `d = 2`, 1024×1024 sites, 16384 steps, 4 seeds (`--p2prime 0..3`). Everything else is as §4. The hop is computed on occupied cells only (`hop_sparse`). That gives the same distribution as `hop` and reproduces it exactly on test seeds.

**Predictions.**
- **P2′.** The late density exponent of the seed-mean `ρ`, fitted over `t ∈ [T/16, T]`, lies in `[−0.60, −0.40]`. This is the same window as P2, around the classical `−1/2`, which Bramson and Lebowitz (1988) proved rigorously for `d < 4`. Expected from the 512×512 run: a narrow pass near `−0.58`. A fail leaves the `d = 2` law unreached by this simulator at this size and duration. It does not touch P1.
- **P5 (structural).** At every sample the lattice's `ℓ¹` ledger equals its initial value, and the strand mass is at least that value (`surviving_mass_ge_ledger`). Any violation is a code bug.

## 5. Result

Run of the pre-registered configuration (8 seeds each), [`data/morphogenesis_census.json`](data/morphogenesis_census.json). Final-time values, mean ± standard error over seeds:

| Variant | `d` | `S` | `Q` | `ρ` | late `ρ` exponent |
|---|---|---|---|---|---|
| G | 1 | **+0.463 ± 0.009** | +0.172 ± 0.033 | 0.139 | −0.270 |
| R_all | 1 | not measurable (A2) | not measurable | 0.0070 | −0.423 |
| D | 1 | +0.001 ± 0.011 | −0.004 ± 0.003 | 1.005 | 0.000 |
| G | 2 | **+0.399 ± 0.017** | +0.106 ± 0.015 | 0.040 | −0.640 |
| R_all | 2 | not measurable (A2) | −0.138 | 0.0026 | −0.874 |
| D | 2 | +0.001 ± 0.003 | +0.000 ± 0.001 | 0.998 | 0.000 |
| G + pair source | 1 | +0.111 ± 0.041 (last three: +0.129 ± 0.040) | +0.044 | 0.246 | — |
| G + pair source | 2 | −0.028 ± 0.011 (last three: +0.000 ± 0.009) | 0.000 | 0.208 | — |

Verdicts, as registered:

- **P1 passes in both dimensions.** `S_G = 0.46` (`d = 1`) and `0.40` (`d = 2`), against `0.001` for D, far beyond 3 standard errors. R_all leaves at most one strand per site, so no bond carries the same axis at both ends and its `S` is undefined (amendment A2). Its density falls about 20 times faster than G's, so it closes away almost everything and leaves nothing to organise. The kill condition is not met. **The algebra's conserved ledger differentiates a diverse, patternless population into segregated domains, and with the ledger broken (R_all) or closure disabled (D) there is no organisation.** Grade N.
- **P2 passes in `d = 1` and fails in `d = 2`.** G in `d = 1` gives `−0.270` (theory `−1/4`) and R_all gives `−0.423` (theory `−1/2`). G in `d = 2` gives `−0.640`, outside the window `[−0.60, −0.40]` around the classical `−1/2`. So the simulator check fails in `d = 2` as registered. An exploratory run that is not graded (128×128, 16384 steps, 3 seeds) shows why the window was not reached: the local exponent rises from `−0.15` through a plateau near `−0.61` between `t ≈ 50` and `t ≈ 1200`, then turns toward zero as the domains fill the lattice and `S` falls to `0` (one domain per axis left). A second exploratory run on 512×512 (8192 steps, 2 seeds), where the domains stay far smaller than the lattice, shows the plateau without the turn: the local exponent is `−0.64` around `t ≈ 1000` and relaxes slowly to `−0.60` by `t = 8192`, while `S` keeps growing to `0.46`. Reaching the asymptotic `d = 2` regime needs a larger lattice. Until it is reached, the `d = 2` density law is unchecked. P1 does not depend on it.
- **P4 passes narrowly in `d = 1` and fails in `d = 2`.** The registered expectation was failure in both. With a ledger-conserving pair source, `S` over the last three samples is `0.129 ± 0.040` in `d = 1` (threshold `0.1` and 3 standard errors, met by a small margin) and `0.000 ± 0.009` in `d = 2`. So in `d = 2` the source keeps the population mixed and no persistent differentiation forms. In `d = 1` some survives. One dimension and one source rate do not establish persistent pattern, so rung 5 stays B-OPEN.

What was shown. Rungs 1 to 3 (F) derive an opposite-charge compatibility rule and its conservation from closure alone. Rung 4 (N) shows that this conservation, and nothing else in the rule, is what turns a uniform, eight-species population into domains. This is the classical `A + B → 0` segregation result, reached here with no species, rates or forces put in. It is not a Turing pattern. Domains coarsen, they have no preferred size, and in `d = 2` a source erases them. The persistent, scale-selected pattern is the next rung, and §6 lists the routes.

## 6. Suggestions for the next rungs

Each is stated with what would make it fail.

1. **A second length scale from capacity.** A capacity-`R` horizon receives only the closures with `maxExcursion ≤ R` (`closedAtHorizon_iff_maxExcursion_le`). If closure is local at the hop scale but a strand's ability to reach a partner is cut at the horizon `R`, the two scales are the ingredients of a Turing instability. Test: the linearised lattice operator built from these two rules has a band of unstable wavenumbers. Kill: no band for any `R`.
2. **Cross-axis coupling through composite strands.** At the count level the four axes are independent (rung 1), so a single-twist population segregates as four separate charges. Composite open strands (`^<`, and so on) carry two charges at once and couple the axes. Test: whether the coupled population forms interfaces where one axis's domain wall pins another's. Kill: cross-axis wall correlation is not distinguishable from the single-twist run.
3. **Receipts as a field.** Each closure emits a receipt with `ΔF = −log 2`. If receipts are counted where they are emitted, the receipt density marks the domain walls of rung 4, which is where closure happens. Test: receipt density peaks at sign changes of `φ`. This would be a reading of where free energy is released, not a new mechanism.
4. **Connect rung 4 to folding.** A contact in [Protein_Folding.md](Protein_Folding.md) is a closure along a chain. The chain version of rung 4 is whether a heteropolymer with a charge sequence segregates its contacts into domains. Kill: contact domains are no more ordered than in a randomized sequence of equal composition.
5. **Collective intelligence.** In [Game_Theory_QLF.md](Game_Theory_QLF.md) a joint closure is a shared objective. The analogue of rung 4 is that a population of agents whose proposals close only with opposite proposals segregates into conventions. Kill: no segregation relative to a complete-compatibility control. This is a reading until such a run exists.

## Sources

- Turing, A. M. (1952). The chemical basis of morphogenesis. *Phil. Trans. R. Soc. Lond. B* 237, 37–72.
- Ovchinnikov, A. A., Zeldovich, Ya. B. (1978). Role of density fluctuations in bimolecular reaction kinetics. *Chem. Phys.* 28, 215–218.
- Toussaint, D., Wilczek, F. (1983). Particle–antiparticle annihilation in diffusive motion. *J. Chem. Phys.* 78, 2642–2647.
