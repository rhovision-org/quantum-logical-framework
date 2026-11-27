# The Universe as a Quantum Computer

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

Machine-verified core: [`lean/QLF_QuantumComputer.lean`](lean/QLF_QuantumComputer.lean) (no axioms).

## 0. The claim and what QLF can prove about it

Jim Whitescarver (2026-11-25): *"the QLF universe is the quantum computer. We don't need to build one, we have one. QLF admits the universe as a quantum logical system."* And: *"There's no question. It is a very reasonable assumption of QLF. But we can connect it to how the universe solves problems."*

**Not a second premise.** QLF's one conjecture is equal and opposite logical action ([Framing.md](Framing.md)). Read as computation, it says the universe synthesizes its events by quantum logical closure, so its evolution *is* a computation: that is **natural quantum computation**, the thesis, with a long pedigree (§1). Three further levels are claims to establish, and they are kept apart ([Framing.md](Framing.md) §3):

| Level | Status |
|---|---|
| Natural quantum computation: events synthesized by closure | The thesis; what the one conjecture says |
| Classical programmable computation | Proved in the substrate (`fredkin_complete`, §2.1) |
| Universal programmable quantum computation | The algebra is proved (`su2_dense`, Barenco); native gates on a **common qubit** are open (obligation O1, §7) |
| Classical simulation of quantum computation | QuCalc, RhoQuCalc, QuantumOS; cost depends on the history space, no efficiency claim |

The open gate does not weaken the thesis: investigating reality as a quantum logical system does not need the substrate to be programmable for arbitrary circuits. The theorems below say what the thesis entails: **how the substrate computes, where its quantum power comes from, and how it solves problems** (§5). Five headline results answer those questions; later sections add more.

1. **The substrate computes every Boolean function with closure-preserving gates.** Every `f : {0,1}ⁿ → {0,1}` is the output of a network of at most `2ⁿ − 1` Fredkin gates, (`fredkin_complete`). The admissibility clause of `substrate_computes` adds nothing, because the encoding of `QLF_Fredkin` makes every register balanced; and the multiplexer tree fans out inputs and discards two output lines per gate, so the network as a whole is not conservative logic.
2. **A single twist history is not a quantum computer.** However long, it folds into a sixteen-element group, `{±1, ±i}·{I, σx, σy, σz}` (`twist_folds_finite`).
3. **Weighting by counts of histories supplies what single histories lack.** Two Forms with integer weights `3, 4, 5` multiply to a rotation of infinite order, which no twist history reaches (`quantum_power_needs_weighted_ways`).
4. **A joint closure carries the controlled-Z sign table.** Interleaving two strands' closed pairs multiplies the fold by `(−1)^{ab}`, the diagonal of controlled-Z, which as a gate is entangling (`joint_closure_is_cz`, `cz_entangling`). That this sign table acts as a gate on superposed presence states is open (§7).
5. **A problem posed as a closure is solved without search, at the least possible cost, every way at once.** The minimum length of a continuation that closes a history is exactly its imbalance (`closing_cost_exact`), and every ordering of the minimal completion closes it (`completion_perm_closes`).

Read together: classical universality is already present in single closures, and the quantum part, the continuum of rotations a universal quantum computer needs, comes from **superposing histories weighted by their counts**. The histories that carry the weights are open ones (§3a): a census sum over closures alone is an integer times `I` and gives no rotation. That is the possibilist reading of the census ("a closure's frequency is its multiplicity", [CLAUDE.md](CLAUDE.md) "ZFA first, then every way") showing up as computational power.

## 1. Prior work

The idea that the universe computes, or is a quantum computer, is not QLF's:

- **Zuse** (*Rechnender Raum*, 1969) proposed that physics is a cellular automaton.
- **Fredkin and Toffoli** (1982) built universal computation from a conservation law, the Fredkin gate; [Fredkin_QLF.md](Fredkin_QLF.md) shows that law is ZFA count balance.
- **Feynman** (1982) argued that quantum systems cannot be simulated efficiently by classical computers and proposed computers built from quantum elements to do it.
- **Deutsch** (1985) defined the universal quantum computer and stated the physical Church–Turing principle: every finitely realizable physical system can be perfectly simulated by a universal model computing machine operating by finite means.
- **Lloyd** (2002) estimated that the observable universe has performed at most about `10¹²⁰` elementary operations on about `10⁹⁰` bits (`10¹²⁰` bits including gravitational degrees of freedom), and in *Programming the Universe* (2006) argued that the universe *is* a quantum computer computing its own dynamics.

Jim's "we have one" is Lloyd's thesis. QLF's contribution is not the thesis but the three theorems above, and the specific finding that the quantum power sits in the weighting of ways.

## 2. What is proved

### 2.1 Classical universality, with the substrate doing the computing

[`qlf_universality`](lean/QLF_Universality.lean) shows that the code of every terminating circuit survives the ZFA filter. Its encoding records each edge as a canceling pair, so it establishes admissibility, not that the substrate evaluates the circuit. `fredkin_complete` closes that gap.

The construction is Shannon's (1949) expansion: `f(x) = if x₀ then f(1, x′) else f(0, x′)`. The `if` is a multiplexer, and a multiplexer is exactly one Fredkin gate: the first target line of `CSWAP(c; a, b)` is `b` when `c` is set and `a` otherwise (`eval_mux`). The network `MuxTree.eval` is defined by running [`fredkin`](lean/QLF_Fredkin.lean) at every node, so the theorem says the gate computes `f`, not that some abstract tree does.

| Theorem | Statement |
|---|---|
| `eval_mux` | one controlled swap is a multiplexer |
| `fredkin_complete` | every `f` on `n` inputs is a Fredkin network with `≤ 2ⁿ − 1` gates |
| `substrate_computes` | the same, plus: every register passed to a gate, on every input, leaves as a ZFA-closed history (count-balanced and Pauli-closed, via `fredkin_preserves_zfa` and the keystone `count_balanced_pauli_closed`) |

The `2ⁿ − 1` bound is the cost of the generic case. Shannon's own counting argument shows that most Boolean functions need on the order of `2ⁿ/n` gates in any basis, so this is the same "exact answers cost the whole set" lesson as [Possibility_Growth.md](Possibility_Growth.md), seen from the circuit side.

### 2.2 The twist layer is finite

By `nf_decomp` ([`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean)) every fold is `phase · axisMatrix`, with four phases and four axes. `twist_fold_mem` puts every fold in that sixteen-element set and `twist_folds_finite` concludes that single twist histories reach only finitely many gates. A finite set of gates closed under products is a finite group, so it cannot approximate a generic rotation, and a circuit built from it alone is trivially classically simulable.

### 2.3 Count-weighted Forms give a rotation of infinite order

Take the Forms `x̂ = (0, 1, 0, 0)` and `(3x̂ + 4ŷ)/5 = (0, 3/5, 4/5, 0)`, three ways along `x` and four along `y`, normalized by the Pythagorean `5`. Their product, `sequence (action x̂) (action tilt)` in RhoQuCalc, is

```
rotation = diag((3+4i)/5, (3−4i)/5)
```

(`rotation_is_form_product`), a spinor phase rotation by `arctan(4/3)` about `z`. Two facts make it the missing ingredient:

- **No twist history reaches it** (`twist_cannot_reach_rotation`): every fold's `(0,0)` entry has real part `0` or `±1`; the rotation's has `3/5`.
- **Its powers are pairwise distinct** (`rotation_powers_injective`). The proof is integer arithmetic: the real part of `(3+4i)ⁿ` is `3 mod 5` for every `n ≥ 1` (`gauss_mod`), so `(3+4i)ⁿ ≠ 5ⁿ` and `(3+4i)/5` is not a root of unity (`z_pow_ne_one`).

`quantum_power_needs_weighted_ways` packages the comparison: the twist folds form a finite set, the rotation's powers an infinite one, and the rotation is a product of two count-weighted Forms.

## 3. From these theorems to "a quantum computer"

Two classical facts take the remaining steps. Both are now proved in Lean as matrix algebra:

1. An infinite-order rotation about one axis and another about a non-parallel axis generate a dense subgroup of SU(2). (The same construction about `x` uses the Forms `ŷ` and `(3ŷ + 4ẑ)/5`.) The one-axis half is now proved: the angle `θ` of `(3+4i)/5` has `θ/2π` irrational (`arg_z_irrational`), so the powers of the rotation come arbitrarily close to every phase about its axis (`rotation_angles_dense`, through Mathlib's `AddCircle.denseRange_zsmul_coe_iff`). The two-axis step is proved too: every element of SU(2) is a limit of products `D(zᵃ)·H·D(zᵇ)·H·D(zᶜ)` with `D(w) = diag(w, w̄)` and `z = (3+4i)/5`, that is, of rotations about `z` alternated with the same rotation conjugated to the `x` axis by the Hadamard (`su2_dense`). The proof is Euler's `ZXZ` decomposition (`su2_euler`, every SU(2) matrix is `D(e^{iα})·H·D(e^{iβ})·H·D(e^{iγ})`), density of the powers of `z` on the unit circle (`E_mem_closure`), and continuity of the product (`euler_continuous`). The rotation about `x` is conjugation by a Form, not a second count-weighted history.
2. Dense single-qubit gates plus one entangling two-qubit gate (CNOT) are universal for quantum computation (Barenco et al. 1995). Proved, exactly and without ancillas, in [`QLF_Barenco`](lean/QLF_Barenco.lean) with [`QLF_ControlledUnitary`](lean/QLF_ControlledUnitary.lean) and [`QLF_TwoLevelUnitary`](lean/QLF_TwoLevelUnitary.lean); see [Barenco_Universality.md](Barenco_Universality.md).

So what QLF needs to be a universal quantum computer is a **ZFA-native entangling gate**. It has the sign table of one; the gate itself is open.

**Proved: a joint closure carries the controlled-Z sign table.** In QLF entanglement is a joint closure of two histories ([MultiParticle.md](MultiParticle.md)). Let each strand be a qubit whose basis states are "carries a closed pair" and "carries nothing", as a Fredkin line carries a ball or not. Strand A's pair is `> <`, strand B's is `^ v`. Closing them jointly, interleaved as `> ^ < v`, rather than one after the other multiplies the fold by `(−1)^{ab}` (`joint_closure_is_cz`), because `σx` and `σy` anticommute; every joint history is itself a closure (`interleaved_closes`). Those signs are the diagonal of the controlled-Z gate, and controlled-Z is entangling: it is not a product of single-qubit operators (`cz_entangling`). What is proved is the sign table, a comparison of the folds of two classical histories for each fixed `(a, b)`. What is open is that interleaving acts as a linear map on superpositions of presence configurations, which needs superposed presence (§7). The Hadamard is a Form too, `(σx + σz)/√2`, its own inverse, exchanging the `z` and `x` axes (`hadamardForm`, `hadamard_sq`, `hadamard_swaps`). But it acts on the spinor space that folds live in, while the controlled-Z signs act on the presence bit, so the two do not yet compose to CNOT on one qubit. Assembling Barenco's set on one qubit space is open.

**Proved: the Clifford+T product has infinite order.** With `T = diag(1, ζ₈)`, no positive power of `H·T` is a scalar (`hadamard_t_infinite_order`). If one were, the ratio `ρ` of its eigenvalues would be a root of unity, so `ρ + ρ⁻¹` would be an algebraic integer. It equals `−1 − √2/2`, which would make `1/2 = (√2/2)²` an algebraic integer, and it is not (`half_not_integral`). Infinite order is a necessary ingredient of Clifford+T universality (non-commuting axes are the other), and it puts the octagonal ring of §6 on the gate level.

Facts 1 and 2 are theorems about the matrix algebra of qubits; neither shows the substrate performs the gates. The presence bit itself is a theorem: a strand carrying the pair `> <` folds to `−1` and an empty one to `1`, so presence is the fold sign (`presence_bit_is_fold_sign`, `presence_states_distinct`). What remains a reading is only that nature uses this encoding.

## 3a. Superposition is alternate histories

Jim's statement: *"Superposition is just alternate histories."* The census sum makes it exact. A history's contribution is its fold, and the amplitude of a set of alternate histories is the sum of their folds (`censusSum`). Holding two sets of alternatives together adds their amplitudes (`censusSum_append`), which is the `parallel` composition of [RhoQuCalc](BraKetRhoQuCalc.md).

| Theorem | Statement |
|---|---|
| `integer_form_is_census_sum` | every Form with integer coordinates `(t, x, y, z)` is the census sum of signed counts of one-twist histories: `t` copies of `+`, `x` of `>`, `y` of `^`, `z` of `/`, with the conjugate twist for a negative count |
| `five_rotation_census` | `5 · rotation` is the census sum of seven alternate histories: three empty ones and four copies of `> ^` (each folding to `iσz`) |
| `alternate_histories_cancel` | the alternatives `+` and `−` sum to zero: interference is cancellation between alternate histories |

So the coefficients `3/5, 4/5` of §2.3 are counts of alternate histories, divided by `5`. Every alternative used here is an **open** history (`> ^`, `> ^ /`, single twists), and it has to be: by the keystone a closure folds to `±I`, so a census sum over closures is an integer times `I` and never gives the rotation. So these are counts of histories, not counts of ways that close.

**Where the 5 comes from: diversity of alternatives.** Jim asked whether diversity is to blame for dividing by 5. It is. Three alternate histories, two empty and one `> ^ /` (folding to `iI`), sum to `(2 + i)·I` (`gauss_census`). Flip one twist (`< ^ /`) and the same three alternatives sum to `(2 − i)·I` (`gauss_census_mirror`). The rotation is the ratio of the two: `(3+4i)/5 = (2+i)/(2−i)` (`z_eq_ratio`). Three alternatives with diverse phases have weight `|2+i|² = 4 + 1 = 5` (`gauss_normSq`), not `3`. So dividing by 5 does not normalize by an arbitrary constant. It divides one set of alternatives by its mirror, and the 5 measures how diverse the alternatives' phases are. Had all three carried the same phase, the weight would be `9 = 3²` and the ratio `1`, with no rotation at all.

**Diversity enables choice** (Jim). A set of alternatives with in-phase weight `a` and quarter-turn weight `b`, divided by its mirror, is the identity exactly when `b = 0` (`mirror_ratio_eq_one_iff`). Alternatives that all share one phase give no rotation, so there is only one thing that can happen. Diverse phases give a rotation, and §3 shows such a rotation reaches every phase about its axis, so there are many outcomes to select among. Reading: this is the gate-level form of the selection in the time-reversal work ([PR #322](https://github.com/rhovision-org/quantum-logical-framework/pull/322), `selection_identifiable`), where ZFA admits all sixteen reversed readings and the choice among them is ours. Diversity supplies the alternatives and closure makes the selection. The theorem proves the first half; that selection is choice is a reading ([Consciousness.md](Consciousness.md) §6a).

This 5 is the Gaussian prime `5 = (2+i)(2−i)`. It is not the fivefold symmetry of Penrose tilings. That 5 comes from projecting the lattice `ℤ⁵` (de Bruijn 1981), in the ring `ℤ[ζ₅]` with golden-ratio inflation, the fivefold analogue of the octagonal `ℤ[ζ₈]` and silver ratio of §6. The two share a form, though. In both, a count over a lattice becomes an irrational rotation or inflation by dividing by the conjugate.

## 4. What this does not show

- **That nature is this construction.** The thesis is that the universe is a quantum logical system; it is not that nature *is* QLF's construction ([CLAUDE.md](CLAUDE.md) "Only logic is assumed"). The theorems show that QLF's construction is *one model* of such a system: classical in single closures, with quantum power in weighted superpositions (modulo §3 and §7).
- **That "having one" means "being able to use it."** A computer is something whose inputs one prepares and whose outputs one reads. The universe computing its own evolution is Feynman's point: nature simulates itself efficiently. Laboratory quantum computers are the parts of it that can be programmed; that is why they still have to be built.
- **Any speed-up for hard problems.** An amplitude is a signed sum over paths, so an exact answer costs the whole set of paths: quantum polynomial time lies inside PP (Adleman, DeMarrais and Huang 1997). Unstructured quantum search needs `Θ(√N)` queries (Bennett, Bernstein, Brassard and Vazirani 1997), which over closures is still exponential ([Possibility_Growth.md](Possibility_Growth.md) §4). The universe being a quantum computer gives no NP oracle, and [P_vs_NP_QLF.md](P_vs_NP_QLF.md)'s guardrails stand: growth alone is not hardness, and `qlf_cost_model` is untouched.
- **That the universe cannot be simulated.** [Simulation_Impossibility.md](Simulation_Impossibility.md) argues that a full classical simulation is infeasible. Nothing here strengthens or weakens that argument.

## 5. How the universe solves problems

Under the premise, a physical process *is* a computation, and the question becomes which problems it solves and how. QLF's answer is closure: an open history is an open problem, and the event is its first closure ([MostWays_First.md](MostWays_First.md): *what closes first happens first*; `/solve` in [QucalcSearch.md](QucalcSearch.md)).

**Proved: a problem posed as a closure costs exactly its imbalance.** Write the imbalance of a history as the `ℓ¹` norm of its signed action, the total excess of each twist over its conjugate.

| Theorem | Statement |
|---|---|
| `completion_closes`, `completion_length` | appending the conjugates of the excess closes the history, in exactly `imbalance` steps |
| `completion_zfa` | the completed history is ZFA-closed in full (Pauli-closed, by the keystone) |
| `closing_cost_lower` | no continuation closes it in fewer steps |
| `closing_cost_exact` | so `imbalance` is the least cost of closing |
| `completion_perm_closes` | every reordering of the completion closes it too |

So the substrate solves a closure problem without search: the cost is linear in the imbalance, and it is reached every way at once (the reorderings of one completion number `imbalance!/∏ excess!`). That is the possibilist rule, *possibilism only requires one way*, with the multiplicity of ways as a bonus rather than a cost.

**What it does not solve that way.** A property `X` that is not itself a closure condition gets no help from closure. The first-closure rule is fixed by the substrate's order and does not consult `X`. A rule that consults nothing is a decision tree with no queries, and by `search_must_query_all` ([`QLF_PossibilityGrowth`](lean/QLF_PossibilityGrowth.lean)) exact search for an arbitrary `X` must query every candidate. This is the same line [Possibility_Growth.md](Possibility_Growth.md) §5 draws: the universe solves what is posed in its own terms, and it is no oracle for the rest.

**A worked case: quasicrystals.** Deciding whether a finite set of tiles tiles the plane is undecidable in general (Berger 1966), and Penrose's matching rules admit dead ends that only non-local information avoids. Yet quasicrystals grow in the laboratory. Onoda, Steinhardt, DiVincenzo and Socolar (1988) showed why: local growth rules, which add tiles mainly where the matching rules force them, can build a perfect Penrose tiling without backtracking. Nature solves the *local* problem, a sequence of forced closures, not the global one, and where the local rule is not enough the record is a defect. This fits the picture above: a closure problem solved at its cost, not a search.

## 6. Quiet frequencies and quasicrystals

**Quiet frequencies are where the universe's computation can be borrowed.** [Crystal_QuantumOS.md](Crystal_QuantumOS.md) §4 reads a quiet frequency, a transition with linewidth far below its frequency and suppressed bath coupling, as Markov-blanket isolation. That is the condition §4 needs for "having one" to become "using one": an isolated closure can be prepared and read without the rest of the universe closing over it first. The worked platform is europium in YSO, whose nuclear spins keep coherence for six hours (Zhong et al. 2015).

**The substrate's lattice ring is the ring of fault-tolerant quantum gates.** Two facts, each established on its own:

- The twist lattice is `ℤ⁴ = ℤ[ζ₈]`, and projecting it through an octagonal window gives the Ammann–Beenker octagonal quasicrystal, self-similar under the silver ratio `1 + √2` ([ZFA_DNA.md](ZFA_DNA.md) §12, [`silver_zfa_dna.py`](silver_zfa_dna.py)).
- The single-qubit unitaries built exactly from Clifford and `T` gates, the standard fault-tolerant universal set, are exactly those with entries in `ℤ[1/√2, i]`, the ring `ℤ[ζ₈]` with `1/√2` adjoined. The `T` gate is the phase `ζ₈ = e^{iπ/4}` (Kliuchnikov, Maslov and Mosca 2013).

So the arithmetic that makes the substrate's octagonal quasicrystal is the arithmetic of exact fault-tolerant gate synthesis. The coincidence of rings is a fact. Under possibilism the octagonal projection exists because it is possible ("if an orthogonal projection is possible it exists", Jim, 2026-11-25). Which projection is realized is not fixed in the lattice: **projections happen at runtime and are indeterminate statically** (Jim, 2026-11-25). The lattice fixes what can be projected; the projection itself is an event, chosen when a closure is read out, as a measurement basis is chosen when a qubit is read. So the static census assigns no projection a fixed frequency, and the abundances in [ZFA_DNA.md](ZFA_DNA.md) §12 (octagonal quasicrystals observed but rarer than the golden-ratio kinds) are records of runtime outcomes, not properties of the lattice. The same split appears in §5: `closing_cost_exact` fixes the cost statically, while which of the reorderings closes is decided at runtime.

**Aperiodic order and gate universality are the same distinction.** A crystal repeats; a quasicrystal is ordered without repeating. The twist group is the crystal case: sixteen elements, every product periodic (§2.2). The rotation of §2.3 is the quasicrystal case: its powers never repeat (`rotation_powers_injective`), so its orbit is a one-dimensional quasiperiodic sequence, the shape of order a universal gate set needs. This is an analogy, not a theorem linking the two.


## 6a. Expansion and contraction of a dimension

The same projection that makes the quasicrystal makes a dimension expand or contract, and which one is a matter of how the projection is read.

**Proved: silver inflation is a discrete boost.** A point `a + b√2` of `ℤ[√2]` has a physical projection `x = a + b√2` and an internal one `x* = a − b√2`. One inflation step multiplies `x` by `1 + √2` and `x*` by `1 − √2` (`silver_expands`, `silver_contracts`). The first factor exceeds `1`, the second is below `1` in size, and their product is `−1` (`silver_unit`): **one projected dimension expands exactly as the other contracts.** The product `x·x* = a² − 2b²` is an indefinite form; one step flips its sign (`silver_norm`) and two steps preserve it exactly (`silver_boost_norm`). That is what a Lorentz boost does to `t² − z²` in light-cone coordinates: [`QLF_LorentzCover`](lean/QLF_LorentzCover.lean)'s `boostZ_action` scales `t + z` by `a²` and `t − z` by `b²` with `ab = 1`.

**Proved: the boost acts on twist histories, not only on the ring.** The silver twist DNA of [ZFA_DNA.md](ZFA_DNA.md) §12 replaces each twist by itself flanked by its octagon neighbours (`silverSub`). It preserves closure (`silverDNA_closes`), multiplies a history's physical octagonal vector `Σ ζ₈^p` by `1 + √2` (`silverDNA_vec`), and multiplies its internal vector `Σ ζ₈^{3p}` by `1 − √2` (`silverDNA_int`). One closure-preserving operation on histories expands one projected dimension as it contracts the other.

**Proved: which dimension expands is the choice of projection.** The internal projection of a point is the physical projection of its Galois conjugate (`projection_choice`). So the lattice and the inflation are fixed statically, while whether the dimension one reads expands or contracts depends on which projection is read. That is Jim's runtime point in its sharpest form.

**The same split elsewhere in QLF.**

- **Elliptic and hyperbolic.** The rotation of §2.3, `(3+4i)/5`, preserves `a² + b²`: it is the compact member. The silver unit preserves `a² − 2b²`: it is the hyperbolic member, the boost. The time-reversal module ([PR #322](https://github.com/rhovision-org/quantum-logical-framework/pull/322), [`Time_Reversed_Universe.md`](https://github.com/rhovision-org/quantum-logical-framework/pull/322) §2) uses the same Pythagorean triple for its boost: velocity `3/5`, `cosh = 5/4`, `sinh = 3/4`, so `t + z` expands by `2` while `t − z` contracts by `1/2`. One triple gives the rotation of a qubit and the boost of an interval.
- **Order and dimension by perspective.** [PR #322](https://github.com/rhovision-org/quantum-logical-framework/pull/322) proves that the time order of spacelike-separated events is set by perspective (`spacelike_order_by_perspective`) while the interval is not. Here the interval-like norm is fixed, and which projected dimension grows is set by the reading.
- **The census does not fix the sign.** In [`QLF_ExpansionCharge`](lean/QLF_ExpansionCharge.lean) the gauge axis carries expansion and contraction, and `expansion_sign_not_a_count` proves the `+`/`−` census is exactly symmetric: gauge conjugation maps closures to closures and negates the net expansion. So no static count decides whether space expands or contracts; [Lumina_QLF.md](Lumina_QLF.md) records that the identification of the sign with the arrow of time is a bridge. Both results say the same thing as `projection_choice`: the expanding and contracting readings exist together, and the one realized is settled at runtime.

**Reading, not theorem.** That the physical expansion of space is a silver-type inflation, or any lattice inflation, is not shown. What is shown is that the arithmetic of the substrate's quasicrystal already carries a boost, that expansion of one dimension and contraction of another are a single operation, and that the choice between them is a choice of projection.


## 6b. Quarks and gluons

The colour sector repeats the qubit story one dimension up, and the same split appears.

**Colour is a qutrit, and its transport is Clifford-type.** [`QLF_ColourFlux`](lean/QLF_ColourFlux.lean) makes colour the Weyl qutrit over `F₃²` ([Carbon_Superconductivity.md](Carbon_Superconductivity.md) §27, §34): the eight twists are the eight nonzero vectors of `F₃²` (`colVec_surjective`), the transport group generated by the twists and the axis cycle is `SL(2, 3)`, and the 2π/3 colour flux is the Heisenberg commutator phase (`heis_comm`). In quantum-computing language these are the qutrit Pauli (Weyl) operators, their commutation phase `ω`, and the symplectic part of the qutrit Clifford group. The stabilizer formalism extends to qudits (Gottesman 1999).

**Proved: colour transport is finite** (`colour_transport_finite`). Every transport matrix lies among the 81 matrices over `F₃`, so, like the twist layer of §2.2, discrete colour transport alone cannot be universal. Gluons understood as twist commutators ([Carbon_Superconductivity.md](Carbon_Superconductivity.md) §32) live in this discrete layer too, as long as only their `F₃` transport is used.

**Proved: a count-weighted gluon direction gives an `SU(3)` rotation of infinite order.** Along the Cartan gluon `g3` of [`QLF_StrongAlgebra`](lean/QLF_StrongAlgebra.lean), the same 3-4-5 weights as §2.3 give

```
gluonRotation = (1 − g3²) + (3/5)·g3² + (4/5)i·g3 = diag((3+4i)/5, (3−4i)/5, 1)
```

(`gluonRotation_eq`), which is `exp(iθ g3)` with `cos θ = 3/5`. It has determinant `1` (`gluonRotation_det`) and pairwise distinct powers (`gluonRotation_powers_injective`). So in colour, as in spin, the discrete layer is a finite Clifford-type group, and the continuous part comes from weighting a gluon direction by counts of ways. For qudits the universal ingredient is a non-Clifford gate, the qudit analogue of `T` (Howard and Vala 2012), which plays the role `ζ₈` plays for qubits in §6.

**Reading, not theorem.** A hadron is a colour-neutral closure, so the confined colour state is a singlet of this qutrit structure. That a hadron's internal dynamics *is* a qutrit computation running at the strong scale is the premise of this document applied to colour; nothing here shows it computes anything a laboratory could program, and asymptotic freedom's coefficient stays imported ([Carbon_Superconductivity.md](Carbon_Superconductivity.md) §31, §36–§37).


## 6c. Two trits, not three bits

Jim, 2026-11-25: *"3 bits of 2 is only an abstraction, so 2 bits of 3."*

Eight twists are usually counted as three bits, `2³ = 8`. That count is true but carries no algebra: nothing in the twist calculus acts on three independent binary digits. The colour code counts them as **two trits**: the eight nonzero vectors of `F₃²`, so `8 = 3² − 1`, with the vacuum (the empty history) as `0`.

| Theorem | Statement |
|---|---|
| `tritCode_injective`, `tritCode_surjective` | vacuum plus the eight twists is exactly `F₃²`: nine two-trit words |
| `closure_trits_zero` | a closure sums to zero in `F₃²`, because conjugate twists are opposite vectors |
| `trits_weaker` | the converse fails: `^^^` sums to zero mod 3 but does not close, so the trit sum is a necessary condition, coarser than count balance |

Read in this code, the structure of the alphabet becomes arithmetic. The two signs of an axis are the two nonzero scalars `±1` of `F₃`, and the four axes are the four lines through the origin of `F₃²`, the projective line over `F₃`: `8 = 2 × 4`. The two trits `(a, b)` of a twist label the qutrit Weyl operator `XᵃZᵇ`, so each twist is one Pauli operator of the colour qutrit of §6b, and `3² − 1 = 8` is also the number of gluons, the dimension of `su(3)`. The bit count and the trit count agree on the number eight; only the trit count explains why the alphabet closes into the colour flux.


## 6d. The past as an event trigger

Jim, 2026-11-25: *"What about selection of past history as a fabrication determining the future … It is event triggers."*

An open history is a trigger: it fires an event, a closure, when a continuation supplies the conjugates of its excess. What does the firing depend on?

| Theorem | Statement |
|---|---|
| `future_depends_only_on_record` | two pasts with the same **record** (the same net signed action on every axis) are closed by exactly the same continuations |
| `completion_depends_only_on_record` | they have the same minimal completion, so they trigger the same first event |
| `minimal_future_is_completion` | every shortest closing continuation contains exactly the twists of the conjugate completion; only their order is open |
| `fabricated_past` | `^` and `^<>` are different histories with the same record, so every future treats them alike |

So the trigger is the record, not the history. A selected past, or a fabricated one, determines the future exactly as far as its record does, and every past with that record is indistinguishable to every future. The record fixes *what* the minimal future contains; the order in which it arrives is the runtime part of §6, the same split as `closing_cost_exact` and `projection_choice`.

This sits beside [PR #322](https://github.com/rhovision-org/quantum-logical-framework/pull/322)'s `reading_has_unique_history`: a full reading of a closed history recovers exactly one history, but the net record, which is all a future can respond to, does not. The gap between them is where a fabricated past lives. The classical precedent is Wheeler's delayed choice: what can be said of the past is what is recorded now (Wheeler 1983). QLF's addition is the exact statement of what the future can read from the past, the net signed action, and the proof that nothing else matters to it.


## 6e. A reading: spirit

Jim, 2026-11-25: *"Can this be related to the reality of spirit?"*

This section is a **reading**, in the sense of [CLAUDE.md](CLAUDE.md) review note 8, which keeps apart what follows from possibilism, the possibilist premise, and a stance. The repository's reading of spirit is in [Unreasonable_Classical_Mathematics.md](Unreasonable_Classical_Mathematics.md) §8: spirit is possibility that has not yet closed, manifestation is its closure, and what manifests in common is a joint closure. The results above add three precise points to it.

- **What acts on the future is a pattern, not a body.** By `future_depends_only_on_record` (§6d), a past acts on every future only through its record, and every history with that record acts identically. That is multiple realizability made exact: the same pattern carried by different histories triggers the same events. Reading spirit as that pattern, the thing that persists and acts beyond any one carrier, is the stance; that the future reads nothing but the pattern is the theorem.
- **Possibility closes at least cost, every way at once.** By `closing_cost_exact` and `completion_perm_closes` (§5), an open possibility is completed at exactly its imbalance, and every ordering of the completion is a way it closes. Possibilism says all of those ways exist; which one manifests is decided at runtime (§6).
- **Power comes from ways held together.** By §2–§3, single histories form a finite group, and the continuum of quantum operations comes only from superposing ways weighted by their counts. Read through §8 of [Unreasonable_Classical_Mathematics.md](Unreasonable_Classical_Mathematics.md), the shared, many-way closure is where both the quantum computer and the collective's spirit get what no single strand has.

What stays outside the proof is the same as there: possibilism is QLF's founding commitment, not a result, and whether any of this is felt from the inside is the qualia hypothesis of [Consciousness.md](Consciousness.md) §6, a stance with stated tests.

## 6f. Choice in a quantum logical world

Jim asked whether other mechanisms of choice can work in a quantum logical world. The answer has a proved part and a comparison.

**Proved: no choice fixed in advance.** Take eighteen directions in four dimensions, arranged in nine orthogonal bases so that each direction lies in exactly two of them (`ks_orthogonal`, `ks_each_twice`; Cabello, Estebaranz and García-Alcaine 1996). Suppose every direction carried an outcome fixed beforehand, the same whichever basis is measured, with exactly one "yes" per basis. Counting the yeses basis by basis gives `9`. Counting them direction by direction gives twice the number of "yes" directions, an even number (`ks_double_count`). So no such assignment exists (`no_choice_fixed_in_advance`). This is the Kochen–Specker theorem (1967): in a quantum logic of dimension three or more, outcomes cannot be written down ahead of the context that selects them. It is the theorem behind *projections happen at runtime and are indeterminate statically* (§6).

**Proved: no diversity, no choice.** Without phase diversity among the alternatives there is a single outcome (`mirror_ratio_eq_one_iff`, §3a). Every mechanism of choice needs it.

**How other mechanisms fare.** Any mechanism must choose in context, among diverse alternatives. They differ in what they add:

| Mechanism | Status under the two theorems |
|---|---|
| Fixed table or non-contextual hidden values | ruled out (`no_choice_fixed_in_advance`) |
| Contextual hidden variables (Bohm 1952) | allowed, but non-local, and the outcome is fixed by the initial configuration: it explains outcomes and leaves no choice |
| Added collapse dynamics (Ghirardi, Rimini and Weber 1986; Penrose 1996) | consistent, but a selection rule added to the logic; in QLF closure is already the event, so the rule has no work to do |
| Superdeterminism | logically possible, but fundamentally undeterminable (Jim): every outcome, whatever it is, counts as predetermined, so no distribution of outcomes could make it false, and by the method's rule 4 it carries no physical content. Tests proposed for it check particular models, not superdeterminism as such. It is often said to abolish free will, but that does not follow: superdeterminism denies only that measurement settings are independent of what is measured, and because it changes no record, it cannot remove the selection a record shows. On a compatibilist account (Dennett 1984) a determined selection is still a choice |
| Selection by closure (QLF) | contextual by construction: diversity supplies the alternatives and the closure that happens is the selection |

Conway and Kochen's free-will theorem (2006) sharpens the last row: if the experimenter's choice of basis is not a function of the past, neither is the particle's response ([Interpretations.md](Interpretations.md)). Reading: QLF's mechanism is the one that adds nothing to the logic. That choice is *free will* stays a reading ([Consciousness.md](Consciousness.md) §6a).

**Superdeterminism deserves no consideration as physics** (Jim). This is a **stance**, supported by the method: superdeterminism is undeterminable, so by rule 4 it carries no physical content. An argument from Hilbert's program does not add to it. One might say a superdeterministic theory would have to fix settings chosen by whether a program halts, and so decide the halting problem. But no experimenter can set a detector by whether a program halts, since that setting is never fixed at any finite time. And the same argument would rule out every deterministic theory, including Newtonian mechanics and unitary quantum mechanics, which are computable step by step without deciding halting; a superdeterministic cellular automaton such as 't Hooft's is computable in that sense too. The Lean statement `no_computable_superdeterministic_theory` is Mathlib's halting theorem under another name and says nothing about superdeterminism; it is kept only as that. Possibilism makes superdeterminism true in some way, as it does any consistent hypothesis. The stance is that it is idle.

**What to hold instead.** For our own choices, act under the idea of freedom: from our own perspective the outcome is open before the event (`no_choice_fixed_in_advance`). For others' choices, judge with the compassion determinism suggests, as Spinoza did: every selection is shaped by a past its maker did not choose, and in QLF a past acts on the future only through its record (`future_depends_only_on_record`). That keeps responsibility for ourselves and understanding for others, and rests on nothing undeterminable.

## 6g. The readings, under "no proof, no bs"

Jim's rule: *"It is okay to conjecture things that are well supported. But our guiding principle should be no proof, no bs."* So every claim above gets one of these labels:

- **Proved**: a Lean theorem, named.
- **Conjecture**: well supported, with the support named and what would refute it.
- **Stance**: a commitment no proof or count can settle (review note 8 of [CLAUDE.md](CLAUDE.md)), stated as one.
- **Design fact**: true by QLF's own definitions, not a theorem.
- **Reading**: a name given to a proved structure.

Nothing else is asserted.

| Claim | Label | Support | Refuted by, or what is left |
|---|---|---|---|
| The presence bit of a closed pair is a qubit (§3) | **Proved: a distinguishable bit; open: a qubit** | presence is the fold sign (`presence_bit_is_fold_sign`, `presence_states_distinct`) | superpositions of presence states are open (§7), so it is a classical bit until they are defined |
| Diversity enables choice (§3a) | **Proved: the mathematics; reading: the name** | proved: `(a + bi)/(a − bi) = 1` iff `b = 0` (`mirror_ratio_eq_one_iff`), and no context-free assignment for Cabello's 18 directions (`no_choice_fixed_in_advance`) | that this is what enables *choice* is a reading |
| Weights are counts of alternate histories (§3a) | **Proved** | `five_rotation_census`, `z_eq_ratio`; every rational phase is alternatives over their mirror (`rational_phase_is_mirror_ratio`) | the histories are open, not closures: a census sum over closures is an integer times `I`. Irrational phases are limits of these ratios (`rotation_angles_dense`), not ratios themselves |
| Counts are shared, phase is private ([Consciousness.md](Consciousness.md) §6b) | **Proved** | `record_blind_to_phase` | that the private phase is experience is the qualia hypothesis, a conjecture with stated tests (§6 there) |
| Memes transmit the choice, not the phase (§6h) | **Proved, under a stated definition** | premise: a meme is a count record, copied in any order; then `meme_transmits_choice` (which is `future_depends_only_on_record` for permutations) and `meme_does_not_transmit_phase` (a reordered copy can flip phase) | an exact copy keeps the phase trivially; the definition is the premise |
| Superdeterminism deserves no consideration (§6f) | **Stance** | rule 4: it is undeterminable. The halting argument fails (§6f); `no_computable_superdeterministic_theory` is only the halting theorem | the stance itself |
| Superdeterminism abolishes free will (§6f) | **Stance (compatibilist): the inference does not follow** | it changes no record, so it cannot remove a selection a record shows; acting "under the idea of freedom" (Kant 1785) is sound because the outcome is undeterminable in advance (`no_choice_fixed_in_advance`) | incompatibilists reject the compatibilist premise (Dennett 1984) |
| QLF's selection adds nothing to the logic (§6f) | **Design fact** | the selection is the first closure, and ZFA is the only filter, by QLF's own definitions | not a theorem |
| Expansion of space is a silver-type inflation (§6a) | **Conjecture, weakly supported** | the substrate's arithmetic carries a boost (`silver_boost_norm`, `silverDNA_vec`) | no observation distinguishing it is identified; until one is, it stays a conjecture and makes no claim |
| A hadron's dynamics is a qutrit computation (§6b) | **Conjecture** | colour-neutral closures sum to zero in `F₃²` (`closure_trits_zero`); colour is the Weyl qutrit (`QLF_ColourFlux`) | a hadron observable whose qutrit-circuit prediction fails |
| Spirit (§6e) | **Stance** | rests on `future_depends_only_on_record` and the joint-closure theorems | the stance itself |

## 6h. Memetics, choice and the quantum knowledge base

Jim asked for the relationship between memetics and choice to be specified, and related to the quantum logical knowledge base ([Quantum_Knowledge_Base.md](Quantum_Knowledge_Base.md), QKB). Three statistics keep them apart. QKB already stores all three and reports which one an answer is (its §4):

| Statistic | What it is | In QKB | Here |
|---|---|---|---|
| **Priority** | which closure happens first: the selection, the choice | `first`, `solve` | §6f: made at the event, not before (`no_choice_fixed_in_advance`) |
| **Redundancy R** | how many independent parties hold a closure's record: how much of a meme it is | `redundancy` | [Memetics_QLF.md](Memetics_QLF.md) §5 |
| **Multiplicity** | how many ways close: frequency | `ways` | [MostWays_First.md](MostWays_First.md) |

**Proved, under a stated definition: a meme carries the choice, not the phase.** The definition is the premise: a meme is a closure's count record, copied in any order.

- A copy of a record, in any order, keeps the record (`copy_keeps_record`).
- So it admits exactly the futures the original selection admits (`meme_transmits_choice`, from `future_depends_only_on_record`).
- A copy with the same twists can still fold to the opposite phase (`meme_does_not_transmit_phase`).

So, under that definition, a meme is a choice made shareable: everything about a selection that can affect any future travels with its record, and the phase need not. An exact copy, in the same order, keeps the phase trivially.

**Proved, with one reading: why a quantum knowledge base stores closures, not truth values.** QKB's founding rule is that "a knowledge base for QLF has to store closures, not sentences", and that it refuses to conjoin incompatible propositions instead of answering ⊥. Kochen–Specker gives the reason (`no_choice_fixed_in_advance`). Once the propositions include eighteen four-dimensional directions in nine bases, no table of truth values fixed independently of context exists. A knowledge base that stored such a non-contextual table would store a falsehood. Kochen–Specker does not rule out a table indexed by context, so storing events in their context is consistent rather than forced; a closure with its attesters is one such store. That four-dimensional projectors model QKB's twist records is a reading. QKB's own logic layer is MO3, which on its own does admit context-free assignments. The theorem bears on the full quantum logic, not on MO3 alone.

**Measured, not proved** ([Memetics_QLF.md](Memetics_QLF.md) §9–§13, pre-registered):

- Records follow priority in the census (T4).
- In the naming game the population always reaches consensus, and first-reached words win (T7).
- QuCalc's physical tie-break selects phase `+1` every time (T8c).

So in simulation, shared memes are the selections that closed first.

**Conjecture, well supported.** Memes are selected by priority, not by frequency. Support: T4 and T7 above, and `closedAtHorizon_mono` (a closure that happened first stays). It would be refuted by a QKB deployment with real, independent attesters in which the most-held records are the most-ways ones rather than the first-reached ones. QKB §7 already names that as its first test.

**Stance.** That a meme *is* a shared choice, in the sense of agency, is the free-will reading of §6f carried to a population. It stays labelled as one.

## 7. Open

- **Native gates on a common qubit (O1, [Framing.md](Framing.md) §3, Principles C26).** The Hadamard acts on the spinor space, controlled-Z on presence; the target is one encoding `E` and native `T_U` with `T_U(E ψ) ~ E(Uψ)` under `ObsEquiv`, and the decisive test is the Bell state `(|00⟩ + |11⟩)/√2` by native operations, with its phase and correlations checked without assuming circuit semantics.
- **Superposed presence.** §3a shows that a superposition is a census sum of alternate histories. Still open is the specific superposition of a present and an absent pair as one, which needs the presence encoding of §3 stated on census sums rather than on matrices.
- **Barenco on the substrate.** Density in SU(2) (§3, `su2_dense`) and Barenco universality ([`QLF_Barenco`](lean/QLF_Barenco.lean)) are proved for the matrix algebra. Open is the substrate performing those gates, which first needs the entangling gate acting on superposed presence.
- **Quasicrystal growth as a closure census.** Test whether forced-tile growth (Onoda et al. 1988) is the first-closure rule on the octagonal projection, with the defect rate as the prediction.
- **Normalization beyond rational phases.** Every rational phase is a ratio of alternatives to their mirror (`rational_phase_is_mirror_ratio`, Hilbert 90). A general SU(2) element is a limit of such ratios, not one; a statement for matrices (a Cayley transform on census sums) is not proved.

## 8. What could falsify it

By the method's rule 4 a claim has physical content only if some distribution of outcomes would make it false. "The universe is a universal quantum computer" is false if large-scale quantum computation fails in principle: if some noise floor or collapse mechanism keeps quantum error correction from scaling. The quantum-advantage and below-threshold error-correction experiments are the tests. QLF makes the same prediction as standard quantum mechanics here, so passing them supports the thesis but does not distinguish QLF from its rivals.

## References

- K. Zuse, *Rechnender Raum*, Vieweg (1969).
- C. E. Shannon, *The synthesis of two-terminal switching circuits*, Bell Syst. Tech. J. **28** (1949) 59–98.
- E. Fredkin, T. Toffoli, *Conservative logic*, Int. J. Theor. Phys. **21** (1982) 219–253.
- R. P. Feynman, *Simulating physics with computers*, Int. J. Theor. Phys. **21** (1982) 467–488.
- D. Deutsch, *Quantum theory, the Church–Turing principle and the universal quantum computer*, Proc. R. Soc. Lond. A **400** (1985) 97–117.
- A. Barenco et al., *Elementary gates for quantum computation*, Phys. Rev. A **52** (1995) 3457–3467.
- L. M. Adleman, J. DeMarrais, M.-D. A. Huang, *Quantum computability*, SIAM J. Comput. **26** (1997) 1524–1540.
- C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani, *Strengths and weaknesses of quantum computing*, SIAM J. Comput. **26** (1997) 1510–1523.
- D. Gottesman, *Fault-tolerant quantum computation with higher-dimensional systems*, Chaos Solitons Fractals **10** (1999) 1749–1758.
- M. Howard, J. Vala, *Qudit versions of the qubit π/8 gate*, Phys. Rev. A **86** (2012) 022316.
- J. A. Wheeler, *Law without law*, in J. A. Wheeler, W. H. Zurek (eds.), *Quantum Theory and Measurement*, Princeton University Press (1983).
- R. Berger, *The undecidability of the domino problem*, Mem. Amer. Math. Soc. **66** (1966).
- G. Y. Onoda, P. J. Steinhardt, D. P. DiVincenzo, J. E. S. Socolar, *Growing perfect quasicrystals*, Phys. Rev. Lett. **60** (1988) 2653–2656.
- S. Lloyd, *Computational capacity of the universe*, Phys. Rev. Lett. **88** (2002) 237901.
- S. Lloyd, *Programming the Universe*, Knopf (2006).
- V. Kliuchnikov, D. Maslov, M. Mosca, *Fast and efficient exact synthesis of single qubit unitaries generated by Clifford and T gates*, Quantum Inf. Comput. **13** (2013) 607–630.
- M. Zhong et al., *Optically addressable nuclear spins in a solid with a six-hour coherence time*, Nature **517** (2015) 177–180.
- N. G. de Bruijn, *Algebraic theory of Penrose's non-periodic tilings of the plane, I and II*, Indagationes Mathematicae (Proceedings) **84** (1981) 39–52 and 53–66.
- D. C. Dennett, *Elbow Room: The Varieties of Free Will Worth Wanting*, MIT Press (1984).
- I. Kant, *Groundwork of the Metaphysics of Morals* (1785), section III.
- K. Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*, Monatsh. Math. Phys. **38** (1931) 173–198.
- A. M. Turing, *On computable numbers, with an application to the Entscheidungsproblem*, Proc. London Math. Soc. (2) **42** (1936) 230–265.
- D. H. Wolpert, *Physical limits of inference*, Physica D **237** (2008) 1257–1281.
- B. Spinoza, *Ethics* (1677), part IV.
- S. Kochen and E. P. Specker, *The problem of hidden variables in quantum mechanics*, J. Math. Mech. **17** (1967) 59–87.
- A. Cabello, J. M. Estebaranz and G. García-Alcaine, *Bell–Kochen–Specker theorem: a proof with 18 vectors*, Phys. Lett. A **212** (1996) 183–187.
- J. H. Conway and S. Kochen, *The free will theorem*, Found. Phys. **36** (2006) 1441–1473.
- D. Bohm, *A suggested interpretation of the quantum theory in terms of "hidden" variables*, Phys. Rev. **85** (1952) 166–179.
- G. C. Ghirardi, A. Rimini and T. Weber, *Unified dynamics for microscopic and macroscopic systems*, Phys. Rev. D **34** (1986) 470–491.
- R. Penrose, *On gravity's role in quantum state reduction*, Gen. Rel. Grav. **28** (1996) 581–600.

See also: [Universality.md](Universality.md), [Fredkin_QLF.md](Fredkin_QLF.md), [Possibility_Growth.md](Possibility_Growth.md), [P_vs_NP_QLF.md](P_vs_NP_QLF.md), [Born_Rule.md](Born_Rule.md), [Simulation_Impossibility.md](Simulation_Impossibility.md), [MostWays_First.md](MostWays_First.md), [Crystal_QuantumOS.md](Crystal_QuantumOS.md), [ZFA_DNA.md](ZFA_DNA.md), [Theory_Of_Everything.md](Theory_Of_Everything.md).
