# Stationary Action Is the Continuum Shadow of ZFA

**Claim.** Hamilton's principle `δS = 0` is the law every fundamental theory shares. That includes
Hilbert's 1915 derivation of general relativity from `S = ∫ R √−g d⁴x`, where the field equations are
just the stationarity of the curvature action. QLF proposes the substrate reason in one chain:

\[
\boxed{\text{equal and opposite logical action}
\;\longrightarrow\;
\text{Zero Free Action}
\;\xrightarrow{\text{proposed continuum bridge (open)}}\;
\text{stationary action}.}
\]

Equal and opposite logical action is primitive. When the ledger closes exactly, free action is zero.
**QLF conjectures that this balance is represented by stationarity under admissible continuum
variations.** That last arrow is an open bridge, not a consequence of ZFA alone. An exact closure
condition `F(h) = 0` constrains the *value* at a history; `δS[h] = 0` constrains its first-order
*response* to admissible variations. Neither follows from the other without a map and a theorem: even
`F(q) = q` vanishes at `q = 0` while `dF/dq = 1` there. If the bridge holds, QLF does not need
multiplicity to *cause* stationary action, because conjugate balance supplies the reason. The
multiplicity theorems below show that the discrete census is stationary and maximal at the same
balance point, which is an independent structural check, not a proof of the bridge. First closure
determines event priority; multiplicity determines frequency.

**What the bridge would have to supply.** A proof of the last arrow needs four things, none of which
is formalized yet:

1. the space of closed discrete histories and a continuum reconstruction map `Φ`, saying which fields
   and geometries it reconstructs;
2. the physical (or discrete) action functional, its boundary conditions, and the class of admissible
   variations;
3. a first-variation identity, or a conjugation symmetry of that **action** (not only of the
   multiplicity), strong enough to force `δS[Φ(h)] = 0`;
4. convergence of the **variations**, not merely of the values, of the causal-set action to the
   Einstein–Hilbert variational problem, boundary terms included.

A worked instance of items 2 and 3 in the gauge-link sector, finite and exact, is
[`QLF_LinkAction`](lean/QLF_LinkAction.lean) ([`Closure_Unitarity.md`](Closure_Unitarity.md) §21): the
link action's first variation is `curl F − J`, so stationarity is Ampère's law. It does not supply
items 1 or 4 for gravity.

Lean: [`lean/QLF_StationaryAction.lean`](lean/QLF_StationaryAction.lean) (one axis), and
[`lean/QLF_StationaryPhase.lean`](lean/QLF_StationaryPhase.lean) for the signed phase and all four
axes (§5a). No axioms.

---

## §0 The oldest theory of everything, completed

Stationary action has been put forward as *the* law of physics for nearly three centuries.
Maupertuis (1744) called least action the universal principle of nature. Euler and Lagrange made it
the engine of mechanics, and Hamilton (1834) extended it to optics and dynamics alike. Planck (1915)
ranked it the most comprehensive physical law, the one that covers mechanics, electrodynamics and
thermodynamics in a single statement. **Hilbert's 1915 paper was itself a theory-of-everything
attempt:** *Die Grundlagen der Physik* derived the gravitational field equations *and* Mie's
electrodynamics from one action, meaning to unify all of physics under one variational principle.
Feynman (1948) then showed that quantum mechanics is the same principle read through phases. Today the
whole of known physics, the Standard Model coupled to general relativity, is written as a single
action. Every fundamental theory we have is an instance of `δS = 0`.

What the principle never had was a **reason**. Why should nature extremise anything? And why should
one principle cover both the classical world, where the stationary path is simply *taken*, and the
quantum world, where every path contributes and the stationary one merely dominates? These two
readings are the two halves of the quantum-gravity problem. GR is a classical variational theory of
geometry, and QM is a sum over histories. The principle they share has never been explained, so their
agreement has looked like a coincidence.

**ZFA supplies the reason and makes the two halves one.** The common source is not the modal count
but the conjugate structure itself: every logical action has an equal and opposite partner, exact
balance is ZFA, and QLF conjectures that the continuum image of that balance is stationarity. The
census and phase theorems prove the discrete part: the unsigned census and the signed endpoint
amplitude both peak at that same closure. They do not by themselves give `δS = 0`:

* **The classical half — the GR side.** Conjugate pairing makes exact balance the ZFA condition and
  puts the unsigned census at a stationary, maximal point there (`balance_is_stationary_mode`,
  `ways_mode_at_balance`, §2). The open bridge is to show rigorously that the physical action
  functional used by GR is the continuum rendering of this equal-and-opposite closure condition.
* **The quantum half — the QM side.** The same pairing, read on phases, gives the reversal law
  `K_m(y, x) = (−1)^m K_m(x, y)` (`amp_swap`). The amplitudes are real, so the `m`-step kernel is
  **skew-symmetric for odd `m` and symmetric for even `m`**. The closure amplitude is then the norm of
  the half-way amplitude, and no endpoint beats it (`return_amplitude_sum_sq`,
  `signed_mode_at_balance`, §5a). This is a discrete analogue of Feynman's stationary phase, an
  endpoint-amplitude bound proved for QLF's own phase. It is not by itself a derivation of `δS = 0`.

So QM and GR are not two theories that happen to share a principle. They are **the unsigned and the
signed readings of one closure census**, and ZFA's conjugate pairing is what makes each of them
stationary at the same place. **That is the proposed unification of quantum mechanics and general
relativity, at the level where both were always defined: their shared variational principle.** What is
machine-verified is its discrete half: both readings of the closure census peak at balance, and the
kill condition (§3) shows this has content, because breaking the pairing moves both peaks off the
closure. The physical identification, that the census and the amplitude *are* the GR and QM action
functionals, is the open bridge above. The causal-set continuum step it would rest on is itself an
explicit axiom (`benincasa_dowker_limit` in [`lean/QLF_CausalContinuum.lean`](lean/QLF_CausalContinuum.lean)),
and it concerns the mean value of an operator, not its first variation.

**Why Hilbert could not finish, and why ZFA can.** Hilbert had the right principle and the wrong
arena. He wrote his action over the continuum, and the continuum has produced physical fantasy every
time it was taken literally. Most dramatically, it proves that one solid ball can be cut into five
pieces and reassembled into two identical balls (Banach–Tarski, with the Axiom of Choice): matter from
nothing. And again and again in physics: the infinite point electron with its runaway, acausal motion; the
ultraviolet catastrophe; the `10¹²²` vacuum energy; the Landau pole; singular black holes and a
singular Big Bang; and a perturbation series that cannot be summed ([`TheContinuum.md`](TheContinuum.md), *fantasy, again and again*). Einstein demanded a
unified theory free of singularities and, by 1954, suspected the continuum itself was the obstacle.
Every one of those singularities comes from the continuum. Take the same principle off the continuum
and put it on the finite closure census, and none of them can form: action comes one quantum per
closed cycle, the electron is a closed mode of finite extent, and the sum over histories converges
absolutely (`twist_kraft`). **Stationary action was always the theory of everything. ZFA is the
version of it that does not break.**

**The remaining step**, stated once: first ZFA closure supplies the substrate event semantics, and
stationarity of the closure census is proved. What is not yet proved is the continuum bridge that turns
"no surviving free action" into Hilbert's particular stationary functional `∫R`. The
Benincasa–Dowker causal-set result supplies the continuum target. The multiplicity theorem is supporting
structure, not the selector.

## §1 What the classical principle leaves unexplained

In the classical theories `δS = 0` is an axiom. It picks out the equations of motion, but nothing in
classical mechanics or GR says *why nature extremises an action*. Feynman (1948) gave the
quantum-mechanical reason: amplitudes `e^{iS/ħ}` from nearby paths cancel unless those paths are near a
stationary point, so the classical path is where the contributions pile up. QLF gives the substrate
version of that reason, with the phase replaced by the **count of ways**:

> **What closes first happens first.** Closure is the event, and it is irrevocable
> ([`MostWays_First.md`](MostWays_First.md)). Multiplicity answers a different question: how often a
> closure occurs across the admissible census.

This distinction is proved to matter: [`QLF_ClosureMultiplicity`](lean/QLF_ClosureMultiplicity.lean)
shows `depth_one_not_modal`, so first depth and modal depth can differ. The census result below remains
important: `W` is stationary at ZFA balance. If one additionally identifies `S ↔ −ħ log W`, that
stationarity has the Euclidean action form. But that identification is a bridge, and the mode is not the
selector.

## §2 The proof (one-axis census)

A `2n`-step `±` history with `k` up-steps is realized in `W(k) = C(2n, k)` ways. ZFA balance is `k = n`.

| Theorem | Statement | Reading |
|---|---|---|
| `ways_symmetric` | `W(n+d) = W(n−d)` | conjugate symmetry about balance |
| `first_variation_zero` / `central_difference_zero` | `W(n+d) − W(n−d) = 0` | **`δ log W = 0` at the closure** |
| `balance_is_mode` | `W(k) ≤ W(n)` for all `k` | balance is the modal census outcome; **not** the event-priority rule |
| `balance_strict_max` (+ `'`) | `W(n±1) < W(n)` | negative second variation: a true maximum |
| `straight_path_most_ways` | `C(n,j)² ≤ C(n,⌊n/2⌋)²` | maximum pass-through count at the balanced midpoint; supporting geodesic statistic, not a selector |
| `balance_is_stationary_mode` | all of the above plus the kill witness | summary |

The geodesic statement is the one that looks most like mechanics. Split a `2n`-step closure into a leg
out and a leg back. The closures passing through a given midpoint number `C(n,j)·C(n,n−j) = C(n,j)²`.
That count is largest for the balanced midpoint. This is exact combinatorics and a useful classical
rendering. It does **not** establish that the substrate chooses that path because it has the largest
count. Event priority has already been fixed by first closure; this theorem says where the census is
stationary and most concentrated.

## §2a The continuum rendering of §2 (census action limit)

[`QLF_CensusActionLimit`](lean/QLF_CensusActionLimit.lean) renders §2 at the census scale and proves
the rendering converges. The cost of displacing a balanced history by `d` up-steps is
`I_n(d) = log W(n) − log W(n+d)`. One exact identity, `W(n+j+1)(n+j+1) = W(n+j)(n−j)`, makes each
increment a single logarithm, and the two elementary log bounds give an exact sandwich with no
asymptotics:

\[
\frac{d^2}{n+d} \;\le\; I_n(d) \;\le\; \frac{d^2}{n-d+1}\qquad (0 \le d \le n).
\]

| Theorem | Statement | Reading |
|---|---|---|
| `censusCost_sandwich` | the bound above, every `d ≤ n` | finite and exact |
| `censusCost_gaussian_limit` | `I_n(⌊x√n⌋) → x²` | the value limit (#303 S1) |
| `censusCost_variation_limit` | `√n·(I_n(d+1) − I_n(d)) → 2x` | the **variations** converge to the derivative of the limit (#303 S2), proved on their own because value convergence does not give it (`sin(nx)/n`) |
| `censusCost_curvature_limit` | `n·(I_n(1) + I_n(−1) − 2I_n(0)) → 2` | the return: the continuum curvature, recovered from the exact count |
| `censusCost_eq_zero_iff` | `I_n(d) = 0 ⟺ d = 0` | the limit's minimizer `x = 0` returns to balance, `balance_is_mode` |
| `euclidean_action_limit` | `ħ·I_n → ħx²` | `ħ` is a fixed constant; the limit is in `x = d/√n`, never in `ħ` |

So the continuum is a rendering at large census scale with `S ≫ ħ`, and the quantum of action does
not vanish. What this fixes and what it does not:

* It is **one** stationary continuum functional for a specified finite counting functional (#303
  level S-MATH). The log normalization is a choice the limit inherits: the cost `1 − W(n+d)/W(n)` has
  the same discrete mode and limit `1 − e^{−x²}` ([`census_action_limit.py`](census_action_limit.py),
  check K4).
* `−ħ log W` is a Euclidean, large-deviation weight. The Lorentzian action with its phase `e^{iS/ħ}`
  needs the signed construction of §5a carried to a limit (#303 S3–S5), and that is open.
* The mode is a frequency statistic. Priority is still first closure.

The companion [`census_action_limit.py`](census_action_limit.py) shows the rates numerically (error
`O(1/n)` when `x√n` is an integer, `O(1/√n)` from the floor otherwise). It is evidence, not a
certificate; the proof is the Lean module. Claim record:
[`claim_records/stationary_action.json`](claim_records/stationary_action.json) (`B-OPEN`).

## §2b A physical action whose stationarity forces closure (link sector)

[`QLF_LinkAction`](lean/QLF_LinkAction.lean) has a genuine variational equation: the finite link
action is stationary under every single-link variation iff `curl F = J`. [`QLF_LinkClosure`](lean/QLF_LinkClosure.lean)
sources it with a history. A history of signed axis steps, started at a site, deposits a current
`J` that counts each link traversal with its sign; nothing about the action enters that map.

| Theorem | Statement |
|---|---|
| `sum_walkCurrent` | the total current on axis `k` is the history's net count `#(k,+) − #(k,−)` |
| `div_walkCurrent` | `div J = δ_start − δ_end` |
| `stationary_forces_count_balance` | if **any** link configuration is stationary for this `J`, the history is count-balanced on every axis |
| `stationary_forces_return` | and it returns to its start |
| `open_history_no_stationary` | an unbalanced history has no stationary configuration at all (one step is the minimal witness) |
| `closed_history_gauge_invariant` | a returning history makes the coupling gauge invariant |

So stationarity of a physical-style action, under all variations rather than closure-preserving
ones, forces ZFA's count condition on its source, and with `count_balanced_pauli_closed` full
closure. The reason is short: `curl F` has zero total on every axis, and the current's total is the
net count. The converse, that every count-balanced history admits a stationary configuration, is a
finite Hodge decomposition and is not proved. [`link_closure.py`](link_closure.py) checks it in
exact rational arithmetic on `(ℤ₃)²`, `(ℤ₄)²` (lengths ≤ 6), `(ℤ₃)³` (≤ 5) and `(ℤ₃)⁴` (≤ 4):
stationary exists exactly for the count-balanced histories, and winding histories, which return on
the torus without balancing, have none. On four axes the balanced count at length 4 is 168, the
closed-plaquette count. This is the link sector at fixed time (#303 S-PHYS candidate, not S-PHYS);
it does not identify the link action with the census cost of §2a.

The same current, used as fluxoid labels for a Regge geometry, is the next roadmap step (#301
milestone 1). Its kill conditions are pre-registered in [`Continuum_Limit.md`](Continuum_Limit.md).

## §3 Why this is not bookkeeping — the kill condition

Method rule 4 ([`CLAUDE.md`](CLAUDE.md), [`ScientificApproach.md`](ScientificApproach.md)): a claim has
physical content only if some distribution over ways would make it **false**. Here there is one: the
**biased alphabet**. Weight each up-step `2` and its conjugate `1`:

* `biased_first_variation`: `W'(n+1) = 4·W'(n−1)`. The first variation at balance is **non-zero**.
* `biased_mode_off_balance`: `W'(2,2) = 24 < W'(2,3) = 32`. The mode moves **off** the closure.

So stationarity *at the closure* is not a property of every counting. It holds because every twist has
its conjugate at equal weight, which is exactly the pairing ZFA balances (`^`↔`v`, `<`↔`>`, `/`↔`\`,
`+`↔`−`). Without that pairing there would still be a stationary point, but it would not be a closure.

## §4 Closed histories vs open arcs — reconciling `ℒ = 0` and `δS = 0`

[`Lagrangian_Formulation.md`](Lagrangian_Formulation.md) writes the core principle as `S = ∫ℒ dΩ`
with `ℒ = 0`. [`UniversalRelativity.md`](UniversalRelativity.md) §2 already names the local/global
split, and this module supplies the mechanism behind it:

* **Closed history** (a loop, a Markov blanket, the totality): the ledger balances exactly, and free
  action is `0`. This is `ℒ = 0`.
* **Open sub-arc** (a leg of a closure still in progress): free action need not vanish because no
  event has yet completed. The balanced census nevertheless has a stationary pass-through profile
  (`straight_path_most_ways`). That is a statement about the rendering of open possibilities, not a
  rule selecting an event.

So the logical order is asymmetric: **`ℒ = 0` at first closure is primitive at the substrate**, while
classical `δS = 0` is the continuum variational form that must be recovered from it. The census
stationarity theorem shows the right local signature at balance, but it does not by itself complete that
continuum bridge.

## §5 Hilbert — which action is stationary

The multiplicity argument explains **why** some action is stationary. It does not by itself say
**which** functional. For gravity that functional is Hilbert's `∫R`, and QLF already has it from its
own causal order:

* QLF's reachability order is a causal set ([`QLF_ReachableEvent`](lean/QLF_ReachableEvent.lean)).
  Counting events measures volume ([`QLF_CausalInterval`](lean/QLF_CausalInterval.lean)).
* The **Benincasa–Dowker** action of that causal set converges in the continuum to the
  Einstein–Hilbert action `∫R`. This is settled causal-set mathematics, entered as the cited
  boundary `benincasa_dowker_limit` ([`QLF_CausalContinuum`](lean/QLF_CausalContinuum.lean)),
  unchanged here. See [`Einstein_Equations.md`](Einstein_Equations.md) §6a.

So the corrected chain is: **first ZFA closure ⟹ event selection/order**; **conjugate pairing ⟹
multiplicity stationary at balance** (proved here); and the causal-set Benincasa–Dowker action
**→ `∫R`** (cited continuum result). What remains is to prove that Hilbert's stationarity is the
continuum rendering of the first-closure condition, rather than to assume that the substrate takes a
multiplicity mode. The coefficient `8πG = 2π/η` comes separately from the thermodynamic leg
([`Einstein_Equations.md`](Einstein_Equations.md) §§2–5).

**The named gap.** The continuum identification is open. The proofs here establish stationarity of
the twist census at ZFA balance; they do not prove that the physical action functional is `−ħ log W`,
nor that nature selects the census mode. What remains is to connect the absorbing first-closure condition
to the Benincasa–Dowker/Hilbert variational functional. It is the bridge between
this module and `QLF_CausalContinuum`. It is harder than the two halves proved here for a stated
reason: those are statements about **paths** (twist histories and their endpoints on `ℤ⁴`), while the
Benincasa–Dowker action is a functional of the **causal order**, built from its interval layers. On a
single history that order is a chain and the BD reading is exactly `0` (`bdCurvature_chain_zero`). What
is missing is a count of ways over causal sets whose mode can be compared with the BD stationary
point. No axiom is added for it
([`Open_Problems.md`](Open_Problems.md)).

## §5a The signed half — stationary phase, proved

Feynman's argument uses the *signed* sum, where stationarity comes from phase cancellation. In QLF the
phase of a history is the ℤ₂ holonomy of the edge-sign connection ([`QLF_EdgeSign`](lean/QLF_EdgeSign.lean)),
defined for every history, open or closed. [`QLF_StationaryPhase`](lean/QLF_StationaryPhase.lean)
proves the signed statement on all of `ℤ⁴` with no axioms:

| Theorem | Statement | Reading |
|---|---|---|
| `amp_add` | `amp(m+n) x z = Σ_u phase(u)·amp(n) (end u) z` | a history splits; its phase factors |
| `amp_swap` | `amp m y x = (−1)^m · amp m x y` | reversal flips every edge sign: the real kernel is **skew-symmetric for odd `m`, symmetric for even `m`**, the conjugate pairing at the level of phases |
| `return_amplitude_sum_sq` | `amp(2m) x x = (−1)^m · Σ_y amp(m) x y²` | **the closure amplitude is the norm of the half-way amplitude** |
| `amp_closed_translate` | `amp n x x = amp n 0 0` | a closed loop carries the same phase wherever it starts |
| `signed_mode_at_balance` | `\|amp(2m) 0 x\| ≤ \|amp(2m) 0 0\|` | **stationary phase:** no endpoint beats the closure |
| `ways_mode_at_balance` | `W(2m) 0 x ≤ W(2m) 0 0` | the unsigned (classical) half, now on all four axes |

The proof is short once the pieces exist. Split a `2m`-step history at its midpoint. Reversal turns
the second half into a first half with sign `(−1)^m`. Grouping by midpoint then gives
`amp(2m) 0 x = (−1)^m Σ_y f(y)·g_x(y)`, and Cauchy–Schwarz bounds it by `Σ f² = |amp(2m) 0 0|`.
The one input that is specific to QLF is the reversal step: the connection never reads the
coordinate being stepped (`edgeParity_stepPos_own`), so stepping back through an edge flips exactly
its twist sign.

**Pre-registered test** ([`stationary_phase_census.py`](stationary_phase_census.py), committed before
it was run; exact integers to `L = 12`, [`data/stationary_phase.json`](data/stationary_phase.json)):
S1 (`|A(x)| = |A(−x)|`) **PASS**; S2 (signed mode at balance) **PASS**, and the maximum is unique
(`A₀ = −8, 120, −2144, 41896, −868608, 18816384`). S3 (*coherence* `|A|/W` largest at balance)
**FAIL**, and it failed because it was badly posed rather than because of the physics: any endpoint
reached by a single path has coherence exactly `1`. It is recorded as a failure and not reworded.

## §5b Is the phase an action? (#303 S4–S5, K5–K7) — pre-registration

This section was committed before [`signed_phase_track.py`](signed_phase_track.py) existed. Results are in §5c.

**What is already proved.** For a balanced history the fold is
`(−1)^{#neg} · (−1)^{Φ}`, where `Φ = A_XY + A_XZ + A_YZ` is the sum of the three projected areas
([`QLF_PlaquetteArea`](lean/QLF_PlaquetteArea.lean), `fold_eq_projected_phase`). Count balance makes
`#neg = L/2`. So the phase reads `θ(h) = π·(L/2) + π·Φ(h)` mod `2π`: a constant phase per step pair
plus a uniform flux `π` through every spatial plaquette. This is derived from the matrices, not
assigned, and it is the S4 candidate. It composes under concatenation (`amp_add`) and is fixed by
reversal on closed histories, since `−θ ≡ θ` for a ℤ₂ phase.

**The family of countermodels.** Replace the QLF connection by a U(1) connection with flux `φ`
through every spatial plaquette and sign `σ` on every negative step. QLF is `(φ, σ) = (π, −1)`. The
test family is `φ ∈ {0, π/2, 2π/3, π}`, `σ ∈ {+1, −1}`, on all of `ℤ⁴` with the gauge axis flux-free
as in `QLF_EdgeSign`.

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| P1 (K5) | the stationary-phase bound identifies the phase | `\|A(2m; 0, x)\| ≤ \|A(2m; 0, 0)\|` **fails** for some `(φ, σ) ≠ (π, −1)` at some `2m ≤ 10` | **fail**: the transfer operator is Hermitian or anti-Hermitian with translation-covariant diagonal for every `(φ, σ)`, so Cauchy–Schwarz gives the bound for all of them |
| P2 (K6) | the Pauli fold fixes the action | `(π, −1)` is the only member whose weight equals the fold on every balanced history of length `≤ 6` | pass, with `φ = −π` indistinguishable from `π`: the phase fixes the plaquette action only mod `2πħ` and up to sign |
| P3 (S4 laws) | the phase composes and reverses | weight(`u ++ w`) = weight(`u`)·weight(`w`) for closed `u, w`; weight(reverse `h`) = conjugate(weight `h`)·`σ^L` | pass, structural |
| P4 (K7) | the action has a smooth limit with `ħ` fixed | recorded before the run, not computed | **fail** for an Aharonov–Bohm reading: flux `π` per plaquette of side `a` is a field `π/a²`, which diverges as `a → 0` |

**Verdict rule.** If P1 fails as expected, the bound `signed_mode_at_balance` is supporting evidence
only (as #303 says) and no phase/action identification may rest on it. If P2 passes, the phase
fixes the plaquette action to the ℤ₂ class `π` mod `2π`, and that, not the bound, is what the
identification must use. P4 failing means the S4 candidate does not render as a smooth classical
action. The standing continuum reading of a uniform π-flux lattice is a Dirac operator (staggered
fermions, Kogut & Susskind 1975; the symbol is `QLF_LorentzSymbol`'s `2i·Form(sin k)`), so S5 must
be posed for that kinetic phase, not for an area action.

## §5c The phase/action test — results

Run: [`signed_phase_track.py`](signed_phase_track.py), exact amplitudes in `ℤ[ζ₁₂]` on all of `ℤ⁴`,
output [`data/signed_phase_track.json`](data/signed_phase_track.json). The candidate form is now a
theorem: [`QLF_PhaseAction`](lean/QLF_PhaseAction.lean) `phase_action_form` proves that a closure of
length `L` has phase `(−1)^{L/2}·(−1)^{Φ}`, from `two_negCount_of_balanced` (`2·#neg = L`).

| | Outcome | What was found |
|---|---|---|
| P1 (K5) | **fails, as predicted** | the stationary-phase bound `\|A(2m;0,x)\| ≤ \|A(2m;0,0)\|` holds for **all eight** members `(φ, σ)` at every `2m ≤ 10` (and at `12`). The bound does not identify the phase. The QLF row reproduces the registry: `\|A₀\| = 8, 120, 2144, 41896, 868608` |
| P2 (K6) | passes | of the ten members tested (`±π` included) on the 5,296 balanced histories of length `≤ 6`, only `(π, −1)` and `(−π, −1)` match the Pauli fold. `(π, +1)` fails exactly when `L/2` is odd, from `+−` on. So the fold fixes the flux to the ℤ₂ class `±π` and the step sign to `−1` |
| P3 (S4 laws) | passes, structurally | composition and reversal hold for every member on all 177 closed histories of length `≤ 4` |
| P4 (K7) | **fails** (recorded before the run) | flux `π` per plaquette of side `a` is the field `π/a²`, which has no limit as `a → 0` |

`σ` never changes a modulus. The number of negative steps to a fixed endpoint is fixed by the
length, so `σ` is a sign per endpoint, and P1 is in effect a test of `φ` alone.

**Verdict.** No phase/action identification can rest on `signed_mode_at_balance`: the bound holds for
every U(1) flux, so it is supporting evidence only, as #303 says. What the phase data do fix is the
ℤ₂ class. Each spatial plaquette carries action `πħ` mod `2πħ`, up to sign, and each step pair
carries phase `π`. That is the S4 candidate, derived and not assigned, and it composes and reverses
correctly. It does not render as a smooth area action at fixed `ħ` (P4). The open S5 problem is
therefore the kinetic reading: the uniform π-flux lattice is the staggered-fermion lattice (Kogut &
Susskind 1975), whose continuum symbol is `QLF_LorentzSymbol`'s `2i·Form(sin k)`. Stationary phase
has to be posed for that Dirac phase. An area action is not available.

Post hoc, not pre-registered: within the family, the return amplitude `\|A₀\|` falls monotonically
from `φ = 0` to `φ = π` at every `2m ≥ 4`. QLF's flux gives the most cancellation of the family.
This was not a test, so it is not evidence.

## §6 Honest scope

* **Signed = quantum half, in the stationary-phase sense only.** §5a proves the signed amplitude
  peaks at balance. It does not derive the Born weights; that remains
  [`Born_Rule.md`](Born_Rule.md)'s question, though `return_amplitude_sum_sq` (closure amplitude =
  norm of the half-way amplitude) bears directly on it.
* **Priority is not multiplicity.** No theorem here says nature selects the modal history. First closure supplies priority; `QLF_ClosureMultiplicity.depth_one_not_modal` proves modal depth can differ from first depth.
* `S ↔ −ħ log W` is an identification (Boltzmann/Jaynes: log-count is entropy; the Euclidean action
  is the log-weight). It is not derived here.

[`Unreasonable_Classical_Mathematics.md`](Unreasonable_Classical_Mathematics.md#technical-ledger-what-zfa-currently-buys) collects least action with the other laws QLF obtains from ZFA in its technical ledger, with the status kept explicit: discrete multiplicity stationary at balance is proved, and the bridge to the physical action functional is open.

## References

* Maupertuis, P.-L. M. de (1744). *Accord de différentes loix de la nature qui avoient jusqu'ici paru incompatibles.* Mém. Acad. Sci. Paris — least action as the universal principle.
* Lagrange, J.-L. (1788). *Mécanique analytique.*
* Hamilton, W. R. (1834). *On a General Method in Dynamics.* Phil. Trans. R. Soc.
* Hilbert, D. (1915). *Die Grundlagen der Physik.* Nachr. Ges. Wiss. Göttingen — `∫R√−g`.
* Mie, G. (1912–13). *Grundlagen einer Theorie der Materie.* Ann. Phys. — the electrodynamics Hilbert folded into his action.
* Planck, M. (1915). *Das Prinzip der kleinsten Wirkung.* In *Die Kultur der Gegenwart* III.3.1 — least action as the most comprehensive physical law.
* Feynman, R. P. (1948). *Space-time approach to non-relativistic quantum mechanics.* Rev. Mod. Phys. 20, 367 — stationary phase.
* Jaynes, E. T. (1957). *Information theory and statistical mechanics.* Phys. Rev. 106, 620 — the mode of the count as the realized macrostate.
* Benincasa, D. M. T. & Dowker, F. (2010). *Scalar curvature of a causal set.* PRL 104, 181301.
