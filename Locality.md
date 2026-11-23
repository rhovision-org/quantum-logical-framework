# Locality in QLF: null intervals, shared closure, perspective boundaries, no signalling

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal
> and opposite quantum logical action with zero free energy, the principle of QLF.

Tracking issue: [#315](https://github.com/rhovision-org/quantum-logical-framework/issues/315).
Lean: [`QLF_LocalityDefinitions`](lean/QLF_LocalityDefinitions.lean) (gates L0, L1) and
[`QLF_PerspectiveLocality`](lean/QLF_PerspectiveLocality.lean) (gates L3, L5). Neither module
uses an axiom. The footprints are in [`QLF_AxiomAudit`](lean/QLF_AxiomAudit.lean) and
[`axiom_footprints.expected.json`](lean/axiom_footprints.expected.json).

The aim is to establish which of Einstein's locality principles follow from QLF, prove those, and
name what is still assumed. Three properties are kept apart until a theorem joins them:
**ZFA** (count balance, hence Pauli closure), **null** (zero Minkowski interval), and **causal
locality** (no influence outside the future cone, and operational no-signalling).

## 1. Result in one paragraph

In **QLF's two-body operator representation** (twists as Pauli matrices on independent tensor
factors, Born weights), locality holds at the level of **local statistics**, for every joint
state, entangled ones included. Whatever one body does, in whatever number of steps and however
those steps interleave with the other body's, the other body's expectations do not change
(`perspective_locality`), and its outcome probabilities, which are real, nonnegative and normalized for dichotomic
observables, do not depend on the remote setting (`no_signalling_typed`). Relative to any finite
complete state `λ` distributed independently of the settings, no factorizable model reproduces
the correlations (`no_factorizable_model`). Correlations come from **outcome dependence** (`singlet_outcome_dependent`) and
reach Tsirelson's `2√2` (`singlet_saturates`). Operationally, parameter independence holds. With the operator state taken as the complete
state, the conjunct of Bell factorization that fails is outcome independence (Jarrett 1984). In
the tick reading of spacetime, a **closure is timelike** (a rest mass) and **null histories never
close**. A shared closure can join two endpoints that are spacelike and that no history joins
(`no_history_connects`). The closure census, used as a global post-selection filter, **signals**
(`census_postselection_signals`). So locality depends on the joint verdict being unavailable to
either body alone, and the joint verdict is unavailable to either body
([`QLF_SharedReality`](lean/QLF_SharedReality.lean) `zfa_not_from_one_body`). **The closure
counting theory has not yet been shown to produce these local quantum statistics.** That is the
next proof that matters (§5, issue [#318](https://github.com/rhovision-org/quantum-logical-framework/issues/318)).

## 2. Vocabulary

| Term | Definition | Where |
|---|---|---|
| Shared closure | `countBalanced (a ++ b)` | [`QLF_LocalityDefinitions`](lean/QLF_LocalityDefinitions.lean) (`ER_EPR_QLF.SharedClosure` in twist form) |
| Prefix reachability | `a <+: b` | [`QLF_ReachableEvent`](lean/QLF_ReachableEvent.lean) |
| Prefix-spacelike | neither is a prefix of the other. This is what [`ER_EPR_QLF`](lean/ER_EPR_QLF.lean) calls `Spacelike` | `PrefixSpacelike` |
| Tick displacement | `(|h|, right−left, up−down, slash−backslash)`: one tick per step, and net spatial displacement | `tick` |
| Interval | `t² − x² − y² − z²` = `Form.interval` = `det` of the Hermitian state | `interval`, `tickForm_interval` |
| Local statistic | expectation of an `A`-observable in the **globally evolved** two-body state | `expect (onA X) (jointFold w *ᵥ ψ)` |
| No-signalling | `A`'s outcome marginal is independent of `B`'s setting | `no_signalling` |

The **tick reading** is the repository's own reading of time as an event count
([`QLF_CausalInterval`](lean/QLF_CausalInterval.lean) `intervalVolume`, the Kitada clock,
and the time axis of [`QLF_LightCone`](lean/QLF_LightCone.lean)). Gauge twists take a tick and
move nowhere. Why this reading is the operational spacetime separation is the **L2 bridge**, and
it is open. The geometric statements in §3 are about the reading.

## 3. Pre-registered predictions and results

The predictions were frozen in the issue body before the Lean for them was written. All eight
came out as predicted.

| # | Prediction | Result | Theorem |
|---|---|---|---|
| P1 | Every history is in the closed future cone | **holds** | `tick_causal`, `tick_not_spacelike` |
| P2 | A nonempty closure is strictly timelike | **holds** | `closure_timelike` |
| P3 | A straight run is null, with time and space both nonzero (Test A) | **holds** | `straight_run_null` |
| P4 | Pair-born halves close together, their endpoints are spacelike, and no history joins them (Test C) | **holds** | `pair_shared_closure`, `pair_endpoints_spacelike`, `no_history_connects`, `up_down_pair` |
| P5 | Reachable ⇒ causal. The converse fails, and prefix-spacelike ⇏ spacelike | **holds** | `reachable_causal`, `causal_not_reachable`, `prefixSpacelike_not_spacelike` |
| P6 | The census conditioned on Bob's setting signals | **signals** (predicted) | `census_postselection_signals` |
| P7 | Local expectations depend only on the local projection, for every joint state (Tests D, F) | **holds** | `perspective_locality`, `local_expectation_local` |
| P8 | No-signalling holds, and outcome independence fails on the singlet | **holds** | `no_signalling`, `singlet_outcome_dependent`, `locality_profile` |

Added after review (not pre-registered; proofs, not tests): typed probabilities
(`probT_nonneg`, `probT_sum`, `no_signalling_typed`) and the `λ`-relative Bell bound
(`chsh_factorizable_le`, `no_factorizable_model`).

## 4. What each result means, and what it does not

**Closures are massive, light is open.** Under the tick reading, count balance sets the spatial
displacement to zero while the clock advances, so a nonempty closure has interval `|h|² > 0`
(`closure_timelike`). That matches [`QLF_Inertia`](lean/QLF_Inertia.lean): a rest mass is a
closed null circulation. A null history has to move one axis unit per tick in one direction, and
`null_not_closed` shows it never closes. The draft target "radiative ∧ ZFA ⇒ null" therefore has
no nonempty instance. The target that replaces it is that **light is the open half of a shared
closure**: two null halves born at one event that close jointly.

**The signed reading is degenerate.** Read the gauge axis as a signed coordinate
([`QLF_EdgeSign`](lean/QLF_EdgeSign.lean) `position`) and every closure goes to the zero vector
(`zero_displacement_degenerate`). There, "ZFA ⇒ null" holds only because the interval of `0` is
`0`. That map cannot serve as the L2 bridge.

**`ER_EPR_QLF`'s `Spacelike` is an order relation.** The primordial pair `[plus]`, `[minus]` is
prefix-incomparable, and both halves land on the same tick event
(`prefixSpacelike_not_spacelike`). Its `no_ftl_in_epr` is the second conjunct of the
`ERBridge` definition, which is bookkeeping and says nothing about signalling. The signalling
content is in §4 of this doc ("Locality of statistics").

**A shared closure across a spacelike gap.** This is a formal conjugate construction. That physical
pairs are born this way is the separate shared-pair birth posit (PR #219), which no theorem here
assumes or proves. Halves `ts` and `ts.map conj` always close together
(`pair_shared_closure`). When they have moved, their endpoints are separated by `(0, 2x)`, which
is spacelike, and no history has that displacement (`no_history_connects`). So a shared closure
is a relation that no causal history carries. That is the substrate form of "correlation without
a channel". It does **not** make the endpoints null-separated: their interval is `−4|x|² < 0`.

**Locality of statistics.** The global two-body fold factorizes into the bodies' own folds
(`jointFold_factorizes`, from `indexed_factors_commute`), and every twist word folds to a unitary
(`fold_unitary`). `A`'s expectation is defined on the globally evolved state, yet it equals the
initial expectation of `A`'s Heisenberg-evolved observable (`local_expectation_local`). Hence
`perspective_locality`: two global histories with the same `A`-projection give `A` identical
statistics for **every** joint state. The theorem has content because the restriction is not
vacuous: one `B` token flips `B`'s own `σz` expectation from `1` to `−1`
(`perspective_locality_nontrivial`). This strengthens [`QLF_SharedReality`](lean/QLF_SharedReality.lean)
§5, which proved projection invariance for chosen record maps on independent bodies. Here the
statistic comes from an entangled global state. The dynamics is still a product of local
twists on independent tensor factors, so the theorem says nothing yet about interacting ZFA
evolution or a dynamically reconstructed boundary.

**Typed probabilities.** `prob` accepts any matrix and any `α`, so `no_signalling` is a weight
identity. For `Dichotomic` observables (Hermitian, `X² = 1`) and outcomes `±1`, the weights are
real and nonnegative (`probT_nonneg`) and sum to the state's norm, which every history preserves
(`probT_sum`). `no_signalling_typed` is no-signalling as a probability statement.

**Bell audit.** Bell's factorization is conditional on a complete state `λ`.
`chsh_factorizable_le` proves that every model with a finite space of complete states, `λ`
distributed independently of the settings (measurement independence), and factorized responses
`E(x,y|λ) = a_x(λ) b_y(λ)` with `|a|, |b| ≤ 1`, has `|CHSH| ≤ 2`. The singlet's operator
correlations reach `2√2` ([`QLF_JointClosure`](lean/QLF_JointClosure.lean) `singlet_saturates`),
so `no_factorizable_model`: no such model reproduces them. Given measurement independence,
factorization fails at **every** finite `λ`. Operationally, parameter independence holds
(`no_signalling_typed`). Which conjunct fails at a hidden `λ` depends on the model. Taking the
operator state itself as `λ` (the orthodox completeness reading), it is outcome independence:
`P(+,+) = 0` while `P(+) = P(+) = 1/2` (`singlet_outcome_dependent`). No joint value assignment
exists for `σz` and `σx`, because they anticommute
([`QLF_Tsirelson`](lean/QLF_Tsirelson.lean) `chsh_classical` is the commuting case). **Bell's
theorem is not evaded.** What QLF owes is a statement of its complete state, and that is open.
Finite `Λ` is a restriction of this formalization.

**The census signals.** Count joint closures uniformly, conditioned on the words Bob may use. With
one twist each, both of Bob's settings admit 2 joint closures, but Alice's count for `slash` is `1`
under `z` and `0` under `x` (`census_postselection_signals`). Conditioning on a joint closure is
post-selection on a joint fact. [`QLF_ClockIntervention`](lean/QLF_ClockIntervention.lean)
`record_signals` is the same failure for a naive record. The resolution is not a new rule. The
joint verdict is not a function of either body's record (`zfa_not_from_one_body`), so the
conditioning can only be done where both records meet, inside the common future. Before then,
Alice's statistics are the operator-layer ones, and those do not signal.

## 5. Scope and what is open

* **Representation result.** The probabilities in `QLF_PerspectiveLocality` are Born weights on the
  twist operator algebra. A census-level measure that is no-signalling and reproduces these
  correlations has not been constructed. P6 shows that plain uniform counting over joint closures
  is not that measure.
* **Measurement independence** is a modelling input. Settings and state are independent variables
  in every theorem.
* **The substrate measure.** The missing construction is a measure `μ_QLF` over admissible
  histories, built only from what each perspective holds, whose marginals satisfy
  `Σ_B P_μ(A,B|a,b) = P_μ(A|a)` for every remote context while reproducing the quantum
  correlations. P6 shows uniform counting over joint closures is not it.
* **L2: why the tick reading is spacetime.** This is open. The shared-pair birth posit (PR #219) is
  the physical input to "light is the open half of a shared closure".
* **L2b: from open null strands to completed light interactions.** Only ZFA events occur, so a null
  strand is physical only as part of a completed closure (emission and absorption). Which
  closures realize a light exchange, and that their open legs are the null strands of §4, is an
  open bridge.
* **Complete state.** QLF has not specified its complete state `λ`; the Bell audit above is
  relative to that choice.
* **Accessibility.** The two-body split is given. Where a perspective boundary comes from is open
  ([`Holography_Audit.md`](Holography_Audit.md) §5).
* **L4, L6, L7** are not attempted here. L6 has its ingredients:
  [`QLF_HolographicArea`](lean/QLF_HolographicArea.lean) `pair_local_of_steps` gives range `≤ 2k`
  for pairs of age `k`, and `tick_causal` is its Minkowski form. The premise still to replace in
  [`QLF_LocalAreaLaw`](lean/QLF_LocalAreaLaw.lean) is a pair age bounded independently of the
  region.

## 6. Overclaims to avoid

* "Null means zero distance" (`null_not_zero_time`, `null_not_zero_space`).
* "Shared closure means zero Minkowski separation" (`pair_endpoints_spacelike`).
* "No-signalling is Bell locality" (§4, Bell audit).
* "QLF locality is derived from the closure census" (it is proved in the operator representation).
* "QLF evades Bell's theorem".
* "`no_ftl_in_epr` proves no-signalling".
