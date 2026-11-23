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

QLF's locality holds at the level of **local statistics**, and it holds there for every joint
state, entangled ones included. Whatever one body does, in whatever number of steps and however
those steps interleave with the other body's, the other body's expectations do not change
(`perspective_locality`), and its outcome marginals do not depend on the remote setting
(`no_signalling`). Correlations come from **outcome dependence** (`singlet_outcome_dependent`) and
reach Tsirelson's `2√2` (`singlet_saturates`). Bell locality is the conjunction of parameter and
outcome independence (Jarrett 1984), and the conjunct that fails here is outcome independence. In
the tick reading of spacetime, a **closure is timelike** (a rest mass) and **null histories never
close**. A shared closure can join two endpoints that are spacelike and that no history joins
(`no_history_connects`). The closure census, used as a global post-selection filter, **signals**
(`census_postselection_signals`). So locality depends on the joint verdict being unavailable to
either body alone, and the joint verdict is unavailable to either body
([`QLF_SharedReality`](lean/QLF_SharedReality.lean) `zfa_not_from_one_body`).

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

**A shared closure across a spacelike gap.** Halves `ts` and `ts.map conj` always close together
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
statistic comes from an entangled global state.

**Bell audit.** On the singlet with both settings `σz`, `P(+,+) = 0`, while `P(+) = P(+) = 1/2`
(`singlet_outcome_dependent`). Outcome independence fails. Parameter independence holds for every
state (`no_signalling`). The singlet saturates CHSH at `2√2`
([`QLF_JointClosure`](lean/QLF_JointClosure.lean) `singlet_saturates`), above the `2` that
jointly valued, commuting observables obey ([`QLF_Tsirelson`](lean/QLF_Tsirelson.lean)
`chsh_classical`). No joint value assignment exists for `σz` and `σx` because they anticommute.
So QLF keeps local causal influence and operational no-signalling, and it does not keep Bell-local
factorization. **Bell's theorem is not evaded.** Its premise of outcome independence is the one
that fails.

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
* **L2: why the tick reading is spacetime.** This is open. The shared-pair birth posit (PR #219) is
  the physical input to "light is the open half of a shared closure".
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
* "QLF evades Bell's theorem".
* "`no_ftl_in_epr` proves no-signalling".
