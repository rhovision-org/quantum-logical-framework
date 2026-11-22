# Closing bridges with strange loops, fractals, Zipf, bisimulation and turbulence

Part of the [Quantum Logical Framework (QLF)](README.md). Status ledger: [Claim_Status.md](Claim_Status.md); method: [ScientificApproach.md](ScientificApproach.md).

**Question (Jim, 2026-11-16).** Can any of the missing bridges be closed now, perhaps with strange loops, fractals, Zipf's law, bisimulation or turbulence, reasoned possibilistically?

**Short answer.** One bridge requirement is now a theorem, in its possibilist form: **one closure decides**, and the first closure is one that does (§2). One route to the Koide phase is shown not to close, which is a fact about that route only (§3). Zipf's law holds for the closure inventory, but its exponent is bookkeeping, and only its correction carries content (§4). The ledger statuses of the physical bridges (α's scale map, Born, the clock map, the detector map, map ≡ territory) are unchanged, and §5 says what one way would look like for each. §6 records the bridge-closure plan of 2026-11-21: seven pre-registered steps, each with a Lean module and no new axiom.

**How "possibilistically" is read (Jim, 2026-11-16).** *Possibilism only requires one way. The first closure is the strongest way.* A bridge exists once one way across it is exhibited; nothing has to be shown about all ways. Among the ways, the first closure has priority, because closure is irrevocable (`closedAtHorizon_mono`). Two consequences follow. A route that fails to close (§3) counts for nothing against the bridge it aimed at. And the quantifier over every context in §2 is not needed: one closing context does all the work.

---

## 1. What each tool can and cannot do here

A bridge closes only with a theorem or a decided, pre-registered test ([ScientificApproach.md](ScientificApproach.md)); an analogy closes nothing. With that bar:

| Tool | What it offers QLF | Verdict on the open bridges |
|---|---|---|
| **Bisimulation** | The greatest relation compatible with continuation and an observable is unique, so a bridge's equivalence can be *derived* rather than chosen | **Theorem (§2).** One closing context decides the class, the first closure included. It closes the "why this equivalence" part of Paper I §11.2 on the two-body domain. The physical half of map ≡ territory (that the joint-closure phase is the only observable) stays open, but it is now one statement. |
| **Strange loops** | A level-crossing return to a finite record. QLF already uses it as the review shape of every bridge ([Strange_Loops.md](Strange_Loops.md), `QLF_StrangeLoop`) | No new closure. A loop is closed by a conservative return, and for Born and MO2 the return needs a physical refinement or detector map that no loop supplies. |
| **Return bounds (transience)** | Exact control of how much possibility ever comes back. This is the Pólya property behind `QLF_PolyaTransience` | **Decided a pre-registered test (§3):** the Koide census limit `P` fails, now with a certificate. |
| **Zipf** | Rank-frequency of closures | **Measured (§4).** A staircase with `f = Θ(1/(r (ln r)^{d/2}))`. The exponent `−1` is Miller's random-typing bookkeeping. The `(ln r)^{−d/2}` correction counts axes. It decides no bridge. |
| **Fractals / self-similarity** | Self-similar closures exist ([self_similar_closures.py](self_similar_closures.py)). Through the bifibration, self-similarity already rules out log-periodic corrections, so `w = ½` is structural ([Category_Theory_QLF.md](Category_Theory_QLF.md) §3a) | Self-similarity forces the octave-to-scale map to be geometric, `Q(R) = Q₀λ^R`, but leaves `Q₀` and `λ` free. That is exactly what the α bridge lacks, so this route stops one step short (§5). |
| **Turbulence** | An inertial-range cascade would supply a per-octave exponent for the α residual | Already run twice, pre-registered: [intermittency_bridge.py](intermittency_bridge.py) on the vacuum census and [intermittency_seeded.py](intermittency_seeded.py) on seeded censuses. Neither shows an inertial range at the census depths reached. That is incomplete rather than negative, because physical closures are far deeper, but nothing new is available to try without a physical injection scale. The side result `C₀ = 2` stands. |

## 2. Bisimulation: one closure decides the bridge equivalence (Lean, no axioms)

Paper I §11.2 asks every bridge to state a physical-equivalence relation on histories and to justify it. [`QLF_ObservationalEquivalence`](lean/QLF_ObservationalEquivalence.lean) (PR #241) proved that "no appended context tells two histories apart by joint-closure phase" is exactly the tensor-image relation. Its new §7 proves the step-by-step form, which is the one a reviewer can check:

- `IsBisim R`: related histories have the same observable *now* (they close jointly with the same phase, or both do not) and stay related after any one-token extension. This is a bisimulation of the append transition system (Park 1981; Milner 1989).
- `bisim_le_obsEquiv`: **every** such relation is contained in observational equivalence.
- `obsEquiv_isBisim`, `obsEquiv_iff_exists_bisim`: observational equivalence is one, so it is the **greatest** bisimulation.
- `bisim_le_pairEquiv`, `pairEquiv_isBisim`: hence so is the tensor relation `PairEquiv`.

**One way suffices (§8 of the module).** The definition of observational equivalence asks about every context and every phase. None of that is needed:

- `one_closure_decides`: if any one context `c` closes `w` with phase `z`, then `w'` is in `w`'s class exactly when `c` closes `w'` with the same phase.
- `IsFirstClosure w c z`: `c` closes `w` and no proper prefix of `c` does. This is first **along the chosen context** `c`.
- `exists_first_closure`: every history has one. The proof takes the shortest closing prefix of the dagger completion.
- `first_closure_decides`: such a closure alone tells apart everything that all contexts together could.

Scope of "first". `IsFirstClosure` is prefix-minimality inside one context. It does not say the context is the globally earliest closure among all contexts, and it does not single out a physically privileged first observation. The theorem does not need either: `one_closure_decides` holds for **every** closing context, so whichever closure comes first under any ordering is covered. In that sense no later or longer closure distinguishes two histories that an earlier one does not. The reason is that a fold is invertible, so a closing context loses nothing. This also removes the quantifier a reviewer would otherwise have to trust. To check that two histories are the same event class, run one closure.

**What this closes.** On the two-body domain the bridge equivalence is no longer a choice. Any bridge that respects continuation and joint-closure outcomes can only use `PairEquiv` or something finer, and `PairEquiv` is the coarsest. A coarser relation would merge histories that some continuation tells apart. This is the Myhill–Nerode right congruence (Nerode 1958) read as a bisimulation, and the step is standard. The QLF-specific content is `obsEquiv_iff_pairEquiv`, which says the greatest bisimulation is the tensor quotient.

**What it does not close.** The theorem takes the joint-closure phase as *the* observable. That this is the only physically available observable is the apparatus half of map ≡ territory ([Map_Is_Territory.md](Map_Is_Territory.md), #213), and it stays `B-OPEN`. Also open are the entangled sector and the `N`-body version. For the self-knowledge target ([self_knowledge_target.md](verification/strange-loop/self_knowledge_target.md)), this supplies obligation 8 (the bisimulation is proved, and the choice of equivalence is stated and shown canonical) for this observable. The embedding, reflection and update obligations are untouched.

## 3. Koide census limit: this one route does not close

[`lepton_phase_series.py`](lepton_phase_series.py) pre-registered a single statistic. `P` is the probability that a non-backtracking walk on `ℤ³` first returns as an electron-like free half-spin closure, under the hypothesis `Δ = P` radians, which is killed if `2/3` lies outside a bracket on `P`. The run estimated `P ≈ 0.041`, but the review on PR #240 showed that the only certified enclosure was `[0.040, 0.944]`, which does not exclude `2/3`. It also named the missing piece, a proved bound on the walk's total return probability. [`lepton_phase_certify.py`](lepton_phase_certify.py) supplies that bound.

**The bound.** Every electron-like first return of length `n` is a walk at the origin at step `n`. So `P ≤ E`, where `E` is the expected number of returns, and `P − S_N ≤ E − U_N`. Non-backtracking counts obey `A_{n+1} = A·A_n − 5A_{n−1}`, which gives `Σ A_n z^n = (1 − z²)/(1 − Az + 5z²)` (standard; Alon, Benjamini, Lubetzky, Sodin 2007). At `z = 1/5` the denominator becomes `(6/5)(1 − D(k))`, which gives

```
E = (2/3)·G − 5/6,   G = Watson's integral (1939), the simple walk's expected visits to the origin
```

**What is proved and what is computed.** The reduction `P ≤ E = (2/3)G − 5/6` is an analytic argument, written out in the script's docstring with the interchange of sum and integral; it is not machine-checked. The numerical inequality is certified in exact rational arithmetic, with no floating point. `G` is the sum of the simple walk's return probabilities `u_{2n}`. The script sums the first 400 exactly and bounds the rest by `u_{2n} < 1.001 · 0.467 · (n − 2)^{−3/2}`, which follows from Robbins' (1955) factorial bounds, the balanced maximum of the trinomial, and `C(2n,n)/4ⁿ ≤ 1/√(πn)`. It asserts that term bound against every exact `u_{2n}` it computes. This gives

```
G ≤ 1.493079 + 0.046864 = 1.539943 < 9/4        (rational arithmetic)
```

It also checks the non-backtracking recurrence against direct enumeration for every `n ≤ 22`. Watson's value `G = 1.516386` in Glasser and Zucker's Gamma form (1977) and in the Bessel form `∫₀^∞ e^{−t} I₀(t/3)³ dt` is printed as a floating-point cross-check only, and is not part of the certificate.

**Result.** With the certified `G`, `E ≤ 0.193295`, so `P ∈ [0.03999, 0.12902]` and `P ≤ 0.1933` at any depth. `2/3` lies outside by a factor of five, by exact comparison. The route does not close, given the analytic reduction. With Watson's value the same bound reads `E = 0.17759`.

**Scope.** This is a statement about one route, the one limit built from the frozen protocol rules. Since one way suffices, a route that does not close is no evidence against the Koide phase having a way; it only stops this route from being offered again. It says nothing about deeper selections or other limits, and the Lindemann fork in [Weak_Force.md](Weak_Force.md) §5c⁗ item 7 still applies: an exact `Δ = 2/3` must be a limit, and it must be forced. The Koide phase stays open (#140).

## 4. Zipf: the closure inventory's rank-frequency law

[`zipf_closures.py`](zipf_closures.py) ranks every prime (first-return) closure by its frequency, the cylinder weight `(2d)^{−L}`, using exact counts. The law is a **staircase**: every prime closure of one length has the same frequency, so a block of ranks whose size grows like `(2d)^L` shares one value. Two statements hold, and they are different:

```
arbitrary ranks:   f(r) = Θ( 1 / ( r · (ln r)^{d/2} ) )
endpoint ranks:    f(r_L) · r_L · (ln r_L)^{d/2} → C      (r_L = number of primes of length ≤ L)
```

Inside one block `f` is constant while `r` grows by `(2d)²`, so the normalized product varies by about that factor (measured at `L = 40`: 36.2 for `d = 3`, 64.8 for `d = 4`). No single constant holds on all ranks.

At endpoints, the finite-difference slope `Δ ln f / Δ ln r` between successive lengths is `−1.003` at `L = 300` for both `d`, approaching `−1`. The endpoint product is `2.18` (`d = 4`) and `0.69` (`d = 3`) there and still rising slowly, consistent with `O(ln L / L)` corrections; the prime counts behave as `I_L·L²/8^L ≈ 0.52` and `I_L·L^{3/2}/6^L ≈ 0.287`. The `d = 4` total prime mass, `0.1923` through `L = 300`, matches [Closure_Walk.md](Closure_Walk.md)'s `p₄ = 0.1932`.

**What is content (method rule 4).** The exponent `−1` is not. It holds for any inventory whose words of length `L` share one weight and whose number grows like `(2d)^L` times a subexponential factor. That is Miller's random-typing argument (1957), after Mandelbrot (1953), and no distribution over ways would make it false. The correction `(ln r)^{−d/2}` is content: it is the `L^{−d/2}` decay of first returns, so it counts the independent axes and would be different with two axes or five. So Zipf gives the closure inventory a **dimension fingerprint**, not a bridge. A physical frequency table read as closure frequencies would have to show the `(ln r)^{−2}` correction and the equal-frequency blocks, which makes the reading testable. No such table has been identified, so nothing is claimed.

## 5. The other open bridges

Under the possibilist standard each of these needs **one** exhibited way, and its first closure is the one to look for. The ledger's `B-OPEN` records a further, reviewer-facing demand from Paper I §11.2, a conservative return. The two standards are kept apart here, and no ledger status is changed by this note.

- **α scale map.** Self-similarity fixes the octave-to-scale map's form, `Q(R) = Q₀λ^R`, and the bifibration fixes `w = ½` ([Alpha_Residual.md](Alpha_Residual.md) §9b–§9c). The map's two constants are a physical identification, and none of the five tools supplies them. Turbulence was the candidate that could have supplied a per-octave exponent, and §1 records why it did not.
- **Born uniqueness.** `born_from_ways` holds given refinement additivity. What is missing is a dynamics that performs an amplitude-preserving refinement. PR #245 (readout criterion) is the live work, and nothing here bears on it.
- **Gupta clock map.** This is in the clock-domain stack (PRs #237 and #246), which none of the five tools touches.
- **MO2 → detector, map ≡ territory.** §2 reduces the formal side to an apparatus map that respects continuation. That apparatus cannot factor through the joint-closure observable alone: the gauge twist `+` folds to `I`, so the observational record does not return ZFA ([`QLF_TerritoryReturn`](lean/QLF_TerritoryReturn.lean), §6). It must also read the integer ledger. The physical side, what apparatus reads it, stays `B-OPEN`.
- **SPARC.** This needs prospective, blinded replication ([blinded_protocol.md](verification/strange-loop/blinded_protocol.md)), not a new tool.

## 6. The bridge-closure plan (2026-11-21)

Jim asked for one plan merging the ChatGPT and Grok roadmaps, aimed at a first verified continuum
reconstruction. The ground rules were:

- `ħ` is never sent to zero;
- one way suffices, and the first closure is preferred;
- the Python companion comes first, then Lean;
- every step keeps a `B-OPEN` claim record whose `strange_loop` returns a finite invariant;
- kill conditions are committed before the run, and nothing is identified by definition.

Each step below follows those rules and adds no axiom. The census action limit merged in PR #304;
the other six are PR #305.

| Step | Issue | Result | Status | Where |
|---|---|---|---|---|
| Census action limit | #303 S1–S2 | The census cost `I_n(⌊x√n⌋) → x²`, with first variation `→ 2x` and curvature `→ 2`, at fixed `ħ`. Exact sandwich `d²/(n+d) ≤ I ≤ d²/(n−d+1)` | **proved**, S-MATH only (a Euclidean weight, not the physical action) | [`QLF_CensusActionLimit`](lean/QLF_CensusActionLimit.lean), [Stationary_Action.md](Stationary_Action.md) §2a |
| Link closure | #303 §3.2 | The link action sourced by a history is stationary under every link variation only if the history is count-balanced and returns. The converse is checked exactly, not proved | **proved** (one direction) | [`QLF_LinkClosure`](lean/QLF_LinkClosure.lean), [link_closure.py](link_closure.py), [Stationary_Action.md](Stationary_Action.md) §2b |
| Perspective holography | #296 | Reconstruction ⟺ equal records force equal values. The joint fold is the minimal record for joint closure. Two one-body perspectives share only constants | **proved** | [`QLF_PerspectiveHolography`](lean/QLF_PerspectiveHolography.lean), [Holographic.md](Holographic.md) |
| Fluxoid → Regge | #301 milestone 1 | The current labeling gives a geometry finer than the closure class (143 geometries in the closed class). The axis labeling is constant on closure. ZFA is the vertex identity `div = 0`, not a face identity | **rejected** by its kill conditions | [`QLF_FluxoidRegge`](lean/QLF_FluxoidRegge.lean), [Continuum_Limit.md](Continuum_Limit.md), [fluxoid_regge.py](fluxoid_regge.py) |
| Signed phase | #303 S4–S5 | The closure phase is `π(L/2 + Φ)`, Φ the projected area. The stationary-phase bound holds for every U(1) flux, so it cannot identify the action. Only the fold fixes flux `±π`, and that flux has no smooth area-action limit | **S4 candidate proved; S5 open** (Dirac reading) | [`QLF_PhaseAction`](lean/QLF_PhaseAction.lean), [Stationary_Action.md](Stationary_Action.md) §5b–§5c, [signed_phase_track.py](signed_phase_track.py) |
| Territory return | #213 | The observational record (joint closure tests with phase) does not return ZFA: `[(A,+)]` is equivalent to `[]`, and only `[]` closes. The 64 classes are `(K_A, K_B, phase)`. The integer ledger returns ZFA | **observational reading refuted**; map ≡ territory stays `B-OPEN` | [`QLF_TerritoryReturn`](lean/QLF_TerritoryReturn.lean), [Map_Is_Territory.md](Map_Is_Territory.md) §3a–§3b, [territory_return.py](territory_return.py) |
| Spatial response | #287 SR3 | With both ledgers derived from the same steps, the mean growth of the squared separation is `2 − ΔS` (the parallelogram law). Binding steps push apart on average | **hypothesis reversed** for per-event ledgers; selection is untested | [`QLF_SpatialResponseDerived`](lean/QLF_SpatialResponseDerived.lean), [Spatial_Response_Derived.md](Spatial_Response_Derived.md), [spatial_response_derived.py](spatial_response_derived.py) |

**What the plan established.** Three of the seven steps closed what they set out to close (the
census limit, link closure, perspective holography). The other four were decided negatively, and
each one locates its gap precisely:

- a continuum geometry must come from a labeling that is a class function and still varies on
  closure;
- the action must be read from the Dirac phase, not from an area;
- a return to the territory needs an apparatus that reads the integer ledger;
- spatial contraction, if it exists, comes from which events happen, not from the per-event ledger.

Under possibilism none of these failures counts against its bridge. Each records one route that does
not close, together with the first step a route that does would have to take.

The deferred items are being run the same way: #302 C1 ([Conformal_Comparison.md](Conformal_Comparison.md)) and #290 E1 ([Diversity_Novel_Outcome_E1.md](Diversity_Novel_Outcome_E1.md)).

**Claim records** (all `B-OPEN`):
[`stationary_action.json`](claim_records/stationary_action.json),
[`continuum_limit.json`](claim_records/continuum_limit.json),
[`map_is_territory.json`](claim_records/map_is_territory.json) and
[`spatial_response_derived.json`](claim_records/spatial_response_derived.json).

## References

- Alon, N., Benjamini, I., Lubetzky, E., Sodin, S. (2007). Non-backtracking random walks mix faster. *Commun. Contemp. Math.* 9, 585–603.
- Glasser, M. L., Zucker, I. J. (1977). Extended Watson integrals for the cubic lattices. *PNAS* 74, 1800–1801.
- Mandelbrot, B. (1953). An informational theory of the statistical structure of language. In *Communication Theory* (ed. W. Jackson), Butterworths.
- Miller, G. A. (1957). Some effects of intermittent silence. *Am. J. Psychol.* 70, 311–314.
- Milner, R. (1989). *Communication and Concurrency.* Prentice Hall.
- Nerode, A. (1958). Linear automaton transformations. *Proc. AMS* 9, 541–544.
- Park, D. (1981). Concurrency and automata on infinite sequences. *LNCS* 104, 167–183.
- Robbins, H. (1955). A remark on Stirling's formula. *Am. Math. Monthly* 62, 26–29.
- Watson, G. N. (1939). Three triple integrals. *Q. J. Math.* 10, 266–276.
