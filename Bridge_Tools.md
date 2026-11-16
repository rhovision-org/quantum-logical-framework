# Closing bridges with strange loops, fractals, Zipf, bisimulation and turbulence

Part of the [Quantum Logical Framework (QLF)](README.md). Status ledger: [Claim_Status.md](Claim_Status.md); method: [ScientificApproach.md](ScientificApproach.md).

**Question (Jim, 2026-11-16).** Can any of the missing bridges be closed now, perhaps with strange loops, fractals, Zipf's law, bisimulation or turbulence, reasoned possibilistically?

**Short answer.** One bridge requirement is now a theorem, in its possibilist form: **one closure decides**, and the first closure is one that does (§2). One route to the Koide phase is shown not to close, which is a fact about that route only (§3). Zipf's law holds for the closure inventory, but its exponent is bookkeeping, and only its correction carries content (§4). The ledger statuses of the physical bridges (α's scale map, Born, the clock map, the detector map, map ≡ territory) are unchanged, and §5 says what one way would look like for each.

**How "possibilistically" is read (Jim, 2026-11-16).** *Possibilism only requires one way. The first closure is the strongest way.* A bridge exists once one way across it is exhibited; nothing has to be shown about all ways. Among the ways, the first closure has priority, because closure is irrevocable (`closedAtHorizon_mono`). An earlier draft of this note read the word as "bound all the ways at once". That was wrong, and two consequences follow. A route that fails to close (§3) counts for nothing against the bridge it aimed at. And the quantifier over every context in §2 is not needed: one closing context does all the work.

---

## 1. What each tool can and cannot do here

A bridge closes only with a theorem or a decided, pre-registered test ([ScientificApproach.md](ScientificApproach.md)); an analogy closes nothing. With that bar:

| Tool | What it offers QLF | Verdict on the open bridges |
|---|---|---|
| **Bisimulation** | The greatest relation compatible with continuation and an observable is unique, so a bridge's equivalence can be *derived* rather than chosen | **Theorem (§2).** One closing context decides the class, the first closure included. It closes the "why this equivalence" part of Paper I §11.2 on the two-body domain. The physical half of map ≡ territory (that the joint-closure phase is the only observable) stays open, but it is now one statement. |
| **Strange loops** | A level-crossing return to a finite record. QLF already uses it as the review shape of every bridge ([Strange_Loops.md](Strange_Loops.md), `QLF_StrangeLoop`) | No new closure. A loop is closed by a conservative return, and for Born and MO2 the return needs a physical refinement or detector map that no loop supplies. |
| **Return bounds (transience)** | Exact control of how much possibility ever comes back. This is the Pólya property behind `QLF_PolyaTransience` | **Decided a pre-registered test (§3):** the Koide census limit `P` fails, now with a certificate. |
| **Zipf** | Rank-frequency of closures | **Measured (§4).** The exponent `−1` is Miller's random-typing bookkeeping. The `(ln r)^{−d/2}` correction counts axes. It decides no bridge. |
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
- `exists_first_closure`: every history has a first closure, a closing context none of whose proper prefixes closes.
- `first_closure_decides`: the first closure alone tells apart everything that all contexts together could.

So the first closure is the strongest way in a precise sense: no later or longer closure distinguishes two histories that the first one does not. The reason is that a fold is invertible, so a closing context loses nothing. This also removes the quantifier a reviewer would otherwise have to trust. To check that two histories are the same event class, run one closure.

**What this closes.** On the two-body domain the bridge equivalence is no longer a choice. Any bridge that respects continuation and joint-closure outcomes can only use `PairEquiv` or something finer, and `PairEquiv` is the coarsest. A coarser relation would merge histories that some continuation tells apart. This is the Myhill–Nerode right congruence (Nerode 1958) read as a bisimulation, and the step is standard. The QLF-specific content is `obsEquiv_iff_pairEquiv`, which says the greatest bisimulation is the tensor quotient.

**What it does not close.** The theorem takes the joint-closure phase as *the* observable. That this is the only physically available observable is the apparatus half of map ≡ territory ([Map_Is_Territory.md](Map_Is_Territory.md), #213), and it stays `B-OPEN`. Also open are the entangled sector and the `N`-body version. For the self-knowledge target ([self_knowledge_target.md](verification/strange-loop/self_knowledge_target.md)), this supplies obligation 8 (the bisimulation is proved, and the choice of equivalence is stated and shown canonical) for this observable. The embedding, reflection and update obligations are untouched.

## 3. Koide census limit: this one route does not close

[`lepton_phase_series.py`](lepton_phase_series.py) pre-registered a single statistic. `P` is the probability that a non-backtracking walk on `ℤ³` first returns as an electron-like free half-spin closure, under the hypothesis `Δ = P` radians, which is killed if `2/3` lies outside a bracket on `P`. The run estimated `P ≈ 0.041`, but the review on PR #240 showed that the only certified enclosure was `[0.040, 0.944]`, which does not exclude `2/3`. It also named the missing piece, a proved bound on the walk's total return probability. [`lepton_phase_certify.py`](lepton_phase_certify.py) supplies that bound.

**The bound.** Every electron-like first return of length `n` is a walk at the origin at step `n`. So `P ≤ E`, where `E` is the expected number of returns, and `P − S_N ≤ E − U_N`. Non-backtracking counts obey `A_{n+1} = A·A_n − 5A_{n−1}`, which gives `Σ A_n z^n = (1 − z²)/(1 − Az + 5z²)` (standard; Alon, Benjamini, Lubetzky, Sodin 2007). At `z = 1/5` the denominator becomes `(6/5)(1 − D(k))`, which gives

```
E = (2/3)·G − 5/6 = 0.177591,   G = 1.516386…  (Watson's integral, 1939)
```

The script also justifies the interchange of sum and integral. It checks the recurrence against direct enumeration for every `n ≤ 22`, and checks `G` in two independent forms: Glasser and Zucker's Gamma-function product (1977) and the Bessel integral `∫₀^∞ e^{−t} I₀(t/3)³ dt`.

**Result.** `P ∈ [0.03999, 0.11331]`, and `P ≤ 0.1776` at any depth. The verdict is **FAIL (certified)**: `2/3` is outside the bracket by a factor of six. The verdict needs only `G < 9/4`.

**Scope.** This is a statement about one route, the one limit built from the frozen protocol rules. Since one way suffices, a route that does not close is no evidence against the Koide phase having a way; it only stops this route from being offered again. It says nothing about deeper selections or other limits, and the Lindemann fork in [Weak_Force.md](Weak_Force.md) §5c⁗ item 7 still applies: an exact `Δ = 2/3` must be a limit, and it must be forced. The Koide phase stays open (#140).

## 4. Zipf: the closure inventory's rank-frequency law

[`zipf_closures.py`](zipf_closures.py) ranks every prime (first-return) closure by its frequency, the cylinder weight `(2d)^{−L}`, using exact counts. The frequency at rank `r` follows

```
f(r) ~ C / ( r · (ln r)^{d/2} )
```

At `L = 300` the local exponent `d ln f / d ln r` is `−1.020` for `d = 4` and `−1.019` for `d = 3`, still approaching `−1`. The prime counts settle as `I_L·L²/8^L → 0.52` for `d = 4` and `I_L·L^{3/2}/6^L → 0.287` for `d = 3`, with slow `O(ln L / L)` corrections. The `d = 4` total prime mass, `0.1923` through `L = 300`, matches [Closure_Walk.md](Closure_Walk.md)'s `p₄ = 0.1932`.

**What is content (method rule 4).** The exponent `−1` is not. It holds for any inventory whose words of length `L` share one weight and whose number grows like `(2d)^L` times a subexponential factor. That is Miller's random-typing argument (1957), after Mandelbrot (1953), and no distribution over ways would make it false. The correction `(ln r)^{−d/2}` is content: it is the `L^{−d/2}` decay of first returns, so it counts the independent axes and would be different with two axes or five. So Zipf gives the closure inventory a **dimension fingerprint**, not a bridge. A physical frequency table read as closure frequencies would have to show the `(ln r)^{−2}` correction, which makes the reading testable. No such table has been identified, so nothing is claimed.

## 5. The other open bridges

Under the possibilist standard each of these needs **one** exhibited way, and its first closure is the one to look for. The ledger's `B-OPEN` records a further, reviewer-facing demand from Paper I §11.2, a conservative return. The two standards are kept apart here, and no ledger status is changed by this note.

- **α scale map.** Self-similarity fixes the octave-to-scale map's form, `Q(R) = Q₀λ^R`, and the bifibration fixes `w = ½` ([Alpha_Residual.md](Alpha_Residual.md) §9b–§9c). The map's two constants are a physical identification, and none of the five tools supplies them. Turbulence was the candidate that could have supplied a per-octave exponent, and §1 records why it did not.
- **Born uniqueness.** `born_from_ways` holds given refinement additivity. What is missing is a dynamics that performs an amplitude-preserving refinement. PR #245 (readout criterion) is the live work, and nothing here bears on it.
- **Gupta clock map.** This is in the clock-domain stack (PRs #237 and #246), which none of the five tools touches.
- **MO2 → detector, map ≡ territory.** §2 reduces the formal side to one statement: an apparatus map that factors through the joint-closure observable and respects continuation. The physical side is that statement, and it stays `B-OPEN`.
- **SPARC.** This needs prospective, blinded replication ([blinded_protocol.md](verification/strange-loop/blinded_protocol.md)), not a new tool.

## References

- Alon, N., Benjamini, I., Lubetzky, E., Sodin, S. (2007). Non-backtracking random walks mix faster. *Commun. Contemp. Math.* 9, 585–603.
- Glasser, M. L., Zucker, I. J. (1977). Extended Watson integrals for the cubic lattices. *PNAS* 74, 1800–1801.
- Mandelbrot, B. (1953). An informational theory of the statistical structure of language. In *Communication Theory* (ed. W. Jackson), Butterworths.
- Miller, G. A. (1957). Some effects of intermittent silence. *Am. J. Psychol.* 70, 311–314.
- Milner, R. (1989). *Communication and Concurrency.* Prentice Hall.
- Nerode, A. (1958). Linear automaton transformations. *Proc. AMS* 9, 541–544.
- Park, D. (1981). Concurrency and automata on infinite sequences. *LNCS* 104, 167–183.
- Watson, G. N. (1939). Three triple integrals. *Q. J. Math.* 10, 266–276.
