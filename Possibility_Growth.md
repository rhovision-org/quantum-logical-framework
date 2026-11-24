# Possibility growth and blind search in [Quantum Logical Framework (QLF)](README.md)

> **Summary.** The number of possible histories grows exponentially with depth, and so does the
> number of closures among them. From that, one thing follows as a theorem: **exact blind search
> pays for every candidate, and any smaller budget gives an approximate answer.** It is proved
> in [`lean/QLF_PossibilityGrowth.lean`](lean/QLF_PossibilityGrowth.lean) with no axiom. It is a
> black-box (query) bound, so it does not settle P vs NP, and the growth of the count alone
> makes nothing hard. §5 sets out how far "the possibilities are real" can be argued, and labels
> what is interpretation.

Places on the [Theory of Everything index](Theory_Of_Everything.md) as a boundary (§6), beside
the [Millennium reformulations](Millennium.md). It rests on the possibilist a priori solution
([Philosophy.md](Philosophy.md) §3a).

## 1. What QLF already says about P vs NP

[P_vs_NP_QLF.md](P_vs_NP_QLF.md) and [`lean/QLF_PvsNP.lean`](lean/QLF_PvsNP.lean) hold the
reformulation. The **classical** P vs NP question is not settled here. Proved: the realized set is
the linear-time verify-filter of the generated candidates (`realized_is_verify_filter`) and has
exactly `C(2n,n)` members (`realized_count_eq_central_binomial`). The separation itself is the one
bridge axiom `qlf_cost_model`, and its strength has been measured: `costModel_nonempty` satisfies
it with a toy model containing no running times, so in Lean it constrains nothing about polynomial
time. That document also records the guard this one keeps: producing *a* closure is an `O(n)`
loop, so the size of the space is not evidence of hardness. Everything rests on the qualifier
"a closure **with property `X`**".

## 2. The VP ≠ VNP announcement

Anthropic posted a Claude-authored paper and Lean formalization claiming **VP ≠ VNP** on
2026-11-23 ([CASRAI](https://casrai.org/news/anthropic-claude-authored-vp-vnp-proof-unverified-lean-2026),
[XenoSpectrum](https://xenospectrum.com/en/anthropic-claude-vp-vnp-proof/),
[OfficeChai](https://officechai.com/ai/claude-vp-vnp-proof-valiant-conjecture-p-vs-np/)). As
reported: a lower bound of `m^{c·(log m)^{1/3}}` gates for arithmetic circuits computing the
`m × m` permanent in characteristic ≠ 2 (characteristic 2 is excluded because there the permanent
*is* the determinant), the Hamiltonian-cycle polynomial for every field, about 73,000 lines of
Lean 4 with Mathlib on the standard axioms only. Hours later OpenAI posted its own claimed proof
of VP ≠ VNP ([FourWeekMBA](https://fourweekmba.com/ai-openai-posts-its-own-vp-vnp-proof-5-hours-after-anthropic/),
[OfficeChai](https://officechai.com/ai/openai-vp-vnp-proof-hours-after-anthropic-claude/)). As of
2026-11-24 **no human mathematician has checked either claim**, and the reports agree that neither
settles P vs NP.

Valiant's question (1979) is the algebraic analogue: the determinant (signed sum over
permutations) has polynomial-size circuits; is the permanent (the same sum without the signs)
exponentially harder? The known transfer goes from the Boolean side to the algebraic side:
Bürgisser (2000) showed, assuming the generalized Riemann hypothesis, that the non-uniform Boolean
separation `NP ⊄ P/poly` implies VP ≠ VNP. So VP ≠ VNP, if it holds, is the weaker statement and
does not imply P ≠ NP.

**Where it touches closure counting.** QLF has both kinds of sum. The unsigned census counts the
ways a history closes (`walkCount`), and the signed census weights each way by its phase, whose
rule `(−1)^{#neg}·sign(axis permutation)` (`QLF_PhaseRule`) carries a permutation sign, as the
determinant does. But both QLF censuses are **easy**. `walkCount L` is a closed form with `L + 1`
terms ([`QLF_PolyaTransience`](lean/QLF_PolyaTransience.lean)), and the signed census is a
transfer-matrix sum over the edge-sign connection ([`QLF_EdgeSign`](lean/QLF_EdgeSign.lean)). Their
fixed alphabet and product structure make them easy, as for the determinant. The permanent's
hardness lives in sums with unstructured weights, and the census acquires such weights only when a
global constraint is added. Self-avoidance is the example in this repo: the
[protein census](Protein_Folding.md) counts self-avoiding walks, for which no polynomial-time
counting algorithm is known. So the honest connection is a contrast, not a derivation: **counting
closures is easy; counting or finding closures under an unstructured constraint is where hardness
can enter.** Nothing in QLF bears on whether the VP ≠ VNP proof is correct.

## 3. What is proved

All in [`lean/QLF_PossibilityGrowth.lean`](lean/QLF_PossibilityGrowth.lean), no axiom.

| Theorem | Statement |
|---|---|
| `possibilities_card` | `8^L` twist histories of length `L` |
| `closures_card` | the closures (count-balanced, hence Pauli-closed) number `walkCount L` |
| `closures_exponential` | `16^n ≤ (2n+1)² · #closures(2n)` (a deliberately weak bound, see below) |
| `realized_exponential` | one axis: `4^n ≤ (2n+1) · C(2n,n)` |
| `DTree.agree` | a query run sees only the candidates it queries |
| `DTree.search_must_query_all` | a decision tree that answers "does some candidate have property `X`?" correctly for **every** `X` queries every candidate on the empty instance |
| `DTree.bounded_search_detects_few` | a tree that says "no" on the empty instance detects at most as many single-witness instances as it queries |
| `DTree.bounded_search_misses` | with budget `k` it is wrong on at least `N − k` of the `N` single-witness instances |
| `closure_search_lower_bound` | exact blind search over the length-`2n` closures needs `≥ 16^n/(2n+1)²` queries |
| `closure_search_detects_few` | a budget of `k` queries detects at most `k` of the `walkCount(2n)` single-witness instances |

`closures_exponential` keeps only the one term of `walkCount(2n)` in which every step lies on one
plane, which contributes `C(2n,n)²`. Both the base `16` and the factor `(2n+1)²` come from that
choice, not from the count. The full count is much larger: [Closure_Walk.md](Closure_Walk.md)
gives `W_L = (8/π²)·8^L/L²·(1 + O(1/L))`, about `(2/π²)·64^n/n²` at `L = 2n`, computed exactly to
`L = 1000` but not proved in Lean. The weak bound is enough here, because any exponential lower
bound on the candidates gives an exponential query bound.

The decision tree is the general deterministic procedure that sees the property only through
queries "does candidate `a` have it?". The proof is the adversary argument: an unqueried
candidate cannot be told apart from the empty instance (`unqueried_invisible`).

This is the exact form of the claim "possibilities explode with depth, so only approximations can
be given": for **blind** search, an exact answer costs the whole exponential set, and a polynomial
budget succeeds on a vanishing fraction `k/N` of the single-witness instances.

## 4. What it does not prove

- **It does not settle P vs NP.** The bound is relativized: `X` is an oracle. Baker, Gill and
  Solovay (1975) built oracles relative to which P = NP, so no argument of this kind can separate
  P from NP. A polynomial algorithm for a concrete `X` reads its structure; it does not query
  blindly. `qlf_cost_model` is untouched.
- **Growth alone makes nothing hard.** Producing *a* closure is linear, and counting them is a
  closed form. The hardness lives entirely in an arbitrary `X`.
- **Deterministic and classical.** Randomized classical search also needs `Ω(N)` queries (not
  formalized here). Quantum search needs `Θ(√N)`: Grover's algorithm achieves it and Bennett,
  Bernstein, Brassard and Vazirani (1997) proved it optimal. Over closures `√N` is still
  exponential (`≥ 4^n/(2n+1)`), so the conclusion "exact blind search is exponential" survives
  quantum mechanics, with the exponent halved.
- **"Approximate" here means "correct on a fraction of instances".** It is not a statement about
  approximation algorithms for optimization (PCP, inapproximability), which concern structured
  problems.

## 5. Are the possibilities real?

The repository keeps three layers apart ([CLAUDE.md](CLAUDE.md) review note 8;
[Unreasonable_Classical_Mathematics.md](Unreasonable_Classical_Mathematics.md) §8): what follows
from possibilism, the possibilist premise itself, and a stance. The question belongs to the second
and third, and only part of it can be argued.

**What the theorems above do not show.** The query bound holds in every model in which the
candidates form a finite set, whether or not anyone calls them real. By the method's rule 4 (a
claim earns physical content only when it changes a count of ways,
[CLAUDE.md](CLAUDE.md) "ZFA first, then every way"), it is therefore **not** evidence for
possibilism. Stating otherwise would be the trap [P_vs_NP_QLF.md](P_vs_NP_QLF.md) §3 already names.

**What can be argued: unrealized alternatives have measurable effects.** Three standard results
make the count of ways that did *not* happen show up in what is measured.

1. **Entropy is a count of possibilities.** Boltzmann's `S = k log W` counts microstates the
   system is not in, and the measured heat capacity of a gas depends on that count.
2. **Interference.** The probability of an outcome depends on the paths that were not taken, with
   their signs. In QLF this is the signed census: phases of alternative closures cancel or add
   ([Born_Rule.md](Born_Rule.md)).
3. **Interaction-free measurement.** In the Elitzur–Vaidman bomb test (1993) the mere possibility
   of an absorption changes the detection frequencies.

In each case the alternatives are causally efficacious in the only sense physics checks: changing
their number changes a frequency. That is the precise content QLF can give "possibilities are
real": **real in the sense that their multiplicity enters observed frequencies**, which is the
census reading "a closure's frequency is its multiplicity". Whether they are real beyond that, as
worlds in Lewis's sense, no experiment separates from the instrumentalist reading that they are
bookkeeping. That further step is the possibilist premise, a founding commitment, and should be
labelled as one.

**A consequence that could fail.** If every possibility is real and nature "runs" them all, could
a physical process act as an oracle for an arbitrary `X`? QLF says no, for a structural reason: what
the substrate selects is the **first closure** ("possibilism only requires one way; the first
closure is the strongest way", and `/solve` in [QucalcSearch.md](QucalcSearch.md)), a fixed criterion
that does not depend on `X`. So the possibilist reading predicts that no physical device solves
NP-complete problems in polynomial time, and that quantum devices gain at most the `√N` above on
unstructured search. A scalable physical NP-solver would falsify it. This is the "NP-hardness
assumption" Aaronson (2005) proposed as a physical principle. It is a real prediction, but standard
quantum mechanics plus the usual complexity conjectures make the same one, so it does not
distinguish possibilism from its rivals.

## 6. Open

- **A structured lower bound.** Anything beyond the oracle setting must say what `X` is. The
  natural QLF candidate is a constraint that destroys the census's product structure, such as
  self-avoidance. Whether counting self-avoiding closures is `#P`-hard is open in the literature as
  well.
- **Randomized and quantum query bounds** in Lean: the randomized `Ω(N)` is a short averaging
  argument over the adversary; BBBV needs a Hilbert-space model the repo does not yet carry.
- **VP ≠ VNP.** Await independent checking of either claimed proof before citing it as established.

## References

- T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP question*, SIAM J. Comput. **4** (1975) 431–442.
- L. G. Valiant, *Completeness classes in algebra*, Proc. 11th ACM STOC (1979) 249–261.
- P. Bürgisser, *Cook's versus Valiant's hypothesis*, Theoret. Comput. Sci. **235** (2000) 71–88.
- L. K. Grover, *A fast quantum mechanical algorithm for database search*, Proc. 28th ACM STOC (1996) 212–219.
- C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani, *Strengths and weaknesses of quantum computing*, SIAM J. Comput. **26** (1997) 1510–1523.
- A. C. Elitzur, L. Vaidman, *Quantum mechanical interaction-free measurements*, Found. Phys. **23** (1993) 987–997.
- S. Aaronson, *NP-complete problems and physical reality*, SIGACT News **36** (2005) 30–52.
- D. Lewis, *On the Plurality of Worlds*, Blackwell (1986).
