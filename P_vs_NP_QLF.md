# P vs NP in [QLF](README.md)

> **The engine (path integral · all closures · Witten 1988).** This attack is the *most literal* instance of
> QLF's one Millennium move — *generate every possibility, then select the invariant* — the exact/constructive
> form of the Feynman path integral (all paths happen; stationary phase selects) and of Witten's 1988
> Jones-polynomial path integral (a physics sum-over-everything that proved rigorous mathematics, discharged
> by Reshetikhin–Turaev). **Generate:** the `4ⁿ` candidate histories (`generated_count`). **Select:** the O(n)
> verify-filter = `C(2n,n)` closing ones (`realized_is_verify_filter`) — generate-cheap, check-cheap, the
> firebreak ([`QLF_Firebreak`](lean/QLF_Firebreak.lean)). **Bridge (Class A):** `qlf_cost_model`
> — the complexity separation itself. See [Millennium.md](Millennium.md) § *The engine*.

> **Status: `p_vs_np_proof_in_progress` — a reformulation.** *Contrast (once):* the **classical** P
> vs NP question is not settled here. *What is proven (the reformulation):* the generate/verify
> asymmetry on real theorems — the realized set *is* the O(n) verify-filter of the candidates, with
> size `C(2n,n)` ([`lean/QLF_PvsNP.lean`](lean/QLF_PvsNP.lean)). *The gap:* the formal complexity
> separation is the one bridge axiom `qlf_cost_model`, over an abstract cost model
> (QLF has no machine model). P vs NP is a *finitary* statement about computation, **not** a known
> independence phenomenon — so "ZFC's defect" does not apply (that is for halting / Busy Beaver). So:
> contrast (classical, not settled) → the proven asymmetry → the named bridge. See
> [Open_Problems.md](Open_Problems.md), [Continuum_Choice_Fallacy.md](Continuum_Choice_Fallacy.md).

## 1. The classical problem

The most famous Millennium Prize Problem: is **P = NP**? Is every problem whose
solution can be *verified* quickly (NP) also *solvable* quickly (P)? Equivalently,
is search no harder than checking? The expected answer is **P ≠ NP** — that finding
a needle is fundamentally harder than recognising one — but no proof is known, and
the difficulty is that lower bounds on computation are notoriously hard to establish.

## 2. The QLF substrate already separates the two operations

QLF's engine is literally a *generate-then-verify* machine, and the two halves have
visibly different cost:

- **Generate (search).** The QuCalc expansion enumerates the possibility space of
  phase-string histories. At depth `2n` the branching is exponential: there are
  `4^n` length-`2n` twist strings before any filtering. This is the modal-realist
  space — *all* logically admissible histories exist a priori
  ([Philosophy.md](Philosophy.md)); finding the physical ones is a search through an
  exponentially large tree.
- **Verify (check).** ZFA closure is a **linear-time** predicate: walk the string
  once and check `count_pos = count_neg` (and Pauli closure, which
  `count_balanced_pauli_closed` shows is entailed). `qlf_universality`
  ([`lean/QLF_Universality.lean`](lean/QLF_Universality.lean)) is the statement that
  this O(n) closure check is exactly what selects the physical (terminating)
  computations from the full ruliad. Verification is cheap; generation is not.

So in QLF the **P/NP boundary is the boundary between the ZFA *filter* and the QuCalc
*generator*.** Verification = "is this history a ZFA closure?" (P). Search =
"produce a ZFA closure with property X" (NP). They are different objects in the
framework, not two views of one.

## 3. The structural reading: why the asymmetry should be irreducible

QLF's selection principle gives a reason the asymmetry does not collapse:

- **Closure is global; it cannot be assembled greedily.** A ZFA closure is balanced
  *as a whole* (and Pauli-closed in *order*); a prefix of a closure is generally not
  a closure (the half-spin pruning `full_zeno_prune` discards unclosed fractions).
  There is no local certificate that a partial history can be *extended* to a
  closure with a target property — which is precisely the obstruction to turning
  fast verification into fast search.
- **Of the exponentially many depth-`2n` histories, exactly `C(2n,n)` are ZFA-balanced**
  (`find_stable_states_length_even`, [`lean/QLF_QuCalc.lean`](lean/QLF_QuCalc.lean)) —
  a `~4^n/√n` fraction. **This count is *not* evidence for hardness, and must not be
  cited as such** ([Millennium.md](Millennium.md) § *The competing-route trap*):
  producing *a* ZFA closure of length `2n` is an `O(n)` loop — emit `^` `n` times, then
  `v` `n` times — so the unqualified search problem is in **P**, and `C(2n,n)` counts
  *solutions*, a density that makes random sampling **easier**, not harder. The entire
  asymmetry therefore rests on the qualifier: search is "produce a closure **with
  property `X`**", and `X` carries the whole burden. Stating that plainly is what keeps
  the reformulation honest — a large haystack is not a hard needle.
- This is the same wall as the **Busy-Beaver / ZFC ultraviolet catastrophe**
  ([Active_Inference_Mathematics.md](Active_Inference_Mathematics.md) §6,
  [ReverseMathematics.md](ReverseMathematics.md)): QLF lives at the **RCA₀** floor,
  below the uncomputable. Within that floor, the cost of *constructing* a witness is
  not bounded by the cost of *recognising* one — the generator and the filter are
  genuinely separate machines.

QLF therefore *leans* P ≠ NP — but on the **no-extension-certificate** point above, not
on the size of the space: constrained search through the possibility space exhibits no
mechanism reducing it to the linear closure check. The lean is exactly as strong as that
absence, and no stronger.

## 4. Where the boundary sits

A *structural* asymmetry is not a *complexity-theoretic lower bound*. Turning
"closure is global and has no greedy certificate" into "no polynomial-time algorithm
decides SAT" is the genuinely hard analytic/combinatorial step — the same kind of
RCA₀ → higher-strength crossing QLF marks elsewhere with an explicit axiom. QLF makes
the generate/verify gap concrete and gives a substrate reason it should not close; the
formal separation P ≠ NP is the remaining step, over an infinite computational model —
the sector where ZFC is *itself proven to fail* (Gödel/Turing/Busy Beaver). It is ZFC's
defect, not a gap in this reading.

This is Lean-anchored in [`lean/QLF_PvsNP.lean`](lean/QLF_PvsNP.lean): the two halves
that *are* QLF facts are proven by reusing verified theorems — the realized set IS the
O(n) verify-filter of the generated candidates (`realized_is_verify_filter`, definitional)
and its cardinality is the genuine `C(2n,n)` (`realized_count_eq_central_binomial`, reusing
`find_stable_states_length_even`) — while the separation itself is the single explicit
boundary axiom `qlf_cost_model` over an abstract `PTime`/`search` cost
model, with the `p_vs_np_proof_in_progress` status marker.

## 4a. Blind search, proved

[`lean/QLF_PossibilityGrowth.lean`](lean/QLF_PossibilityGrowth.lean) proves the part of the lean
that can be proved without a machine model, with no axiom: the closures grow exponentially
(`16^n ≤ (2n+1)²·#closures(2n)`), and any deterministic procedure that sees a property `X` only by
querying candidates must query all of them to decide exactly whether some closure has `X`
(`closure_search_lower_bound`); a budget of `k` queries detects at most `k` single-witness
instances. This is a relativized bound, so by Baker–Gill–Solovay it cannot settle P vs NP, and
`qlf_cost_model` is unchanged. See [Possibility_Growth.md](Possibility_Growth.md), which also covers
the VP ≠ VNP announcement and the scope of "possibilities are real".

## 5. Epistemic stance

Within QLF's frame, P ≠ NP is the computational face of the same principle as the
ZFC ultraviolet catastrophe: **possibility is cheap to enumerate and cheap to check,
but expensive to *select*.** The universe is the ZFA-closed subset of an exponential
possibility space, and there is no free lunch that hands you the closure you want
without searching for it. The circuit lower bound is the remaining step, carried by the one
bridge axiom `qlf_cost_model` over an abstract cost model.

**How much that axiom assumes, measured.** `costModel_nonempty` constructs a satisfying cost
model out of `verify` and boolean negation: read `PTime f` as "`f` agrees with `verify`
somewhere" and `search` as pointwise `!`, and verification is polynomial because `verify`
agrees with itself, while the separation holds because `!b ≠ b`. Nothing about running times,
machine models or `C(2n,n)` is needed. So the axiom **constrains nothing about polynomial
time** — it is satisfiable by construction, and exhibiting a model is no evidence at all. Its
whole force is the claim that the *intended* cost model, real polynomial time and real search,
is an instance; that claim is P ≠ NP. This is the same shape as the BSD interface and the
opposite of `QLF_LatticeCalculus`, where a *nondegenerate* instance genuinely discharged
"suppose such a calculus exists". Two smaller findings: `verify_is_ptime` is consumed by
nothing, and `p_vs_np_in_qlf` is the boundary restated verbatim, which the `#print axioms`
footprint confirms. None of it touches the proven core — the verify-filter identity and the
`C(2n,n)` count stand independent of the boundary.

**P vs NP is a
*finitary* statement about computation — not a known independence phenomenon — so the "ZFC's
defect" framing (which belongs to genuine uncomputability: halting, Busy Beaver) does *not*
apply here.** The honest reading: the substrate-constructive generate/verify asymmetry is
proven; the formal separation is the named open bridge — genuine progress, not a finished
classical proof.

## References

- S. A. Cook, *The complexity of theorem-proving procedures*, Proc. 3rd ACM STOC (1971) 151–158 — NP-completeness.
- L. A. Levin, *Universal sequential search problems*, Probl. Peredachi Inf. **9** (1973) — independent formulation.
- R. M. Karp, *Reducibility among combinatorial problems*, in *Complexity of Computer Computations* (1972) 85–103.
- S. Cook, *The P versus NP Problem* — Clay Mathematics Institute (official problem description). <https://www.claymath.org/millennium-problems/>
