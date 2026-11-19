# Closure Uncertainty — a finite kernel for first-completion counts

**Status:** pre-registration plus a finite reference implementation. The Lean gate is open; this is
a **draft** program, not a completed theorem layer. Tracking issue:
[#269](https://github.com/rhovision-org/quantum-logical-framework/issues/269).

**Layers.** This is the uncertainty kernel. The static assembly index is
[`Assembly_Index_QLF.md`](Assembly_Index_QLF.md) (#264 / PR #265); the tensor-sector index is #266;
the transport screen is [PR #268](https://github.com/rhovision-org/quantum-logical-framework/pull/268)
(#267, negative). This kernel does not cross into either sector silently.

---

## 0. The one-sentence program

> **Possibility creates uncertainty; entanglement creates joint closure; closure resolves
> uncertainty locally and creates a reusable object; reuse enlarges the next assembly space;
> enclosing closures constrain that space from above.**

The scientific discipline is the gate table in §3. Some arrows are existing theorems; some are
bridges; some are open. Shared vocabulary is not evidence of a shared mechanism.

---

## 1. Frozen definitions

A **finite closure system** is a tuple

```
(S, step, closed, context)
```

where:

- `S` is a finite type of states (histories, game profiles, charge configurations, …);
- `step : S → Finset S` is the one-event transition relation;
- `closed : S → Prop` is a decidable closure predicate;
- `context : S → Prop` is a decidable admissibility predicate (the blanket/niche).

For a start state `h`, horizon `R`, and context `B`:

- a **path** is a finite sequence `h = s₀ → s₁ → … → sₖ` with `step sᵢ sᵢ₊₁` and every `sᵢ` in
  `B`;
- a path is a **first completion** if `k ≤ R`, `closed sₖ`, and no earlier `sᵢ` (`i < k`) is
  closed;
- `Ω_R(h | B)` is the **set of first-completion paths**;
- `W_R(h | B) = |Ω_R(h | B)|` is an integer;
- `U_R(h | B) = log₂ W_R(h | B)` is derived, never primitive.

**First-completion rule.** If `h` is already closed, the empty path is its unique first completion,
so `W = 1` and `U = 0`. This prevents counting arbitrarily many appended closed decorations as new
resolutions. If `Ω_R` is empty, `U` is **undefined**, not infinite; the state is simply not
completable within the horizon.

**Why integer first.** `W` is finitary and computable on finite systems. `U` is defined afterward
only where `W > 0`. Lean does not need to begin with real logarithms.

---

## 2. What is being counted

`W` is a count of **completion histories**, not a probability. Turning it into a probability
requires a measure; the caution in [`MostWays_First.md`](MostWays_First.md) applies here:
multiplicity alone does not determine frequency. `U` is an information *capacity* of the
first-completion space under a declared measure, not a physical entropy.

The count is context-dependent by construction. A tighter context gives a subset of paths and
therefore cannot increase `W`. The closure predicate itself is not changed by the context; only the
admissible paths are. That is the formal version of “the observer conditions access, not the
closure rule.”

### 2a. Measure gate (U5)

`W_R` is a raw path count. A physical probability requires a declared measure `μ` on completion
histories. The natural QLF candidate is the cylinder/Kraft weight

```
μ(c) = 8^(-|c|)
P(c | h, B) = μ(c) / Σ_{c' ∈ Ω_R(h|B)} μ(c').
```

The count and the probability answer different questions:

- `W_R = |Ω_R|` is the number of alternatives;
- `P` is the normalized weight of those alternatives;
- `U_R = log₂ W_R` is count-information, not physical entropy.

No motion, affect, or cosmology use of `U`/`W` is allowed until the measure is declared. The
reference implementation computes the cylinder weights for the flat-ZFA completions and checks that
they normalize to one.

---

## 3. Gates

| gate | requirement | status |
|---|---|---|
| **U0** | state space, step, closure, context, horizon, and first-completion rule frozen before applications | **done** in this document |
| **U1** | finiteness; tighter context ⇒ subset and `W' ≤ W`; unique completion ⇒ `U = 0`; context changes `Ω` not `closed`; joint closure can resolve what neither component resolves alone | **finite Python checks** in `closure_uncertainty.py`; **Lean open** |
| **U2** | flat-history statements never cross silently into tensor independence | **done**: this document is flat-sector only; #266 controls the boundary |
| **U3** | closed/isolated component is reusable | **cited**: `isolated_iff_closed`, `closed_insertion_is_phase`; formal reuse lemma open |
| **U4** | at least two nontrivial domains instantiate the kernel without changing its definitions | **pass (two exact)**: game theory and flat-history ZFA (`countBalanced`); confinement is a charge toy plus theorem citations, full colour enumeration open |
| **U5** | raw `W` is separated from a declared measure before physical use | **defined**: cylinder/Kraft `μ(c)=8^(-|c|)`, normalized `P`; finite check in `closure_uncertainty.py` |

The PR remains draft until U1 is Lean-checked. U4 now has two exact instantiations; the confinement
row is a partial extra, not one of the two required domains. U5 is a prerequisite for using `W`/`U`
in motion, affect, or cosmology; it is not a claim that the cylinder weight is the final physical
measure.

---

## 4. Instantiation 1 — game theory (exact)

A finite normal-form game provides:

- `S` = action profiles;
- `step` = one player's unilateral move to another action;
- `closed` = Nash equilibrium;
- `context` = the game's admissible profiles.

This is a direct instantiation because QLF already proves

```
nash_iff_closure : IsNash game profile ↔ IsClosure game profile
```

in `QLF_PotentialGames` / `QLF_NPlayerPotential`. The kernel does not redefine Nash; it only counts
first-completion paths to it. The reference implementation uses a 2×2 Stag Hunt and reports `W_R`
for each start profile and horizon.

The game-theory gate is **formal, not empirical**: it shows the kernel can host an existing QLF
closure predicate, not that players literally compute `Ω_R`.

---

## 5. Instantiation 2 — flat-history ZFA (exact)

The second exact instantiation uses the real QLF closure predicate:

- states = all twist words up to length 4 (4,681 states);
- `step` = append one twist (until the length bound);
- `closed` = `countBalanced` / `is_closed` from `assembly_index.py` (177 closed words);
- `context` = all states;
- start = the single twist `^`.

From `^`, the first-completion counts are

| `R` | 0 | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|---:|
| `W_R` | 0 | 1 | 1 | 14 | 14 |

The first completion is the unique conjugate pair `^v` at path length 1. Beyond that, first
completions can only occur at odd path lengths (the start has length 1 and closures have even
length), so `R = 4` adds nothing over `R = 3`. The 14 length-3 paths are the first-return histories
that avoid the length-1 closure. This is an exact enumeration of the flat QLF closure predicate, not
a toy.

---

## 6. Instantiation 3 — confinement (partial)

The confinement reading is:

- an open quark is `quark_not_closed` / `charged_not_closed`;
- only colour singlets close (`singlet_closure`);
- a lone quark therefore has no independently reusable assembly node; a hadron does.

The reference implementation includes a **U(1) charge toy**: states are net charge counts, `step`
adds a charge or anticharge, `closed` is net zero, and `context` is the confinement band. It
reports the first-completion count from a lone charge. This is an illustration of the counting
kernel, **not** the full SU(3)/Borromean colour theory. A full colour enumeration is an open extra,
not one of the two exact domains that satisfy U4.

---

## 7. Instantiation 4 — flat shared closure (illustration)

The flat-sector witness `^ | v` is jointly count-balanced while neither half is scalar
(`shared_closure_not_factorizable`). In the kernel, a joint completion can exist where each
component alone has no completion. The reference implementation includes a small shared-completion
system to check the joint-closure gate; it is an illustration, not a new theorem.

---

## 8. Non-goals

- No claim that `U` is thermodynamic entropy, physical randomness, or a measure of qualia.
- No claim that a domain with the same vocabulary shares a mechanism; see gate U4.
- No tensor-sector statement; #266 is separate.
- No empirical or chemical claim.
- No “consciousness = uncertainty” claim. Feelings, if pursued, are a separate affect hypothesis
  with measurable timescales, not a consequence of this kernel.

---

## 9. Reproduce

```bash
python3 closure_uncertainty.py --self-test
python3 closure_uncertainty.py --run
python3 -m unittest tests.test_closure_uncertainty -v
```

The run writes `data/closure_uncertainty_census.json`. The kernel definitions are frozen at the
commit that adds this file; later changes require a new pre-registration.
