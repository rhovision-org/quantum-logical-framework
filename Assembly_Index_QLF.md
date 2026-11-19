# Assembly Index of ZFA Histories

**Status:** definitions frozen; exhaustive computation through length 10; Lean formalization
open; no chemistry or selection claim. Companion code: [`assembly_index.py`](assembly_index.py).
Census summary: [`data/assembly_index_census.json`](data/assembly_index_census.json).
Tracking issue: [#264](https://github.com/rhovision-org/quantum-logical-framework/issues/264).

---

## 0. The short version

An earlier 30-history simulation scored words with

$$
\text{“unique twist types”} + \text{“effective joins”} - \text{“reuse credit”}.
$$

That is **not** the Assembly-Theory assembly index. The assembly index is the *minimum number of
joining operations* needed to construct an object from elementary objects, with previously
constructed subobjects available for reuse
([Sharma et al. 2023](https://doi.org/10.1038/s41586-023-06600-9)). In the eight-twist alphabet,
with single twists as primitives and concatenation as the join, the correct small values are:

| word | joins | why |
|---|---|---|
| `<>` | **1** | one join of the primitives `<` and `>` |
| `^v^v` | **2** | build `^v`, then join it with a copy of itself |
| `^^^^` | **2** | build `^^`, then join it with a copy of itself |
| `^^^^vvvv` | **5** | build `^^` and `vv`, double each, then join |

This document freezes the definition, implements an exact solver, and runs an exhaustive census of
**every count-balanced word through length 10**: 8,134,424 histories, represented by 39,368
symmetry classes. It then asks the only question that matters for the QLF variant:

> If only closed (count-balanced) intermediate objects may be freely reused, does the resulting
> index say anything beyond ordinary assembly, word length, and generic compression?

On this census the answer is **yes, but modestly**: the closure constraint changes 574,592 words
(7.06%) and leaves 0.164 bits of conditional entropy beyond `(length, ordinary index, LZ78)`
(0.159 bits when zlib is also conditioned on). That is a real signal, not a derivation of chemistry
or selection.

---

## 1. Frozen object semantics

The freedom in an assembly index is in what counts as an object, a primitive, and a join. Those
choices are fixed here **before** looking at any chemical data, and they are not changed after
seeing results.

1. **Objects are raw words** over the eight twists `^ v < > / \ + -`. No quotient by global Pauli
   phase, no quotient by `ClosureEquiv`, no relabeling of twists.
2. **Primitives are the eight one-letter words.** A primitive costs zero joins.
3. **A join concatenates two available objects**: `(u, v) -> u + v`. The result is a new object;
   the two operands remain available (ordinary AT) or remain available according to the closure
   rule below.
4. **A construction is a straight-line program (SLP)**: a finite set of objects, each either
   primitive or the concatenation of two earlier objects, containing the target. The **cost** is
   the number of distinct non-primitive objects built.

The last point is the exact meaning of “reuse”: if a subobject is built once, every later join may
use it without paying again. The assembly index is the minimum cost over all constructions.

### 1.1 Ordinary assembly index

$$
a(x) = \min\{\text{joins needed to build } x \text{ with unlimited reuse}\}.
$$

This is the minimum number of nonterminals in an SLP for `x`. It is the standard Assembly-Theory
index specialized to words.

### 1.2 Closure-constrained assembly index

QLF supplies a distinguished class of intermediate objects: the **closed** ones, where
`countBalanced` holds, i.e. every conjugate pair `^/v`, `</>`, `/\`, `+/-` occurs equally often.
The QLF variant is:

> **Only count-balanced intermediate objects may be freely reused.** A non-closed object may be
> built and used, but it has **fan-out one**: it is consumed by the single join that uses it.

Equivalently, in the construction DAG, a node with out-degree greater than one must be closed.
The resulting minimum cost is `a_ZFA(x)`. Every QLF-valid construction is an ordinary construction,
so

$$
a(x) \le a_{\mathrm{ZFA}}(x) \le |x| - 1.
$$

The upper bound is the naive left-to-right assembly, which is always QLF-valid: each prefix is
used once, and a prefix that happens to be closed is merely reusable, not required to be reused.

### 1.3 Why raw words, not closure classes

`a(x)` is invariant under arbitrary relabeling of the eight symbols; it depends only on the
*equality pattern* of the word. `a_ZFA(x)` is not: it depends on which symbols are conjugate pairs.
Quotienting by `ClosureEquiv` before computing the index would collapse histories that have
different construction trees, which is exactly what an assembly index is supposed to distinguish.
The raw-word choice is the strictest one; a phase-quotient or relabeling-quotient version is a
separate follow-up, not a silent change to this one.

---

## 2. Why closure is the natural QLF reuse boundary

Three machine-verified facts make `countBalanced` the right candidate for “can be reused as an
independent object”:

| Theorem | Statement | Consequence for assembly |
|---|---|---|
| [`count_balanced_pauli_closed`](lean/QLF_TwistAlphabet.lean) | every count-balanced history folds to a Pauli scalar `{±I, ±iI}` | a closed subhistory has a phase-only effect on its environment |
| [`isolated_iff_closed`](lean/QLF_Manifestation.lean) | a part is invisible to the closure of every environment **iff** it is count-balanced | closure is the exact isolation boundary, not an analogy |
| [`closed_insertion_is_phase`](lean/QLF_Manifestation.lean) | inserting a closed part anywhere changes the rest only by a global Pauli phase | reusing a closed part does not disturb the construction around it |

That is a genuine reason to *try* the closure-constrained index. It is not a theorem that nature
uses it, and AT itself imposes no such restriction: AT allows any constructed object to be reused.
The QLF variant is a **hypothesis with a precise definition**, and the census is its first test.

Two distinctions must be kept sharp.

**Pauli closure is weaker than count balance.** The converse of
`count_balanced_pauli_closed` is false: `^^^^` folds to `+I` but is not count-balanced. The runtime
conjunct `is_count_balanced ∧ is_pauli_closed` therefore still needs the first check; the second is
redundant *given the first*, not equivalent to it. The assembly restriction uses count balance, not
scalar fold.

**Distance is not assembly index.** QLF proves

$$
d(h) = \min\{\text{additional twists needed to close } h\} = \lVert \mathrm{net}(h) \rVert_1
$$

([`distance_eq_delay`](lean/QLF_Manifestation.lean)). That asks how far an *unfinished* object is
from closure. The assembly index asks how economically a *finished* object can be built from
reusable pieces. They are different optimization problems. Any relation between them — for example
a bound of the form `a_ZFA(h) ≥ f(d(h))` — is a theorem target, not an identification made here.

**Fold classes are coarse.** On the count-balanced census the fold is always `+I` or `−I`; no
`±iI` class occurs at any length through 10. This is expected: each twist is Hermitian, and a
product with every axis occurring an even number of times reduces to `±I`. The consequence is that
the QLF closure token `(ledger, fold)` has only two fold values on closures, so the size of a
closure class is a coarse “ways” quantity. It is **not** AT copy number. A possibility-space count
`W(x)` and an observed abundance `N(x)` are different objects; this census contains one copy of
each word and says nothing about abundance.

---

## 3. Exact method

Both indices are computed by branch-and-bound over the substrings of the target. Every object that
can appear in a construction of `x` is a contiguous substring of `x`; a join of two substrings that
is not a substring of `x` can never be used later.

### 3.1 Ordinary index

A construction is a set `D` of distinct non-primitive substrings containing `x`, with each
`s ∈ D` assigned a split `s = u · v` whose children are primitives or members of `D`. The cost is
`|D|`. The solver branches on an unassigned `s`, tries every split, and prunes when the current
set cannot beat the best known construction. The naive bound `|D| ≤ |x| - 1` seeds the search.

### 3.2 Closure-constrained index

The search state is a multiset of required objects plus the set of already-built closed objects.
When a required object `s` is closed, one build satisfies every copy and `s` joins the reusable
set; when `s` is non-closed, one copy is consumed and the other copies remain. A lower bound is the
number of distinct remaining requirements, and a budget bounds the remaining joins. Memoization is
keyed by `(required multiset, built closed set)` and only stores states solved within budget.

The minimum SLP problem is NP-hard in general, so neither solver is claimed polynomial. Length 10
is tractable because the target has at most 55 distinct substrings and the optimal cost is at most
9. The full census ran in **2m41s on four cores**.

### 3.3 Validation

| Check | Result |
|---|---|
| Both indices vs. independent BFS, every canonical class through length 4 | pass |
| Ordinary index vs. BFS, every canonical class through length 6 | pass |
| Canonical orbit weights vs. direct balanced-word counts, lengths 2–10 | pass |
| Fold classes partition the balanced words, lengths 2–8 (and 10 in the census) | pass |

The canonical form numbers axes by first appearance and makes each axis's first occurrence
positive. If a word uses `k` of the four axes, its orbit under the 384-element group (axis
permutations times per-axis sign flips) has size

$$
\frac{384}{(4-k)!\,2^{4-k}},
$$

because unused axes may be permuted and sign-flipped freely while used axes are fixed. Summing
these weights over the canonical classes reproduces the direct count of balanced words at every
length.

---

## 4. The exhaustive census

All count-balanced words of even length 2 through 10 were enumerated. “Words” counts actual
histories; “classes” counts canonical representatives.

| length | balanced words | classes | mean `a` | mean `a_ZFA` | words with gap | max gap | prime closures |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 8 | 1 | 1.000 | 1.000 | 0 | 0 | 8 |
| 4 | 168 | 6 | 2.952 | 2.952 | 0 | 0 | 104 |
| 6 | 5,120 | 70 | 4.931 | 4.931 | 0 | 0 | 2,944 |
| 8 | 190,120 | 1,365 | 6.881 | 6.903 | 3,728 (1.96%) | 2 | 108,136 |
| 10 | 7,939,008 | 37,926 | 8.791 | 8.869 | 570,864 (7.19%) | 2 | 4,525,888 |
| **total** | **8,134,424** | **39,368** | — | — | **574,592 (7.06%)** | **2** | — |

The gap `a_ZFA − a` is zero for 7,559,832 words, one for 527,064, and two for 47,528. No word
through length 10 has a gap larger than two. A “prime closure” here means a closed word that is
not the concatenation of two nonempty closed words.

The ordinary-index distributions at the two largest lengths:

| length | `a = 3` | `4` | `5` | `6` | `7` | `8` | `9` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 8 | 8 | 160 | 1,504 | 19,104 | 169,344 | — | — |
| 10 | — | 8 | 800 | 9,848 | 154,464 | 1,318,032 | 6,455,856 |

The closure-constrained distributions:

| length | `a_ZFA = 3` | `4` | `5` | `6` | `7` | `8` | `9` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 8 | 8 | 160 | 672 | 16,640 | 172,640 | — | — |
| 10 | — | 8 | 800 | 7,680 | 53,824 | 907,824 | 6,968,872 |

At length 10 the ordinary index is already close to the linear bound `|x| − 1 = 9`; the mean is
8.791. The closure constraint pushes some words up, but the maximum gap is still two. This is a
short-word census, not evidence that the gap stays bounded.

### 4.1 Fold classes

| length | `+I` | `−I` |
|---:|---:|---:|
| 2 | 0 | 8 |
| 4 | 144 | 24 |
| 6 | 1,488 | 3,632 |
| 8 | 116,008 | 74,112 |
| 10 | 3,535,200 | 4,403,808 |

No `+iI` or `−iI` class occurs. The fold of a count-balanced word is real.

---

## 5. Predeclared information tests

The question was fixed before the census: **does the closure constraint add information beyond
ordinary assembly, length, and compression?** The tests use weighted Shannon entropy over the
8,134,424 words (each canonical class carries its orbit size as weight).

| quantity | value (bits) |
|---|---:|
| `H(a)` | 0.914 |
| `H(a | length)` | 0.790 |
| `H(a | length, LZ78)` | 0.723 |
| `H(a | length, zlib)` | 0.738 |
| `H(a_ZFA)` | 0.722 |
| `H(a_ZFA | length)` | 0.580 |
| `H(a_ZFA | length, a)` | 0.185 |
| `H(a_ZFA | length, a, LZ78)` | 0.164 |
| `H(a_ZFA | length, a, zlib)` | 0.181 |
| `H(a_ZFA | length, a, LZ78, zlib)` | **0.159** |
| `H(a_ZFA | length, LZ78)` | 0.536 |

The bucket test is the same statement without averaging:

| target given | buckets | mixed buckets | words in mixed buckets | max values in a bucket |
|---|---:|---:|---:|---:|
| `a` given `(length, LZ78)` | 18 | 11 | **99.47%** | 6 |
| `a` given `(length, zlib)` | 14 | 8 | **99.997%** | 4 |
| `a_ZFA` given `(length, a)` | 17 | 5 | 18.48% | 3 |
| `a_ZFA` given `(length, a, LZ78)` | 45 | 13 | 16.34% | 3 |
| `a_ZFA` given `(length, a, zlib)` | 30 | 15 | 18.48% | 3 |
| `a_ZFA` given `(length, a, LZ78, zlib)` | 81 | 30 | **16.25%** | 3 |
| `a_ZFA` given `(length, LZ78)` | 18 | 11 | 99.47% | 6 |

Rank correlations (weighted Spearman):

| pair | ρ |
|---|---:|
| `a` vs `a_ZFA` | 0.813 |
| `a` vs `LZ78` | 0.333 |
| `a` vs `zlib` | 0.441 |
| `a` vs `length` | 0.369 |
| `a` vs distinct substrings | 0.661 |
| `a_ZFA` vs `LZ78` | 0.276 |
| `a_ZFA` vs `zlib` | 0.468 |
| `a_ZFA` vs `length` | 0.433 |
| `a_ZFA` vs distinct substrings | 0.514 |

**What the tests say.**

1. **The ordinary index is not just length or compression.** `H(a | length, LZ78) = 0.723` bits and
   `H(a | length, zlib) = 0.738` bits; 99.47% (resp. 99.997%) of words sit in a
   `(length, compressor)` bucket that contains more than one value of `a`. The AT critique that the
   index may collapse to compression is not supported in its strongest form on this census — though
   the residual is not large.
2. **The closure constraint is not vacuous.** `a_ZFA` differs from `a` on 7.06% of all words, and
   18.48% of words lie in a `(length, a)` bucket that contains more than one `a_ZFA` value. It
   retains 0.164 bits of entropy beyond `(length, a, LZ78)`, and 0.159 bits when zlib is added.
3. **The effect is modest.** Most words have `a_ZFA = a`; the maximum gap is two; the conditional
   entropy beyond the ordinary index is small. The honest summary is “a real, small effect on
   short words,” not “QLF solves Assembly Theory.”

The predeclared failure condition is therefore explicit: if a larger or chemistry-relevant census
drives `H(a_ZFA | length, a, LZ78, zlib)` to zero, or if the closure-constrained ranking adds
nothing once molecular graph structure is known, the QLF variant fails and should be withdrawn. A
negative result is a valid outcome of this program.

---

## 6. Examples

| word | length | `a` | `a_ZFA` | gap | note |
|---|---:|---:|---:|---:|---|
| `<>` | 2 | 1 | 1 | 0 | the minimal closure |
| `^v^v` | 4 | 2 | 2 | 0 | build `^v`, reuse it |
| `^^^^` | 4 | 2 | 3 | 1 | not closed; `^^` cannot be reused |
| `^^^^vvvv` | 8 | 5 | 7 | 2 | ordinary reuses `^^` and `vv`; QLF must rebuild both |
| `^><<^>vv` | 8 | 6 | 7 | 1 | smallest word in the census with a gap |
| `^><><><v` | 8 | 5 | 5 | 0 | closure constraint inactive on this optimum |
| `^^vvvv^^` | 8 | 5 | 7 | 2 | same length and `a` as the previous row, different `a_ZFA` |
| `^vvvvv^^^^` | 10 | 7 | 9 | 2 | largest gap at the largest length |

The `^^^^vvvv` case is the cleanest illustration. Ordinary assembly:

$$
\underbrace{^^}_{1},\quad \underbrace{^^^^}_{2},\quad
\underbrace{vv}_{3},\quad \underbrace{vvvv}_{4},\quad
\underbrace{^^^^vvvv}_{5}.
$$

Both `^^` and `vv` are reused. Under the QLF rule neither is closed, so each needs two copies:

$$
\underbrace{^^}_{1},\ \underbrace{^^}_{2},\ \underbrace{^^^^}_{3},\quad
\underbrace{vv}_{4},\ \underbrace{vv}_{5},\ \underbrace{vvvv}_{6},\quad
\underbrace{^^^^vvvv}_{7}.
$$

This is exactly the behavior the closure hypothesis predicts: the ordinary index exploits
reusable structure that QLF does not certify as isolated.

---

## 7. What this does and does not show

**Shown.**

- A precise, reproducible definition of the ordinary assembly index for ZFA histories, and a
  separate closure-constrained variant.
- Exact solvers, validated against independent breadth-first searches for short words.
- An exhaustive census of all 8,134,424 count-balanced words through length 10.
- The closure constraint changes 7.06% of those words and retains 0.164 bits beyond
  `(length, ordinary index, LZ78)`; 0.159 bits remain when zlib is added.

**Not shown.**

- No chemistry. No molecules, bonds, fragments, mass spectra, or abundances are modelled.
- No selection. The census counts possible histories once each; it says nothing about which
  histories are realized, replicated, or abundant.
- No universal life threshold. The often-quoted “about 15” value came from a particular 2021
  sample and should not be turned into a universal QLF constant
  ([Marshall et al. 2021](https://doi.org/10.1038/s41467-021-23258-x)).
- No claim that `a_ZFA` is the assembly index nature uses. It is a QLF-motivated restriction, and
  the census is a first test of whether it is worth pursuing.
- No length-12 census. There are 357,713,664 balanced words of length 12; the length-10 run is the
  current exhaustive boundary.

The “ways vs copies” distinction is the most important discipline here. QLF’s `8^n`-style
possibility counts and the census multiplicities are **not** AT copy number. AT’s empirical
quantity combines assembly complexity with the abundance of the same object in an observed
ensemble; a formal possibility count and an observed copy count must not be identified.

---

## 8. Next steps

### 8.1 Lean targets

The next PR should be a `QLF_AssemblyIndex` module, not more prose. Minimum targets:

1. Define an `AssemblyDAG` for `List Twist`: leaves are primitives, internal nodes are joins, and
   the root is the target.
2. Define `assemblyIndex` as the minimum number of internal nodes, and `assemblyIndexClosed` with
   the closed-reuse fan-out rule.
3. Prove `assemblyIndex_le_length_sub_one` and `assemblyIndex_le_closed`.
4. Prove the fold of a count-balanced word is `±1` (if not already derivable from existing
   modules).
5. Add `native_decide` checks for the small values in §0 and §6.

Local Lean builds are not practical on this machine; CI is the verification path.

### 8.2 Chemistry, only after the mathematics

The physical bridge, when it is attempted, must be operational:

$$
\text{QLF closed subassemblies}
\longrightarrow
\text{molecular reusable motifs}
\longrightarrow
\text{molecular assembly space}
\longrightarrow
\text{measured fragmentation}.
$$

The endpoint is a laboratory quantity. The falsifier is stated in §5: if the QLF-constrained
assembly space predicts molecular assembly ordering or fragmentation structure worse than ordinary
molecular AT, or adds no information once ordinary molecular graph structure is known, the QLF
contribution fails.

---

## 9. Reproduce

```bash
python3 assembly_index.py --self-test
python3 assembly_index.py --max-length 10 --jobs 4 \
    --json data/assembly_index_census.json
python3 -m unittest tests.test_assembly_index -v
```

The census is deterministic; the JSON contains no timestamps. The length-10 run took 2m41s on four
cores on the development machine. `--max-length 8` is a fast smoke test: 195,416 words through
length 8 in 1,442 classes.

---

## 10. References

**External**

- Sharma, A., Czégel, D., Lachmann, M., Kempes, C. P., Walker, S. I., & Cronin, L. (2023).
  *Assembly theory explains and quantifies selection and evolution.* Nature 622, 321–328.
  [doi:10.1038/s41586-023-06600-9](https://doi.org/10.1038/s41586-023-06600-9)
- Marshall, S. M., Mathis, C., Carrick, E., Keenan, G., Cooper, G. J. T., Graham, H., Craven, M.,
  Gromski, P. S., Moore, D. G., Walker, S. I., & Cronin, L. (2021). *Identifying molecules as
  biosignatures with assembly theory and mass spectrometry.* Nature Communications 12, 3033.
  [doi:10.1038/s41467-021-23258-x](https://doi.org/10.1038/s41467-021-23258-x)
- Abrahão, F. S., Hernández-Orozco, S., Kiani, N. A., Tegnér, J., & Zenil, H. (2024).
  *Assembly Theory is an approximation to algorithmic complexity based on LZ compression that does
  not explain selection or evolution.* arXiv:2403.06629; PLOS Complex Systems 1, e0000014.
  [arXiv:2403.06629](https://arxiv.org/abs/2403.06629),
  [doi:10.1371/journal.pcsy.0000014](https://doi.org/10.1371/journal.pcsy.0000014)
- Cronin, L., & Walker, S. I. (2016). *Beyond prebiotic chemistry.* Science 352, 1174–1175.
  [doi:10.1126/science.aaf6310](https://doi.org/10.1126/science.aaf6310)

**Internal**

- [`lean/QLF_TwistAlphabet.lean`](lean/QLF_TwistAlphabet.lean) — the 8-twist Pauli mapping and
  `count_balanced_pauli_closed`.
- [`lean/QLF_Manifestation.lean`](lean/QLF_Manifestation.lean) — `isolated_iff_closed`,
  `closed_insertion_is_phase`, `distance_eq_delay`.
- [`Closure_Token_Basis.md`](Closure_Token_Basis.md) — the closure token `(ledger, fold)`.
- [`MostWays_First.md`](MostWays_First.md) — multiplicity, “ways,” and the measure bridge.
- [`Evolution.md`](Evolution.md) — generate-and-select; the selection-side context.
- [`Chemistry.md`](Chemistry.md) and [`Protein_Folding.md`](Protein_Folding.md) — the possible
  later molecular rungs; not used in this census.
- [`Related_Frameworks.md`](Related_Frameworks.md) — where Assembly Theory sits among the
  neighbors.
