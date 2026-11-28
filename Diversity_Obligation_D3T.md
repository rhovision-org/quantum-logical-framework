# Diversity Obligation D3T — typed-provenance residual-obligation pre-registration

**Status:** pre-registration for issue [#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290),
after the D8c2b negative synthesis ([#298](https://github.com/rhovision-org/quantum-logical-framework/pull/298)).
No D3T census has been run in this document. **D8c2 remains unpassed.** No diversity-advantage,
Penrose, persistence, holographic-dictionary, or physical claim is made here.

This note freezes a genuinely new interface relation before any count. It is not another
append/weight variant of the failed D8c2 family. The relation changes **which residual obligations
are available at an interface**, not how existing closure records are counted or weighted.

---

## 1. Why this relation is admissible

The D8c/D8c2 sequence established three negatives:

1. Closed-block concatenation is extension-independent: every closed base admits the same closed
   extensions (#293).
2. The conjugate-boundary join is interface-dependent, but heterogeneous axis support has lower
   mean continuation multiplicity, and the net-zero null matches ZFA exactly (#295, #297).
3. Phase-labelled closure classes add no classes; two-interface continuation remains negative (#298).

The stop condition is therefore:

> No further append/weight variant is admissible. The next relation must change the underlying
> obligations or the available interfaces.

This pre-registration uses typed provenance and residual obligations. Origins are fixed before any
closure is observed, and an open provenance stream carries the complementary action still required
for closure. A continuation must answer those obligations stream by stream. The relation is
Boolean; there is no score, weight, fitted parameter, or target type.

---

## 2. Frozen primitive objects

All primitives come from [`assembly_index.py`](assembly_index.py):

```
TWISTS, CONJUGATE, AXIS, SIGN
net(w)        signed action vector on the four axes
pauli(w)     full Pauli product (phase, axis)
is_zfa(w)    count balance and scalar Pauli fold
fold(w)      scalar phase of a closed word
```

A **provenance-typed history** is a finite nonempty sequence

```
h = ((o_1, t_1), ..., (o_n, t_n))
```

with `o_i` an origin label and `t_i` a twist. Origins are part of the input record; they are fixed
before any closure is observed. Renaming origins is an equivalence, not a new history. We write:

```
word(h)             the twist word, ignoring provenance
origins(h)          the origins appearing in h
proj(h, o)          the twist word of events with origin o, in schedule order
open(h)             not is_zfa(word(h))
```

For each origin, the **residual obligation** is

```
obligation(h, o) = ( net(proj(h, o)),
                      axis(pauli(proj(h, o))),
                      phase(pauli(proj(h, o))) )
```

The first two components are the **closure obligation**: the net action still required, and the
Pauli axis that must be met for a product to become scalar. The phase is a **closure label**, not an
obligation: any phase is compatible with closure once the axes match.

The **boundary record** is the sorted multiset

```
B(h) = { obligation(h, o) : o in origins(h) }        (sorted, origin labels forgotten)
```

`B(h)` is deliberately coarser than the interior history. It preserves each stream's net action,
Pauli axis, and phase; it forgets the internal order of twists within a stream and the global
schedule.

The **aggregate closure data** is

```
O(h) = ( net(word(h)), pauli(word(h)) )
```

`O(h)` is the coarse description that ignores provenance entirely.

---

## 3. The relation \(R_T\)

Let \(a\) and \(b\) be provenance-typed histories. \(R_T(a,b)\) holds exactly when:

```
R_T(a, b) iff
  a and b are nonempty;
  origins(a) and origins(b) are disjoint;              (fresh continuation streams)
  open(a) and open(b);                                 (both carry residual obligations)
  |origins(a)| = |origins(b)|;
  there is a bijection f : origins(a) -> origins(b) such that, for every o in origins(a),

      net(proj(a, o)) + net(proj(b, f(o))) = 0
      axis(pauli(proj(a, o))) = axis(pauli(proj(b, f(o))));

  is_zfa(word(a) ++ word(b));
  no proper prefix of word(a) ++ word(b) that contains every declared origin is ZFA-closed.
```

### 3a. Why the bijection is part of the relation

The bijection is the **no-pooling rule**. Each base provenance stream's obligation must be answered
by a distinct continuation stream. Allowing one continuation stream to cancel several base streams
would reduce the relation to the aggregate net and erase the provenance distinction the relation is
meant to test.

This is a declared interface rule, not a theorem. The aggregate control in §5 measures what pooling
would do. A future pooling relation is a different relation and requires its own pre-registration.

### 3b. Why phase is recorded but not matched

Two Pauli elements with the same axis multiply to a scalar for any pair of phases. Matching phase
would therefore introduce a target closure type. The phase is retained in \(B(h)\) so the boundary
record can be tested for phase reconstruction, but it does not constrain admission.

### 3c. The typed first-closure condition

A prefix of `word(a) ++ word(b)` is a **joint** prefix only after every declared origin has
appeared at least once. A closure before that point is a partial closure of a subset of streams, not
a closure of the declared interface. The relation therefore rejects only earlier closures that
contain **all** declared origins. This is the typed refinement of the first-joint-closure notion in
[#283](https://github.com/rhovision-org/quantum-logical-framework/issues/283) and its
[#284](https://github.com/rhovision-org/quantum-logical-framework/pull/284) model.

The final prefix must be ZFA-closed. Partial closures are allowed; they are not the interface's
first joint closure.

### 3d. No target geometry

The relation uses only twists, net action, Pauli product, provenance labels, and first closure. It
uses no distance, Penrose matching, golden-ratio substitution, desired pattern, or physical target.
Any such clause is a kill condition.

---

## 4. Continuation profile and the dictionary question

For a fixed origin count \(m\), base length \(L\), and extension bound \(k\), define the
**continuation profile**

```
C_T(a) = { B(b) : b is a typed history, |b| <= k, |origins(b)| = m, R_T(a, b) }
```

This is a **set of boundary records**, not a count or a weighted sum. Two bases are
boundary-distinguishable when their profiles differ.

The dictionary question for this relation is:

> Does \(B(a)\) determine \(C_T(a)\), and does \(C_T(a)\) distinguish interiors with identical
> aggregate closure data but different provenance?

The phase question is separate:

> Does \(B(h)\) determine the closure phase `fold(word(h))` of a closed history \(h\)?

The first is a continuation/composability question. The second is a finer reconstruction question.
They are tested separately and are not allowed to substitute for one another.

---

## 5. Pre-registered gates

### D3T.0 — definitions frozen

This document is committed before the census. No clause depends on an observed result.

### D3T.1 — interface dependence

At fixed \(L,k\), the profiles \(C_T(a)\) are not all equal. At least two bases must have different
profiles. If every base has the same profile, the relation is extension-independent and is rejected.

### D3T.2 — closure preservation

Every admitted join must satisfy `is_zfa(word(a) ++ word(b))`. The census checks this independently
for every obligation-matching candidate, not only for joins that pass the first-closure test. Any
failure rejects the relation.

### D3T.3 — provenance separation

Two checks must pass:

1. **Aggregate separation:** there exist two bases with the same aggregate closure data
   \(O(a)=O(a')\) but different profiles \(C_T(a)\neq C_T(a')\).
2. **Word separation:** there exist two bases with the same raw word but different provenance
   schedules and different profiles.

If either check fails, provenance is epiphenomenal in the tested domain and the relation is rejected
as a provenance relation.

The **aggregate control** \(C_{\mathrm{agg}}(a)\) is also computed. It keeps the same bases,
extensions, openness, and first-closure rule, but admits an extension whenever the aggregate net is
complementary. It ignores per-origin matching. If \(C_T(a)=C_{\mathrm{agg}}(a)\) for every base,
the typed relation adds nothing over the aggregate control.

### D3T.4 — first-closure integrity

Every admitted join must have no earlier all-origin prefix closure. The census checks this
independently for every obligation-matching candidate. Any failure rejects the relation.

### D3T.5 — continuation-boundary sufficiency

For any two bases with \(B(a)=B(a')\), the profiles must satisfy \(C_T(a)=C_T(a')\). If a single
boundary record maps to two different continuation profiles, the boundary record is not a
well-defined boundary description for the continuation observable. This is a **positive** dictionary
test for \(C_T\).

### D3T.6 — phase-boundary sufficiency

This gate is declared in scope because the closure phase is a ZFA invariant and a candidate shared
observable. It has two parts:

1. **Whole-history phase.** For closed typed histories, if \(B(h)=B(h')\), then
   `fold(word(h)) = fold(word(h'))`. The census enumerates closed two-origin histories at lengths
   4 and 6.
2. **Extension phase.** For a fixed base \(a\) and a fixed \(B\in C_T(a)\), every admitted extension
   \(b\) with \(B(b)=B\) must give the same joint phase `fold(word(a) ++ word(b))`.

If either part finds a boundary record with two phases, D3T.6 **fails**. A failure is a stop
condition for the phase observable: the boundary record does not determine the closure phase. It is
not a reason to add a post-hoc field, weight, or tie-breaker. A schedule-resolved or
prefix-resolved boundary is a different relation and requires a new pre-registration.

### D3T.7 — no target geometry

By construction. Any geometric or target-pattern clause is a kill.

---

## 6. Declared census parameters

These parameters are fixed before the run:

| panel | origin count | open base length | extension bound | purpose |
|---|---|---|---|---|
| **A** | 2 | 3 | 3 | primary gate census |
| **B** | 2 | 4 | 2 | length/extension robustness panel |

Additional fixed parameters:

- Whole-history phase check: closed two-origin histories of lengths **4 and 6**.
- Extension phase check: panels A and B, using the same admitted joins.
- Exhaustive enumeration; no sampling, no random seed.
- A base is an **open** typed history. Closed bases are excluded because they carry no residual
  obligation and cannot participate in a first joint closure. The excluded count is reported.
- Extensions are open typed histories of exactly two origins, with length at most the panel bound.
- No population-size matching in this PR; this is a gate census, not D8c2.

---

## 7. Declared comparison cases

The census reports, without selecting a favourable subgroup:

1. **Aggregate groups:** bases with identical \(O(a)\) and the number of distinct profiles in each
   group.
2. **Word groups:** bases with identical `word(a)` but different provenance schedules, and whether
   their profiles differ.
3. **Boundary groups:** bases with identical \(B(a)\), and whether their profiles differ.
4. **Typed vs aggregate control:** the number of bases where \(C_T(a)\neq C_{\mathrm{agg}}(a)\).
5. **Phase groups:** boundary records with one phase and boundary records with multiple phases.
6. **Pattern-resolved phase:** the same phase test after adding the extension's origin schedule.
   This is diagnostic only; the relation itself is not changed.
7. **Word-resolved phase:** the same phase test after adding the full extension word. This is a
   diagnostic control: it should resolve the ambiguity if the missing information is the internal
   schedule/order.

No comparison case is added after the results are seen.

---

## 8. Failure and stop conditions

| condition | consequence |
|---|---|
| D3T.1 fails | relation is extension-independent; reject |
| D3T.2 fails | closure preservation is violated; reject |
| D3T.3 fails | provenance is epiphenomenal; reject or pre-register a different relation |
| D3T.4 fails | first-closure integrity is violated; reject |
| D3T.5 fails | \(C_T\) is not a function of \(B\); reject the boundary description for the continuation observable |
| D3T.6 fails | boundary record does not determine the closure phase; stop the phase-dictionary claim |
| D3T.7 fails | target geometry imported; kill |
| D8c2 | **not run** in this PR; remains unpassed |

If D3T.6 fails, the admissible next steps are:

- declare the closure phase out of scope for the continuation-profile dictionary and design a
  separate matched D8c2 test under the frozen \(C_T\) relation; or
- pre-register a schedule-resolved boundary relation and retest D3T.6 from scratch.

Neither step is taken in this PR.

---

## 9. What this pre-registration does not claim

- No D8c2 pass or fail.
- No diversity advantage, axis-support advantage, or three-axis claim.
- No holographic dictionary reconstruction.
- No identification of the structural closure phase with a physical phase.
- No persistence (D9), Penrose/golden-ratio, materials, or collective claim.
- No Lean theorem.
- No claim that the finite panels extend beyond the tested lengths.

---

## 10. Links

- Issue [#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290) — diversity program.
- [#298](https://github.com/rhovision-org/quantum-logical-framework/pull/298) — D8c2b negative synthesis and stop condition.
- [#295](https://github.com/rhovision-org/quantum-logical-framework/pull/295) — D3 interface census.
- [#294](https://github.com/rhovision-org/quantum-logical-framework/pull/294) — D3 pre-registration.
- [#293](https://github.com/rhovision-org/quantum-logical-framework/pull/293) — D8c0 negative pilot.
- [#283](https://github.com/rhovision-org/quantum-logical-framework/issues/283) — co-incidence and typed provenance.
- [#284](https://github.com/rhovision-org/quantum-logical-framework/pull/284) — typed-provenance and first-joint-closure finite model.
- [`Diversity_Revision_D8c2b.md`](Diversity_Revision_D8c2b.md) — the stop condition this note answers.
- [`Diversity_Interface_D3.md`](Diversity_Interface_D3.md) — the previous frozen relation.
- [`assembly_index.py`](assembly_index.py) — primitive twist, net, Pauli product, and closure functions.
