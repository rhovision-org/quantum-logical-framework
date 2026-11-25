# Diversity Obligation Census — D3T typed provenance and residual obligations

**Status:** **D3T.1–D3T.5 pass.** **D3T.6 fails for the closure phase.** **D8c2 was not run and
remains unpassed.** This is a gate census, not a diversity-advantage test and not a holographic
dictionary claim.

The relation was frozen in
[`Diversity_Obligation_D3T.md`](Diversity_Obligation_D3T.md) before this census was run. The
implementation is [`diversity_obligation.py`](diversity_obligation.py); the data is
[`data/diversity_obligation_census.json`](data/diversity_obligation_census.json); the tests are
[`tests/test_diversity_obligation.py`](tests/test_diversity_obligation.py).

---

## 1. Relation in one paragraph

A provenance-typed history records `(origin, twist)` events. For each origin `o`, the residual
obligation is

```
obligation(h, o) = ( net(proj(h, o)),
                      axis(pauli(proj(h, o))),
                      phase(pauli(proj(h, o))) )
```

and the boundary record `B(h)` is the sorted multiset of these obligations. Two open histories
`a,b` with the same number of origins join, `R_T(a,b)`, when there is a bijection between their
origins such that matched streams have opposite net action and the same Pauli axis, the combined
word is ZFA-closed, and the final prefix is the first prefix containing **all** declared origins
that is ZFA-closed. Phase is recorded but not matched. The continuation profile is

```
C_T(a) = { B(b) : b a declared extension and R_T(a, b) }.
```

See the [pre-registration](Diversity_Obligation_D3T.md) for the no-pooling and typed-first-closure
rationale.

**Scope note.** The typed first closure is evaluated over all four tagged streams (two base, two
extension). A closure of a subset of streams is a partial closure and is allowed; the relation
rejects only an earlier closure that contains every declared origin. A variant that requires
base-level first closure or pair-level first closure is a different relation and is not tested here.

---

## 2. Declared panels

| panel | origin count | open base length | extension bound | purpose |
|---|---|---|---|---|
| **A** | 2 | 3 | 3 | primary gate census |
| **B** | 2 | 4 | 2 | length/extension robustness panel |

Whole-history phase check: closed two-origin histories of lengths **4 and 6**. All enumeration is
exhaustive. Closed bases are excluded because they carry no residual obligation; the excluded
counts are 0 in panel A and 1,176 in panel B.

---

## 3. Gate results

| gate | status | evidence |
|---|---|---|
| **D3T.1 — interface dependence** | **PASS** | 264 distinct typed profiles over 1,536 bases in panel A; 33 over 27,496 in panel B |
| **D3T.2 — closure preservation** | **PASS** | 12,096 + 8,736 admitted joins; 0 closure failures among obligation-matching candidates |
| **D3T.3 — provenance separation** | **PASS** | same aggregate data but different profile in 150/158 aggregate groups (A) and 62/402 (B); same raw word but different provenance profile in 504/512 word groups (A) and 2,048/3,928 (B); typed differs from the aggregate control on 1,512/1,536 bases (A) and 9,632/27,496 (B) |
| **D3T.4 — first-closure integrity** | **PASS** | 0 earlier all-origin closures among admitted joins |
| **D3T.5 — continuation-boundary sufficiency** | **PASS** | 0 boundary groups with multiple continuation profiles (360 groups in A; 2,238 in B) |
| **D3T.6 — phase-boundary sufficiency** | **FAIL** | whole-history phase ambiguous in 34/46 boundary groups at length 4 and 178/199 at length 6; extension phase ambiguous in 1,368/2,112 groups (A) and 2,016/4,704 (B) |
| **D3T.7 — no target geometry** | **PASS** | relation uses only twist, net, Pauli product, provenance, and first closure |
| **D8c2** | **NOT RUN** | D3T.6 fails; no advantage test under a boundary record that does not determine the phase. D8c2 remains **NOT PASSED** |

The exact counts are in the JSON. The gate strings in the JSON are generated from the same data,
not hand-entered.

---

## 4. What the positive gates show

### 4a. Typed provenance is visible

The same raw word can carry different provenance schedules and different boundary records. The
census finds this in 504 of 512 word groups in panel A and 2,048 of 3,928 in panel B. The same
aggregate closure data can likewise split into different profiles: 150 of 158 aggregate groups in
panel A and 62 of 402 in panel B.

A concrete panel-A witness is the word `^^v`, with aggregate closure data
`net = (+1,0,0,0)`, `axis = Y`, `phase = -1`:

| history | provenance | boundary record | continuation profile |
|---|---|---|---|
| `H1` | `A:^^`, `B:v` | `B: net (-1,0,0,0), axis Y, phase -1`; `A: net (+2,0,0,0), axis I, phase +1` | one record: `A_cont: net (-2,0,0,0), axis I, phase +1`; `B_cont: net (+1,0,0,0), axis Y, phase +1` |
| `H2` | `A:^`, `B:^`, `A:v` | `A: net (0,0,0,0), axis I, phase -1`; `B: net (+1,0,0,0), axis Y, phase +1` | one record: `A_cont: net (-1,0,0,0), axis Y, phase -1`; `B_cont: net (0,0,0,0), axis I, phase -1` |

`H1` and `H2` have the same word and the same aggregate data but different boundary records and
different continuations. Provenance is not epiphenomenal in the tested domain.

### 4b. The boundary record determines the continuation profile

Across both panels, no boundary group contains two different continuation profiles:

```
panel A: 360 boundary groups, 0 split profiles
panel B: 2,238 boundary groups, 0 split profiles
```

This is the positive dictionary result for the continuation observable. It is not a phase result.

### 4c. The aggregate control is less discriminating

The aggregate control keeps the same bases, extensions, openness, and first-closure rule, but
admits an extension whenever the total net is complementary, ignoring per-origin matching. Typed
profiles differ from aggregate profiles on 1,512 of 1,536 bases in panel A and 9,632 of 27,496 in
panel B. The typed relation has 264 distinct profiles versus 96 for the aggregate control in panel
A. Per-origin obligations carry information the aggregate net does not.

---

## 5. The phase failure

### 5a. Whole-history phase

For closed two-origin histories, `B(h)` does not determine `fold(word(h))`:

| length | closed typed histories | boundary groups | groups with both phases |
|---|---|---|---|
| 4 | 1,176 | 46 | 34 |
| 6 | 158,720 | 199 | 178 |

A length-4 witness:

```
B = { (-1,0,0,0), axis Y, phase -1 ;
      (+1,0,0,0), axis Y, phase -1 }

h1 = A:^^v, B:v      word ^^vv      fold = +1  (phase 0)
h2 = A:^<>, B:v      word ^<v>      fold = -1  (phase 2)
```

Both origins carry the same net, axis, and phase in both histories, but the internal order of
origin `A`'s twists differs (`^^v` versus `^<>`). The total Pauli product is order-sensitive, so the
same boundary record produces two closure phases.

### 5b. Extension phase

The same failure appears at the interface. In panel A, 1,368 of 2,112 `(base, B)` groups admit both
phases. A witness:

```
base = A:+- , B:/        word +-/
B    = { A_cont: net (0,0,0,0), axis I, phase -1 ;
         B_cont: net (0,0,+1,0), axis Z, phase -1 }

extension e1 = A:^v , B:\    word ^v\    joint phase -1  (fold 2)
extension e2 = A:^  , B:\ , A:v  word ^\v  joint phase +1  (fold 0)
```

The two extensions have the same boundary record `B` but different internal order within origin
`A` (`^v` versus `^` then `v`), and the joint closure phase differs.

### 5c. The missing information is the internal order, not just the schedule

Adding the extension's origin schedule reduces the panel-A ambiguity from 1,368 to 432 groups, but
does not eliminate it. Adding the full extension word eliminates it (0 ambiguous groups). In panel
B the extension length is 2, so there is only one two-origin schedule and the schedule diagnostic
does not reduce the 2,016 ambiguous groups; the full word again resolves it (0 ambiguous groups).

The boundary record `B` preserves each stream's net, axis, and phase. It does not preserve the order
of twists inside a stream. The closure phase depends on that order. A schedule-resolved record is
therefore still insufficient; a prefix-resolved record would be a different relation and would need
its own pre-registration.

---

## 6. What this census proves

- The D3T relation is a genuine new interface relation: it is not extension-independent, it
  preserves closure, and it respects typed first closure.
- Typed provenance changes continuation profiles relative to both the same-word schedule and the
  aggregate control.
- The boundary record `B` determines the continuation profile on the tested panels.
- The boundary record `B` does **not** determine the closure phase. The phase-dictionary candidate
  fails on both whole histories and extensions.

## 7. What this census does not prove

- **No D8c2 pass or fail.** D8c2 was not run.
- **No diversity advantage.** The typed relation is more restrictive than the aggregate control; a
  lower or different profile is not an advantage claim.
- **No holographic dictionary.** The continuation observable passes; the phase observable fails.
- **No physical phase identification.** The structural fold phase is not claimed to be a physical
  phase.
- No persistence (D9), Penrose/golden-ratio, materials, collective, or Lean claim.
- No claim beyond the tested lengths and two-origin scope.

---

## 8. Decision and next step

The pre-registered stop condition applies:

> If D3T.6 fails, do not add a post-hoc field, weight, or tie-breaker to rescue the phase claim.

Two admissible next steps remain, and neither is taken in this PR:

1. **Declare the closure phase out of scope** for the continuation-profile dictionary, then design a
   separate matched D8c2 test under the frozen D3T relation. That test must pre-register origin
   count, base length, extension bound, aggregate-net matching, and the homogeneous/heterogeneous
   populations.
2. **Pre-register a prefix-resolved boundary relation** and retest D3T.6 from scratch. This is a new
   relation, not a D3T patch, and it risks retaining the complete interior history; the
   reconstruction-vs-compression question must be stated before the run.

D8c2 remains unpassed under both options.

---

## 9. Reproduce

```bash
python3 diversity_obligation.py --self-test
python3 diversity_obligation.py --run
python3 -m unittest tests.test_diversity_obligation -v
```

The run writes `data/diversity_obligation_census.json`.

---

## 10. Links

- [Issue #290](https://github.com/rhovision-org/quantum-logical-framework/issues/290) — diversity program.
- [#298](https://github.com/rhovision-org/quantum-logical-framework/pull/298) — D8c2b negative synthesis and stop condition.
- [#295](https://github.com/rhovision-org/quantum-logical-framework/pull/295) — D3 interface census.
- [#294](https://github.com/rhovision-org/quantum-logical-framework/pull/294) — D3 pre-registration.
- [#293](https://github.com/rhovision-org/quantum-logical-framework/pull/293) — D8c0 negative pilot.
- [#283](https://github.com/rhovision-org/quantum-logical-framework/issues/283) — co-incidence and typed provenance.
- [#284](https://github.com/rhovision-org/quantum-logical-framework/pull/284) — typed-provenance and first-joint-closure finite model.
- [`Diversity_Obligation_D3T.md`](Diversity_Obligation_D3T.md) — the frozen pre-registration.
- [`Diversity_Revision_D8c2b.md`](Diversity_Revision_D8c2b.md) — the stop condition this census answers.
- [`assembly_index.py`](assembly_index.py) — primitive twist, net, Pauli product, and closure functions.
