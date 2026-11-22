# Diversity Continuation — D8c pilot and the naive-count failure

**Status:** pilot for issue [#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290).
D8c does **not** pass. The pilot records a negative methodological result: raw closed-extension
counting is invariant across axis-support classes. A canonical-composite variant is reported as
exploratory only.

---

## 1. Question

Can three-axis histories access more distinct continuation closures than one- or two-axis histories?

The naive candidate:

For a closed base `w` and a nonempty closed extension `e` of length ≤ 2:

```
admitted(w) = # { e : is_zfa(w ++ e) }
distinct(w) = # { canonical_word(w ++ e) }
```

The first is a raw continuation count; the second counts distinct canonical composite types.

---

## 2. The closure lemma

If `w` is ZFA-closed, then:

```
is_zfa(w ++ e)  ⇔  is_zfa(e)
```

because closure is additive on net action and the fold of a concatenation is the product of the
folds. A closed base does not constrain which closed extension can follow.

So `admitted(w)` is **independent of `w`**: every closed base has exactly the same eight closed
extensions of length 1–2:

```
^v, v^, <>, ><, /\, \/, +-, -+
```

Raw continuation counting therefore cannot distinguish axis diversity. It is not a D8c measure.

---

## 3. Finite census

All ZFA-closed words of length 6; grouped by number of distinct spatial axes.

```
closed bases: 5120
closed extensions (length 1–2): 8

support 0:   20 bases   admitted = 8 each   mean distinct canonical composites = 3.000
support 1: 1140 bases   admitted = 8 each   mean distinct canonical composites = 4.895
support 2: 3240 bases   admitted = 8 each   mean distinct canonical composites = 6.333
support 3:  720 bases   admitted = 8 each   mean distinct canonical composites = 7.000
```

The raw admitted count is identical in every group. The canonical-composite mean rises with axis
support, but this is **not** a measured diversity advantage:

- the groups are unmatched in size and base structure;
- the metric depends on the chosen `canonical_word` quotient;
- the extension set is the same for every base;
- no independent probability/measure is declared.

The canonical variation is a structural diagnostic, not D8c evidence.

---

## 4. Gate status

| gate | status |
|---|---|
| **D8c0 — raw continuation** | **failed as a diversity metric**: admitted count is invariant |
| **D8c1 — canonical variety** | **exploratory only**: unmatched, quotient-dependent |
| **D8c2 — matched measure** | **open**: requires a richer D3 composition relation |

D8c needs a composition relation whose available continuations actually depend on the base's
structure, not merely on appending a closed block. Candidate directions:

1. local interface composition (which twists at the boundary can join);
2. open base states with closure obligations;
3. matched homogeneous/heterogeneous populations at fixed resource counts;
4. an independent measure (U5 gate) and a null model.

---

## 5. What this does not claim

- No three-axis advantage.
- No D8c pass.
- No Penrose/golden-ratio claim.
- No persistence or physical application.
- No promotion of the exploratory canonical metric.

The negative result is the useful part: it rules out the easiest continuation count before it could be
mistaken for evidence.

---

## 6. Reproduce

```bash
python3 diversity_continuation.py --self-test
python3 diversity_continuation.py --run
python3 -m unittest tests.test_diversity_continuation -v
```

The run writes `data/diversity_d8c_census.json`.

---

## 7. Links

- Issue #290 — diversity program; D8a–D8c.
- #291 — D8a cross-type composition witness.
- #292 — quark three-colour necessity/existence.
- `assembly_index.py` — closure, fold, canonical word.
