# Diversity Composition — D8a cross-type witness

**Status:** D8a **passes** as a finite primitive-algebra witness for issue
[#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290). D8b (novel outcome)
and D8c (measured advantage) remain open and are **not** claimed.

This is a first slice, not the diversity theorem.

---

## 1. Definitions

Use the QLF twist alphabet and the primitive signed-action/closure functions from
[`assembly_index.py`](assembly_index.py):

```
is_zfa(w) = is_closed(w) and fold(w) is not None
kind(w)   = net(w)          # oriented net action on the four axes
compose(a,b) = a ++ b
```

The **provisional structural type** is the oriented net-action vector. It is defined before any
composition result and does not use distance, geometry, or a target pattern.

A pair is an **admissible cross-type composition** when:

```
a and b are nonempty
not is_zfa(a)
not is_zfa(b)
is_zfa(a ++ b)
kind(a) != kind(b)
```

The relation therefore uses only primitive closure and the declared type.

---

## 2. Explicit witness

```
a = "^"      net(a) = (1, 0, 0, 0)      is_zfa(a) = false
b = "v"      net(b) = (-1, 0, 0, 0)     is_zfa(b) = false
a ++ b = "^v" net = (0, 0, 0, 0)        is_zfa("^v") = true, fold = 2 (-I)
```

So:

```
kind("^") != kind("v")
admissible_composition("^", "v")
```

This is a genuine cross-type composition under the declared type. It is the same complementary pair
that appears as the strong co-incidence example in #283/#284, now used for the diversity gate.

### Why the composite closes

`net("^v") = net("^") + net("v") = 0`; every axis is count-balanced, and `fold("^v")` is a Pauli
scalar. The composite is therefore ZFA-closed.

---

## 3. Finite census

Enumerating nonempty twist words of length 1–2:

```
words:                    72
open words:               64
admissible compositions: 112
cross-type compositions: 112
same-type compositions:    0
```

At this depth there is no open word with zero net action, so no same-type admissible pair exists. Thus
the short census realizes only the cross-type branch; that is a limitation of the depth, not a claim
that homogeneous composition is impossible in general.

The witness is exact and independent of the census; the census shows it is not an isolated accident.

---

## 4. What this proves — and what it does not

**Proved (D8a):**

```
∃ a,b: admissible_composition(a,b) and kind(a) != kind(b)
```

with an explicit primitive witness.

**Not proved:**

- **D8b — novel outcome:** that a complementary composite is inequivalent to every same-type
  composite and to simple repetition. At this depth every admissible composite has net zero, so the
  census cannot distinguish novel outcomes.
- **D8c — measured advantage:** that heterogeneous populations have more continuation multiplicity
  than matched homogeneous populations. No measure or comparison is declared here.
- **D9 — persistence:** no iterative survival test.
- **D10 — physical relevance:** no materials, error-correction, or collective claim.

The E0 pair-count lemma is not used as evidence. D8a supplies the missing hypothesis for a *future*
E0 statement, but D8a alone is one witness, not a diversity advantage theorem.

---

## 5. Scope and next steps

The type `kind(w) = net(w)` is provisional. D2 (equivalence) may refine it; if so, the witness must be
rechecked under the refined type. The composition is concatenation only; D3 may add a richer
composition relation.

Next:

1. **D2/D3** — freeze the structural equivalence and the composition relation.
2. **D8b** — find a composite whose closure type is unreachable by same-type composition.
3. **D8c** — declare an independent measure, matched homogeneous/heterogeneous populations, and test
   the advantage.
4. **D7** — only then ask whether aperiodic order emerges without importing its substitution.

---

## 6. Reproduce

```bash
python3 diversity_composition.py --self-test
python3 diversity_composition.py --run
python3 -m unittest tests.test_diversity_composition -v
```

The run writes `data/diversity_d8a_census.json`.

---

## 7. Links

- Issue #290 — diversity program; D8a–D8c gates.
- #283/#284 — typed-provenance co-incidence; `^ | v` strong example.
- `assembly_index.py` — primitive twist, net, closure, fold.
- `Manifestation.md` — closure and multiplicity background.
