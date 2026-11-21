# Diversity Interface D3 — pre-registration for the next composition relation

**Status:** pre-registration for issue [#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290).
No census has been run. D8c remains open.

This note freezes the next candidate relation **before** any new count, because the D8c pilot (#293)
showed that closed-block concatenation is extension-independent.

---

## 1. Why a new relation is required

#293 proved the negative methodological result:

```
w closed  ⇒  (is_zfa(w ++ e) ⇔ is_zfa(e))
```

Every closed length-6 base admits the same eight closed extensions. Raw continuation counting cannot
distinguish one-, two-, and three-axis bases.

Therefore D8c2 needs a relation whose available continuations depend on the **base's boundary
structure**, not merely on appending an independently closed block.

---

## 2. Candidate relation: conjugate boundary join

Use only the primitive twist alphabet and the existing conjugate map.

For a nonempty history `h`:

```
first(h) = first twist of h
last(h)  = last twist of h
```

Define the interface condition:

```
interface_ok(a,b) := last(a) = CONJUGATE[first(b)]
```

Define an admissible join:

```
join(a,b) :=
  a and b are nonempty
  ∧ interface_ok(a,b)
  ∧ is_zfa(a ++ b)
```

`solve`/`is_zfa` is the existing count-balance plus Pauli-scalar closure predicate. The relation uses
no distance, Penrose matching rule, target geometry, or desired outcome.

A **continuation profile** of a nonempty base `a` at extension bound `k`:

```
C_k(a) = { canonical_word(a ++ b) :
           b nonempty, |b| <= k, join(a,b) }
K_k(a) = |C_k(a)|
```

`canonical_word` is the existing 384-group canonical form. `K_k` is a provisional count; the matched
measure is defined in §4.

---

## 3. Mandatory sanity gates before any D8c2 census

### D3.0 — definitions frozen

Freeze `first`, `last`, `interface_ok`, `join`, `C_k`, `K_k`, the equivalence relation, and the
resource budget. No outcome-dependent clause.

### D3.1 — interface dependence

Exhibit at least two bases with **different** admissible continuation sets under the same `k` and
resource budget. This is required to avoid reproducing #293's invariance.

If `join` is extension-independent for all tested bases, D3.1 fails and the relation is rejected.

### D3.2 — closure preservation

Every admitted join must satisfy `is_zfa(a ++ b)` by construction or proof. A join that bypasses
closure fails.

### D3.3 — no target geometry

The relation may use only twist, conjugate, count balance, fold, and canonicalization. Any distance,
Penrose matching, golden-ratio substitution, or desired pattern is a kill.

### D3.4 — matched measure

Before looking at results, declare:

- total length/resource budget for base plus extension;
- base population sizes;
- homogeneous vs heterogeneous population definitions;
- primary endpoint (`K_k` mean or distinct union);
- independent measure (exact count or U5 cylinder/Kraft weight);
- null model with generic local conservation but no ZFA fold.

---

## 4. Matched comparison design

### Populations

A population is a finite set of nonempty open bases with declared axis support and net-action budget.

- **Homogeneous population:** all bases from one declared axis family/boundary type.
- **Heterogeneous population:** bases drawn from at least two complementary axis families/boundary
  types, matched to the homogeneous population by:
  - number of bases;
  - total twist length;
  - net-action budget;
  - extension bound `k`.

No post-hoc matching after seeing `K_k`.

### Primary endpoint

```
K_het > K_hom
```

where `K` is the mean number of distinct continuation classes per base under the frozen relation, or
a pre-declared union measure. The measure must not be defined from the diversity result.

### Secondary endpoints

- number of novel closure types reachable only from cross-type joins;
- distribution of `K_k`, not only the mean;
- persistence of the same classes under a second interface join (D9 only if D8c passes).

### Null model

Repeat the matched comparison with closure replaced by generic local conservation:

```
net(a ++ b) = 0
```

but without the Pauli fold. If the null model gives the same advantage, the result is a property of
local conservation counting, not a distinctive ZFA effect.

---

## 5. Kill conditions

1. `join` is extension-independent (D3.1 fails).
2. The relation uses geometric distance, Penrose matching, or a desired pattern.
3. The measure is the same quantity used to define diversity.
4. Populations are not matched before the run.
5. The null model reproduces the same advantage.
6. Canonicalization is chosen after seeing which quotient makes the advantage appear.
7. A finite-depth result is reported as an unbounded theorem.
8. D9/D10 claims are made before D8c passes.

---

## 6. Proposed PR sequence

| PR | scope | gates |
|---|---|---|
| **D3-note** | this pre-registration | D3.0, D3.3, D3.4 design |
| **D3-census** | `diversity_interface.py`, tests, data; finite conjugate-boundary joins | D3.1–D3.2 |
| **D8c2-test** | matched homogeneous/heterogeneous comparison and null model | D3.4, D8c2 |
| **D8c2-Lean** | interface invariants and any conditional advantage theorem | after D8c2 finite pass |

Do not combine D3-census and D8c2-test. The relation and populations must be frozen before the
comparison is run.

---

## 7. What this note does not claim

- No D8c pass.
- No three-axis advantage.
- No Penrose/golden-ratio claim.
- No persistence or physical relevance.
- No Lean theorem yet.
- No census result.

---

## 8. Links

- Issue #290 — diversity program; D8 gates.
- #293 — D8c0 negative result: closed-block continuation is invariant.
- #291 — D8a cross-type composition witness.
- #292 — quark three-colour necessity/existence.
- `assembly_index.py` — twist, conjugate, closure, canonical word.
