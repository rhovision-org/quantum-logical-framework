# Diversity Interface Census — D3.1–D3.3 results

**Status:** the frozen D3 conjugate-boundary relation is implemented. **D3.1 and D3.2 pass**, D3.3 is
satisfied by construction, and **D8c2 was not run**.

This is an interface census, not a diversity-advantage test.

---

## 1. Relation

From the pre-registration in
[`Diversity_Interface_D3.md`](Diversity_Interface_D3.md):

```
interface_ok(a,b) := last(a) = CONJUGATE[first(b)]

join(a,b) :=
  a, b nonempty
  ∧ interface_ok(a,b)
  ∧ is_zfa(a ++ b)

K_k(a) := |{ canonical_word(a ++ b) : |b| <= k, join(a,b) }|
```

Only the twist alphabet, conjugate map, ZFA closure, and canonicalization are used.

---

## 2. Finite census

All nonempty bases and extensions of length 1–3:

```
bases:                 584
extensions:            584
admitted joins:       1544
closure failures:        0
distinct K values: {1, 2, 4, 6}
```

By base length:

| base length | bases | K distribution |
|---|---|---|
| 1 | 8 | `K=4` for all 8 |
| 2 | 64 | `K=1` for all 64 |
| 3 | 512 | `K=1`: 64, `K=2`: 384, `K=4`: 16, `K=6`: 48 |

At fixed length and extension bound, `K_k` is **not** constant. The relation therefore passes the
D3.1 interface-dependence requirement; unlike the closed-block concatenation in #293, the available
continuation classes depend on the base.

---

## 3. Dependence witnesses

| base | admitted extensions | distinct K |
|---|---|---|
| `^v<` | 9 | **6** |
| `^<^` | 2 | **2** |
| `^^^` | 1 | **1** |

The canonical-composite collisions in `^v<` are why 9 admitted extensions give 6 distinct closure
classes. This is a property of the declared quotient, not an advantage claim.

---

## 4. Gate status

| gate | status | evidence |
|---|---|---|
| **D3.1 — interface dependence** | **pass** | multiple K values and extension sets at fixed length/bound |
| **D3.2 — closure preservation** | **pass** | 1,544 joins, 0 closure failures |
| **D3.3 — no target geometry** | **pass** | conjugate boundary + ZFA closure only |
| **D8c2 — matched comparison** | **not run** | separate pre-registered test |

---

## 5. What this proves

- The conjugate-boundary join is not extension-independent.
- Different bases have different admissible continuation sets and different `K_k`.
- Every admitted join in the census is ZFA-closed.
- The D3.1 prerequisite for a future D8c2 design is satisfied.

## What this does not prove

- No homogeneous/heterogeneous advantage.
- No three-axis advantage.
- No physical or Penrose claim.
- No persistence.
- `K_k` is a provisional count, not a probability or an independent measure.
- No D8c2 result has been produced.

---

## 6. Next step

D8c2 can now be designed against a relation that actually varies with the base. It still needs:

1. matched homogeneous/heterogeneous populations;
2. a declared U5-style measure independent of the diversity endpoint;
3. a null model with generic local conservation but no ZFA fold;
4. pre-registered stopping/rejection rules.

Those belong in a separate D8c2 test PR, not this census.

---

## 7. Reproduce

```bash
python3 diversity_interface.py --self-test
python3 diversity_interface.py --run
python3 -m unittest tests.test_diversity_interface -v
```

The run writes `data/diversity_d3_census.json`.

---

## 8. Links

- Issue #290 — diversity program.
- [`Diversity_Interface_D3.md`](Diversity_Interface_D3.md) — frozen relation and gates.
- #293 — D8c0 negative pilot.
- #291 — D8a cross-type witness.
- #292 — quark three-colour necessity/existence.
