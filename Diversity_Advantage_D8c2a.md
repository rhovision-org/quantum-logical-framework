# Diversity Advantage — D8c2a screen

**Status:** D8c2a base-level screen **fails**. D8c2 was **not run** and remains open.

This is a negative result for the frozen D3 conjugate-boundary relation under the declared screen. It
does not refute diversity advantages in other relations or measures.

---

## 1. Screen

Using the D3 relation:

```
interface_ok(a,b) := last(a) = CONJUGATE[first(b)]
join(a,b) := interface_ok(a,b) ∧ is_zfa(a ++ b)
K_k(a) := |{ canonical_word(a ++ b) : |b| <= k, join(a,b) }|
```

Declared classes at fixed base length `L` and extension bound `k=3`:

- **homogeneous:** bases with exactly one spatial axis;
- **heterogeneous:** bases with two or three spatial axes;
- **endpoint:** mean `K_k` per base.

This is a base-level screen, not the full population-size-matched test. It is sufficient to block the
full D8c2 test if it shows no candidate signal.

---

## 2. Results

| base length | homogeneous mean K (n) | heterogeneous mean K (n) | heterogeneous advantage |
|---|---|---|---|
| 3 | 2.500 (168) | 2.214 (336) | **no** |
| 4 | 0.550 (720) | 0.279 (3360) | **no** |
| 5 | 1.790 (2976) | 1.140 (29760) | **no** |

Total bases: 37,376.

At every tested length, the heterogeneous support classes have **lower** mean continuation-class
count than the one-axis class. No length shows the pre-declared advantage.

### Null model

Replace ZFA closure with generic net-action zero, keeping the conjugate boundary and canonicalization:

```
null_join(a,b) := interface_ok(a,b) ∧ net(a ++ b) = 0
```

For all 37,376 bases, the null continuation set is **exactly equal** to the ZFA continuation set:

```
null differences: 0
```

So the `fold` adds no distinction in this tested domain. The screen's behavior is a property of
net-conservation + boundary + canonicalization, not a distinctive ZFA effect.

---

## 3. Gate status

| gate | status |
|---|---|
| **D8c2a heterogeneous advantage** | **fail** — no length shows mean K increase for support 2/3 |
| **D8c2a null separation** | **fail** — null matches ZFA exactly |
| **D8c2 matched population** | **not run** — blocked by the screen |

---

## 4. What this proves

- Under the frozen D3 relation and the declared base-level screen, axis-support diversity does not
  increase continuation multiplicity.
- The null model reproduces the ZFA result exactly in this domain.
- The full matched D8c2 population test is not warranted under this relation/measure.

## What this does not prove

- No claim that diversity never helps in QLF.
- No D8c2 pass or fail for other relations/measures.
- No Penrose/golden-ratio claim.
- No persistence (D9) or physical relevance (D10).
- The screen groups are not population-size matched; it is a screen, not the full test.

---

## 5. Next step

Do **not** proceed to D9. The next admissible step is a **relation/measure revision**, pre-registered
before looking at results. Candidates:

1. a boundary relation with an explicit interface obligation (not just conjugate endpoint);
2. open bases with residual net/phase obligations;
3. a phase- or amplitude-weighted measure rather than canonical type count;
4. a null model that preserves the boundary relation but removes the closure fold in a controlled
   way.

Any revision must pass D3.1 interface dependence again and must not use the desired advantage as an
axiom.

---

## 6. Reproduce

```bash
python3 diversity_advantage.py --self-test
python3 diversity_advantage.py --run
python3 -m unittest tests.test_diversity_advantage -v
```

The run writes `data/diversity_d8c2a_screen.json`.

---

## 7. Links

- Issue #290 — diversity program.
- #295 — D3 interface census.
- #294 — D3 pre-registration.
- #293 — D8c0 negative pilot.
- `assembly_index.py` — closure, fold, net, canonical word.
