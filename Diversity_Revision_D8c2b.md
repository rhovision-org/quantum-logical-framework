# Diversity Revision — D8c2b negative synthesis

**Status:** both tested rescues of the D8c2 relation fail. D8c2 is not passed. The next step is a
genuinely new relation derived from the primitive algebra, not another measure tweak.

This note records two pre-declared revisions of the D3/D8c2 family:

1. **phase-labelled closure classes**;
2. **two-interface continuation** (`a → b → c`).

---

## 1. Candidate 1 — phase-labelled closure classes

Instead of counting canonical closure types, count:

```
K_phase(a) = |{ (canonical_word(a ++ b), fold(a ++ b)) : join(a,b) }|
```

using the frozen D3 join and extension bound 3.

Result over bases of length 3–5:

```
bases:                       37,376
bases with added classes:         0
phase-added classes:              0
```

The phase label adds **no** new classes in the tested range. Candidate 1 is rejected as an empty
revision; it cannot change the D8c2 conclusion.

---

## 2. Candidate 2 — two-interface continuation

A continued-composability variant:

```
a → b → c, where join(a,b) and join(a ++ b,c)
K2(a) = |{ canonical_word(a ++ b ++ c) }|
```

with extension bound 2.

Result:

| base length | homogeneous mean K2 (n) | heterogeneous mean K2 (n) | advantage |
|---|---|---|---|
| 3 | 0.214 (168) | 0.071 (336) | **no** |
| 4 | 0.550 (720) | 0.279 (3360) | **no** |

Total bases: 4,608.

The two-interface extension remains negative: heterogeneous support has lower mean K2, not higher.

### Null model

Replace ZFA closure with net-action zero:

```
null differences: 0
```

The null continuation sets match the ZFA sets exactly for all 4,608 bases. The fold again adds no
distinction in this range.

---

## 3. Gate status

| gate | status |
|---|---|
| **D8c2b phase revision** | **fail** — no new classes |
| **D8c2b two-interface** | **fail** — no advantage; null matches ZFA exactly |
| **D8c2** | **not passed** — requires a genuinely new relation |

---

## 4. What this proves

- Neither phase-labelling nor a second interface rescues the negative D8c2a result.
- The failure is not an artifact of a single extension count.
- Further metric tweaks within the same append/closure family are not justified.

## What this does not prove

- No claim that diversity never helps in QLF.
- No D8c2 pass/fail for a genuinely different relation.
- No Penrose, persistence, or physical claim.

---

## 5. Stop condition

No further D8c2 variant should be run until a relation is derived that changes the **available
interfaces or obligations**, not merely the count/weight of appended closed blocks. Candidate sources:

- typed-provenance / first-joint-closure composition (the #284 direction);
- open bases with explicit residual obligations and a capacity budget;
- substitution or assembly composition rather than concatenation.

Any new relation must pass D3.1 interface dependence first and must be frozen before the D8c2 test.

---

## 6. Reproduce

```bash
python3 diversity_advantage_variants.py --self-test
python3 diversity_advantage_variants.py --run
python3 -m unittest tests.test_diversity_advantage_variants -v
```

The run writes `data/diversity_d8c2b_revision.json`.

---

## 7. Links

- Issue #290 — diversity program.
- #297 — D8c2a negative screen.
- #295 — D3 interface census.
- #294 — D3 pre-registration.
