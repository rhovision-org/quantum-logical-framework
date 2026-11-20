# Diversity from Quarks — three-axis necessity and the first D8b test case

**Status:** first quark slice for the diversity program (#290). It proves the **necessity + existence**
half of three-colour emergence. It does **not** prove a diversity advantage or additional continuation
opportunities.

---

## 1. Why quarks are the first test case

Quark colour is the first QLF sector with:

- three primitive complementary axes (`x`, `y`, `z`);
- a defined structural invariant (`baryonNumber` / gauge-invariant `junctionBaryon`);
- a machine-checked necessity theorem (`baryon_needs_all_three_axes`);
- a closed witness with nonzero invariant (`proton_simplest_isolated_imbalance`).

This is a better first test than Penrose tilings: the axes and invariant are already primitive, and
the witness is already formal.

---

## 2. Existing anchors

From `lean/QLF_QuarkStructure.lean`:

- `baryon_zero_of_missing` — if a colour axis never appears, `baryonNumber = 0`.
- `baryon_needs_all_three_axes` — `baryonNumber ts ≠ 0` requires a twist on every colour axis.

From `lean/QLF_BaryonWinding.lean`:

- `junctionBaryon` — the gauge-invariant winding read on the spatial projection.
- `junctionBaryon_eq_of_noGauge` — on gauge-free words it agrees with `baryonNumber`.

From `lean/QLF_Manifestation.lean`:

- `protonClosure = >^/<\\v`;
- `proton_simplest_isolated_imbalance` — `countBalanced protonClosure`,
  `junctionBaryon protonClosure = 1`, and no shorter closure carries baryon number.

---

## 3. New Lean theorem

`lean/QLF_DiversityEmergence.lean` proves:

```
three_colour_emergence :
  (∀ ts,
    (∃ a : Ax, ∀ t ∈ ts, axOf t ≠ some a) →
    junctionBaryon ts = 0)
  ∧
  (∃ ts,
    countBalanced ts ∧ junctionBaryon ts ≠ 0)
```

The first half applies `baryon_zero_of_missing` to the junction; the second uses the proton closure.
Both halves use the same gauge-invariant invariant, avoiding the `baryonNumber` / `junctionBaryon`
mismatch in the original sketch.

Also:

```
junctionBaryon_zero_of_missing
three_colour_witness
```

The witness has the first three twists `>^/` on the three colour axes.

---

## 4. What this proves

**Proved:**

- no history missing any one colour axis can carry nonzero junction baryon number;
- at least one ZFA-closed three-axis history carries nonzero junction baryon number.

This is a concrete **structural-novelty** result: the invariant is inaccessible to every one-axis and
two-axis history, and accessible to a three-axis witness.

**Not proved:**

- that the three-axis structure is more prevalent than homogeneous structures;
- that it has more distinct continuation opportunities (the decisive Theorem E/D8c question);
- that it is more persistent;
- that this is physical QCD confinement;
- that every three-axis history is a baryon (the theorem is one-way).

The existence half is not a selection advantage. It is the first candidate witness that diversity can
**permit** a new invariant.

---

## 5. Next decisive theorem

The next target is not another existence statement. It is:

> **Three-axis complementarity creates additional, distinct opportunities for subsequent ZFA
> closure, beyond what one- and two-axis histories can generate.**

That requires:

1. a declared continuation/composition relation;
2. a finite/countable set of continuation classes;
3. a matched comparison between three-axis and fewer-axis histories;
4. a measure independent of the conclusion.

This is the D8c/D8b bridge, not implied by `three_colour_emergence`.

---

## 6. Reproduce

```bash
lake build QLF_DiversityEmergence
# or in CI:
lake build
```

The module is registered in `lakefile.lean`.

---

## 7. Links

- Issue #290 — diversity program; D8 gates.
- `lean/QLF_QuarkStructure.lean`, `lean/QLF_BaryonWinding.lean`, `lean/QLF_Manifestation.lean`.
- `Quarks.md` — colour and confinement reading.
- `Diversity_Composition_QLF.md` — D8a finite composition witness.
