# Co-incidence — typed provenance and first shared closure

**Status:** first slice for issue [#283](https://github.com/rhovision-org/quantum-logical-framework/issues/283).
CO0 and the CO1/CO2 provenance schedule are implemented as a finite model. CO3 — the universality
census — remains open. This document does **not** claim that every event is a co-incidence, and it
does not touch the frozen `quantum-os#322` experiment.

---

## 1. The trap

If co-incidence is defined as:

```
A open, B open, A ++ B closed
```

then every closed word of length at least 2 is a co-incidence by an arbitrary split:

```
A = [w0]
B = W[1:]
```

`A` is open (a single twist has nonzero net). `B` is open (since `W` is closed and `A` has nonzero
net, `B` has net `-net(A)`). `A ++ B = W` is closed.

So the bare definition is vacuous. The substantive content must be **where the two sides came from**
and **whether their meeting is the first joint closure**.

---

## 2. Typed provenance

Origins are part of the input record, before any closure is observed:

```
ProvTwist = Origin × Twist
w = [(o_1, t_1), (o_2, t_2), …]
```

For origins `o_A ≠ o_B`, the monotone projections at prefix length `n` are:

```
A_n = proj_{o_A}(w[0:n])
B_n = proj_{o_B}(w[0:n])
```

The origins are fixed in the record. They cannot be assigned after seeing which pair closes.

`coincidence.py` implements `ProvEvent(origin, twist)`, `project`, and `origins`.

---

## 3. First joint closure

```
FirstJointClosure(w, o_A, o_B, n) :=
  A_n ≠ [] ∧ B_n ≠ [] ∧
  SharedClosure(A_n, B_n) ∧
  ∀ m < n, ¬ SharedClosure(A_m, B_m)
```

and:

```
CoIncides(w, o_A, o_B) :=
  o_A ≠ o_B ∧
  ∃ n, FirstJointClosure(w, o_A, o_B, n)
       ∧ ¬ Closed(A_n)
       ∧ ¬ Closed(B_n)
```

A **strong co-incidence** additionally requires non-factorizability:

```
StrongCoIncides(w, o_A, o_B) :=
  CoIncides(w, o_A, o_B) ∧ ¬ ProductForm(A_n, B_n)
```

`StrongCoIncides` is not redundant. `¬ Closed(A)` concerns ZFA closure (count balance plus Pauli
closure); `¬ ProductForm(A, B)` concerns whether each side folds to a scalar on its own. QLF has
scalar folds that are not count-balanced, so the two conditions differ.

---

## 4. CO0 finite check

`coincidence.py` enumerates all ZFA-closed words over the eight-twist alphabet through length 6 and
checks the first-twist split. The result is:

```
closed words checked: 5296
failures: 0
```

This is a **finite check of the proof sketch**, not a Lean theorem. The analytic argument covers
arbitrary length; the Lean/formal target remains open.

---

## 5. CO1/CO2 examples

### Strong co-incidence — `^ | v`

```
events: [A:^, B:v]
n = 2
A_2 = "^"   open
B_2 = "v"   open
A_2 ++ B_2 = "^v" closed
product sector: false
strong: true
```

This is the `shared_closure_not_factorizable` witness: neither side contains the event; the joint
closure exists only in their relation.

### Product-sector contrast — `+ | -`

```
events: [A:+, B:-]
n = 2
A_2 = "+"   open
B_2 = "-"   open
A_2 ++ B_2 = "+-" closed
product sector: true
strong: false
```

The gauge pair is a co-incidence under the typed schedule, but not a **strong** one: each side folds
to a scalar on its own (`gauge_pair_is_product_sector`).

### First, not last

```
events: [A:^, B:v, A:v, B:^]
n = 2, not 4
```

The first prefix whose projections jointly close is the event. Later extensions are not the
co-incidence.

---

## 6. Scope: interaction events vs all events

Two distinct claims:

1. **Interaction co-incidence:** every event with at least two pre-existing provenance streams is a
   co-incidence.
   ```
   ∀ E ∈ InteractionEvents, CoIncidence(E)
   ```
2. **Universal resolution:** every realized event can be represented as the first shared closure of
   pre-existing provenance streams.
   ```
   ∀ E ∈ Events, ∃ A, B: CoIncidence(E)
   ```

Only claim 2 supports “nothing happens individually.” Claim 1 supports “every interaction is a
co-incidence.” CO3 is the census that decides which claim survives.

---

## 7. What this does not claim

- No claim that every event is a co-incidence.
- No theorem that causation is a succession of co-incidences.
- No consciousness, feeling, or memory claim. D8 is a finite toy; it does not establish separate
  provenance for feeling and memory.
- No claim that lexical overlap, embeddings, or unification are interchangeable listener relations.
- No change to the frozen `quantum-os#322` experiment.
- No Lean theorem yet for CO0; only the finite check and the analytic proof sketch.

---

## 8. Reproduce

```bash
python3 coincidence.py --self-test
python3 coincidence.py --run
python3 -m unittest tests.test_coincidence -v
```

The run writes `data/coincidence_census.json`.

---

## 9. Anchors

- [`lean/ER_EPR_QLF.lean`](lean/ER_EPR_QLF.lean) — `SharedClosure`, `Spacelike`, `ERBridge`,
  `no_ftl_in_epr`.
- [`lean/QLF_IndexedFactors.lean`](lean/QLF_IndexedFactors.lean) — `shared_closure_not_factorizable`,
  `gauge_pair_is_product_sector`.
- [`lean/QLF_QuantumTurbulence.lean`](lean/QLF_QuantumTurbulence.lean) — `prime_closure_irreducible`
  (period divisibility only; not event decomposition).
- [`lean/QLF_Manifestation.lean`](lean/QLF_Manifestation.lean) — `distance_eq_delay`.
- [`assembly_index.py`](assembly_index.py) — the twist alphabet, count balance, and Pauli fold used by
  the finite check.
- [Issue #283](https://github.com/rhovision-org/quantum-logical-framework/issues/283) — CO0–CO3
  gates.
- [Event timing](Event_Timing_QLF.md) — listening `tau > 0`, closure `tau = 0`; merged in #281.
- [AI cognition](AI.md) — running system vs listener architecture; merged in #282.
- [Conscious dynamics (PR #279)](https://github.com/rhovision-org/quantum-logical-framework/pull/279)
  — D8 finite toy; not evidence for CO.
- [quantum-os#322](https://github.com/rhovision-org/quantum-os/pull/322) — frozen listener-controller
  experiment; not touched here.
