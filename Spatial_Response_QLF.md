# Spatial Response of Closure — expansion, contraction, and the ΔS/Δd test

**Status:** first slice for issue [#287](https://github.com/rhovision-org/quantum-logical-framework/issues/287).
SR0–SR3 are implemented as a finite **independence ledger**. SR4–SR7 are **out of scope for this PR**,
tracked in #287; they are not claimed. This is not a physical spatial model, not a gravity derivation,
and not a 3D metric.

---

## 1. The question

The proposal is:

> Interactions can synthesize spatial relation or eliminate it. The sign belongs to the
> relation/event, not to a particle species.

Define two quantities independently:

```
ΔS(E) = S_after - S_before      spatial-response ledger
Δd(E) = d_after - d_before      closure distance
```

The bridge to test is:

```
Δd < 0 ?⇒ ΔS < 0
```

for binding interactions. It must not be a definition.

---

## 2. Exact orientation anchor

`lean/QLF_MagneticOrientation.lean` proves:

```
jointSpace p q = if p = q then +2 else -2
netSpace es = 2 * (likeCount es - oppositeCount es)
```

and:

- `like_poles_expand` — all like pairs give `netSpace = +2n`;
- `opposite_poles_destroy` — all opposite pairs give `netSpace = -2n`;
- `fixed_distance_iff` — `netSpace = 0` iff like and opposite counts balance.

This is a boolean orientation ledger, not a physical metric.

Pauli/electron anchors:

- `pauli_exclusion` — identical processes exclude;
- `shells_from_pauli_exclusion` — shells exist because identical closures are excluded;
- `QLF_ElectronClosure` — like charges admit no closure; opposite charges can.

The electron statement is about **like-spin/identical-fermion interaction**, not “every electron
expands space.” Opposite-spin configurations can form singlets and contract.

---

## 3. Finite independence ledger

`spatial_response.py` uses:

- `S` = `netSpace(history)` over orientation pairs;
- `d` = Hamming distance of a separate two-bit closure state;
- an event appends a `like` or `opposite` orientation pair and independently flips one closure bit,
  or flips none.

The two updates never consult each other.

### Result

```
events: 72
binding events (Δd < 0): 24
binding and contraction (ΔS < 0): 12
binding and expansion (ΔS > 0): 12
binding and neutral (ΔS = 0): 0
```

So, in this finite ledger:

```
Δd < 0  does not imply  ΔS < 0.
```

Examples:

- `opposite` pair + bit flip: `ΔS = -2`, `Δd = -1` — binding and contraction;
- `like` pair + bit flip: `ΔS = +2`, `Δd = -1` — binding and expansion.

The result is **not evidence about physics**. It is a logical test: if `ΔS` and `Δd` are independent
functions, closure-distance reduction does not determine spatial contraction. The physical bridge
must be derived, not assumed.

---

## 4. What this means for #286

#286 tests the gluon-specific contraction branch. Its GL2 move relation is still the blocker: the
repo proves when a gluon vertex/commutator is nonzero, but not which colour-state transitions are
allowed. A census of `d_G` cannot be honest until that relation is defined independently of distance.

The parent issue keeps the sign at the event/relation level. A gluon binding event may be a
contraction example; it is not the definition of contraction.

---

## 5. Scope closure

| gate | status |
|---|---|
| **SR0** definitions | **finite**; `S` and `d` independent |
| **SR1** electron/Pauli expansion | **cited**; physical reading interpreted |
| **SR2** singlet/binding contraction | **cited**; physical reading interpreted |
| **SR3** ΔS/Δd independence | **finite test**; implication fails in the toy |
| **SR4** aggregation / gravity | **out of scope**; follow-up #287; no coarse-graining or curvature claim |
| **SR5** propagation vs interaction | **out of scope**; follow-up #287; free carrier ≠ joint spatial response |
| **SR6** timing | **cited** #281; `d` and `f` separate |
| **SR7** 3D spatial relation | **out of scope**; follow-up #287; boolean ledger is not a 3D metric |

SR0–SR3 are the complete gates of this PR. SR4–SR7 are not open gates here; they are separate
follow-ups under #287.

Methods hygiene: DRAFT test ledger `claim_records/spatial_response_slice.json`; registry row in
`Open_Problems.md`; FlowChart entry in §1.

`Frequency_Synchronization.md` says a gluon creates local space. That remains a propagation reading,
not the sign of every gluon interaction; the wording correction is part of the SR5 follow-up, not this
finite slice.

---

## 6. What this does not claim

- No claim that electrons always expand space.
- No claim that gluons always contract space.
- No claim that gravity is derived.
- No claim that the boolean `netSpace` ledger is a physical 3D metric.
- No claim that logical distance equals physical separation.
- No change to #322 or the frozen AI experiment.

---

## 7. Reproduce

```bash
python3 spatial_response.py --self-test
python3 spatial_response.py --run
python3 -m unittest tests.test_spatial_response -v
```

The run writes `data/spatial_response_census.json`.

---

## 8. Links

- Issue #287 — parent spatial-response gates.
- Issue #286 — gluon closure dynamics (GL2 blocker).
- #281 — event timing: `tau_listen > 0`, `tau_event = 0`.
- #283/#284 — co-incidence: the sign belongs to the relation/event.
- #271 — closure uncertainty; no ΔS probability claim.
- `lean/QLF_MagneticOrientation.lean`, `lean/PauliExclusion.lean`,
  `lean/QLF_ElectronClosure.lean`, `lean/QLF_Confinement.lean`.
