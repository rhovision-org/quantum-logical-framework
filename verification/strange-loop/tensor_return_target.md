# TensorConservativeReturn — theorem target

**Status:** `PROVED` as a quotient construction in `lean/QLF_TensorConservativeReturn.lean` (`tensorTrigger_exists`, `tensor_conservative_return`). The theorem is in the 375-anchor reviewed baseline and does not by itself close the tensor bridge.

## Why

`QLF_TensorFromClosure` derives the tensor product for independent bodies from three premises:

1. each body has its own QLF fold;
2. the joint fold is multiplicative;
3. events belonging to distinct independent bodies have no relative order.

From interleaving invariance it derives commutation and the universal property
`composite_is_tensor`; the two-body realization is `tensorEquiv`, and the `N`-body
versions are `n_composite_is_tensor` / `nTensorEquiv`.

The tensor product is therefore not assumed for the independent sector. The
remaining question is the strange-loop one: what does the return map recover?

## What is proved

`QLF_TensorConservativeReturn` defines the quotient of two-body histories by
equality of the tensor image

```
w ~ w'  iff  fold(projA w) ⊗ fold(projB w) = fold(projA w') ⊗ fold(projB w').
```

`F` maps a class to its tensor image; `R` chooses a class from an image;
`R ∘ F = id` is proved on classes. `class_of_step` shows that interleaving moves
land in the same class. `tensorTrigger_exists` instantiates
`QuotientStrangeLoopTrigger`.

What this establishes is the **coherence of the quotient return**. What it does
not establish is that this quotient is the physically selected closure
equivalence, or that the entangled sector returns a shared closure. Those remain
open, and every actual bridge record stays `B-OPEN`.

## Target

```
TensorConservativeReturn :
  QuotientStrangeLoopTrigger
```

with:

- `Core` = finite closure classes, not raw words;
- `Tensor` = `M ⊗[ℂ] M` or the `N`-body tensor algebra;
- `coreEquiv` = physical closure equivalence;
- `forward` = the map induced by `composite_is_tensor` / `n_composite_is_tensor`;
- `ret` = the closure-class invariant read from the tensor representation;
- `forward_respects` = the forward map is well-defined on classes;
- `composite_id_on_quotient` = `ret (forward c) ~ c`.

The quotient is required. `pair_scalar_ambiguity` shows:

```
(-I) ⊗ I = I ⊗ (-I)
```

so a literal `R (F (h_A, h_B)) = (h_A, h_B)` is false. The return must be on
physical equivalence classes, not syntax.

## What counts as a proof

A Lean theorem instantiating `QuotientStrangeLoopTrigger` with the actual tensor
algebra, using the existing `composite_is_tensor` / `tensorEquiv` results, and
proving `composite_id_on_quotient`. **This is now done at the quotient level**;
the physical selection of the equivalence and the entangled-sector return remain
open. The theorem is in the 375-anchor baseline.

## Non-goals

- Recovering the raw pair of factors. `pair_scalar_ambiguity` rules this out.
- Proving the entangled-sector shared-closure return. That is a separate target.
- Claiming physical validation or closing G3.
- Adding a `sorry` or an axiom to make the target look proved.

## Entangled sector

The next target after the product sector is a shared-closure return:

```
primitive shared/independent closure relations
        ↓
H_A ⊗ H_B
        ↓
product or entangled state
        ↓
closure-class invariants
```

An entangled state is acceptable as a QLF rendering only when its return identifies
an irreducible shared closure rather than two independently closed factors. The
singlet is the worked example; it is not proved here.

## Relation to the claim records

This target is formal-only. It does not change `evidence_status.bridge = OPEN`,
`strange_loop.status = B-OPEN`, the `G3 = INCOMPLETE` or `G5 = INCOMPLETE` gate
outcomes, or the 375-anchor baseline. The theorem is in the reviewed baseline;
the tensor bridge still remains a **near-complete conservative bridge**, not a
closed physical bridge.
