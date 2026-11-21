# Perspective Holography — nested-frontier falsification protocol (#296)

Base: `4311aad5fc5d93fdefaf038201126bedfa4bb730` (merged #305 following #300 and #304).

## Frozen finite surrogate and verdict rules

This screen extends the two-body record-map result to three independently tagged histories
(`A,B,C`). It is not a model of physical accessibility, interaction or a Planck-scale blanket.
Enumerate every word over the 24 tagged canonical twists with total length 0–3.
Retain the four signed net-action coordinates for each body and its ordered Pauli fold. Build each view from its own projection: AB and BC, with B shared.
Use per-body folds, not only their tensor product; this is a deliberately stronger,
tagged surrogate record, not a derivation of its physical availability.

- F1: both views must reconstruct the shared body's signed ledger and count-balanced
  verdict; any collision with unequal values rejects the candidate for that observable.
- F2: a view containing only A or only C must fail to reconstruct B's ledger; each AB/BC
  view must fail to determine full three-body ZFA when a hidden body can change.
  A fold-only B view must fail territorial ZFA (empty versus gauge +).
- F3: restriction from ABC to AB and BC must recover each independently built record
  for every sampled history. This is a nested *record* property, not expansion.
- F4: nested cumulative face sets are not additive without disjoint increments.
  Use finite face-ID sets as a separate accounting surrogate; reject summing cumulative
  cardinalities if overlap creates a double count. Distinct face IDs and truly disjoint
  increments are necessary for an additive count.

Only finite computational evidence is in scope. No new Lean theorem is asserted.
The existing [Planck-scale theorem](lean/QLF_PlanckScale.lean) yields the strict bound
on coherent radii under its stated premises; equality is the self-dual boundary,
not an attained strictly coherent minimum. It does not itself derive a physical
boundary tessellation, a causal observer map, finiteness of an arbitrary universe,
or a sum over horizon faces. The identity for nested counts requires a disjoint
partition of the terminal frontier into increments and a physical face-identification
map. The continuum-area expression and entropy normalization remain conditional;
see [Cosmological Constant](Cosmological_Constant.md) and [Holographic](Holographic.md).
Do not promote Omega_Lambda = log 2 from numerical coincidence to a dynamical result.

## Result

The frozen F1–F4 checks ran over 14,425 tagged histories. Reproduce with
`python3 perspective_frontier.py` from the repository root; the deterministic output
is retained in [data/perspective_frontier.json](data/perspective_frontier.json).

| Gate | Observed result |
| --- | --- |
| F1 | Both views reconstruct B's ledger and B's territorial ZFA. |
| F2 | A-only and C-only fail B-ledger reconstruction. AB/BC each fail global ZFA. B-fold fails B-ZFA with empty vs B:+. |
| F3 | Both independently constructed views agree with the restriction of ABC on every sampled history. |
| F4 | Cumulative counts 1+2+3=6; disjoint increments 1+1+1=3 equals the terminal count. |

F1 and F3 are structural consequences of explicitly accessible tagged data, not
evidence that a physical boundary contains those data. F2 supplies the non-promotion
controls. F4 is an accounting identity, not a cosmological prediction. Stage D
remains B-OPEN pending a derived accessibility rule and a nonduplicating
physical face-ID map. No Lean proof is added by this experiment.
