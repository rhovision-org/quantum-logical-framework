# Perspective Holography — nested-frontier falsification protocol (#296)

Base: `4311aad5fc5d93fdefaf038201126bedfa4bb730` (merged #305 following #300 and #304).

## Frozen finite surrogate and verdict rules

This screen extends the two-body record-map result to three independently tagged histories
(`A,B,C`). It is not a model of physical accessibility, interaction or a Planck-scale blanket.
Enumerate every word over the 24 tagged canonical twists with total length 0–3.
Retain the eight signed-twist counts through each body's integer action ledger and the
ordered Pauli fold. Build each view from its own projection: AB and BC, with B shared.
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

## Deviation from pre-registration — documented 2026-11-24

This is an **after-the-result disclosure**, not an amendment to the frozen protocol.
The original pre-registration at `dee8efc15b5c89395a7bbb988913ae80e20daa0f`
(2026-11-21 17:50:03 UTC) requires retaining all **eight per-body twist counts**
as well as the ordered Pauli fold. During implementation at
`872cdf65fc0a266f119dd3b2481cb4bd68981b46`
(2026-11-21 17:50:48 UTC), the actual record instead used
`territory_return.ledger`: **four signed net-action coordinates**, one per
axis, together with each body's fold. The change to the wording of the frozen
protocol in that implementation commit was improper; the original wording is
restored above without retroactively changing what was run.

The four-coordinate ledger maps each conjugate twist pair to its net
difference, `n(+axis) - n(-axis)`; it does **not** reconstruct the individual
eight twist counts. Therefore the observed **F1 B-ledger reconstruction**
establishes the *four-coordinate net ledger* only, **not** the frozen
eight-count record. The same restriction applies to the recorded F3
nested-view check: it is over net-ledger-plus-fold records, not the original
eight-count views. The original eight-count F1/F3 observations remain **not
executed** and are not claimed to pass.

This narrower record does **not** change the reported **territorial ZFA**
verdicts: for each body, count balance is exactly the requirement that all four
net coordinates vanish. F1's B-ZFA positive, F2's negative controls (including
the missing-body and fold-only collisions), and F3's *record-restriction*
result within the executed four-coordinate scope remain as observed.
F4's disjoint-face accounting is independent of the ledger. The F3 phrase
"sampled history" in the *frozen* rule is left unedited; execution in fact
enumerated all `1 + 24 + 24² + 24³ = 14,425` histories, as stated below.

This disclosure is a provenance correction, **not a new run**, a changed
pre-registered acceptance criterion, or a physical-claim promotion.
An eight-count replication is required before asserting the full frozen
count-level reconstruction claim.

## Result

The frozen F1–F4 checks ran over 14,425 tagged histories. Reproduce with
`python3 perspective_frontier.py` from the repository root; the deterministic output
is retained in [data/perspective_frontier.json](data/perspective_frontier.json).

| Gate | Observed result |
| --- | --- |
| F1 | Both views reconstruct B's **four-coordinate net ledger** and B's territorial ZFA; the originally frozen **eight-count** ledger was not tested. |
| F2 | A-only and C-only fail B's **four-coordinate net-ledger** reconstruction. AB/BC each fail global ZFA. B-fold fails B-ZFA with empty vs B:+. |
| F3 | Both independently constructed **four-coordinate net-ledger-plus-fold** views agree with the restriction of ABC on every **enumerated** history. Eight-count views were not tested. |
| F4 | Cumulative counts 1+2+3=6; disjoint increments 1+1+1=3 equals the terminal count. |

F1 and F3 are structural consequences of explicitly accessible tagged data, not
evidence that a physical boundary contains those data. F2 supplies the non-promotion
controls. F4 is an accounting identity, not a cosmological prediction. Stage D
remains B-OPEN pending a derived accessibility rule and a nonduplicating
physical face-ID map. No Lean proof is added by this experiment.

## Frozen eight-count replication — separate witness

The original four-coordinate run and disclosure above remain unchanged.
A separate CI test, `tests/test_perspective_frontier_eight.py`, implements the
original eight-count record over the same 14,425 tagged histories. It builds
each view independently, checks both nested restrictions for every word,
and checks positive and negative factorization cases against the full
eight-count observable. The additional negative control checks that even
net action plus exact fold does not reconstruct all eight counts.
F4 remains a separate face-set accounting check.

This is a replication protocol and executable test, not a reported result
until the pinned CI execution succeeds. No change to the frozen protocol,
historical JSON, or physical bridge status is implied.
