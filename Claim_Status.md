# Claim status — what QLF claims, and at what approximation

This is the repository-side index for Paper I v0.3. It states each physical claim at the approximation or regime in which QLF makes it, records the provenance of the inputs, and gives the bridge/evidence status. It is an **inventory and status ledger**, not a claim that the physical results are established.

The numerical agreements below are as reported by QLF. The claim records in `claim_records/` carry the detailed fields; this table is the human-readable index.

| Claim | QLF result | Approximation / regime | Comparator | Reported agreement | Inputs | Bridge status | Evidence status |
|---|---|---|---|---|---|---|---|
| Fine-structure α | α⁻¹ = 137 leading; formal comparator-residual band `(1/64, 0.04814)`; reported structural 137.032 | Leading + structural; residual running not derived | CODATA | 0.026% (reported) | 8-twist count (derived); w = ½ (declared/structural); CODATA (external) | `B-OPEN`: count → renormalized coupling at a scale | Audited finite identities; `N` for leading arithmetic; physical bridge open |
| m_p/m_e | 6π⁵ | Structural; no QCD derivation | PDG | 0.002% (reported) | 3-quark/5-angle structure (declared/structural); PDG (external) | `B-OPEN` | Audited defined Lenz identity; reported numerical comparison |
| Electron anomaly `a_e = (g_e − 2)/2` | `alpha_QLF/(2π) = 1/(274π)`; `g_e − 2 = alpha_QLF/π` at one loop | One-loop Schwinger form; higher orders omitted | Reported electron anomaly | 0.18% (reported for model α = 1/137) | `alpha_QLF` derived within the model; measured anomaly external | `B-OPEN`: model coupling → measured coupling; algebraic form agrees with QED | Numerical consistency; no independent QLF confirmation |
| Ω_Λ | log 2 ≈ 0.693, reported late-epoch match | Observed numerical match; physical derivation open | Planck | 1.2% (reported) | Observed fraction external; H₀ calibrates the dimensionful cosmological sector, not log 2 itself | `B-OPEN`: count → physical dark-energy fraction | Reported numerical consistency; not a derived cosmological fraction |
| SPARC/RAR | a₀ = cH₀/2π; g² = g_bar(g + a₀); 0.1327 dex, mean −0.0002 dex | Non-relativistic equilibrium; canonical M/L; local H₀ | SPARC | 0.133 dex, mean −0.0002 dex (reported) | H₀ (declared); M/L (external); SPARC (external); a₀ (derived) | `B` for interpolation form; a₀ derived within model | `N` consistency benchmark; empirical support not established |
| Mercury perihelion | 42.99″/century | Weak-field; standard GR inputs | Ephemeris | 0.03% (reported) | M_☉, a, e, T (external) | `B`: holographic count → GR potential | `N` (consistency) |
| α cannot drift | Continuity plus membership in the discrete structural value set implies constancy | Conditional mathematical null; measured-coupling identification open | A future specified clock comparison | Pending | Measured-coupling/residual map not supplied | `B-OPEN`: structural α → measured α | proposed null test; registration incomplete |
| Born-rule characterization | `ProbAssignment` satisfying the stated symmetry/refinement conditions equals `bornProb` | Finite Gaussian-integer amplitude registers; interface assumptions explicit | Quantum probabilities | Structural; no detector experiment | Unit-way counts plus declared assignment rules | `B-OPEN`: physical realization of the assignment rules | Existing footprint coverage for `born_from_ways`/`assignment_unique`; no empirical promotion |

## Status vocabulary

- `F` — kernel-checked against declared axioms and a reviewed footprint.
- `F-CANDIDATE` — claim-scoped formal assurance remains incomplete (for example an absent anchor/baseline, unresolved theorem-to-claim correspondence or missing review receipt). The exact missing obligation must be named; this label does not imply every candidate lacks anchors.
- `N` — reproducible computation/enumeration with a declared independence tier.
- `B` / `B-OPEN` — interpretation depends on an explicit bridge; `OPEN` means the bridge is not yet specified/proved.
- `E` / `E-candidate` — empirical comparison; `candidate` means retrospective/self-sealed or not independently replicated.

## Strange-loop / two-phase bridge shape

A strange loop is a level-crossing self-reference that returns to its starting level. In the claim ledger it is a **review shape**, not a new evidence type: every bridge candidate must name its levels and the finite record to which it returns, or remain `B-OPEN`. The conceptual note is [`Strange_Loops.md`](Strange_Loops.md); the validator enforces the fields and the `TESTED`-for-`CLOSED` rule.

| Claim | Loop levels | Conservative return | Status |
|---|---|---|---|
| MO2 → optical apparatus | MO2 lattice → toy `ℂ²` embedding → ideal polarizer → detector | finite MO2 count/detector record; the `1/8` is imported Malus/Born, not derived | `B-OPEN`; G3 inconclusive |
| α count → coupling | 8-twist census → residual multiplicity → coupling at scale → CODATA | leading `137` and formal band `(1/64, 0.04814)`; `137.032` reported, scale map not proved | `B-OPEN` |
| SPARC RAR | public data → closure-balance RAR → `a₀ = cH₀/(2π)` → residual | retrospective residual summary only; no predeclared prediction | `N`; G5 open |
| Born uniqueness | Gaussian-integer register → unit-way refinement → ZFA closure → outcome | finite unit-way count; physical refinement is a premise | `F` formal; `B-OPEN` |

The four corresponding JSON records carry a `strange_loop` object with `name`, `levels`, `return_level`, `conservative_return`, `noncircularity_witness`, `status` and `defeater`, plus a `proof_obligation` naming the domain, codomain, forward/return maps, composite identity, conservative-return status, imported axioms and falsifier. MO2 and Born are `PARTIAL` with the toy Lean artifacts `QLF_StrangeLoop` and `QLF_StrangeLoopBorn`; α and SPARC remain `NOT_STARTED`. A `TESTED` loop requires `PROVED` plus a real artifact, and a `bridge: CLOSED` record requires a `TESTED` loop.

## Claim records

- `claim_records/alpha.json` — α claim record (draft).
- `claim_records/sparc_rar.json` — SPARC/RAR claim record (draft).
- `claim_records/kill_conditions.json` — draft falsification/test ledger; no completed preregistration is asserted.
- `claim_records/three_polarizer.json` — migrated finite/optical bridge record.
- `claim_records/born_rule.json` — scoped Born-assignment characterization.

## Related formal developments (not physical claims)

The current 319-anchor baseline also covers two formal developments that are **not**
rows in the physical-claims table and do not have physical `E` status:

- **Metric singlet / lattice Einstein equations** (PR #225; 5 anchors; three
  `QLF.MetricSinglet`, two `QLF.LatticeDivergence`). The exact statements are `F`
  under the stated premises. The physical reading of the metric, spacetime and
  gravity remains `B-OPEN`; the local Rindler/Raychaudhuri arrow and the
  substrate curvature are still open.
- **Manifestation** (PR #226; 12 anchors). Orientation, isolation-is-closure,
  unbounded closures, `distance_eq_delay`, and the proton as the simplest
  isolated imbalance are `F` as formal statements. Physical selection, a
  detector/apparatus map, and empirical adequacy remain `B-OPEN`/not established.
  See `Manifestation.md`.

These are claim-map and formal-coverage entries, not promotions of a physical
claim. A named theorem is not an `N` reproduction and not an `E` observation.

## Validation

```bash
python3 scripts/validate_claim_records.py
python3 -m unittest discover -s tests -p 'test_claim_records.py' -v
```

The validator discovers every JSON record recursively by explicit record type, checks nested content and source identifiers, and enforces the mandatory gate paths documented in `claim_records/README.md`. It cannot authenticate a receipt, prove chronological blinding, or establish physical truth.

## Related documents

- `Proof_Trust.md` — the axiom-footprint gate and its current coverage.
- `Proof_to_Physics.md` — the evidence registry and open bridges.
- `Manifestation.md` — the Manifestation formal results and their `B-OPEN` physical reading.
- `Einstein_Equations.md` §6d–§6e — the metric-singlet/lattice-Einstein representational result.
- `ScientificApproach.md` — the governing method, bridge grades, and pre-registration rules.
- `SPARC.md` — the retrospective public-data benchmark SPARC analysis and its receipt.
- Paper I v0.3 §2 — the manuscript's positive-claims table and prose.
