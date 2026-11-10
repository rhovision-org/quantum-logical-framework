# Claim status — what QLF claims, and at what approximation

This is the repository-side index for Paper I v0.3. It states each physical claim at the approximation or regime in which QLF makes it, records the provenance of the inputs, and gives the bridge/evidence status. It is an **inventory and status ledger**, not a claim that the physical results are established.

The numerical agreements below are as reported by QLF. The claim records in `claim_records/` carry the detailed fields; this table is the human-readable index.

| Claim | QLF result | Approximation / regime | Comparator | Reported agreement | Inputs | Bridge status | Evidence status |
|---|---|---|---|---|---|---|---|
| Fine-structure α | α⁻¹ = 137 leading; bracket 137 < α⁻¹ < 137.048; structural 137.032 | Leading + structural; residual running not derived | CODATA | 0.026% (reported) | 8-twist count (derived); w = ½ (declared/structural); CODATA (external) | `B-OPEN`: count → renormalized coupling at a scale | `F-CANDIDATE` + `N` (retrodiction) |
| m_p/m_e | 6π⁵ | Structural; no QCD derivation | PDG | 0.002% (reported) | 3-quark/5-angle structure (declared/structural); PDG (external) | `B-OPEN` | `F-CANDIDATE` + `N` |
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

## Claim records

- `claim_records/alpha.json` — α claim record (draft).
- `claim_records/sparc_rar.json` — SPARC/RAR claim record (draft).
- `claim_records/kill_conditions.json` — draft falsification/test ledger; no completed preregistration is asserted.
- `claim_records/three_polarizer.json` — migrated finite/optical bridge record.
- `claim_records/born_rule.json` — scoped Born-assignment characterization.

## Validation

```bash
python3 scripts/validate_claim_records.py
python3 -m unittest discover -s tests -p 'test_claim_records.py' -v
```

The validator discovers every JSON record recursively by explicit record type, checks nested content and source identifiers, and enforces the mandatory gate paths documented in `claim_records/README.md`. It cannot authenticate a receipt, prove chronological blinding, or establish physical truth.

## Related documents

- `Proof_Trust.md` — the axiom-footprint gate and its current coverage.
- `Proof_to_Physics.md` — the evidence registry and open bridges.
- `ScientificApproach.md` — the governing method, bridge grades, and pre-registration rules.
- `SPARC.md` — the retrospective public-data benchmark SPARC analysis and its receipt.
- Paper I v0.3 §2 — the manuscript's positive-claims table and prose.
