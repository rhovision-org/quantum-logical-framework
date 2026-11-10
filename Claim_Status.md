# Claim status — what QLF claims, and at what approximation

This is the repository-side index for Paper I v0.3. It states each physical claim at the approximation or regime in which QLF makes it, records the provenance of the inputs, and gives the bridge/evidence status. It is an **inventory and status ledger**, not a claim that the physical results are established.

The numerical agreements below are as reported by QLF. The claim records in `claim_records/` carry the detailed fields; this table is the human-readable index.

| Claim | QLF result | Approximation / regime | Comparator | Reported agreement | Inputs | Bridge status | Evidence status |
|---|---|---|---|---|---|---|---|
| Fine-structure α | α⁻¹ = 137 leading; bracket 137 < α⁻¹ < 137.048; structural 137.032 | Leading + structural; residual running not derived | CODATA | 0.026% (reported) | 8-twist count (derived); w = ½ (declared/structural); CODATA (external) | `B-OPEN`: count → renormalized coupling at a scale | `F-CANDIDATE` + `N` (retrodiction) |
| m_p/m_e | 6π⁵ | Structural; no QCD derivation | PDG | 0.002% (reported) | 3-quark/5-angle structure (declared/structural); PDG (external) | `B-OPEN` | `F-CANDIDATE` + `N` |
| g − 2 | α/(2π) (Schwinger) | One-loop QED | PDG | 0.18% (reported) | α (external) | `B`: standard QED, not QLF-specific | `N` (consistency) |
| Ω_Λ | log 2 ≈ 0.693 | Late-time; H₀ calibration | Planck | 1.2% (reported) | H₀ (declared/calibrated) | `B`: calibration | `N` |
| SPARC/RAR | a₀ = cH₀/2π; g² = g_bar(g + a₀); 0.133 dex, zero offset | Non-relativistic equilibrium; canonical M/L; local H₀ | SPARC | 0.133 dex, mean −0.0002 dex (reported) | H₀ (declared); M/L (external); SPARC (external); a₀ (derived) | `B` for interpolation form; a₀ derived within model | `N` / `E-candidate` (retrospective blind) |
| Mercury perihelion | 42.99″/century | Weak-field; standard GR inputs | Ephemeris | 0.03% (reported) | M_☉, a, e, T (external) | `B`: holographic count → GR potential | `N` (consistency) |
| α cannot drift | α(d) = 1/(128 + d²), no time argument | Structural null | Nuclear-clock bounds | Pending | — | `B`: formula → α | `E-candidate` (pre-registered null) |
| Born rule | Ratio of integer closure-path counts | Finite counting | Quantum probabilities | Structural | Closure counts (derived) | `F`/`B`: probability bridge open | `F-CANDIDATE` + `B-OPEN` |

## Status vocabulary

- `F` — kernel-checked against declared axioms and a reviewed footprint.
- `F-CANDIDATE` — source-inspected and/or authors' CI, but the theorem-specific `#print axioms` anchor or baseline entry is missing.
- `N` — reproducible computation/enumeration with a declared independence tier.
- `B` / `B-OPEN` — interpretation depends on an explicit bridge; `OPEN` means the bridge is not yet specified/proved.
- `E` / `E-candidate` — empirical comparison; `candidate` means retrospective/self-sealed or not independently replicated.

## Claim records

- `claim_records/alpha.json` — α claim record (draft).
- `claim_records/sparc_rar.json` — SPARC/RAR claim record (draft).
- `claim_records/kill_conditions.json` — pre-registered nulls and kill conditions.
- `claim_records/three_polarizer.json` — three-polarizer record (to be migrated from Paper I v0.2).

## Validation

```bash
python3 scripts/validate_claim_records.py
python3 -m unittest discover -s tests -p 'test_claim_records.py' -v
```

The validator checks schema completeness and rejects illegal promotions (for example, `formal = VERIFIED` without G1 `PASS`, or `empirical = ESTABLISHED` without G3/G5 `PASS`). It is not a truth checker.

## Related documents

- `Proof_Trust.md` — the axiom-footprint gate and its current coverage.
- `Proof_to_Physics.md` — the evidence registry and open bridges.
- `ScientificApproach.md` — the governing method, bridge grades, and pre-registration rules.
- `SPARC.md` — the retrospective blind SPARC analysis and its receipt.
- Paper I v0.3 §2 — the manuscript's positive-claims table and prose.
