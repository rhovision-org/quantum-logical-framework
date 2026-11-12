# Paper I v0.3 — scoped review and reproduction receipt

**Audited source:** `59b92e082a73ba8bccb48ce0597463b665da727b`.
This is a collaborator technical receipt for `aixaria0`, not independent physical
validation, publication approval or a cryptographically signed third-party certificate.

**Scope note (post-merge):** this receipt records the PR #224 **302-anchor**
closure. PR #225 later added five anchors (baseline **307**), PR #226 added
twelve (baseline **319**), and PR #230 added twenty-four conservative-return/
tensor-return anchors (baseline **343**); those deltas are recorded in their PRs
and in the current `lean/axiom_footprints.expected.json`. This receipt is not
rewritten.

## Kernel evidence and baseline

The original project job is
[42845773351 / 129932700521](https://github.com/rhovision-org/quantum-logical-framework/actions/runs/42845773351/job/129932700521),
for head `41182f739979227906cc1412e33f03be1ecba4f5`, tested as merge
`8cf63f32b3ede1fee696bfbd7de479a1c4549a39`. Its original `lake build` succeeded;
the separate audit printed 302 reports and its baseline comparison failed because
62 entries were missing. That historical failure is preserved in the archived
step output.

`ci-41182f7-axioms.log` is the original contiguous audit-step output after removing
GitHub prefixes. Multiline axiom reports are preserved. It is **not a local Lean
execution**. All Lean sources and the toolchain, lakefile, lockfile, gate script
and Lean workflow at the audited source were compared byte-for-byte against that
original CI source and were unchanged.

The reviewed `--record` operation ran outside CI. It added 62 entries (17 MO2,
18 QuantumLogic, 27 further anchors), changed none of the old 240 sets, and the
normal exact-footprint check then passed for all 302 anchors. New sets contain
only standard Lean axioms or no axioms. `baseline_delta.json` records the delta.
The subsequent regression build on the PR head is a separate CI run; inspect
its actual conclusion rather than treating these archived results as its result.

## Numerical execution

`receipt.json` records Python/architecture, execution time, source-file digests,
the original kernel evidence and hashes of the numerical artifacts.

- `mo2_results.json`: all 19 finite checks; 15 comparable pairs; 36 orthomodular
  implications (15 non-vacuous); 24 distributive failures in each direction.
- `alpha_arithmetic.json`: leading `1/137` model arithmetic and comparison with a
  fixed reported comparator. The structural residual/running is not re-derived.
- `sparc_receipt.json` / `sparc_run.log`: 147 galaxies, 2696 points; unchanged
  numerical scores and byte-identical prediction CSV. Metadata now describes
  target-informed selection and a seal before residual scoring, not a controlled
  first reveal of Vobs. No per-galaxy QLF fit is performed by this script.

The record validator checks the local receipt references against their digests;
regression tests also check this receipt's artifact manifest. Hash agreement does
not establish issuer authenticity, a trusted timestamp or prior data isolation.

## Current action boundary

The finite formal component can have VERIFIED status at the declared collaborator
assurance tier while the measured-coupling, probability and detector bridges remain
OPEN and empirical status remains NOT_ESTABLISHED. All falsification entries remain
DRAFT until an operational specification and pre-exposure chronology are documented.

Run the normal commands; never auto-record a new baseline in CI:

```bash
python3 scripts/validate_claim_records.py
python3 -m unittest discover -s tests -p 'test_*.py' -v
python3 scripts/proof_trust.py --scan-only
./scripts/axiom_audit.sh
lake build
set -o pipefail
lake env lean lean/QLF_AxiomAudit.lean | tee qlf_axioms.log
python3 scripts/proof_trust.py --log qlf_axioms.log
```

The full manuscript is a separate review draft. Human authorship, conflicts,
license and final circulation require agreement. This receipt does not reopen the
separate Paper II discussion.

— Ω-WITNESS
