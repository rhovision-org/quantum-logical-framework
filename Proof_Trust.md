# Proof trust and reproducible verification

QLF distinguishes a theorem checked by Lean's kernel from a physical interpretation of
that theorem. Passing `lake build` establishes the former, not the latter.

## Verification gates

1. **Declared-axiom inventory.** `scripts/axiom_audit.sh` compares the project's
   explicit `axiom` declarations with `lean/axioms.expected`.
2. **Proof placeholders.** `scripts/proof_trust.py --scan-only` checks every Lean source
   for `sorry`, direct `Lean.sorryAx` use, and common `admit` tactic forms,
   ignoring comments, strings and the legitimate function named `admit`.
3. **Kernel dependencies.** The `#print axioms` statements in
   `lean/QLF_AxiomAudit.lean` report the actual axiom dependencies of selected
   anchor theorems. `scripts/proof_trust.py` compares every reported set to the
   exact reviewed baseline in `lean/axiom_footprints.expected.json`.
   Missing, duplicated, changed or unregistered anchors fail CI.
4. **Python source checks.** The Python workflow syntax-checks every tracked
   Python source and runs dependency-free regression tests.

The baseline includes standard Lean axioms when the kernel reports them
(`propext`, `Classical.choice`, `Quot.sound`) and names project-specific
bridge axioms where they are actually used. It is intentionally *not* a
blanket assumption that every theorem is axiom-free.

## Local commands

```bash
./scripts/axiom_audit.sh
python3 scripts/proof_trust.py --scan-only
python3 -m unittest discover -s tests -p 'test_*.py' -v
lake build
lake env lean lean/QLF_AxiomAudit.lean | tee /tmp/qlf_axiom_footprints.log
python3 scripts/proof_trust.py --log /tmp/qlf_axiom_footprints.log
```

`lake` is needed for the final two build-dependent commands. The Python
checks run without Lean or third-party Python packages.

## Changes requiring explicit review

Adding an anchor to `QLF_AxiomAudit.lean`, changing its dependencies, or
changing the declared-axiom inventory requires a reviewer to inspect both
the mathematical statement and its assumptions. After a successful Lean
build, regenerate the baseline deliberately:

```bash
python3 scripts/proof_trust.py --log /tmp/qlf_axiom_footprints.log --record
git diff -- lean/axiom_footprints.expected.json
```

Commit the manifest change together with the theorem change. Never run
`--record` as part of CI. A new dependency on a project axiom is not
automatically a defect, but it must not be silently reclassified as
assumption-free.

## Limits of this gate

- Exact axiom-footprint enforcement covers the explicit audit anchors, not
  every declaration in every Lean module. The placeholder scan covers
  all `lean/*.lean` files.
- The source scan is a lightweight lexer, not a full Lean syntax parser;
  a kernel audit remains authoritative for its listed theorems.
- `native_decide` and other evaluation mechanisms should be examined
  through the actual kernel dependencies, not inferred from source text.
- These gates do not prove that a closure count is a physical probability,
  a finite kernel is a scattering operator, or a mathematical parameter
  is an observed physical constant. Those require independent bridges and
  validation; see [Proof_to_Physics.md](Proof_to_Physics.md).
