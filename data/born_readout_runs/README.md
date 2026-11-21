# Born readout survey: evidence bundle

Part of the [Quantum Logical Framework (QLF)](../../README.md). This bundle is the reproducible record
behind the counts in [`Born_Readout_Criterion.md`](../../Born_Readout_Criterion.md) §1 and §5a. It was
produced by [`born_readout_certified.py`](../../born_readout_certified.py) at commit `15ee9ab`. That
commit is in main through PR #245, and the three source files are unchanged since.

## What was run

Every rule below was rerun from scratch with fresh checkpoints, using the source files whose SHA-256
hashes appear in `manifest.json` under `provenance_header.sources`. Environment: Python 3.13.18,
numpy 2.5.3, sympy 1.14.0, Linux x86_64, 4 worker processes.

```
python3 born_readout_certified.py --selftest
python3 born_readout_certified.py --R <rule> --procs 4 --checkpoint <rule>.jsonl
```

The nine rules: `l1:1`, `l1:2`, `l1:3`, `split:1,1`, `split:2,1`, `split:3,1`, `split:2,2`,
`split:2,3` and `linf:1`.

## Files

| file | contents |
|---|---|
| `<rule>.log` | complete program output, with start and finish times (UTC) |
| `<rule>.pairs.csv` | one row per absorbing target pair (820 per rule): the certified annihilator degree, the number of primes, and the verdict counts over its geometries |
| `selftest.log` | the exact disk test against 3,000 polynomials with prescribed roots |
| `manifest.json` | the provenance header shared by every checkpoint (seed, geometry-set hash, source hashes), the environment, the totals per rule, and the SHA-256 and size of each full checkpoint |
| `SHA256SUMS` | hashes of every file in this directory |

The full per-geometry checkpoints (about 170 MB) are not committed. Their hashes are in
`manifest.json`, and rerunning a rule with the commands above regenerates its checkpoint. The
`.pairs.csv` files add up to every total in §1 and §5a.

## Totals (summable / marginal of 180,288 geometries)

| rule | summable | marginal |
|---|---:|---:|
| `l1:1` | 7,112 | 0 |
| `l1:2` | 1,536 | 1,656 |
| `l1:3` | 0 | 0 |
| `split:1,1` | 7,744 | 8,230 |
| `split:2,1` | 0 | 0 |
| `split:3,1` | 0 | 0 |
| `split:2,2` | 0 | 0 |
| `split:2,3` | 0 | 0 |
| `linf:1` | 496 | 4,492 |

These match the counts in the doc exactly. They are certified computations by an inspectable
deterministic program; no one has independently reproduced the survey.
