# D8c2 under D3T: result

Part of [Quantum Logical Framework (QLF)](README.md). Issue
[#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290). The test was frozen in
[`Diversity_Advantage_D8c2_Prereg.md`](Diversity_Advantage_D8c2_Prereg.md) at commit `c683f60`,
before [`d8c2_census.py`](d8c2_census.py) existed. Reproduce with `python3 d8c2_census.py`. The
output is [`data/d8c2_census.json`](data/d8c2_census.json), and
[`tests/test_d8c2_census.py`](tests/test_d8c2_census.py) is the regression test.

**Registered verdict: PASS (D8c2).** The pass is carried by one stratum and, by construction, only by
the per-stream phase label (§3). So it does not establish a diversity advantage in continuation
richness. Grade **N** (finite census), for these two panels only.

---

## 1. Primary result (as registered)

Measure: `K = |C_T(a)|`, the number of distinct boundary records of admitted extensions, `|b| ≤ k`.

| stratum (panel, per-stream \|net\|₁) | homogeneous n, mean K | heterogeneous n, mean K | sign |
|---|---|---|---|
| A, {1,2} | 48, 1 | 720, 7/5 | + |
| B, {1,1} | 672, 1 | 4,032, 1 | 0 |
| B, {1,3} | 64, 0 | 4,032, 0 | 0 |
| B, {2,2} | 888, 0 | 2,448, 0 | 0 |

The weighted difference is `Δ = 12/1045 ≈ 0.0115 > 0`, and no stratum is negative.

Nulls:

- **N1, no provenance (pooled):** `Δ = −23/55`. The signs are −, 0, −, −, so homogeneous bases are
  *richer* when streams may pool. This differs from `R_T`, which is the condition the rule requires
  for a PASS.
- **N2, no first closure:** identical to `R_T` in every stratum. The typed first-closure condition
  removes nothing in these panels.

By the decision table this is **PASS (D8c2)**. Reading the extension bound as `|b| = k`, as the D3T
census code enumerates it, gives identical numbers. That reading was registered as a sensitivity
check only.

## 2. Where the panel runs out

In panel B, the strata {1,3} and {2,2} have `K = 0` in both populations. With an extension bound of
2, no two-stream extension can answer a per-stream obligation of total size 4. These strata are
eligible under the registered rule, but they measure the bound, not diversity. Stratum {1,1} is tied
at `K = 1`. All of the positive weight comes from panel A, {1,2}.

## 3. What `K` can measure under `R_T` (found after the run)

`R_T` admits an extension only if its phase-free boundary key equals the complement of the base's
key (`obligations_match`). So every admitted extension of a base has the **same** net and axis
record, and `C_T(a)` can vary only through the per-stream **phase labels** of its records. The
post-hoc diagnostic `diag_R_T_no_phase_label` confirms this: with the label dropped, `K` is 0 or 1
in every stratum, and `Δ = 0`.

So the registered PASS says that, in stratum A {1,2}, the streams that answer a disjoint-support base
carry more distinct per-stream phase labels (mean 7/5) than those answering an equal-support base
(mean 1). The pre-registration put the closure phase out of scope (§1 there), but it kept D3T's `B(b)`
as the measure, and `B(b)` includes the per-stream phase. That was a design gap in the
pre-registration. It is recorded here, and the registered verdict is not changed.

A second post-hoc diagnostic counts admitted extensions instead of distinct records
(`diag_R_T_raw_admitted`). It favours heterogeneous bases in A {1,2} (27/5 vs 3) and B {1,1} (2 vs
1). Raw counts are not the registered measure, and #293 showed that raw counts alone are not a
diversity metric, so this does not change the verdict either.

## 4. Reading

- **Registered outcome:** PASS (D8c2), at grade N, on two finite panels.
- **What it supports:** under per-stream (no-pooling) matching, complementary obligations are answered
  by streams with more varied per-stream phase. This difference comes from provenance: pooling (N1)
  reverses the sign.
- **What it does not support:** a diversity advantage in *which obligations* can be answered. Under
  `R_T` that is fixed by the base. Where the profile can genuinely vary (N1), homogeneous bases come
  out ahead in three of four strata, the same direction as #297.
- **Incomplete, not settled:** both panels are shallow (`L ≤ 4`, `k ≤ 3`), and two of the four strata
  sit at the extension-bound floor.

**What would decide it.** The next relation needs a profile with genuine freedom in what answers a
base, so that `K` does not collapse to phase labels, while keeping provenance. One option is pooling
restricted to matched provenance classes. It needs its own pre-registration, with the phase label
either excluded from the record or registered as the observable. It must also use an extension bound
that clears the floor (`k ≥` the largest per-stream \|net\|₁ sum in the panel). D9 (persistence)
stays closed until a D8c2 pass that is not measure-limited.
