# Does a diverse library of closures assemble more cheaply? (result)

Part of [Quantum Logical Framework (QLF)](README.md). Issues
[#264](https://github.com/rhovision-org/quantum-logical-framework/issues/264) and
[#290](https://github.com/rhovision-org/quantum-logical-framework/issues/290). The test was frozen in
[`Library_Diversity_Assembly_Prereg.md`](Library_Diversity_Assembly_Prereg.md) at commit `69a09ef`,
before [`library_diversity_census.py`](library_diversity_census.py) existed. Reproduce with
`python3 library_diversity_census.py` (about four minutes on four cores). The output is
[`data/library_diversity_census.json`](data/library_diversity_census.json), and
[`tests/test_library_diversity_census.py`](tests/test_library_diversity_census.py) is the regression
test.

**Registered verdict: PASS (ZFA), coverage-only.** At equal size, a library of closed parts spread
over several axes saves more joins than one concentrated on one axis, in 25 of 28 strata, with 3 ties
and none against. The whole advantage is **redundancy in the homogeneous library**: parts on one axis
duplicate each other's help, and parts on different axes add up exactly (§2). There is no
cooperation between parts on different axes. The closure rule plays almost no part (§3). Grade
**N** (finite census), for these panels only.

---

## 1. Primary result (as registered)

The saving is `S(w | L) = a_ZFA(w) − a_ZFA(w | L)`, averaged over every count-balanced target of
length `n` and over every library in the group. `Δ_s = S̄_div − S̄_hom` per stratum, and `Δ` is the
unweighted mean over the 28 strata.

| quantity | value |
|---|---|
| `Δ` (primary) | `344143/170347520 ≈ 0.00202` joins per target |
| stratum signs | 25 `+`, 3 `0`, 0 `−` |
| `Δ` under N1 (ordinary assembly) | `49209/24335360 ≈ 0.00202` |
| `Δ_cov` (saving per covered target) | `≈ −0.0253` |

Selected strata (mean saving per target):

| panel, k, shapes, n | homogeneous | diverse | `Δ_s` |
|---|---|---|---|
| A, 2, `DD`, 6 | 147/512 | 771/2560 | 9/640 |
| A, 2, `DD`, 8 | 1525/4753 | 16249/47530 | 999/47530 |
| B, 3, `BNN`, 8 | 321/9506 | 1367/38024 | 83/38024 |
| B, 2, `AB`, 6 | 113/5120 | 113/5120 | 0 |

The effect is largest with the two-letter parts of panel A (about 6% of the homogeneous saving at
`n = 8`) and small with the four-letter parts of panel B, which occur in about 1% of targets.

By the decision table this is a **PASS**. N1 does not give the same signs in every stratum (B, 2,
`BB`, 8 is `+` under the closure rule and `0` under ordinary assembly), so the frozen rule labels it
**ZFA**. `Δ_cov < 0`, so the frozen rule also labels it **coverage-only**: the diverse library saves
more in total because its parts occur in more targets, not because it saves more where it occurs.

## 2. What carries the advantage (an identity plus one census fact)

Write the saving of a library as the sum of its parts' single savings plus a **synergy** term
(registered as a descriptor in the pre-registration, §6):

$$
S(w \mid L) = \sum_{p \in L} S(w \mid \{p\}) + \mathrm{syn}(w \mid L).
$$

The two groups in a stratum have the same shapes, and the alphabet's symmetries (axis permutations
and conjugation) carry any part to any other part of its shape. So the summed single savings are
equal in the two groups, and

$$
\Delta_s = \overline{\mathrm{syn}}_{\mathrm{div}} - \overline{\mathrm{syn}}_{\mathrm{hom}}.
$$

That is an identity of the design. The census fact is the value of the two terms:

- **Diverse synergy is exactly 0** in all 28 strata.
- **Homogeneous synergy is negative** in 25 strata and 0 in the 3 tied ones.

So `Δ_s = −syn_hom`. A post-hoc check (not a decision input, run after the result was seen) looks
at each target separately. For every diverse library and every target, the saving equals the sum of
the single savings exactly. For homogeneous libraries most nonzero cases are sub-additive (3,996
targets for `+-, -+` at `n = 8`), but a few are **super-additive**: 2 to 6 targets per library at
`n = 8` in the panel-B strata, where two same-axis parts build something together that neither
saves alone. In these panels, cooperation between parts exists only **within** an axis, and it is
far outweighed there by overlap. Parts on one axis share letters, so they occur in the same targets and overlap
there (`^v^` contains both `^v` and `v^`). A join saved by one is often a join the other would have
saved. Parts on different axes share no letters, and here their savings simply add.

Diversity therefore helps assembly in these panels only in the sense that **redundancy costs**. No
stratum shows parts on different axes helping more together than apart. That positive synergy would
be the complementarity the diversity hypothesis is usually after, and the census does not find it.

## 3. The closure rule plays almost no part

N1 replaces the closure-constrained index with ordinary assembly, where every built object is
reusable. Its `Δ` agrees with the primary to three significant figures, and its signs agree in 27
of 28 strata. The single difference is B, 2, `BB`, 8, where the primary `Δ_s` is `1/23765` (one
join in the whole stratum). The registered label is **PASS (ZFA)**, because the frozen rule asks for
identical signs. In substance the advantage is the same with or without the closure rule, and it
should be read as **not ZFA-specific**.

## 4. Reading

- **Registered outcome:** PASS (ZFA), coverage-only, grade N, two panels, `n ∈ {6, 8}`.
- **What it supports:** at equal size, parts spread over axes waste less than parts on one axis,
  because same-axis parts duplicate each other's savings.
- **What it does not support:** that parts on different axes cooperate. Diverse synergy is exactly
  zero. It also does not support a closure-specific effect (§3), selection of diverse libraries, or
  anything about abundance.
- **Open:** mixed-axis parts (such as `^<v>`), open parts that are used up, larger libraries and
  longer targets. The only positive synergy seen is between parts on the **same** axis (§2).
  A test of cooperation across axes would need parts that can build each other, for example
  mixed-axis parts. That needs its own pre-registration.

Together with D8c2 ([`Diversity_Advantage_D8c2.md`](Diversity_Advantage_D8c2.md)), this is the second
registered diversity PASS that turns out to be carried by something narrower than the hypothesis:
there, per-stream phase labels; here, the absence of redundancy.
