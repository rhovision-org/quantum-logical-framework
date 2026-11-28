# Lepton mass ratios, Stage B: what can the admissible observables carry? (#140)

Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF. Issue #140 asks for the
charged-lepton mass ratios from closure data. [Lepton_Mass_Ratio_Protocol.md](Lepton_Mass_Ratio_Protocol.md)
freezes the rules: the three rungs `e = ^<v>`, `μ = ^^<vv>`, `τ = ^^</>vv\`, the Koide form
`m_i = M (1 + √2 cos(δ + 2πi/3))²` as the only admissible functional, and a list of admissible closure
observables (§4). Its Stage B asks for `δ` from closure counts, or a record that none exists. This
note runs the step that comes first: a noncircular mass map can only use what the admissible
observables distinguish, so it asks what they distinguish.

## §1 Pre-registration (committed before the companion script was run)

No muon or tau mass is read in this note.

### Tests

The observables are the protocol's §4 list, computed by the functions of
[`lepton_blind_classifier.py`](lepton_blind_classifier.py) on the three frozen representatives: axis
content, first-return depth `L`, fold sign, rooted baryon winding `B`, and orbit multiplicity (the size
of the class under signed spatial-axis permutations and particle/antiparticle).

| | Claim under test | Passes if | Prior |
|---|---|---|---|
| L1 | the table | the five observables are computed for each rung | axes `2, 2, 3`; `L = 4, 6, 8`; fold `−I`; `B = 0`; orbit `24, 48, 96` |
| L2 | which observables separate the rungs | only `L` and the orbit multiplicity take three distinct values | pass |
| L3 | the separating observables are one integer | on the ladder, orbit `= 24 · 2^k` and `L = 4 + 2k` with `k = 0, 1, 2` | pass |
| L4 | no per-rung datum beyond the index | every function of the §4 observables on the three rungs is a function of `k` | pass if L2 and L3 pass |

**Verdict rule.** If L2 to L4 pass, the per-rung admissible data are equivalent to the generation
index `k`, so a mass map built from them can name the rungs but cannot supply any number that
differs between them except through `k`. The three masses then carry two numbers from outside the
per-rung data, a scale `M` and a phase `δ` common to all rungs, which is the Koide shape. So `δ` has
to be a global quantity. Two global routes are already closed: a finite closure phase cannot be a
nonzero rational number of radians ([Weak_Force.md](Weak_Force.md) §5c⁗ item 7), and the census-limit
`P` is certified not to reach `2/3` ([Bridge_Tools.md](Bridge_Tools.md)). Under the protocol's §3 rule
this attempt then has no ratio prediction, and the next attempt needs an admissible observable that is
not a function of `k`. If L3 fails, the separating observables carry more than the index, and Stage B
continues with them.

## §2 Results

Run by [`lepton_stage_b.py`](lepton_stage_b.py); output in
[`data/lepton_stage_b.json`](data/lepton_stage_b.json). The closure facts are proved in
[`lean/QLF_LeptonStageB.lean`](lean/QLF_LeptonStageB.lean), no QLF axioms.

| rung | word | axes | depth `L` | fold | `B` | orbit |
|---|---|---|---|---|---|---|
| e | `^<v>` | 2 | 4 | `−I` | 0 | 24 |
| μ | `^^<vv>` | 2 | 6 | `−I` | 0 | 48 |
| τ | `^^</>vv\` | 3 | 8 | `−I` | 0 | 96 |

| | Result | Verdict |
|---|---|---|
| L1 | the table above; each rung is first-return (`rung_balanced`, `rung_first_return`) | pass |
| L2 | only depth and orbit take three distinct values; fold and `B` are constant (`rung_fold`), axes split `{e, μ}` from `τ` | **pass** |
| L3 | orbit `= 24 · 2^k`, `L = 4 + 2k` (`rung_length`) | **pass** |
| L4 | every function of the five observables on the ladder is a function of `k` | holds, but as bookkeeping: on any three distinguishable rungs every datum is a function of the index, so L4 could not have failed. The content is L3 |

**Verdict.** L3 carries the result. The separating observables are not three independent numbers;
they are one progression with fixed constants, the orbit doubling and the length growing by two per
rung. So the per-rung admissible data contain no number beyond `24`, `2` and `4`, and a mass map
built from them is `m_k = F(k)` with `F` assembled from those constants. That is the Koide shape the
protocol froze: a scale `M` and one phase `δ` common to all rungs, with the rung entering only as
`2πk/3`. The axis split `2, 2, 3` adds nothing, since it was a declared input of the `τ` selection.

`δ` therefore has to be a global quantity. The two global routes tried so far are closed: no finite
closure phase is a nonzero rational number of radians, and the census-limit `P` stays below
`0.1933`. Under the protocol's §3 rule this attempt has no ratio prediction.

The next attempt needs an admissible observable that breaks the progression, which means adding
one to the protocol's §4 list before any comparison. One candidate is already computed: the parent
edges between consecutive rungs are `192` and `96` ([`lepton_blind_classifier.py`](lepton_blind_classifier.py)
part G1), halving where the orbit doubles, so they are not generated by the orbit progression. It is
named here as a candidate only; adding it is a protocol change and has to be frozen before a Stage C.
