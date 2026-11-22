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

To be filled from `lepton_stage_b.py` after this section is committed.
