# The No-Continuum Conjecture: straight-line histories and census coherence

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**The question (Jim, 2026-11-02).** *"Is it worthwhile to relate electron interaction to rogue waves
that are the rule rather than the exception in QLF? Perhaps the failure of the straight line law is the
story. Can we resurrect a version of the conjecture that denies a continuum?"*

**Short answer.** Yes, with one qualification. The repository has denied the continuum for a long time,
but in pieces: the realizability theorem `no_continuum_in_finite_region`
([`QLF_Realizability`](lean/QLF_Realizability.lean)), the catalogue of wrong continuum answers in
[`TheContinuum.md`](TheContinuum.md), the discrete-frequency correction to Mead in
[`Collective_Electrodynamics.md`](Collective_Electrodynamics.md) §5, and the rule that irrationals are
limits of rational processes ([`Hofstadter_Butterfly_QLF.md`](Hofstadter_Butterfly_QLF.md),
[`Unreasonable_Classical_Mathematics.md`](Unreasonable_Classical_Mathematics.md) §5c). There was no
single statement that could fail. This page supplies one. It rests on two new exact facts about QLF's lattice-walk census. Both are
properties of the census definitions, not of physical waves:

1. **No closure is a straight line.** In the census, a straight-line history never balances, and
   straight-line histories make up an exponentially vanishing fraction of all histories (at most
   `16·2^{−L}` at length `L`) (§3).
2. **The signed census has large excess coherence over a random-sign null model.** The exact signed
   sum `A_L` is `κ_L = |A_L|/√W_L` times the standard deviation it would have if its `W_L` terms carried
   independent fair signs: `9.3` at `L = 4`, `1.2·10⁵` at `L = 20`, `2.8·10¹⁰` at `L = 40` (exact
   integers, [`rogue_census.py`](rogue_census.py); §4). Rogue waves are a classical *analogy* for this
   (phase correlation beating a random-phase baseline), not a shared threshold or a claim about
   physical waves.

The qualification is the one the method always imposes. Both facts are exact statements about the
census, so they are theorems or exact computations *about the model*. They become physics only through
a measurement/realization map from census quantities to physical observables, which is not derived
here. §5 applies the census to two electrons; its registered test (T3) and a toy diagnostic (D-MT) are
reported in §5a.

---

## 1. Definitions

All objects are finite. Nothing below uses a real number except as the name of a limit.

- **Twist history.** A finite word over the eight twists `^ v < > / \ + −`, read as unit steps
  `±e_a` on the four axes of `ℤ⁴` ([`Closure_Walk.md`](Closure_Walk.md)). Net displacement
  `x(h) ∈ ℤ⁴`.
- **Closure.** A count-balanced history: `x(h) = 0`. By `count_balanced_pauli_closed`
  ([`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean)) every closure is also Pauli-closed, so it is a
  ZFA closure, both conjuncts.
- **Census.** `W_L` is the number of closures of length `L`. `A_L` is their signed sum, each closure
  weighted by its fold phase `±1`. The phase is the holonomy of the ℤ₂ edge-sign connection
  (`fold_eq_connectionPhase`, [`QLF_EdgeSign`](lean/QLF_EdgeSign.lean)).
- **Census observable.** A function of finitely many census counts at finite lengths. When it is a
  ratio of counts its value is rational.
- **Rendering.** A real number `r` is *rendered* by a sequence of census observables `q_L` when
  `q_L → r`. The sequence is the physical object; `r` names where it goes.
- **Geodesic (straight-line) history.** A history with `|x(h)|₁ = |h|`: every step moves away from the
  origin. Equivalently, it never uses both twists of a conjugate pair.
- **Random-sign null model.** A hypothetical model in which the `W_L` closures carry independent fair
  signs. Then `E[A_L²] = W_L`, so a typical amplitude is `√W_L`, and by the normal approximation
  `P(|A_L| ≥ κ√W_L) ≈ e^{−κ²/2}`. It is a reference distribution for the diagnostic below, not a model
  of any physical wave.
- **Excess coherence.** `κ_L = |A_L| / √W_L`, the realized signed sum in units of the null model's
  standard deviation. A model-relative diagnostic, not an observable.

---

## 2. The conjecture

> **No-Continuum Conjecture (NC), a conjecture with modeling assumptions marked.** What nature
> records is closure counts.
>
> - **(NC1) Observables are census observables.** Every measured quantity is a census observable at a
>   finite length. *(Modeling assumption.)*
> - **(NC2) Real numbers are renderings.** Every real-valued quantity in a physical law (a position, a
>   field value, a coupling, `π`) is rendered by a sequence of census observables. The limit is never
>   itself the value of a measurement.
> - **(NC3) Classical laws are laws of means.** A law stated for a continuous trajectory or a smooth
>   field (straight-line inertial motion, a smooth Coulomb field) holds of an average over ways and of
>   no single way, and each single physical history is a closure. *(Modeling assumption: the census
>   facts of §3–§4 hold for the census definitions; reading them as facts about physical histories
>   needs the realization map, which is not derived.)*

**What is assumed.** Only that nature is logical ([`Philosophy.md`](Philosophy.md) §3d), plus one named
premise that QLF did not invent: a bounded region holds finitely many distinguishable states
(Bekenstein; the `[Finite R]` hypothesis of `no_continuum_in_finite_region`). QLF's construction is
one model of these, not a postulate about nature.

**Contrast, once.** NC does not say `ℝ` is inconsistent; it is consistent, and the claim is
**consistency ≠ realizability** ([`TheContinuum.md`](TheContinuum.md)). It also does not reject the
continuum as mathematics. It denies that the continuum is *realized*, and keeps it as the rendering,
which is how [`TheContinuum.md`](TheContinuum.md) §Summary already puts it.

**Which parts are proved, and which are assumed.** The Bekenstein premise with
`no_continuum_in_finite_region` gives only that a bounded region has finitely many distinguishable
states. It does not make observable *values* rational (a finite-valued observable can carry irrational
labels), so NC1 is a modeling assumption, not a consequence. S1–S3 (§3) are proved, and the coherence
figures (§4) are exact, but both are properties of the chosen lattice-walk definitions. NC3 as a claim
about physical histories is a modeling assumption. What is conjectural throughout is the
realization map: that physical amplitudes are signed closure censuses.

---

### 2a. The lineage

NC is an old position with a new instrument, and the history matters because each earlier version
failed or stalled at a specific point.

- **Atoms against the continuum.** Leucippus and Democritus held that matter is made of indivisible
  units; Aristotle (*Physics* VI) argued that magnitude, motion and time are continuous, and his view
  ruled for two thousand years. Zeno's paradoxes are the original pressure on the continuous side
  ([`TheContinuum.md`](TheContinuum.md) §5).
- **The constructive critique.** Weyl's *Das Kontinuum* (1918) and Brouwer's intuitionism attacked the
  completed continuum on logical grounds; reverse mathematics later showed how little of it ordinary
  analysis needs ([`ReverseMathematics.md`](ReverseMathematics.md)). NC takes the logical side from
  this line and adds a physical premise it lacked, the Bekenstein bound.
- **Physics forced to be discrete.** Planck's quantum (1900) was the first time a continuum answer was
  replaced by a count because the continuum answer was wrong. Einstein, in the 1954 letter to Besso
  quoted in [`TheContinuum.md`](TheContinuum.md), allowed that physics may not be based on continuous
  structures at all. He did not say what would replace them; NC's answer is closure counts.
- **Discrete and still Lorentz-invariant.** Snyder (1947) showed a quantized spacetime need not pick a
  frame, and causal set theory (Bombelli, Lee, Meyer and Sorkin 1987) made that the working answer to
  the lattice objection. NC inherits the objection as kill condition K4.

## 3. Straight-line histories in the census (proved for the census)

For a history `h` with `n_a⁺` and `n_a⁻` steps in the two directions of axis `a`,

```
|x(h)|₁ = Σ_a |n_a⁺ − n_a⁻|  ≤  Σ_a (n_a⁺ + n_a⁻) = |h|,
```

with equality exactly when no axis is used in both directions. Three consequences:

- **(S1) No closure is a straight line.** A closure of positive length has `x = 0 < |h|`, so it is not
  geodesic. Every event contains a reversal on some axis.
- **(S2) Net motion slower than one step per step requires a reversal.** `|x(h)|₁ < |h|` holds iff some
  axis carries both a twist and its conjugate. Under the framework's hypothesis that every substrate
  step runs at `c` ([`Inertia.md`](Inertia.md); a hypothesis there, not yet a theorem), straight
  histories are null rays, and no history with a massive straight trajectory exists. A massive body is
  a closed null circulation (Route A, [`QLF_Inertia`](lean/QLF_Inertia.lean)), and its uniform motion is
  the drift of that circulation.
- **(S3) Straight lines are exponentially rare.** The number of geodesic histories of length `L` is
  `G_L = Σ_{k=0}^{4} C(4,k)·2^k·k!·S(L,k)` (choose `k` axes, a sign on each, and a word using all `k`
  letters; `S` is the Stirling number of the second kind). So `G_L/8^L ≤ 16·2^{−L}`. The formula is
  checked by brute force to `L = 5`:

  | `L` | `G_L/8^L` | bound `16·2^{−L}` |
  |---:|---:|---:|
  | 4 | 0.459 | 1 |
  | 8 | 5.04·10⁻² | 6.25·10⁻² |
  | 12 | 3.66·10⁻³ | 3.91·10⁻³ |
  | 20 | 1.52·10⁻⁵ | 1.53·10⁻⁵ |

  A single repeated twist, the literal straight line along one axis, is 8 histories out of `8^L`, one
  way to reach its endpoint. It is the least-multiplicity history there is, which is where
  [`Law_Of_Exceptions.md`](Law_Of_Exceptions.md) says exceptions live.

**Reading (interpretive, under NC3).** S1–S3 are statements about the census. If physical histories
are closures (NC3, assumed), the following reading applies. The straight line is what free motion looks like on average. The mean position of an unbiased
population of histories stays at the origin, and that of a biased one drifts along a straight line. But a mean over ways need not be a way, and here it never is (CLAUDE.md, "ZFA first,
then every way", rule 3). On that reading, Newton's first law survives as a law about the mean and
holds of no single closure. This is the sense in which "the failure of the straight-line law is
the story": what classical physics treats as the default (unforced straight motion) is not anything a
closure does, and what it treats as the departure (interaction, turning) is what every closure does.

**Lean target.** S1 and S2 are a few lines over `List Twist`. They are not yet in Lean.

**History.** Straight-line inertia is younger than it looks. Galileo's inertia was circular, motion
along the Earth's surface; Descartes (*Principia Philosophiae*, 1644) first stated that free motion is
straight, and Newton made it Law I (1687). Quantum mechanics already broke it at the level of single
paths. Dirac (1933) and Feynman (1948) wrote the amplitude as a sum over all paths with equal weight,
the classical path emerging only by stationary phase, and Feynman and Hibbs (1965) noted that the
paths that dominate are zigzags, continuous but nowhere differentiable. Closer still: Feynman's
checkerboard (Feynman and Hibbs, problem 2-6) recovers the 1+1-dimensional Dirac equation from paths
that always move at the speed of light and only turn, with an amplitude per corner, and Schrödinger's
*Zitterbewegung* (1930) is the same light-speed trembling in the free electron. S2 is the discrete core
of both: a massive straight trajectory is made of null steps that reverse. What QLF adds is the
counting form (S3) and the requirement that what is realized is a closed loop, not an open path.

---

## 4. Excess coherence of the signed census (exact computation)

**The classical analogy, and its limits.** Rogue waves are real and classically explained. The Draupner platform in the
North Sea recorded a 25.6 m wave in a sea of significant height about 12 m on 1 January 1995. In a
linear random sea, wave heights are Rayleigh-distributed (Longuet-Higgins 1952), and a height above
twice the significant height has probability `e^{−8} ≈ 3.4·10⁻⁴`; such waves are seen more often than
that. The accepted explanations are linear focusing and the nonlinear modulational instability
(Benjamin & Feir 1967), whose prototype is the Peregrine breather, peaking at three times the
background (Peregrine 1983); the review is Kharif & Pelinovsky (2003). Optical rogue waves were found by
Solli et al. (2007). The common thread is that **phases are correlated**, so the random-phase baseline
underestimates large amplitudes. That is the only point of contact with the census. The Rayleigh
criterion concerns a different observable (crest-to-trough height) and a different sampling
distribution, so it does not give a threshold for `κ`, and nothing below is a claim about ocean or
optical waves.

**The census.** In QLF the phases are correlated by construction: they are the holonomies of a ℤ₂
connection with π flux through every mixed spatial plaquette ([`QLF_EdgeSign`](lean/QLF_EdgeSign.lean)).
So the question is how far the realized signed sum sits from the random-sign null model. [`rogue_census.py`](rogue_census.py)
computes `W_L` and `A_L` exactly by a transfer recursion on `ℤ⁴`, checks `W_L` against
[`closure_walk.py`](closure_walk.py) at every length, and reproduces the signed census `−8, 120, −2144`
of [`Closure_Walk.md`](Closure_Walk.md) §3:

| `L` | `W_L` | `A_L` | `\|A_L\|/W_L` | `κ_L = \|A_L\|/√W_L` | null-model `log₁₀ P` (hypothetical) |
|---:|---:|---:|---:|---:|---:|
| 2 | 8 | −8 | 1 | 2.83 | −1.7 |
| 4 | 168 | 120 | 0.714 | 9.26 | −18.6 |
| 10 | 7,939,008 | −868,608 | 0.109 | 308 | −2.1·10⁴ |
| 20 | 2.23·10¹⁵ | 5.54·10¹² | 2.5·10⁻³ | 1.18·10⁵ | −3.0·10⁹ |
| 30 | 1.08·10²⁴ | −5.64·10¹⁹ | 5.2·10⁻⁵ | 5.43·10⁷ | −6.4·10¹⁴ |
| 40 | 6.57·10³² | 7.30·10²⁶ | 1.1·10⁻⁶ | 2.85·10¹⁰ | −1.8·10²⁰ |

(All rows are in [`data/rogue_census.json`](data/rogue_census.json); `L ≤ 40` runs in about 25 s. The
last column is the normal-approximation tail `−κ²/(2 ln 10)` of the hypothetical random-sign model, an
illustration of how far the census is from that model, not a probability of anything physical.)

**What the table shows.**

- **(R1) Excess coherence grows with `L`.** `κ_L` is above 4 from `L = 4` on (4 is the convention
  registered for T3, not an ocean-derived threshold). The step ratio `κ_L/κ_{L−2}` is 3.2 at `L = 6`
  and rises to 3.5 at `L = 40`, so `κ_40 ≈ 2.85·10¹⁰`.
- **(R2) The rate.** Following Jim's rule, the rate is a rational process: the ratio sequence
  `A_{L}/A_{L−2}` runs `−15.0, −17.9, −19.5, …, −26.8` at `L = 40`. With the leading `L^{−2}` correction
  of a four-dimensional walk taken out it reads `29.70`, consistent with `(2 + 2√3)² = 29.86`, the
  square of the band edge of the π-flux hopping on the three spatial axes (`2√3`) plus the commuting
  gauge axis (`2`). `W_L` grows at `8² = 64` per two steps. So `κ_L` grows like
  `((2+2√3)/√8)^L ≈ 1.93^L`. This identification is numerical; nothing below depends on it.
- **(R3) Excess coherence does not mean "most ways in phase".** `|A_L|/W_L` falls toward zero, like
  `((2+2√3)/8)^L ≈ 0.68^L`. The net coherent excess is a vanishing fraction of the ways. The amplitude is
  enormous compared with the random-sign model and small compared with full alignment. Both
  statements are true and the claim is only the first.

**The rule-4 test.** For which sign assignment would R1 be false? For one with independent
phases: then `κ_L` stays near 1. The census is not such a distribution, so R1 has content, but the
content is about the census's own phase structure, which is a theorem (`QLF_EdgeSign`). R1 is therefore
an exact property of the model. It is not yet evidence about nature; it becomes a physical claim only
through NC's bridge, and the next section names the first place to test that bridge.

**Why this belongs with the straight line.** The straight trajectory and the smooth Gaussian field are
the same move made twice. Average over ways with unsigned weights and the central limit gives a
straight drift with diffusive spread; average with independent phases and you get the Gaussian sea in
which large amplitudes are exceptional. Each average erases what a single way has: the loop in §3 and
the phase correlation here. NC3 (assumed) says that physics lives in what the averages erase.

### 4a. A straight-line bound for waves, falsified: Mizohata–Takeuchi

*The conjecture itself, and its resurrection without the continuum, now has its own page:
[`Mizohata_Takeuchi_QLF.md`](Mizohata_Takeuchi_QLF.md). This section keeps the connection to the census.*

The cleanest independent instance of "straight lines fail, coherence wins" comes from harmonic
analysis, and it was settled in 2025.

**The conjecture.** For a `C²` hypersurface `Σ ⊂ ℝ^d`, the extension operator `E` turns a function
`f` on `Σ` into a wave `Ef` on `ℝ^d` (a superposition of plane waves with frequencies on `Σ`). The
Mizohata–Takeuchi conjecture, which arose from well-posedness questions for dispersive equations,
says the energy a wave deposits on any nonnegative weight `w` is controlled by straight lines:

```
∫ |Ef|² w  ≲  ‖f‖²_{L²(Σ)} · sup over lines ℓ of ∫_ℓ w      (the X-ray transform of w)
```

So no arrangement of mass can absorb more of a wave's energy than the heaviest single line through it
allows. It is a straight-line law for waves.

**The counterexample.** Hannah Cairo, aged 17, disproved it (arXiv:2502.06137, 2025), with a loss of
`log R` at scale `R`, for every `C²` hypersurface that does not lie in a hyperplane. In her
construction, `N ≈ log R` separated frequencies `ξ_1, …, ξ_N` on `Σ` generate the set
`Q = { Σ c_i ξ_i : c ∈ {0,1}^N, Σ c_i = ⌊N/2⌋ }`: the sums that use exactly half of the frequencies,
`|Q| ≈ N^{−1/2} 2^N` of them. The weight is built from `Q`. On the energy side, translating `Q` by any
`ξ_i` lands about half of its points back in a set of the same kind, so wave packets add
constructively there. On the line side, an incidence lemma shows that no hyperplane meets more than
`2^{d−1}` of the balls around `Q`, so every line carries little weight. The ratio between the two sides
is about `N ≈ log R`, and it grows without bound.

**Why it belongs here.** Cairo's result is exactly the pattern of §3–§4 in classical mathematics, with
no QLF input:

- the bound that failed is a **straight-line** bound (the X-ray transform);
- it failed because of **constructive interference** on a combinatorial set, the same kind of phase
  correlation the rogue-wave analogy points to; and
- the failure **grows with scale** (`log R`). The census `κ_L` also grows with `L`, but it is a
  different quantity, so this is a parallel, not a comparison of sizes.

There is one more resemblance. Cairo's interference set is the set of **half-balanced** sums: choose
exactly half of `N` frequencies, a central-binomial family of size about `2^N/√N`. QLF's one-axis
closure census is the same count, `C(2n, n)` balanced words. We note this as a structural resemblance
only. Nothing here derives Cairo's construction from closures, and her theorem stands on its own.

**What it does for NC.** It shows that NC3's kinematic claim has a precise analogue in the continuum
itself: even inside classical harmonic analysis, straight-line bounds on wave energy are false at
large scale, and they fail because of coherence that a straight line cannot see. A toy diagnostic in
this direction (D-MT, §5a) compared the census wave with the classical walk against nine substrate
line families. Its registered prediction **failed** at `L ≤ 8`: the census wave focuses no more than
the classical walk. D-MT is not the Fourier-extension inequality, and it neither tests nor supports
the Mizohata–Takeuchi conjecture or [`Mizohata_Takeuchi_QLF.md`](Mizohata_Takeuchi_QLF.md)'s MT-Q.

---

## 5. Electron interaction as joint coherence (conjecture, test registered)

**What is proved.** Charge is the residue of non-closure, and no event is charged
(`zfa_closure_is_neutral`, [`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean)). Coulomb's rule is a
counting rule: a joint closure of two histories carries total charge zero, two like charges admit no
joint closure, and opposite charges admit some (`coulomb_is_a_counting_rule`). No force, no field, no
action at a distance. Mead's transactional photon is the same joint closure
([`Collective_Electrodynamics.md`](Collective_Electrodynamics.md) §2).

**The conjecture (NC-E).** The interaction amplitude of two electrons is the signed census of their
joint closures, and it carries large excess coherence over the random-sign null model wherever joint
closures exist. Coulomb's smooth `1/r²` is the rendering of those counts, the large-count, phase-averaged limit,
and the field that classical electrodynamics integrates is the average that erases the coherence.

**History.** Coulomb measured the inverse-square law in 1785 as a force at a distance; Faraday and
Maxwell replaced it with a field. A line of physicists then tried to remove the field again:
Schwarzschild (1903), Tetrode (1922) and Fokker (1929) wrote electrodynamics as a direct interaction
between charges, and Wheeler and Feynman (1945, 1949) made it work with the absorber, so that a
radiated photon is a handshake between emitter and absorber. Mead's *Collective Electrodynamics*
(2000) continues that line, and QLF reads its handshake as a joint closure
([`Collective_Electrodynamics.md`](Collective_Electrodynamics.md)). NC-E differs from all of them in
one place: they kept continuous spacetime and continuous phase, and NC-E replaces both with counts.

**Existing data, read honestly.** The signed two-electron census of
[`logical_bang_census.py`](logical_bang_census.py)
([`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) §43–§45) reported `C = |S|/N`, the
analogue of `|A_L|/W_L`, never `κ = |S|/√N`. It found that interleaved electrons with orthogonal spins
cancel exactly at lengths 8 and 10, while collinear ones survive. An exact zero is `κ = 0`: orthogonal
spins make a dark fringe at those lengths. (Superseded at greater depth: see §5a.)

**Registered test T3** (registered in commit `743c7e8`; result in §5a). Run [`logical_bang_census.py`](logical_bang_census.py)
unchanged, with the §44 definition of entangled (`--depth12`, `--depth 14`), at lengths 10, 12 and 14, and compute `κ = |S|/√N` for the entangled collinear class (P and A
pooled, as in §44).

- **Pass:** `κ ≥ 4` at all three lengths, and `κ` does not decrease from 10 to 14. (The threshold 4
  is a convention fixed at registration.)
- **Fail:** `κ < 4` at any of the three lengths.
- **Reported either way:** `κ` for the orthogonal class and for every remainder class.

Following [`ScientificApproach.md`](ScientificApproach.md) and the project's depth rule, a failure at
length 14 says that the collinear joint census is near random phase *at that depth*. That would make
NC-E unsupported at the depth reached and is how it will be reported. It would not decide physical
electrons, whose closures are thousands of bits deep.

### 5a. Results and registrations (2026-11-02)

**T3 result: PASS.** Run as registered by `python3 t3_coherence.py` ([`t3_coherence.py`](t3_coherence.py),
which calls `census_dp` from [`logical_bang_census.py`](logical_bang_census.py) unchanged). Every class's
`N`, `S` and `κ` at each length is in [`data/t3_coherence.json`](data/t3_coherence.json). The script enforces the criterion stepwise (`κ(10) ≤ κ(12) ≤ κ(14)`) and exits nonzero on FAIL. It is a manual check: CI runs only the doc-network check, and none of the numerical scripts here are CI-enforced. Entangled
classes, all remainders pooled:

| length | orthogonal `N` | orthogonal `S` |
|---:|---:|---:|
| 10 | 4,700,160 | 0 |
| 12 | 1,085,736,960 | −172,032 |
| 14 | 200,740,700,160 | 34,111,488 |

and

| length | collinear `N` | collinear `S` | collinear `κ` | orthogonal `κ` |
|---:|---:|---:|---:|---:|
| 10 | 2,350,080 | −76,800 | 50.1 | 0 (exact zero) |
| 12 | 542,868,480 | 8,825,856 | 378.8 | 5.2 |
| 14 | 100,370,350,080 | −741,470,208 | 2,340.4 | 76.1 |

The collinear joint census is past `κ = 4` at all three lengths and rising (factor ~6–7 per two steps),
which passes T3. Two honest notes. First, T3 was not fully blind: the length-12 totals were already
recorded in [`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) §44a, although `κ` had not
been computed from them. Second, the "orthogonal = dark fringe" scoping in §5 was a shallow-depth
reading: orthogonal spins cancel exactly at length 10, but they cross `κ = 4` at 12
(`κ = 5.2`) and reach `κ = 76` at 14, while staying 30× weaker than collinear. Several orthogonal
classes (`gggggg`, `ggggnn`, `ggggss`, `ggssss`, `ssssss`, entangled) still cancel exactly at 14. By
the rule-4 test, the pass shows that the joint census is far from random phase, as the vacuum census
is; it does not by itself show that physical electrons interact this way.

**D-MT, registered before it was run.** A limited toy-model diagnostic, inspired by
Mizohata–Takeuchi but not the Fourier-extension inequality: nine chosen line families on normalized
time-slice distributions, not the supremum over all lines. It is not a test of MT or of MT-Q.

- *Wave.* `ψ_k(x)`, the signed sum over histories of length `k` from the origin ending at `x ∈ ℤ⁴`
  (holonomy signs, as in §4). Density per time slice `ρ_k(x) = ψ_k(x)² / Σ_y ψ_k(y)²`.
- *Random-phase baseline.* Independent signs give `E[ψ_k(x)²] = W_k(x)`, so the baseline density is
  `p_k(x) = W_k(x)/8^k`, the classical walk.
- *Lines.* The substrate's own straight lines in discrete spacetime `(x, k)`, `0 ≤ k ≤ L`: rest lines
  `x = x₀`, and null lines `x = x₀ + k·(±e_a)` for the eight twists. Each spacetime point lies on nine.
- *Constant.* `V_L = max Σ_{k,x} ρ_k(x) w(x,k)` over weights `w ≥ 0` whose sum along every line is at
  most 1 (a linear program). `V_L` is the best constant in `Σ ρ w ≤ V_L · sup_ℓ X w` for this wave, and
  `V_L^{rp}` is the same for `p_k`. Mizohata–Takeuchi holding here means `V_L` stays bounded.
- *NC's prediction (MT fails for the census).* `V_L` increases at every step of the range computed, and
  `V_L / V_L^{rp}` increases at every step.
- *Fail.* Either condition fails at some step. Lengths `L = 2, 4, …` as far as the linear program
  allows. A failure at the depth reached is reported as unsupported at that depth.

**D-MT result: FAIL.** Run by [`discrete_mt.py`](discrete_mt.py) (numpy + scipy; the length-10
linear program did not finish in 12 minutes, so the range is `L ≤ 8`):

| `L` | `V_L` signed | `V_L` random phase | ratio |
|---:|---:|---:|---:|
| 2 | 1.467 | 1.750 | 0.838 |
| 4 | 1.996 | 2.021 | 0.988 |
| 6 | 2.400 | 2.517 | 0.954 |
| 8 | 2.757 | 2.874 | 0.959 |

`V_L` rises at every step, but the ratio falls from `L = 4` to `L = 6`, so the registered prediction
fails. What the numbers say:

- **The coherent wave focuses no more than the classical walk.** Its line constant tracks the
  random-phase one within 5 % from `L = 4` on. The reason is structural. The signed transfer operator
  is antisymmetric (`Σ_x ψ_k(x)² = (−1)^k A_{2k}`, asserted in the script), so the return density is
  `ρ_k(0) = A_k²/|A_{2k}| ≈ 4/k²`, the same decay as diffusion. The coherence `κ` of §4 is measured
  against random *signs* on a fixed set of closures. It does not make the wave pile up in space.
- **Both constants grow, so this line family is too poor to test Mizohata–Takeuchi.** With only the
  nine substrate directions (rest and null), the line bound already fails for the classical walk,
  whereas the continuum statement takes the supremum over all lines. A sharper design would include
  every rational lattice direction. As run, D-MT measures whether coherence beats diffusion against
  the substrate's straight lines, and at `L ≤ 8` it does not.

So §4a's resemblance to Cairo's construction stays a resemblance, and D-MT gives no support to MT-Q. The census does not reproduce her
mechanism, constructive interference that grows with scale on a set that no line sees, at the depth
reached. Following the project's depth rule, this is unsupported at `L ≤ 8`, not settled.

---

## 6. Kill conditions (stated before the tests)

- **K1 (census).** If `κ_L` stops growing at some length beyond 40, R1 is false for the census. The ratio trend makes this unlikely, but it is a computation anyone can extend.
- **K2 (electrons).** T3 fails as registered: NC-E is withdrawn at that depth.
- **K3 (realizability).** A measurement whose outcomes provably distinguish more states than a finite
  region can hold falsifies the Bekenstein premise, and with it the finiteness behind NC1.
- **K4 (Lorentz invariance).** The census is counted on `ℤ⁴`, the space of twist counts. If that lattice
  were read as space, it would predict a direction- and energy-dependent speed of light at first order in
  the Planck energy, and the Fermi observation of GRB 090510 already bounds such an effect beyond the
  Planck scale (Abdo et al. 2009). QLF's answer is that space is the causal order rendered statistically,
  not this lattice ([`TheContinuum.md`](TheContinuum.md) §4; the bridge `order_metric_continuum_limit`
  in [`QLF_OrderMetric`](lean/QLF_OrderMetric.lean)). If a rendering of NC ever implies first-order
  Planck dispersion, NC as built here is refuted by existing data. Hughes–Drever bounds on anisotropy
  play the same role ([`Inertia.md`](Inertia.md)).

---

## 7. Status at a glance

| Claim | Status |
|---|---|
| Finitely many distinguishable states in a bounded region | **Proved** given the Bekenstein premise (`no_continuum_in_finite_region`) |
| NC1: every observable is a census observable | **Modeling assumption** (finiteness does not imply rational values) |
| S1, S2: no census closure is straight; slower-than-one-step net motion needs a reversal | **Proved** for the census definitions (elementary); Lean target |
| S3: straight histories are at most `16·2^{−L}` of all | **Proved** for the census (counting formula, brute-force checked) |
| R1: excess coherence `κ_L` over the random-sign model, `4 ≤ L ≤ 40` | **Exact computation**, model-relative |
| R2: growth rate `(2+2√3)²` per two steps | **Numerical evidence** |
| NC3: classical laws are laws of means; physical histories are closures | **Modeling assumption** |
| NC-E: electron interaction carries excess joint coherence | **Conjecture**; T3 **passed** at lengths 10–14 (collinear `κ` 50 → 2,340); orthogonal passes `κ = 4` at 12 |
| D-MT toy diagnostic (nine line families, not MT) | **Failed as registered** at `L ≤ 8`: coherent and random-phase line constants grow together (§5a) |
| The bridge: a physical amplitude is a signed closure census | **Open bridge**, not derived here |

---

## 8. What not to say

- Not "the continuum is inconsistent" or "false". Say: unrealized, and kept as the rendering.
- Not "rogue waves are the rule", or "QLF explains ocean rogue waves". The ocean's are explained
  classically by focusing and modulational instability. The census result is excess coherence over a
  hypothetical random-sign model, and `κ` has no shared threshold with the Rayleigh criterion.
- Not "D-MT tests Mizohata–Takeuchi". It is a toy diagnostic with nine line families.
- Not "most ways are in phase". `|A_L|/W_L → 0`; the claim is coherence relative to random phase.
- Not "electrons interact by rogue waves" as a finding. It is NC-E, a conjecture with a registered test.
- Not "QLF predicted" or "explains" Cairo's counterexample. It is an independent classical result with the same shape (§4a).
- Not "nature is QLF's construction". The construction is one model of a logical nature.

---

## See also

- [`TheContinuum.md`](TheContinuum.md): the case against the realized continuum, and the Lorentz answer (§4).
- [`Unreasonable_Classical_Mathematics.md`](Unreasonable_Classical_Mathematics.md) §5: failures of the continuum, irrationals as rational processes.
- [`Closure_Walk.md`](Closure_Walk.md): closures as closed walks on `ℤ⁴`, and the ℤ₂ connection.
- [`Law_Of_Exceptions.md`](Law_Of_Exceptions.md): exceptions are the least-multiplicity histories.
- [`Inertia.md`](Inertia.md): rest mass as a closed null circulation.
- [`Electron.md`](Electron.md) and [`Collective_Electrodynamics.md`](Collective_Electrodynamics.md): the electron as a closed mode, and the transactional photon.
- [`Interference_NoGo.md`](Interference_NoGo.md): why an unsigned tally cannot interfere, which is why the signed census is the one that matters here.
- [`ScientificApproach.md`](ScientificApproach.md): status labels, R6a, R7.

## References

- T. B. Benjamin and J. E. Feir, *The disintegration of wave trains on deep water*, J. Fluid Mech. **27** (1967) 417–430.
- M. S. Longuet-Higgins, *On the statistical distribution of the heights of sea waves*, J. Mar. Res. **11** (1952) 245–266.
- D. H. Peregrine, *Water waves, nonlinear Schrödinger equations and their solutions*, J. Austral. Math. Soc. Ser. B **25** (1983) 16–43.
- C. Kharif and E. Pelinovsky, *Physical mechanisms of the rogue wave phenomenon*, Eur. J. Mech. B/Fluids **22** (2003) 603–634.
- D. R. Solli, C. Ropers, P. Koonath and B. Jalali, *Optical rogue waves*, Nature **450** (2007) 1054–1057.
- A. A. Abdo et al. (Fermi LAT and GBM), *A limit on the variation of the speed of light arising from quantum gravity effects*, Nature **462** (2009) 331–334.
- J. D. Bekenstein, *Universal upper bound on the entropy-to-energy ratio for bounded systems*, Phys. Rev. D **23** (1981) 287–298.
- P. A. M. Dirac, *The Lagrangian in quantum mechanics*, Phys. Z. Sowjetunion **3** (1933) 64–72.
- R. P. Feynman, *Space-time approach to non-relativistic quantum mechanics*, Rev. Mod. Phys. **20** (1948) 367–387.
- R. P. Feynman and A. R. Hibbs, *Quantum Mechanics and Path Integrals* (McGraw-Hill, 1965).
- E. Schrödinger, *Über die kräftefreie Bewegung in der relativistischen Quantenmechanik*, Sitzungsber. Preuss. Akad. Wiss. (1930) 418–428.
- J. A. Wheeler and R. P. Feynman, *Interaction with the absorber as the mechanism of radiation*, Rev. Mod. Phys. **17** (1945) 157–181; *Classical electrodynamics in terms of direct interparticle action*, Rev. Mod. Phys. **21** (1949) 425–433.
- C. A. Mead, *Collective Electrodynamics: Quantum Foundations of Electromagnetism* (MIT Press, 2000).
- H. Weyl, *Das Kontinuum* (Veit, Leipzig, 1918).
- H. S. Snyder, *Quantized space-time*, Phys. Rev. **71** (1947) 38–41.
- L. Bombelli, J. Lee, D. Meyer and R. D. Sorkin, *Space-time as a causal set*, Phys. Rev. Lett. **59** (1987) 521–524.
- H. Cairo, *A counterexample to the Mizohata–Takeuchi conjecture*, arXiv:2502.06137 (2025).
