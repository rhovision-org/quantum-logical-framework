# Which readouts carry an amplitude — the Born readout criterion

Part of the [Quantum Logical Framework (QLF)](README.md). Follows [`Born_Rule.md`](Born_Rule.md) §8
and [`Open_Problems.md`](Open_Problems.md) item 3, which reduced the unnormalized-amplitude question to
one combinatorial question: an amplitude `T_c = Σ_d A_c(d)·8^{−d/2}` exists exactly when the readout
ignores every mode of the absorbing closure operator with `|λ|² ≥ 8`, and the convergent cases at
capacity 2 showed only `a² = 5` and `a² = 7`.

## 0. Pre-registration (committed before the survey in §2 is run)

Instrument: [`born_readout_survey.py`](born_readout_survey.py). For each geometry (preparation word,
two apparatus words with distinct absorbing targets) it computes the first-closure amplitudes
`A_±(d)` of [`contextual_census.py`](contextual_census.py) exactly, finds the **exact minimal linear
recurrence** of each branch sequence (Berlekamp–Massey modulo many primes, lifted by CRT and then
verified on every computed integer term), and reads the joint support as the roots of that
recurrence. No float eigen-decomposition and no growth fit enter the verdict.

Survey: capacities `R = 2` and `R = 3`; preparations = every word of length 1 or 2; apparatus =
every word of length 1 or 2; every unordered pair of apparatus words with distinct targets. Geometries
in which nothing closes are counted separately and are not "convergent".

Hypotheses and kill conditions, stated before the run:

* **S (selection rule).** At `R = 2`, every convergent geometry's recurrence has its nonzero roots on
  `|λ|² ∈ {5, 7}`. *Killed by* one convergent geometry with a root at `|λ|² = 6`, at the irrational
  `9 − 4√3 ≈ 2.07` (a root of `x⁴ + 18x² + 33`, which is in the operator's spectrum), or anywhere
  else below 8.
* **I (integrality).** At `R = 2`, every geometry at or below the threshold has only integer `|λ|²`.
  *Killed by* one irrational `|λ|² ≤ 8` in a summable or marginal geometry.
* **C (capacity, the artifact test).** If the convergent class is a property of the substrate rather
  than of the capacity-2 truncation, it must persist at `R = 3`. *Outcome that reads it as a
  truncation artifact:* zero convergent geometries with any closure at `R = 3`. One or more keeps the
  physical reading open.
* **P (old proxies).** The `Born_Rule.md` rules (`a² = 7` ⟺ antipodal targets; `a² = 5` ⟺ shared
  component anti-aligned with the preparation) are expected to fail on the larger survey, as proxies
  did on the 90-geometry set. Recorded, not a kill condition.

Exact facts already in hand before this registration (from the instrument run on the seven
`geometries()` cases only): the non-absorbing capacity-2 operator (328 states) has minimal polynomial
`x(x²+7)(x²+9)(x⁴+18x²+33)`, so its dominant `|λ|² = 9 + 4√3 ≈ 15.93` (the `3.991²` of
`Born_Rule.md`) and **5 is not in its spectrum**: the `5` enters only through absorption, i.e. through
the apparatus. The transverse branch sequences satisfy `x² + 5` exactly and the ZX/ZY mixes
`(x² + 5)(x² + 7)`.

## 1. Results

Both surveys ran over the same **180,288 geometries** (72 preparations × 2,504 apparatus pairs with
distinct targets). The capacity-2 run used the exact instrument (23 minutes on four cores); the
vectorised `--fast` mode, added afterwards to make `R = 3` affordable, reproduced every one of its
category counts and support sets exactly before it was used at `R = 3`.

| | `R = 2` | `R = 3` |
|---|---:|---:|
| transfer-operator minimal polynomial (degree) | 9 | 29 |
| distinct nonzero `\|λ\|²` in the operator's spectrum below 8 | 2 (`7`, `9 − 4√3`) | 6 |
| nothing closes | 9,888 | 9,888 |
| closes at finitely many depths only | 12,560 | 11,952 |
| **summable** (`\|λ\|² < 8` on the whole support) | **1,536** | **0** |
| marginal (top of support exactly `8`) | 1,656 | 0 |
| divergent | 154,648 | 158,448 |
| summable fraction of geometries that close | 0.90 % | 0 % |

Supports at or below the threshold, `R = 2`:

| verdict | `\|λ\|²` in the support | geometries |
|---|---|---:|
| summable | `{5, 7}` | 960 |
| summable | `{5}` | 480 |
| summable | `{7}` | 96 |
| marginal | `{5, 6, 8}` | 960 |
| marginal | `{5, 8}` | 480 |
| marginal | `{6, 8}` | 192 |
| marginal | `{8}` | 24 |

Irrational `|λ|²` at or below the threshold: **none**, at either capacity.

### Verdicts against the registration

* **S — passes.** Every convergent geometry at `R = 2` has its support on `{5, 7}`. The `6` that
  absorption puts into the spectrum does appear, but only together with `8`, so only in marginal
  geometries; `9 − 4√3 ≈ 2.07`, which is in the operator's own spectrum, never appears in any
  support. The `Born_Rule.md` reading, made on 39 cases, holds on 3,192.
* **I — passes.** No irrational `|λ|²` at or below the threshold, in 180,288 geometries.
* **C — the convergent class is a truncation artifact.** At `R = 3` not one of the 170,400
  geometries that close carries an amplitude, although the `R = 3` operator has six distinct
  eigenvalue moduli below 8 for a readout to live on (among them the integer `6`). So the amplitudes
  of `R = 2` are not the first members of a family that persists as the capacity grows: they are a
  property of the smallest capacity at which anything interferes. By the outcome stated in advance,
  this reads the convergent class as an artifact of the capacity-2 truncation, and the integers `5`
  and `7` as eigenvalues of that truncation rather than physical constants.
* **P — not evaluated.** The instrument does not compute the proxy rules; nothing is claimed
  about them here.

What the result does **not** say: it does not touch the measure, the phase rule, or the
sub-additivity no-go, and it does not refute the unnormalized amplitude as a construction. It says
that on the census as encoded (capacity as an `ℓ¹` cut on the running imbalance, with absorption at
the branch targets) a convergent amplitude is confined to `R = 2`. Whether another capacity rule
gives a family that persists is a separate, open question, and it is the one this result makes
pressing. The earlier "1.4 %" was a different survey (1,326 pairs, never committed); 0.90 % is this
one, and the fraction matters less than its collapse to zero one step up.

## 2. Exactness

A branch sequence `A(d) = u·Mᵈ·v` satisfies a linear recurrence whose characteristic polynomial
divides the minimal polynomial of `M`, so `2·deg + 8` terms certify it. The instrument computes
`4·deg + 60` terms (96 at `R = 2`, 176 at `R = 3`), raises an error if any recurrence needs more,
and none did. The exact mode verifies the lifted integer recurrence on every integer term; the fast
mode lifts from six 31-bit primes and checks the lift modulo two further primes on every term.
Every recurrence found was square-free, so every readout is an exponential sum over distinct
eigenvalues and §3 applies to it.

## 3. The criterion, proved

[`lean/QLF_ReadoutCriterion.lean`](lean/QLF_ReadoutCriterion.lean), no axioms. For an exponential
sum `A(d) = Σ_k c_k λ_kᵈ` with distinct `λ_k`:

* **`terms_tendsto_zero`** — if the sum tends to zero, every term does (a Vandermonde inversion: the
  window `A(d), …, A(d+n−1)` is an invertible linear image of the terms).
* **`readout_tendsto_iff`** — `A(d)·rᵈ → 0` iff `|λ_k|·r < 1` for every `k` with `c_k ≠ 0`.
* **`readout_summable_iff`** — the same condition is equivalent to absolute convergence of
  `Σ |A(d)|·rᵈ`, so there is no conditionally convergent middle case.
* **`amplitude_exists_iff`** — at QLF's forced rate `r = 8^{−1/2}`, the amplitude exists iff every
  eigenvalue in the joint support has `|λ|² < 8`.

So the `90 of 90` agreement in [`Born_Rule.md`](Born_Rule.md) §8 is a theorem, and the
survey above decides the support exactly rather than by float overlaps. The theorem is general
linear algebra; it carries no physics, and its value here is that it turns the survey's exact
recurrences into exact verdicts.

## 4. Where this leaves the Born question

The open item was *which apparatus words produce dominant-blind readouts*. The answer for the census
as encoded: at `R = 2`, the 3,192 geometries tabulated above, all with integer supports; at `R = 3`,
none. A selection rule that holds at one capacity and empties at the next is a property of the
truncation. The route to a Born weight through the *unnormalized* amplitude therefore needs a
capacity rule under which convergence persists, or it needs a different readout; the
arbitrary-angle `cos²(θ/2)` target is not reached by either capacity.

Reproduce: `python3 born_readout_survey.py --R 2` (exact, ~25 min on four cores) and
`python3 born_readout_survey.py --R 3 --fast`.
