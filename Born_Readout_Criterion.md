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

> *Note added after review (2026-11-16), the registration above left unchanged.* That claim was
> stronger than the first instrument delivered. It still placed the roots against `|λ|² = 8` with
> `numpy.roots`, and it checked each recurrence on a finite prefix only. Both gaps are now closed by
> [`born_readout_certified.py`](born_readout_certified.py) (§2), which reproduces every count in §1.
> The hypotheses and kill conditions are untouched.

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
distinct targets). The capacity-2 run used the first instrument (23 minutes on four cores); its
vectorised `--fast` mode, added afterwards to make `R = 3` affordable, reproduced every one of its
category counts and support sets before it was used at `R = 3`. Every number below has since been
**reproduced by the certified pipeline of §2** (`R = 2`: 2 minutes, `R = 3`: 66 minutes, both on four
cores). Each is therefore a certified computation, with no float and no unverified depth.

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
* **C — the registered artifact outcome occurs.** At `R = 3` not one of the 170,400 geometries
  that close carries an amplitude (a certified count, §2), although the `R = 3` operator has six
  distinct eigenvalue moduli below 8 for a readout to live on, among them the integer `6`. So the
  `R = 2` amplitudes do not continue one capacity up. They belong to the smallest capacity at which
  anything interferes. The outcome stated in advance reads this as an artifact of the capacity-2
  truncation, and reads `5` and `7` as eigenvalues of that truncation rather than physical
  constants. That reading is an interpretation of a certified count, not a theorem: only two
  capacities were surveyed, under one capacity rule.
* **P — not evaluated.** The instrument does not compute the proxy rules; nothing is claimed
  about them here.

What the result does **not** say: it does not touch the measure, the phase rule, or the
sub-additivity no-go, and it does not refute the unnormalized amplitude as a construction. It says
that on the census as encoded (capacity as an `ℓ¹` cut on the running imbalance, with absorption at
the branch targets) a convergent amplitude is confined to `R = 2`. Whether another capacity rule
gives a family that persists is a separate, open question, and it is the one this result makes
pressing. The earlier "1.4 %" was a different survey (1,326 pairs, never committed); 0.90 % is this
one, and the fraction matters less than its collapse to zero one step up.

## 2. Certification

The first instrument (`born_readout_survey.py`) had two gaps, both pointed out in review. It placed
roots against the threshold with `numpy.roots`, and it verified each lifted recurrence on a finite
prefix of computed terms only. [`born_readout_certified.py`](born_readout_certified.py) closes both
gaps. A run fails loudly rather than return an uncertified verdict.

* **An annihilator valid at every depth.** For each of the 820 absorbing operators `M`, with `X₀` the
  matrix of all 72 preparation vectors, a candidate `m` is found (Wiedemann, lifted by CRT) and then
  checked as the integer identity `m(M)·X₀ = 0`. The check is computed modulo enough primes that
  their product exceeds twice an explicit bound on the entries (`Σ|mᵢ|·ρ^deg m·‖X₀‖∞`, with `ρ` the
  maximum absolute row sum of `M`). A residue of zero modulo that product is therefore zero over `ℤ`.
  Because `m(M)` kills every preparation vector, every branch sequence `u·Mᵈ·X₀` satisfies the
  recurrence `m` at **every** depth `d`, not only on the terms computed. When a random projection
  misses a component the certificate fails, and the run retries with a fresh projection.
  Certified degrees: 6–15 at `R = 2` and 24–48 at `R = 3`, using 6–13 and 19–37 primes.
* **The exact support of each readout.** `m` is factored over `ℤ`, and the multiplicity of each
  irreducible factor in each sequence's minimal polynomial is decided by testing `m / fᵏ`. A sequence
  that obeys `m` is annihilated by a divisor `g` iff `g(shift)·A` vanishes on its first `deg m` terms,
  because that residual sequence obeys `m` too. Each test is again exact modulo primes, under a bound.
* **Root position by exact arithmetic.** For a factor `f`, the polynomial `P` with
  `P(x²) = ±f(x)f(−x)` has the `λ²` as its roots. `S(w) = P(8w)` moves the threshold to the unit
  circle, and the verdict comes from rational arithmetic only. *Summable* means all roots are strictly
  inside: a Schur–Cohn test. *Marginal* means `S = g·h`, where `g = gcd(S, S*)` has every root on the
  circle (decided by Sturm counting of `g`'s Chebyshev image on `[−2, 2]`) and `h` passes Schur–Cohn.
  Anything else is *divergent*. Labels such as `5` or `7` are exact for `x² + n` factors, and any
  other factor would have been reported as non-integer: none occurred at or below the threshold.
  A self-test checks the disk test against 3,000 random polynomials with prescribed roots, including
  repeated roots on the circle.
* **No repeated roots in any support**, at either capacity. So every readout is an exponential sum
  over distinct eigenvalues, and §3 applies to it exactly.

What the certificate covers: the census as encoded in [`contextual_census.py`](contextual_census.py),
at the two capacities surveyed. It certifies the counts. The reading of `C` as a truncation artifact
remains the interpretation registered in §0 *before* the run, applied to a certified count. It is not
a theorem about every capacity rule, and §4 says what would overturn it.

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
survey above decides the support by certified arithmetic rather than by float overlaps. The theorem is general
linear algebra; it carries no physics, and its value here is that it turns the survey's exact
recurrences into exact verdicts.

## 4. Where this leaves the Born question

The open item was *which apparatus words produce dominant-blind readouts*. The answer for the census
as encoded: at `R = 2`, the 3,192 geometries tabulated above, all with integer supports; at `R = 3`,
none. A selection rule that holds at one capacity and empties at the next is a property of the
truncation. The route to a Born weight through the *unnormalized* amplitude therefore needs a
capacity rule under which convergence persists, or it needs a different readout; the
arbitrary-angle `cos²(θ/2)` target is not reached by either capacity.

## 5. Does any capacity rule keep the amplitude? (pre-registration, committed before the run)

§4 leaves one question pressing: is the collapse at `R = 3` a property of the `ℓ¹` cut, or of growing
the capacity under any rule? The capacity rule is the one modelling choice in the census that the
substrate does not fix. `free_action` cuts on `|v|+|h|+|d|+|l|`, a single budget shared by spatial
and gauge imbalance. This section tests other cuts with the same certified pipeline, on the same
180,288 geometries (`--R <rule>`; `parse_rule` in the instrument):

| family | members run | states | what it varies |
|---|---|---|---|
| `l1:R` (the census's own rule) | `R = 1, 2, 3` | 72, 328, 1032 | the shared budget |
| `split:S,1`, with spatial `ℓ¹ ≤ S` and `\|l\| ≤ 1` | `S = 1, 2, 3` | 168, 600, 1512 | spatial capacity, gauge fixed |
| `split:2,G` | `G = 1, 2, 3` | 600, 1000, 1400 | gauge capacity, spatial fixed |
| `linf:1`, every `\|x_a\| ≤ 1` | one member | 648 | the shape of the cut, at a comparable size |

Hypotheses and outcomes, stated before the run:

* **P (persistence).** A family *persists* if it has summable geometries at its two largest members
  run. *P holds* if any family persists. Then the `R = 3` collapse belongs to the `ℓ¹` rule rather
  than to growth, and §1's truncation reading is withdrawn for that family. *P fails* if no family
  persists. Then the collapse is the same under every rule tried, which strengthens the truncation
  reading without making it a theorem.
* **Prior, recorded so that it can be wrong:** P fails. Each step up in capacity adds operator modes
  with `|λ|² ≥ 8`, and a readout must be blind to every one of them. Nothing in a rule that only
  enlarges the state space supplies that blindness.
* **Q (the integers).** In any summable geometry, under any rule, are the supports still integer
  `|λ|²`, and still among `{5, 7}`? Recorded descriptively, not a kill condition.

### 5a. Results (certified, every member of every family run in full)

Summable geometries out of the same 180,288:

| family | smallest member | middle member | largest member | persists? |
|---|---:|---:|---:|---|
| `l1:R` | `R = 1`: **7,112** | `R = 2`: **1,536** | `R = 3`: 0 | no |
| `split:S,1` | `S = 1`: **7,744** | `S = 2`: 0 | `S = 3`: 0 | no |
| `split:2,G` | `G = 1`: 0 | `G = 2`: 0 | `G = 3`: 0 | no |
| `linf:1` | **496** | – | – | (one member) |

No member of any family has a repeated root in a support. Certified annihilator degrees reach 80
(at `split:2,3`), with up to 60 primes per certificate.

* **P fails for the three multi-member families, as the prior said.** None of them has summable
  geometries at its two largest members. (`linf:1` was run at one size only, so persistence is not
  evaluated for it.) In each of the three, convergence appears only at the smallest sizes, and
  once gone it stays gone. The `ℓ¹` family shows this most clearly: it has two convergent members
  before the collapse (`R = 1` and `R = 2`) and still empties at `R = 3`. The collapse is therefore not a feature of the shared `ℓ¹` budget. It
  happens when spatial capacity grows alone (`split:S,1`), and gauge capacity never opens a
  convergent class at all (`split:2,G`).
* **Q, recorded.** The integer supports are a property of the rule, not of the substrate. At
  `l1:1` the supports are `{6}` and `{7}`, and at `l1:2` they are `{5}`, `{7}` and `{5, 7}`. At
  `split:1,1` and `linf:1`, every summable support is a non-integer `|λ|²` below 8 (shown as ≈ 0.26
  and 7.74, ≈ 0.84 and 7.16, and ≈ 0.97, 5.49 and 7.55; the factors are irreducible and not of the
  form `x² + n`, and the verdicts are exact). So the `{5, 7}` selection of §1 does not survive a
  change of rule at fixed small size. That fits reading it as a feature of one truncation.

What this adds to §4: across nine capacity-limited state spaces in three multi-member families, an
unnormalized amplitude exists only at the smallest sizes of each multi-member family. Any route to a Born weight through this amplitude has to explain a
convergent class that persists. These rules give none, so the remaining options are a readout
other than first closure at fixed targets, or a weight that is not this amplitude. The
reproduction commands are `python3 born_readout_certified.py --R <rule>`, with `--checkpoint
<file>` making long runs resumable: `l1:1` takes seconds, and `split:2,3` about 7 hours on two
cores.

Evidence bundle: [`data/born_readout_runs/`](data/born_readout_runs/README.md) holds every rule's complete output, rerun at one pinned commit, with per-target-pair summaries and SHA-256 hashes.

Reproduce (certified): `python3 born_readout_certified.py --selftest`, then `--R 2` (~2 min on four
cores) and `--R 3` (~66 min). The first, uncertified instrument remains as
[`born_readout_survey.py`](born_readout_survey.py).
