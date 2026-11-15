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

*(Filled in after the run.)*
