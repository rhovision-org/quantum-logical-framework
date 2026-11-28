# Cooperative ZFA Assembly Transport — pre-registration

**Status:** pre-registered phenomenological model, not a physical derivation. A negative result is
acceptable and will be recorded. Tracking issue:
[#267](https://github.com/rhovision-org/quantum-logical-framework/issues/267).

**Layers.** This document is the **dynamical transport** layer. The static flat-history index is
[`Assembly_Index_QLF.md`](Assembly_Index_QLF.md) (#264 / PR #265); the tensor-sector state index is
#266. This model does not replace either.

---

## 0. The question

Can an evolving library of **persistent reusable assemblies**, constrained top-down by a blanket
capacity, produce a scale interval with a constant transfer ratio — where the raw closure-count
census did not?

This is a screening test, not a derivation of turbulence. It is successful if it produces a plateau
that the scalar closure-count baseline does not, and if the plateau depends on the assembly memory.
It fails if it does not.

---

## 1. The result that must not be retried

The closure-census turbulence test was already pre-registered and run to the end:

| run | result |
|---|---|
| `intermittency_bridge.py` (vacuum) | `W(R)` peaks near `R = 4`, then decays; **no inertial range** |
| `intermittency_seeded.py` (seeded) | peak shifts to `R_inj + 1`, then decays as vacuum; **no inertial range at any injection scale** |
| `Navier_Stokes_Geometry.md` §“Cross-check that did not go the other way” | the closure census is not a turbulent cascade |

Those results stand. This model must change the **state space**, not reweight the same scalar
closure counts.

---

## 2. Frozen model

Everything in this section is fixed before the first run. The model is deliberately small and
phenomenological; its assumptions are not QLF theorems.

### 2.1 Universe

All canonical balanced words of even length `2, 4, 6, 8` over the eight twists. There are
`1 + 6 + 70 + 1365 = 1442` canonical classes, representing `8 + 168 + 5120 + 190120 = 195416`
words. Each class carries:

- a representative word,
- its orbit size under the 384-element axis/sign group,
- the ordinary assembly index `a`,
- the closure-constrained index `a_ZFA`,
- the fold `φ ∈ {+I, −I}`,
- whether it is a prime closure.

The class data come from [`assembly_index.py`](assembly_index.py), whose census and
brute-force checks are in PR #265.

### 2.2 State

At scale `k` (word length `2k`), the state is a normalized population `n_k` over the classes of
length `≤ 2k`. The initial state at `k = 1` is the single class `^v` (the primordial closure) with
population 1.

**Persistence:** the previous population is carried into the next scale with weight 1. Assemblies
do not disappear unless the top-down filter removes them.

The mass is measured over the **cumulative library** at each scale, not only the newly joined
assemblies. Two diagnostics are always reported:

- `floor_fraction(k)` = share of `M_L(k)` carried by length-2 classes;
- `mean_length(k)` = `Σ n_k[z] · len(z)`.

A plateau carried by the floor is not a cascade. **A candidate plateau is rejected if
`floor_fraction > 0.5` at either of the two plateau scales.**

### 2.3 Bottom-up join `J`

For every ordered pair of classes `(x, y)` with `len(x) + len(y) ≤ 2(k+1)`, concatenate their
representative words, canonicalize, and look up the parent class `z`. Add

```
n_{k+1}[z] += n_k[x] * n_k[y]
```

to the join contribution. Both orders are counted (concatenation is ordered). The join does not
invent a new primitive and does not change the alphabet.

### 2.4 Top-down blanket `S`

A blanket at scale `k` has an assembly capacity

```
A_k = max(1, 2k - 2).
```

An assembly survives at scale `k` only if `len(z) ≤ 2k` and `a_ZFA(z) ≤ A_k`. The capacity is a
phenomenological statement: at scale `k`, an assembly must be at least one join cheaper than the
linear bound `2k − 1`. It is **not** derived from QLF. The `max(1, ...)` floor keeps the primordial
length-2 closure alive.

After the join and filter, the population is normalized to sum to 1.

### 2.5 Mass and transfer

Two masses are reported:

- **primary (fair comparison with the old census):**
  `M_L(k) = Σ n_k[z] · 8^(−len(z))`;
- **assembly-weighted (secondary):**
  `M_A(k) = Σ n_k[z] · 8^(−a_ZFA(z))`.

The transfer ratio is `W(k) = M(k+1) / M(k)` for each mass.

A **candidate plateau** requires the last two ratios to differ by less than 5% and both to lie in
`[0.5, 2.0]`. With only three ratios (scales 1→2, 2→3, 3→4), this is a screen, not an inertial-range
proof. All ratios are reported; no exponent is fitted.

### 2.6 Ablations

| label | change | purpose |
|---|---|---|
| `full` | the model above | the test |
| `no_filter` | `A_k = 2k − 1` (no assembly filter) | does the top-down constraint matter? |
| `ordinary` | filter on `a` instead of `a_ZFA` | does closure-constrained reuse matter, or just ordinary reuse? |
| `scalar` | `M_scalar(k) = balanced_word_count(2k) · 8^(−2k)` | the raw closure-count baseline; no assembly memory |

If `full` and `no_filter` (or `ordinary`, or `scalar`) give the same transfer ratios, the
corresponding ingredient is doing no work.

### 2.7 Kill condition

The route fails in this state space if:

1. `full` has no candidate plateau, **or**
2. `full` and `scalar` are indistinguishable, **or**
3. the plateau appears only after changing `A_k` or the normalization after seeing the run.

A negative result is a valid outcome and must be recorded as such. A positive result is only a
reason to build the next model, not a claim that QLF derives turbulence.

---

## 3. What would count as success

A candidate plateau in `M_L` under the frozen `full` model, **absent** in the `scalar` baseline, and
**sensitive** to the `a_ZFA` filter (i.e. `ordinary` or `no_filter` differs). Only then would we
proceed to the next layer: an octave recursion with circulation `q`, a conserved flux, and the
`E(k)` / Zipf-residual measurements.

A plateau in `M_A` alone is not enough: `M_A` uses the assembly index as the weight, so it is
partly built in. It is reported as a diagnostic, not as the primary test.

---

## 4. Limitations (stated before the run)

- **Mean-field.** The state is a population over canonical classes; correlations between
  subassemblies are discarded.
- **Length ≤ 8.** The universe is the exhaustive census through length 8, not 10. This keeps the
  transition enumeration exact and fast. It gives only four scales.
- **No circulation `q`.** The proposal’s `P_k(a, φ, q)` is reduced to `(a, φ)` for this screen. A
  cascade test with conserved circulation is the next model, not this one.
- **No tensor sector.** This is the flat-history sector only; #266 is separate.
- **Arbitrary capacity.** `A_k = max(1, 2k − 2)` is a model choice, frozen before the run.
- **No physical claim.** No electron, vacuum turbulence, chemistry, or copy-number claim.

---

## 5. Reproduce

```bash
python3 assembly_transport.py --self-test
python3 assembly_transport.py --run
```

The run writes `data/assembly_transport_census.json`. The pre-registration is frozen at the commit
that adds this file; later changes to the model require a new document, not an edit to this one.

---

## 6. Results (post-run)

The frozen model was run at the commit that adds `assembly_transport.py`; nothing below changes the
model.

| model | `W_L` (1→2, 2→3, 3→4) | candidate plateau | floor-dominated |
|---|---|---:|---:|
| `full` | 0.5078, 0.5760, 0.6003 | no | yes (97.2–100%) |
| `ordinary` | identical to `full` | no | yes |
| `no_filter` | identical to `full` | no | yes |
| `scalar` | 0.3281, 0.4762, 0.5802 | no | no |

- 1,442 canonical classes, 195,416 words, 189 allowed transitions.
- `floor_fraction` = 1.000, 0.985, 0.977, 0.972; `mean_length` = 2.000, 3.000, 4.000, 5.122.
- `full` differs from `scalar` (max relative difference of `W_L` = 0.354), so assembly memory does
  change the transfer. But `full`, `ordinary`, and `no_filter` are numerically identical: the
  top-down capacity is non-binding and the closure-constrained/ordinary distinction does no work in
  this screen.
- The last two `full` ratios happen to be within 5%, so the raw plateau rule fires; the
  pre-registered floor diagnostic rejects it. Verdict: **`negative_no_candidate_plateau`**.

**Interpretation.** This is a negative result for this state space, not a refutation of cooperative
assembly. The mean-field library remains dominated by the primordial length-2 closure; the joins add
too little mass to shift it, and the capacity never binds. A next model would need a per-scale
normalization or a circulation-conserving state, but that is a new pre-registration, not an edit to
this one.
