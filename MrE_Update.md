# MrE Update: one binary observation, specified and proved

Part of the [Quantum Logical Framework (QLF)](README.md). Issue #221.

Proofs: [`lean/QLF_MrEUpdate.lean`](lean/QLF_MrEUpdate.lean). Reference implementation and test
vectors: [`mre_update.py`](mre_update.py), [`data/mre_test_vectors.json`](data/mre_test_vectors.json).
Background: [`MRE.md`](MRE.md), [`lean/QLF_FreeEnergy.lean`](lean/QLF_FreeEnergy.lean).

This is the contract for the shared MrE implementations (quantum-os `mre-core`, the rholo native
wrapper, rhogov calibrated trust, BYOID authentication risk). It is a statement about inference,
not physics.

## 1. The model

| Item | Fixed as |
|---|---|
| Hypothesis space | Two outcomes, `H` and `¬H` |
| Prior | `P(H) = p`, any `0 < p < 1`. **Not** restricted to the uniform prior |
| Observation | One binary outcome `E` or `¬E`, with likelihoods `a = P(E \| H)` and `b = P(E \| ¬H)` in `[0, 1]` |
| Feasibility | The observed outcome has positive probability: `m = P(E) = p·a + (1−p)·b > 0` (for `¬E`, `m < 1`) |
| Posterior | `P(H \| E) = p·a / m`, `P(H \| ¬E) = p·(1−a) / (1−m)` |
| Information measure | Kullback–Leibler divergence in **nats**, `D(q ‖ r) = q log(q/r) + (1−q) log((1−q)/(1−r))`, with `0·log 0 = 0` (`binary_kl`) |
| Composition | Observations are **conditionally independent given the hypothesis** |
| Arithmetic | The update is exact rational arithmetic. Logarithms appear only in the information quantities, which are diagnostics and are never fed back into the update |

## 2. What is proved

**The bound is on the expected gain.** Before the observation is made, the information it is
expected to deliver is

`EIG = m·D(P(H|E) ‖ p) + (1−m)·D(P(H|¬E) ‖ p)` (`eig_eq_expected_kl`),

which is the mutual information `I(H; E) = h(m) − p·h(a) − (1−p)·h(b)` (`eig_eq_entropy`), where
`h` is the binary entropy. Since `h ≤ log 2`:

- `eig_le_log_two`: **`EIG ≤ log 2` for every prior and every likelihood pair.** One binary
  observation is expected to deliver at most one bit.
- `eig_nonneg`: `EIG ≥ 0`.
- `eig_eq_log_two_iff`: `EIG = log 2` exactly when the prior is uniform and the observation is
  perfectly discriminating (`{a, b} = {0, 1}`). This is the half-spin closure case,
  `binary_kl_delta_uniform` in `QLF_FreeEnergy`.

**The pointwise bound is false.** The original wording of #221 ("each binary observation moves
the posterior by at most log 2") does not hold. Aria (aixaria0) gave the counterexample on the
issue, now a theorem (`pointwise_bound_false`): prior `p = 0.01`, `a = 1`, `b = 1/9801`. Observing
`E` gives posterior exactly `0.99`, and `D(0.99 ‖ 0.01) = 0.98·log 99 ≈ 4.50 > log 2`. The outcome
was improbable (`P(E) = 0.0101`), so its expected contribution is small: `EIG ≈ 0.055`. The
earlier lemma `binary_kl_uniform_le_log_two` is correct and does not contradict this, because its
reference distribution is the uniform prior.

So an implementation may assert `EIG ≤ log 2` on every observation it is offered, and may not
assert `D(posterior ‖ prior) ≤ log 2` on the outcome it receives.

**The update is MrE, and unique.**

- `mre_update_unique` (likelihoods strictly positive, `0 < a`, `0 < b`): among joint
  distributions that put all their mass on the observed outcome, exactly one has least relative
  entropy to the prior joint, and it is the Bayes posterior. The proof shows the constrained
  divergence equals `D(s ‖ P(H|E)) − log P(E)` (`mre_eq_kl_posterior`), so it is minimised only
  at `s = P(H|E)`. This is Caticha's result that MrE with a data constraint reproduces Bayes'
  rule, specialised to two hypotheses.
- `mre_update_unique_on_support` (the full domain `a, b ∈ [0, 1]` with `P(E) > 0`): the same
  conclusion for candidates on the prior's support (`Admissible`: no mass on `H ∧ E` if
  `p·a = 0`, none on `¬H ∧ E` if `(1−p)·b = 0`). When one likelihood is zero the support leaves
  a single candidate, and it is the posterior (`1` if `b = 0`, `0` if `a = 0`).
- `unrestricted_objective_fails`: the support restriction is necessary. Aria (aixaria0) found
  this in review of PR #242. A candidate with mass where the prior joint has none has relative
  entropy `+∞`, but the real-valued formula returns a finite number there. With `p = 1/2`,
  `a = 1`, `b = 0` it scores the impossible candidate `s = 0` at `0` and the Bayes posterior
  `s = 1` at `log 2`. See the boundary policy in §3.
- `prior_unique_minimizer`: with no constraint the minimiser is the prior itself.
- `uninformative_posterior`, `uninformative_eig`: an observation with `a = b` leaves the prior
  unchanged and carries zero expected information.

**Composition.** `sequential_update`: for conditionally independent observations, updating on
`E₁` and then on `E₂` gives the same posterior as a single update with likelihoods `a₁a₂` and
`b₁b₂`. In odds form, posterior odds = prior odds × `(a₁/b₁)(a₂/b₂)`, so log-likelihood ratios
add. Expected information gains do **not** add in general (`I(H; E₁, E₂)` is at most the sum of
the per-observation gains under conditional independence, and the total over `n` observations is
bounded by the prior entropy `h(p)`), and nothing here claims they do.

All of the above use no axioms beyond Lean's own (see the `QLF_MrEUpdate` block of
[`lean/QLF_AxiomAudit.lean`](lean/QLF_AxiomAudit.lean)).

## 3. Arithmetic model

Inputs (`p`, `a`, `b`) are rationals. The posterior is `p·a / (p·a + (1−p)·b)`, a rational, so
every node computes the same value bit for bit. Implementations should carry numerator and
denominator (or a fixed-point representation with an exact-rational reference check) and must
reject an observation whose probability under the prior is zero. Divergences and `EIG` are
floating-point diagnostics; [`mre_update.py`](mre_update.py) reports them in nats rounded to 12
places.

**Boundary policy.**

| Case | Rule |
|---|---|
| `P(E) = 0` (for example `a = b = 0`) and `E` is reported | Reject the observation. No update is defined |
| `b = 0 < a`, `E` observed | Posterior is exactly `1` |
| `a = 0 < b`, `E` observed | Posterior is exactly `0` |
| Any code that evaluates the MrE objective itself | A candidate with mass where the prior joint is zero has divergence `+∞`. Never evaluate the bare formula there |

The reference `mre_divergence` in [`mre_update.py`](mre_update.py) implements the last row, and
the vectors include both zero-likelihood cases and the impossible observation.

## 4. Worked example: the four FreeTrust risk areas

Each area is a two-hypothesis question with its own prior and one binary signal. The numbers are
illustrative and are the test vectors in [`data/mre_test_vectors.json`](data/mre_test_vectors.json).

| Area | `H` | Prior | Signal `E` | `P(E\|H)` | `P(E\|¬H)` | `P(H\|E)` | `D(post ‖ prior)` | `EIG` |
|---|---|---|---|---|---|---|---|---|
| Identity | the key holder is the owner | 19/20 | login from a known device | 99/100 | 1/20 | 1881/1886 | 0.041 | 0.156 |
| Presence | the peer is live | 4/5 | answers a beacon | 9/10 | 3/10 | 12/13 | 0.059 | 0.145 |
| Security | the node is compromised | 1/50 | anomaly alert fires | 7/10 | 1/100 | 10/17 | 1.632 | 0.045 |
| Privacy | data has leaked | 1/5 | canary is seen | 1/2 | 1/10 | 5/9 | 0.306 | 0.073 |

The security row is the counterexample's shape in practice: a rare alarm that fires moves the
posterior by more than one bit (1.63 nats), while its expected gain is small (0.045 nats).

## 5. Test vectors

`python3 mre_update.py` checks every invariant above on the vectors (bound, non-negativity, the
KL form, the saturation case, Aria's counterexample, the uninformative case, the zero-likelihood
and impossible-observation boundaries, MrE minimality on a grid, sequential composition), and `--write` regenerates the JSON. The crate in quantum-os #260 can check against
the same file.

## 6. Open

- The bound for one observation with more than two outcomes (`EIG ≤ log k`) and for more than two
  hypotheses follows the same proof but is not formalised here.
- `I(H; E₁,…,Eₙ) ≤ h(p)` for many observations is standard but not formalised.
