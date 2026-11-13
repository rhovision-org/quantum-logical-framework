# Lepton mass-ratio protocol — a pre-registered #140 attempt

**Status:** pre-registration draft, `B-OPEN`. **No result is claimed.** This document freezes the selection rules and comparison order for an attempt at the charged-lepton mass ratios before looking at the target numbers. It adds no new prediction, axiom, fitted parameter, or empirical evidence.

**Issue:** [#140](https://github.com/rhovision-org/quantum-logical-framework/issues/140). **Related:** [#11](https://github.com/rhovision-org/quantum-logical-framework/issues/11), [`Claim_Status.md`](Claim_Status.md), [`Proof_to_Physics.md`](Proof_to_Physics.md).

---

## 1. Frozen inputs that already exist

These are used as inputs; none is a mass-ratio derivation.

| Input | Anchor / file | Role |
|---|---|---|
| Three generations from the three spatial axes | `QLF.num_generations_eq_three`, `QLF.three_axis_signature` (`lean/QLF_Generations.lean`) | fixes the generation count |
| Koide invariant `Q = 2/3` from `N = 3`, `A² = 2` | `QLF.koide_two_thirds`, `QLF.three_generations_satisfy_koide` (`lean/QLF_Koide.lean`) | fixes the three-phase form, not its orientation |
| Electron cycle `^<v>` closes, uses axes `{x,y}`, folds to `−I` | `QLF.electronCycle_countBalanced`, `QLF.electronCycle_folds_negI`, `QLF.interleaved_xlvr_folds_to_negI` (`lean/QLF_ElectronClosure.lean`) | the one verified lepton anchor |
| Blind topology tool | `lepton_blind_classifier.py` part A | candidate-class enumeration, no measured masses |

The electron's axis content is not automatically the muon's or tau's. The ladder in the issue thread is a **topology candidate**, not a mass derivation.

## 2. Selection rules frozen before comparison

The following rules are fixed for all selection stages:

1. **Rooted causal histories.** `History := List Twist`; `pfx ++ [t]` extensions are distinct from cyclic rotations. No wraparound quotient is used.
2. **Spatial twists only** for the lepton-content scan.
3. **No immediate Hermitian reversal** in the candidate word.
4. **First-return ZFA:** the word closes, and no proper nonempty prefix closes.
5. **Rooted `B = 0`:** a free lepton, not a confined baryon.
6. **Final Pauli fold `−I`:** the same half-spin signature as the electron.
7. **Quotient** by signed spatial-axis permutations and by particle/antiparticle.
8. **Frequency tie-break:** use the number of rooted realizations only to break a remaining class degeneracy.
9. **Parent continuation:** a next-generation candidate must have a causal parent obtained by deleting one conjugate axis pair.

### Known limitations, frozen with the rules

- The `L = 8` τ uniqueness used a **3-axis filter before** the parent rule. That filter is load-bearing and is not derived by the selection rule.
- The parent rule goes **ambiguous at `L = 10`**. It is not an independent proof of “exactly three generations.”
- Therefore the topology stage may propose an ordered candidate ladder, but it cannot by itself establish the mass ratios.

## 3. Mass functional frozen before comparison

The only admissible functional in this attempt is the existing Koide three-phase form:

```
m_i = M (1 + sqrt(2) cos(delta + 2*pi*i/3))^2,   i = 0,1,2
```

- `Q = 2/3` is already derived; it is not a new result here.
- `M` is the overall scale and may be fixed by the electron mass.
- `delta` is the sole dimensionless input. It must be derived from closure counts **before** any muon or tau mass is read.
- No correction term, tuning, or post-hoc adjustment is permitted after comparison.

If no closure-count derivation of `delta` is produced, this attempt has no ratio prediction and must be recorded as such.

## 4. Admissible closure observables

A candidate mass functional may use only frozen substrate quantities:

- axis content (the `{x,y,z}` participation pattern);
- first-return depth / closure length;
- fold sign (`±I`);
- rooted baryon winding `B`;
- orbit multiplicity / number of rooted realizations;
- the existing Koide phase count `N = 3` and transverse count `A² = 2`.

It may not use:

- `m_mu`, `m_tau`, or any ratio derived from them;
- a parameter chosen to make the comparison pass;
- a “correction” whose only justification is the residual.

## 5. Conservative-return obligation

The mass assignment is not a QLF derivation unless a return map recovers the finitary invariants from it:

```
closure class -> mass assignment -> closure class / ~
```

At minimum, the return must recover:

- axis content;
- first-return depth;
- fold sign;
- rooted `B`;
- orbit multiplicity.

If the return cannot recover these invariants, the functional is a fit, not a derivation. The claim record's `proof_obligation.conservative_return_status` stays `NOT_STARTED` until this is supplied.

## 6. Comparison order

**Stage A — topology only.** Run the frozen rules; record all candidate classes and known ambiguities. No masses.

**Stage B — functional only.** Derive `delta` from closure counts, or record that no derivation exists. Freeze the predicted ratios and the functional's free-parameter count.

**Stage C — compare.** Only now read `m_mu/m_e`, `m_tau/m_e`, and Koide `Q` from the comparator. Record the residuals and uncertainties.

**Stage D — decide.**

- If the frozen prediction agrees within the predeclared uncertainty: record `N`/candidate status, not `E`.
- If it misses: record failure and close that mass map. Do not add a correction.
- If `delta` was chosen after seeing the masses: mark the attempt invalid.

## 7. Falsification and stop rules

This attempt is defeated by any of:

- a `delta` selected using the target masses;
- more than the declared free inputs (`M`, `delta`) needed to fit the ratios;
- a mass functional that cannot return the closure invariants;
- a topology ladder whose uniqueness depends on an undeclared axis filter;
- a comparison that changes the selection rules after the target is known.

Failure is a legitimate result and closes this particular map. It does not close QLF's formal generation/Koide results, which are separate `F` statements.

## 8. Current status

| Component | Status |
|---|---|
| Three generations / Koide form | `F` in existing Lean modules |
| Electron `{x,y}`, `−I` anchor | `F` |
| Blind topology ladder | candidate; known `L = 10` ambiguity |
| `delta` from closure counts | **not derived** |
| Mass ratios | **not evaluated**; `B-OPEN` |
| Conservative return | **`NOT_STARTED`** |

The existing issue-thread attempts have closed several routes and refuted several candidate reductions. None produced a parameter-free ratio. This protocol does not reopen them; it fixes the rules for the next attempt.

## 9. Claim record

[`claim_records/lepton_mass_ratio.json`](claim_records/lepton_mass_ratio.json) records this as a `B-OPEN` protocol with:

- `strange_loop.status: B-OPEN`;
- `proof_obligation.conservative_return_status: NOT_STARTED`;
- `evidence_status.bridge: OPEN`;
- G3/G5 `INCOMPLETE`;
- no observed muon or tau mass in the construction inputs.

## 10. Cross-links

- [`lean/QLF_Generations.lean`](lean/QLF_Generations.lean)
- [`lean/QLF_Koide.lean`](lean/QLF_Koide.lean)
- [`lean/QLF_ElectronClosure.lean`](lean/QLF_ElectronClosure.lean)
- [`lepton_blind_classifier.py`](lepton_blind_classifier.py)
- [`Claim_Status.md`](Claim_Status.md), [`Proof_to_Physics.md`](Proof_to_Physics.md)
- Issue [#140](https://github.com/rhovision-org/quantum-logical-framework/issues/140), [#11](https://github.com/rhovision-org/quantum-logical-framework/issues/11)
