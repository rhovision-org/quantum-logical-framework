# Neutrinos, the vacuum, and what organization adds

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.
> Lean: [`lean/QLF_VacuumCorrelation.lean`](lean/QLF_VacuumCorrelation.lean), no axioms.
> Exact census: [`vacuum_correlation_census.py`](vacuum_correlation_census.py).
> Registry entries: P24, C24, C25 and B16 in [`Principles.md`](Principles.md).

Three AI review notes (2026-11-27), written after [`Colour_Closure.md`](Colour_Closure.md) (#327),
proposed three programmes, each with proof gates:

- a **handedness mass gap**: the electron as the least-energy mode that keeps a confirmed electrical
  handedness (gates H0–H7);
- **neutrino versus vacuum**: what separates a low-energy neutrino from the possibilistic Brownian
  activity of the vacuum (gates N0–N5);
- a **vacuum correlation bridge**: the α residual and neutrino oscillation as two readings of one
  vacuum correlation structure (gates V0–V6).

This page records what was checked, what is now proved (N0, V0, V1, H1), and where the rest stands.

---

## 1. What was checked

Every theorem name, number and file the notes cite was checked against `main`.

| Cited | Found | Note |
|---|---|---|
| `one_axis_majorana`, `twoAxisMinimal_majorana_count`, `electron_not_majorana` | [`QLF_Majorana`](lean/QLF_Majorana.lean) | 16 of 24 two-axis minimal closures are not self-conjugate, as stated. |
| `electronCycle_folds_negI`, `electronCharged_not_countBalanced` | [`QLF_ElectronClosure`](lean/QLF_ElectronClosure.lean) | |
| `electron_neutral_but_handed` | [`QLF_Handedness`](lean/QLF_Handedness.lean) | |
| `delay_colour_blind` | [`QLF_ColourClosure`](lean/QLF_ColourClosure.lean) | |
| Neutrino masses 0.36, 8.62, 50.1 meV | [`Lepton_Generations_Fourier.md`](Lepton_Generations_Fourier.md) §6 | A conditional prediction (signed Koide, normal ordering), pre-registered as P1 there. |
| 0.36 meV ↔ 87 GHz | arithmetic | `E/h = 0.36×10⁻³ eV / 4.1357×10⁻¹⁵ eV s = 87 GHz`. Correct. |
| "below about 100 GHz" | [`VacuumEnergy.md`](VacuumEnergy.md) §4 and §4.1 | The far-IR window is a soft bound, not a line. |
| Vacuum scale about 2.26 meV | outside the repo | `ρ_Λ^{1/4} ≈ 2.2–2.3 meV` for Planck 2018 parameters (2.24 meV with `Ω_Λ = 0.685`, `h = 0.674`). It is the fourth root of an energy density, not a particle threshold, as the note itself says. |
| α table: 137.032002 (−0.003997), 137.040493 (+0.004494), 137.035691 (−0.000308) | [`Carbon_Superconductivity.md`](Carbon_Superconductivity.md) §46–§48 | Verbatim. The third is post hoc, and the same weights fail on the proton (§48). |
| `C(2n,n)` and `I_n = (2/n)C(2n−2,n−1)` | [`QLF_CensusBrownian`](lean/QLF_CensusBrownian.lean), [`alpha_residual_bridge.py`](alpha_residual_bridge.py) | `I_n` is `2·Catalan(n−1)`. |
| `dP/dt = Ω × P` | [`QLF_NeutrinoOscillation`](lean/QLF_NeutrinoOscillation.lean) | `flavor_precession_conserves_number`. The coupling of `Ω` to the vacuum is open, as the note says. |

**The 87 GHz match is a coincidence until a coupling is derived.** The 0.36 meV is itself
conditional, the 100 GHz is a soft edge, and nothing in either derivation refers to the other. The
same holds for the comparison of 0.36 meV with the vacuum scale: they are different kinds of quantity.
Neither is used as evidence below.

---

## 2. N0: the neutrino word is a vacuum closure

QLF reads the minimal neutrino as the one-axis closure `^v`
([`QLF_Majorana`](lean/QLF_Majorana.lean)). A vacuum fluctuation on the same axis is the same word.

- **Provenance is not in the word** (`no_word_observable_separates`, `neutrino_vacuum_same_reading`).
  Any observable that is a function of the word, including the twist counts, the Pauli fold and the
  closing delay, gives the same value on both. This part is bookkeeping: it holds by definition.
- **The reading does not see the order of the pair.** `^v` and `v^` are different words with the same
  reading: counts `(1,1,0,…)`, fold `−I`, delay `0` (`nu_reading`, `nu_reading_order_blind`).
- **The fold does not see the axis.** In every context `b … c`, inserting `^v` folds the same as
  inserting any Hermitian pair `[t, t†]`, on any of the four axes (`neutrino_block_fold_blind`).
- The word is its own antiparticle (`nu_self_conjugate`), so conjugation gives no handle either.

So if a neutrino differs from vacuum activity, it differs by a relation to something outside the
word: its provenance, or how it interleaves with other closures. That is gate N1, and §4 shows that
interleaving is a relation the fold does see.

---

## 3. V0: common-mode closures cancel

A closed part changes the fold of whatever surrounds it by one global Pauli phase
(`closed_insertion_is_phase`, P05). The consequence for comparisons:

- **Common mode cancels** (`common_mode_cancels`). If the same closure is inserted anywhere in both
  branches of a comparison, the relative phase between the branches is unchanged, and conversely.
- **One branch does not cancel** (`one_branch_closure_shifts_phase`). Inserted into one branch only,
  `^v` shifts the relative phase by `−1`.

So the note's V0 ("independent vacuum closures do not alter normalized relative-phase observables")
holds for **common-mode** closures. A closure in one branch is detectable, but only as a phase, and by
N0 that phase is the same for every Hermitian pair. Detectability is relational; identity still is not.

---

## 4. V1: same twists, same balance, opposite phase

| Word | Organization | Count balanced | Delay | `F₃²` colour | Fold |
|---|---|---|---|---|---|
| `^v><` | two closures in sequence | yes | 0 | 0 | `+I` |
| `^>v<` | one interleaved closure | yes | 0 | 0 | `−I` |

The two words are rearrangements of one inventory (`same_inventory_opposite_phase`). The first
splits as `^v` then `><` (`independent_splits`); the second is prime: no proper prefix closes
(`interleaved_prime`). In every context the interleaving flips the sign
(`interleaving_flips_phase`).

This is the statement the notes asked for: the participation of a complementary pair can change a
phase while adding no net action. It is a fact about the closure algebra. Whether vacuum
interleavings are what drives neutrino phase evolution or the α correction is gate V2 onward.

---

## 5. H1: the minimal handed closures with the half-spin sign

"Handed" here means *not its own antiparticle* (conjugate each twist and reverse).

- **Length 2.** All 64 two-letter words were checked: every closure folds to `−I` and is
  self-conjugate (`length_two_closures`). The sign is there, the handedness is not.
- **Length 4, one pair on each of two spatial axes.** Of the 24 orderings, the fold is `−I` exactly
  when the two pairs cross, which happens for 8, and none of the 8 is self-conjugate. This holds on all
  three spatial planes (`two_axis_classification`). With a gauge pair the fold is always `+I`
  (`gauge_pair_never_negI`).
- **The electron class.** On the `y, x` plane the 8 are the electron loop `^<v>` and its mirror
  `^>v<`, each with its four rotations (`electron_class`, `electron_in_class`). The interleaved word of
  V1 is the electron loop's mirror.
- **All length-4 closures** (exact computational, [`vacuum_correlation_census.py`](vacuum_correlation_census.py)):
  of the 168 count-balanced length-4 histories over the eight twists, 80 are handed with `+I`, 64
  self-conjugate with `+I`, and 24 handed with `−I`. The 24 are exactly the electron-class loops above.

So the shortest closures that are both handed and carry the half-spin sign have length 4, and they
are the 24 electron-class loops on the three spatial planes. This is the structural content of the
note's "minimal electron mode".

**The pattern does not continue.** At length 6, among the 720 orderings of one pair per spatial axis,
336 are handed with `+I`, 336 handed with `−I`, and 48 are self-conjugate with `−I`; over all 1,860
count-balanced spatial histories of length 6 the split is 768, 876 and 216
([`vacuum_correlation_census.py`](vacuum_correlation_census.py)). The equivalence "`−I` exactly when
handed" is a length-4 fact.

**What H1 does not say.** These loops are uncharged: charge is the unmatched gauge twist
(`electronCharged_not_countBalanced`), which H1 does not touch. Being the least *complex* handed `−I`
closure says nothing yet about being the least *energetic* persistent charged mode. That is H2–H6.

---

## 6. The remaining gates

| Gate | Target | Status |
|---|---|---|
| H0 | Define confirmed handedness from shared closures, without particle labels | Open. A candidate: handed = not self-conjugate, confirmed = the conjugate pair is distinguished by a joint closure with a third word. |
| H1 | Classify minimal non-self-conjugate spatial closures with `−I` | **Proved** (§5). |
| H2 | Which of these can carry an unmatched gauge distinction | Open. The gauge twist commutes with the spatial loop, so every H1 loop accepts one; the question is which persist. |
| H3 | Persistence of the distinction across successive shared closures | Open. `relay_phase_transfer` ([`QLF_SharedReality`](lean/QLF_SharedReality.lean)) is the closest tool. |
| H4–H6 | Persistence ↔ vacuum resonance ↔ rest energy; a positive minimum; the electron mass | Bridge (B16, B07). No derivation of an energy threshold exists. |
| H7 | Whether sub-vacuum-scale neutrinos take part in the field relations | Conjecture. |
| N0 | Neutrino word indistinguishable from a vacuum closure by counts, fold and delay | **Proved** (§2); the provenance part is bookkeeping. |
| N1 | A relational invariant that separates the neutrino | Partial. Interleaving is a relational invariant the fold sees (§4); that a neutrino carries one is open. |
| N2–N5 | Persistence; a change in the closure census `ΔW_R`; vacuum phase correlations; weak and oscillation phenomenology | Open. N3 needs a matched-conditions definition of "vacuum with ν" before `ΔW_R` means anything. |
| V0 | Independent closures do not alter relative phase | **Proved for common mode** (§3); one-branch insertion shifts the phase. |
| V1 | Interleaving alters relative phase without altering net action | **Proved** (§4). |
| V2 | A connected vacuum correlation `K_R(a,b)` from the closure census | Open; the central step. Needs a phase-weighted measure that is not post hoc (the §47 lesson). |
| V3–V6 | The α screening correction; neutrino phase differences; mixing angles and `Δm²`; one mechanism for both | Bridge (B16). A decoherence bound from oscillation data is the falsifier the note names. |

The registry rows are P24 (proved: organization carries phase), C24 (the handedness mass gap), C25
(a neutrino's significance is relational) and B16 (the vacuum correlation bridge) in
[`Principles.md`](Principles.md).
