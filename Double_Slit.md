# The Double-Slit Experiment in [QLF](README.md)

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

Feynman called the double slit "the only mystery" of quantum mechanics. In QLF it is not a mystery — it is the **physical face of a machine-checked theorem**: `count_does_not_determine_phase` ([`lean/QLF_PhaseInformation.lean`](lean/QLF_PhaseInformation.lean)). The fringe pattern is *phase* information that the *count* (Shannon) cannot carry; a which-path measurement trades that phase for count-definiteness; and "measurement" is just ZFA closure, so no collapse postulate is needed. The whole experiment is the count/phase distinction of [`Shannon_And_Phase.md`](Shannon_And_Phase.md), drawn on a screen.

---

## 1. The setup in QLF

A particle is not a tiny ball and not a literal wave — it is a **history exploring the possibility tree**. Between source and screen, the substrate generates every admissible ZFA-closed history (`expand_generation`); the physical event is the one that closes. Two open slits define **two families of admissible sub-histories** reaching a given screen point `φ`: the bundle `A` through the upper slit and the bundle `B` through the lower slit.

The amplitude at `φ` is the path-integral sum already derived in [`Born_Rule.md`](Born_Rule.md) §2 — the QuCalc realization of Feynman's sum-over-histories, with the path space restricted to admissible Pauli-closed histories:

$$\langle \varphi \mid \psi \rangle \;=\; \sum_{h \,\in\, \mathcal{T}_{\psi \to \varphi}} e^{\,i\,\theta(h)}\;=\; A_A + A_B,$$

where `θ(h)` is the cumulative QuCalc phase of history `h`, and `A_A`, `A_B` are the phase-coherent sums over the two slit bundles.

---

## 2. The fringes are phase, not count

The screen intensity is the Born-rule probability ([`Born_Rule.md`](Born_Rule.md) §3):

$$P(\varphi) \;\propto\; |A_A + A_B|^2 \;=\; |A_A|^2 + |A_B|^2 + 2\,\mathrm{Re}\!\left(A_A^{*} A_B\right).$$

The first two terms are the **counts** — how many ways to reach `φ` through each slit, the Shannon/multiplicity content. The third term — the **cross term** — is the fringe, and it is set entirely by the **phase difference** `θ_A − θ_B` (the path-length difference, accumulated as QuCalc phase). Bright fringe where the two bundles are in phase, dark where they are out of phase.

This is exactly `count_does_not_determine_phase` on a screen: across neighbouring screen points the *number* of contributing paths barely changes, yet the *intensity* swings from bright to dark — **same count, opposite result, because the phase differs.** The interference pattern is pure phase information; the count cannot encode it. (The same theorem says two histories with the identical twist multiset fold to `+I` vs `−I`; here two screen points with the same path-count light up or stay dark depending on phase.)

---

## 3. Which-path measurement: trading phase for count

Put a detector at the slits to learn *which* slit the particle went through. The fringes vanish — you get two plain bumps, `|A_A|^2 + |A_B|^2`, the bare counts. Why, in QLF?

A which-path detector is **an extra ZFA closure** that resolves the path into a **definite count distinction** ("upper" vs "lower"). By the count↔phase conjugacy — the [uncertainty principle](UncertaintyPrinciple.md), which in QLF *is* the Fourier-duality between the count face and the phase face — sharpening the path-count **smears the relative phase** `θ_A − θ_B` across the ensemble. The cross term `2 Re(A_A^* A_B)` then averages to zero, and only the counts survive. No fringe.

Nothing collapses in the textbook sense. The which-path closure simply moves the information from the **phase** (where the count cannot hold it) into a **count** (which Shannon can) — and by conjugacy you cannot keep both. Measurement is synchronization/closure, not a separate physical process ([`Measurement_Problem.md`](Measurement_Problem.md)). Erase the which-path record after the fact and the phase coherence is restored in the coincidence-sorted subset — the **delayed-choice quantum eraser**, already worked out in [`Delayed_Choice_Eraser.md`](Delayed_Choice_Eraser.md).

---

## 4. Wave–particle "duality" dissolved

There is no paradox because the substrate is always **discrete histories**:

- The "**wave**" is the *phase structure of the multiplicity* — the `e^{iθ(h)}`-weighted sum over admissible paths. Interference is what phase-weighted counting looks like.
- The "**particle**" is the *single realized ZFA closure* — one history out of the multiplicity, selected with Born probability (the multiplicity principle, *the thing that can happen in the most ways happens most often*, [`Born_Rule.md`](Born_Rule.md), [`MRE.md`](MRE.md)).

"Goes through both slits" means the **possibility stream explores both bundles**; "lands as a dot" means **one closure realizes**. The two descriptions are the phase face and the count face of the one closure — the very pair the double slit is built to expose.

---

## 5. Honest scope

- The **mechanism** is the QLF content and it rests on proven pieces: the path-integral amplitude and interference Born rule ([`Born_Rule.md`](Born_Rule.md)), the count/phase separation (`count_does_not_determine_phase`, machine-checked), and measurement-as-closure ([`Measurement_Problem.md`](Measurement_Problem.md)). The which-path → no-fringe step is the uncertainty conjugacy ([`UncertaintyPrinciple.md`](UncertaintyPrinciple.md)).
- The **quantitative fringe spacing** (slit separation, de Broglie wavelength `λ = h/p`) is set by the phase-accumulation rate, i.e. the frequency-synthesis relations (`m = ℏf/R`, momentum ↔ phase) developed in [`Frequency_Synchronization.md`](Frequency_Synchronization.md) and [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md); it is not re-derived here. This doc owns the *structural* reading — fringes = phase, which-path = count, conjugacy = no fringes.

**The takeaway:** the double slit is the laboratory demonstration that amplitude (count) is not enough — phase is independent information. QLF proved that as a theorem; the screen shows it as light and dark.

---

## 6. The double slit in time

A spatial double slit lets a history through at two **places**. A time double slit lets it through at two **instants**. The experiment has been done: Tirole et al. switched the reflectivity of an indium-tin-oxide mirror on twice, a few hundred femtoseconds apart, and the reflected light showed interference fringes in its **spectrum**, with spacing set by the inverse of the slit separation ([*Nature Physics* **19**, 999 (2023)](https://doi.org/10.1038/s41567-023-01993-w)). Lindner et al. did the same with electrons ionised in two optical half-cycles ([*PRL* **95**, 040401 (2005)](https://doi.org/10.1103/PhysRevLett.95.040401)). The continuum precursor is Moshinsky's diffraction in time ([*Phys. Rev.* **88**, 625 (1952)](https://doi.org/10.1103/PhysRev.88.625)).

In QLF time is synthesized as a count of ticks and frequency is phase per tick ([`lean/QLF_LoopClosure.lean`](lean/QLF_LoopClosure.lean) `phase k N = k mod N`). So a time slit is the same kind of object as a space slit: a set of ways distinguished by *when* along the history they pass instead of *where*. [`lean/QLF_TimeDoubleSlit.lean`](lean/QLF_TimeDoubleSlit.lean) proves that the two experiments are one theorem.

**What is proved (no axioms; footprint `propext`, `Classical.choice`, `Quot.sound` only):**

| Statement | Lean |
|---|---|
| Both patterns are one function `twoPath a₁ a₂ φ = \|a₁ + a₂e^{iφ}\|²`, at `φ = ω·Δt` in time and `φ = k·Δx` in space. The common phase of the first slit drops out, so only the separation matters | `time_is_twoPath`, `space_is_twoPath` |
| Equal accumulated phase gives equal intensity: the time and space double slits are the same pattern | `space_time_duality` |
| The pattern is the Born weight of the event "either slit", and the fringe is its pairwise interference term `I₂` from [`Interference_NoGo.md`](Interference_NoGo.md) | `twoPath_eq_born`, `twoPath_fringe_term` |
| The spectrum repeats every `2π/Δt` in frequency | `time_fringe_period` |
| Equal slits give `2\|a\|²(1 + cos ωΔt)`: exactly dark at `ωΔt = π`, four times one slit at `ωΔt = 2πn` | `twoPath_equal`, `time_dark_fringe`, `time_bright_fringe` |
| One time slit gives a flat spectrum | `single_time_slit_flat` |
| Which-time records, in any complex inner-product space: identical records keep the fringes, orthogonal records give `\|a₁\|² + \|a₂\|²` at every frequency, and in general the fringe swing is at most `2\|a₁\|\|a₂\|·\|⟨r₁,r₂⟩\|` | `marked_coherent`, `marked_orthogonal`, `marked_visibility_bound` |
| On an `N`-tick clock (`ζ^N = 1`) the amplitude at tick `n` reads only the substrate phase `n mod N` | `tick_amp_phase` |
| Fringes redistribute intensity and create none: summed over the `N` frequencies the total is `N(\|a₁\|² + \|a₂\|²)` whenever the separation is not a whole cycle | `tick_conservation` |
| On the Pauli-scalar clock `ζ = i` (`μ₄ = {±1, ±i}`, `N = 4`) with equal slits one tick apart, the four frequencies read `4, 2, 0, 2` times `\|a\|²` | `mu4_pattern` |

The `μ₄` case is the substrate version of the whole experiment. The dark fringe at `k = 2` is `i² = −1`: two ways that arrive with opposite phase. [`Interference_NoGo.md`](Interference_NoGo.md) N4 (`unsigned_no_dark_fringe`) proves that no tally of unsigned counts can do that, so the dark fringe in time, like the one in space, is phase information that the count does not carry (§2).

The which-time bound is the time form of §3. A record that tells the instants apart (`⟨r₁,r₂⟩ = 0`) moves the information into a count and the fringes go; a partial record weakens them in proportion to its overlap. The eraser of [`Delayed_Choice_Eraser.md`](Delayed_Choice_Eraser.md) works the same way in time.

## 7. The two uncertainty relations

The double slit in space and the double slit in time are the two conjugate pairs of the [uncertainty principle](UncertaintyPrinciple.md): position with momentum, and time with energy. In each experiment the slit separation fixes the fringe spacing in the conjugate variable, and [`lean/QLF_TimeDoubleSlit.lean`](lean/QLF_TimeDoubleSlit.lean) §3a proves the spacing exactly.

| Pair | Slits separated in | Fringes appear in | Proved | With `ℏ` |
|---|---|---|---|---|
| position–momentum | space, `Δx` | wavenumber `k` | a shift `q` is a symmetry of the pattern iff `q·Δx ∈ 2πℤ` (`space_shift_iff`); every positive spacing obeys `q·\|Δx\| ≥ 2π` (`space_reciprocity`) | `Δp·Δx = h` for the least spacing (`p = ℏk`) |
| time–energy | time, `Δt` | frequency `ω` | a shift `p` is a symmetry iff `p·Δt ∈ 2πℤ` (`time_shift_iff`); `2π/\|Δt\|` is a spacing and every positive spacing obeys `p·\|Δt\| ≥ 2π` (`time_reciprocity`) | `ΔE·Δt = h` for the least spacing (`E = ℏω`) |

The two rows are one theorem read twice, because both patterns are `twoPath` of the accumulated phase (`space_time_duality`). Two slits close together in time give coarse fringes in energy; slits far apart give fine ones. This is the Fourier reciprocity between a variable and its conjugate.

Two things this section does not claim. First, these are exact statements about the **fringe spacing**, not the variance inequalities `Δx·Δp ≥ ℏ/2` and `Δt·ΔE ≥ ℏ/2`; the `ℏ/2` quantum is [`lean/QLF_Uncertainty.lean`](lean/QLF_Uncertainty.lean)'s and the sharp Shannon form is the entropic relation in [`UncertaintyPrinciple.md`](UncertaintyPrinciple.md) §3a. Second, `ℏ` enters only as the conversion `E = ℏω`, `p = ℏk`; nothing here derives it. The second face of uncertainty, that learning which slit costs the fringe, is the record bound of §6 (`marked_visibility_bound`), and it holds in both rows for the same reason.

**Scope.** The theorems assume a phase linear in the tick count and idealise each time slit as an instant. They do not derive the Born rule, `ℏ`, or a frequency in hertz, and Moshinsky's finite-width shutter is not treated.

## See also

- [`Shannon_And_Phase.md`](Shannon_And_Phase.md) · [`lean/QLF_PhaseInformation.lean`](lean/QLF_PhaseInformation.lean) — the count/phase separation, proved.
- [`Born_Rule.md`](Born_Rule.md) · [`Superposition.md`](Superposition.md) · [`Measurement_Problem.md`](Measurement_Problem.md) — amplitudes, superposition, closure-as-measurement.
- [`Delayed_Choice_Eraser.md`](Delayed_Choice_Eraser.md) — the eraser variant (fringes in coincidence subsets).
- [`UncertaintyPrinciple.md`](UncertaintyPrinciple.md) — the count↔phase conjugacy behind which-path-erases-fringes.
- [`lean/QLF_TimeDoubleSlit.lean`](lean/QLF_TimeDoubleSlit.lean) · [`Interference_NoGo.md`](Interference_NoGo.md) — the double slit in time and the two uncertainty relations as fringe reciprocities; the Born interference term it reuses.
