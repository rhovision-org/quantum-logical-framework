# Information-Energy Equivalence in QLF: ℏω per Bit, Derived from First Principles

**At any frequency ω, the energy `ℏω` equals exactly one bit of classical information.** This is the QLF formalization of John Wheeler's "it from bit" principle (Wheeler 1990, 2002 conference proceedings) and Chris Fields's recent information-theoretic foundations of physics. The principle is **derived from first principles in QLF**: it follows by conjunction of two axioms already established and (one of them) Lean-anchored.

The two QLF axioms:

1. **Per-event information quantum** — every ZFA closure event carries exactly `log 2` nats = 1 bit of resolved information. [`MRE.md`](MRE.md) §2.1, Lean-anchored as `zfa_closure_minimizes_free_energy` in [`lean/QLF_FreeEnergy.lean`](lean/QLF_FreeEnergy.lean).

2. **Per-event energy quantum** — every ZFA closure event at frequency ω carries energy `E = ℏω`. This is the Planck-Einstein relation, recovered in QLF via the per-qubit ([`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md)) and per-bit ([`Photon_Energy_Bits.md`](Photon_Energy_Bits.md)) accounting.

Their conjunction:

$$\boxed{\;\hbar\omega \;\equiv\; \text{1 bit at frequency } \omega\;}$$

The energy `ℏω` *is* the energy cost of one bit of classical information at observation frequency ω. The Wheeler-Fields principle is therefore not an additional axiom but a **consequence** of QLF's per-event accounting.

*(This `ℏω = 1 bit` equivalence is one row in the broader map of information notions on the QLF substrate — Shannon, algorithmic, Bekenstein/Landauer, quantum, semantic — collected with proof sketches in [`Information_Physics.md`](Information_Physics.md); the bit it prices is the two-valued **½-spin closure**, [`lean/QLF_SpinorInformation.lean`](lean/QLF_SpinorInformation.lean).)*

---

## §1 The Wheeler-Fields principle, stated precisely

**Wheeler 1990, "Information, Physics, Quantum: the Search for Links"** (and continued through Wheeler's 2002 IBM Watson conference contributions and related proceedings): the universe is participatory; every "it" (physical entity, observable property) derives ultimately from a "bit" (yes/no quantum-measurement outcome). Wheeler's "it from bit" recasts physics as information-theoretic: every physical quantity is the answer to a yes/no question; the answer is a single bit; the bit-asking-and-receiving event is the elementary act of physical reality.

**Chris Fields's** more recent work on observers as Markov blankets (Fields 2018, Fields & Levin 2020, and the Friston-Fields collaboration on the free-energy principle) makes the operational version precise: an observer is a Markov-blanket-bounded agent that registers bits of information about its environment, and each bit registration has a minimum energy cost. The minimum action per bit-observation event is `ℏ`; the minimum energy per bit at observation frequency ω is `ℏω`.

The precise claim:

> For any ZFA closure event at frequency ω, the energy contributed and the information resolved are linked by `E_event = ℏω` (energy) and `I_event = 1 bit` (information). Equivalently, the **energy cost per bit at frequency ω is exactly `ℏω`**.

This is a *unit-conversion* identity: it asserts that QLF's natural-units accounting has information and energy as dual quantities, with `ω` as the proportionality factor between them at each closure event.

---

## §2 The QLF derivation chain

### 2.1 Per-event information quantum (Lean-anchored)

From [`MRE.md`](MRE.md) §2.1: the binary partition information-gain bound is

$$D_{KL}(q \mathbin{\Vert} p) \leq \log 2$$

with saturation only at the 50/50 binary partition — exactly the half-spin ZFA closure event. Every ZFA closure event therefore carries

$$I_{\text{event}} \;=\; \log 2 \;=\; 1 \text{ bit (binary)}$$

of resolved information. This is the **per-event information quantum**.

**Lean-anchored** as `zfa_closure_minimizes_free_energy : -binary_kl 1 (1/2) = -Real.log 2` in [`lean/QLF_FreeEnergy.lean`](lean/QLF_FreeEnergy.lean) (commit `ae9ffac` of v0.17.8). The strict-saturation bound `binary_kl_uniform_lt_log_two` (commit `bbcffbe`) confirms uniqueness: no other recognition density on the uniform binary prior achieves more than `log 2`.

### 2.2 Per-event energy quantum

From [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) §1: each qubit (Hermitian-pair half-spin ZFA atom) contributes `ℏω` of rest energy, where `ω` is the qubit's internal Markov-blanket frequency. The constructing delay `Δt = R/f_vac` (per [`Frequency_Synchronization.md`](Frequency_Synchronization.md)) gives `ω = 1/Δt = f_vac/R`, so

$$E_{\text{event}} \;=\; \hbar \omega$$

per ZFA closure event. This recovers the Planck-Einstein relation `E = ℏω` from QLF principles: every quantum event has energy proportional to its frequency, with `ℏ` as the universal proportionality constant.

For photons (gauge-free joint closures, per [`Photon_Energy_Bits.md`](Photon_Energy_Bits.md)), the same per-event `ℏω` applies — but the gauge-free structure means zero rest mass, so the `ℏω` is pure kinetic energy with mass-equivalence `m_rel = E/c²`. For massive constituents (gauge-folded qubits), the `ℏω` per qubit accumulates into rest mass.

### 2.3 Conjunction: ℏω per bit

Each ZFA closure event carries:

- `1 bit` of information (from §2.1)
- `ℏω` of energy (from §2.2)

These are **the same event**. The information quantum and the energy quantum are not independent properties; they are dual characterisations of the same per-event reality. Therefore:

$$\frac{E_{\text{event}}}{I_{\text{event}}} \;=\; \frac{\hbar\omega}{1 \text{ bit}} \;=\; \hbar\omega \text{ per bit}$$

**This is the Wheeler-Fields principle, derived from QLF first principles.** No additional postulate. The principle is a corollary of the per-event information quantum (Lean-anchored) and the per-event energy quantum (Planck-Einstein, recovered in QLF via the per-qubit/per-bit accounting).

---

## §3 Unification with existing QLF mass-energy quanta

The ℏω-per-bit principle unifies the three QLF natural-units quanta into a single framework:

| Quantum | Carrier | Value | Status |
|---|---|---|---|
| **Information per event** | ZFA closure | `log 2` nats = **1 bit** | ✓ Lean-anchored |
| **Rest energy per qubit** | Gauge-folded Hermitian pair | **`ℏω`** | ✗ Lean-open |
| **Photon energy per bit** | Gauge-free joint closure | **`ℏω`** | ✗ Lean-open |

The three are the same quantum viewed from three sides:

- **Information side**: the event resolves 1 bit.
- **Rest energy side** (gauge-folded): the event contributes `ℏω` to rest mass via constructing delay.
- **Kinetic energy side** (gauge-free): the event contributes `ℏω` to photon energy.

In all three cases, the **energy per bit is `ℏω`**. The Wheeler-Fields principle thus identifies the single unifying constant of the QLF accounting: each ZFA closure event is *both* one bit of resolved information *and* one quantum of `ℏω` of energy, with `ω` the event's frequency.

### 3.1 Total energy of a particle as a bit count

For a particle composed of `N` qubits (or `N` bits, in the photon case), each at frequency `ω_i`:

$$E_{\text{particle}} \;=\; \sum_{i=1}^{N} \hbar \omega_i \;=\; \sum_{i=1}^{N} (\text{energy per bit at frequency } \omega_i)$$

Equivalently:

$$E_{\text{particle}} \;=\; N \times \hbar \omega_{\text{characteristic}} \;=\; (\text{bit count}) \times (\text{energy per bit at the characteristic frequency})$$

for a homogeneous particle. For heterogeneous bound states (e.g., muonium), the sum is over species-specific frequencies.

The user's prior insights are seen as **special cases** of the ℏω-per-bit unification:

- "Each qubit contributes ℏω to the mass" → ℏω per bit for gauge-folded events
- "Photons have energy based on the number of bits with a mass equivalence" → ℏω per bit for gauge-free joint closures

Both reduce to the same per-event ℏω = 1 bit identification.

---

## §4 Connection to Margolus-Levitin and Landauer bounds

The ℏω-per-bit principle is the QLF version of two well-known information-theoretic energy bounds:

### Margolus-Levitin (1998)

The minimum time to flip a qubit from one orthogonal state to another with energy `E` is

$$\tau \;\geq\; \frac{\pi \hbar}{2 E}$$

Equivalently, the minimum action per bit-flip is `ℏ` (within a factor of `π/2`). The QLF per-event energy quantum `ℏω = ℏ/Δt` is exactly this bound: each ZFA closure event takes time `Δt = 1/ω` to resolve and carries `ℏω` of energy, giving `E · Δt = ℏ` per bit — the Margolus-Levitin saturation.

### Landauer (1961)

The minimum energy to erase one bit of information at temperature `T` is

$$E_{\text{Landauer}} \;\geq\; k_B T \log 2$$

In the quantum limit (`kT → ℏω`), this becomes `E ≥ ℏω log 2` per bit. The QLF identification `ℏω per bit` matches at the resolution-event level (each closure event resolves 1 bit at energy `ℏω`); the additional `log 2` factor in Landauer is the irreversibility penalty for *erasure* (versus the reversible *resolution* in QLF).

Both bounds are recovered as natural consequences of the QLF per-event accounting.

### Reconciling with the census temperature

[`lean/QLF_CensusTemperature.lean`](lean/QLF_CensusTemperature.lean)
([`Information_Physics.md`](Information_Physics.md) §5b) counts a different event. There an event is
one **twist step**, a choice among eight, which carries `log 8 = 3` bits of history entropy. With
energy `ε` per step, the definition `1/T = dS/dE` gives the census temperature `T = ε/log 8`, and at
that temperature Landauer's `k_B T ln 2` is met exactly: one bit costs `ε/3` (`landauer_eight`).
This page's event is one **closure**, carrying one bit at energy `ℏω`. The two accounts agree if
`ε = 3ℏω`, that is, if one twist step carries three closure-bits at frequency `ω`. So at the census
temperature the `log 2` above is not a separate erasure penalty: `k_B T ln 2` *is* the energy per bit.
The open pieces are the same in both: the energy scale (`ε`, or `ω`) is an input, and identifying
the census temperature with a thermometer's is a bridge. `QLF_CensusTemperature` also gives the
observable: a Zipf exponent of 1 marks a system at the census temperature (`zipf_one_iff`).

---

## §5 Lean theorem candidate

The Wheeler-Fields principle's QLF derivation is a one-line corollary of two existing/proposed Lean theorems:

```lean
/-- Wheeler-Fields information-energy equivalence:
    each ZFA closure event carries 1 bit of information and ℏω of energy.
    Their ratio is ℏω per bit. -/
theorem hbar_omega_per_bit (ω : ℝ) :
    energy_per_event ω / information_per_event = ℏ * ω := by
  rw [information_per_event_eq_log_two]    -- from QLF_FreeEnergy.lean
  rw [energy_per_event_eq_hbar_omega ω]    -- proposed: qubit_mass_is_hbar_omega
  field_simp
```

Where `energy_per_event_eq_hbar_omega` is the proposed `qubit_mass_is_hbar_omega` Lean theorem flagged as open work in [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) §7. Once that is anchored, the Wheeler-Fields equivalence is mechanical.

The information side is already Lean-anchored as `binary_kl_delta_uniform = Real.log 2` and `zfa_closure_minimizes_free_energy`. The energy side awaits formalisation, but the structural derivation chain is complete in prose ([`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) §2, [`Photon_Energy_Bits.md`](Photon_Energy_Bits.md) §2).

---

## §6 What this is and is NOT

### Is

- **A first-principles QLF derivation of the Wheeler-Fields claim** that ℏω equals one bit of classical information at frequency ω.
- **A unification of the three QLF natural-units quanta** (per-event log 2 information, per-qubit ℏω rest energy, per-bit ℏω photon energy) under a single accounting principle.
- **A recovery of the Margolus-Levitin and Landauer bounds** as natural consequences of the per-event quantum structure.
- **Consistent with standard physics**: Planck-Einstein, the Margolus-Levitin time-energy bound, and Landauer's principle are all standard, and QLF reproduces them from its per-event axioms rather than postulating them separately.

### Is NOT

- **Not a new physical claim**. Wheeler's "it from bit" and the Margolus-Levitin/Landauer bounds are standard. The QLF contribution is the **derivation** of the unification from the per-event ZFA-closure axiom.
- **Not a derivation of `ℏ` from QLF first principles**. The value of Planck's constant is set by the QLF natural-units choice (Planck-mass-equals-one normalisation). What is derived is the *relation* `energy per bit = ℏω` given `ℏ` as the unit.
- **Not a derivation of specific particle masses or photon frequencies**. Those require independent QLF determination of the Markov-blanket depths `R_qubit` (e.g., `R_e ≈ 2.4 × 10²²` for the electron, per [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) §3.3 — still open).
- **Not a Wheeler-style "participatory universe"** philosophical claim — the QLF derivation is operational (each ZFA event resolves 1 bit at energy ℏω), without metaphysical commitments about observer-creation of reality.
- **Not the Lean theorem itself yet**. The `hbar_omega_per_bit` theorem is sketched in §5 but awaits the upstream `qubit_mass_is_hbar_omega` formalisation.

---

## §7 Open work

- **Lean theorem `qubit_mass_is_hbar_omega`** in `lean/QLF_FreeEnergy.lean` or a new module: formalise the per-qubit/per-event ℏω contribution from the Hermitian-pair half-spin atom structure.
- **Lean theorem `hbar_omega_per_bit`** as the corollary: information per event × energy per event / event-count. *Partly delivered* by [`lean/QLF_CensusTemperature.lean`](lean/QLF_CensusTemperature.lean): `landauer_saturated` (energy per bit = `ε / log₂ K` at the census temperature) and `landauer_eight` (`ε/3` on the 8-twist alphabet); the `ℏω` per event itself is still an input.
- **Quantitative connection to Bekenstein bound**: the maximum information storage in a region of size `R` with energy `E` is `S_max ≤ 2π R E / (ℏ c)` bits. QLF derivation from joint-closure topology is open.
- **Connection to holographic principle**: every bit corresponds to a Planck area on the horizon (`Holographic.md`, `QLF_Holographic_Computational_Universe.md`). The ℏω-per-bit at the Planck frequency gives `E_Planck` per bit, matching the holographic accounting.
- **Zeta-bridge reading**: the ℏω-per-bit equivalence deepens the MRE-bridge motivation of [`ReverseMathematics.md`](ReverseMathematics.md) §4. See §4.8 there — `Re(s) = 1/2` becomes the joint information-energy saturation locus, a third reinforcing reading on top of the MRE binary-partition argument and the half-spin closure fixed-point argument. The bridge axiom `spectral_hilbert_polya` remains a WKL₀ axiom; its content gains a physical interpretation of the Mellin variable `s` as an energy/frequency variable.

---

## References

### Internal

- [`MRE.md`](MRE.md) — per-event `log 2` information quantum; the information side of the Wheeler-Fields equivalence.
- [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) — per-qubit `ℏω` rest energy; the energy side for gauge-folded constituents.
- [`Photon_Energy_Bits.md`](Photon_Energy_Bits.md) — per-bit `ℏω` photon energy; the energy side for gauge-free constituents.
- [`Frequency_Synchronization.md`](Frequency_Synchronization.md) — `Δt = R/f_vac`, `ω = 1/Δt`.
- [`Hierarchical_Control.md`](Hierarchical_Control.md) §3 — Friston FEP from ZFA; per-event log 2 saturation as free-energy minimisation.
- [`HALF-SPIN-ZFA-EMBEDDING.md`](HALF-SPIN-ZFA-EMBEDDING.md) — half-spin atom as the unit of ZFA closure.
- [`Active_Inference_Mathematics.md`](Active_Inference_Mathematics.md) — Markov-blanket agents as the carriers of the per-event quantum.
- [`Bound_States_QLF.md`](Bound_States_QLF.md) — bound states as joint-closure events.
- [`Holographic.md`](Holographic.md), [`QLF_Holographic_Computational_Universe.md`](QLF_Holographic_Computational_Universe.md) — holographic / Bekenstein connection.
- [`lean/QLF_FreeEnergy.lean`](lean/QLF_FreeEnergy.lean) — Lean module containing the information-side anchor.

### External

- Wheeler, J. A. (1990). *Information, Physics, Quantum: the Search for Links.* In *Complexity, Entropy, and the Physics of Information* (W. H. Zurek, ed.), Addison-Wesley — the canonical "it from bit" statement.
- Wheeler, J. A. (2002+). Continued exposition of "it from bit" in IBM Watson lectures and related conference proceedings.
- Fields, C. (2018). *Sciences of observation*. Philosophies 3(4), 29 — observer-Markov-blanket framing.
- Fields, C., & Levin, M. (2020). *Scale-free biology: integrating evolutionary and developmental thinking*. BioEssays 42, e1900228 — information-theoretic foundations.
- Fields, C., Friston, K., Glazebrook, J. F., Levin, M. (2022). *A free energy principle for generic quantum systems*. Prog. Biophys. Mol. Biol. 173, 36–59 — QLF-adjacent FEP formulation.
- Margolus, N., & Levitin, L. B. (1998). *The maximum speed of dynamical evolution*. Physica D 120, 188–195 — minimum time per bit-flip is `πℏ/2E`.
- Landauer, R. (1961). *Irreversibility and heat generation in the computing process*. IBM J. Res. Dev. 5, 183–191 — minimum energy `kT log 2` per bit erasure.
- Bekenstein, J. D. (1981). *Universal upper bound on the entropy-to-energy ratio for bounded systems*. Phys. Rev. D 23, 287 — `S ≤ 2π R E / ℏc`.
