# Inertia in QLF — a plan, not a result

**Epistemic status: scoping document.** Nothing here is claimed as derived. This is the proof plan
for demystifying inertia in the [Quantum Logical Framework](README.md) (QLF), the order the work
should be attempted in, and — first — the conditions under which it should be abandoned. The
mechanism it settles on (§3) is not a new posit: it is the substrate's own count balance, read
kinematically.

> **The hypothesis.** Every step on the substrate runs at `c` — one Planck length per Planck tick, at
> every depth. So a **rest mass is a closed circulation of light-speed steps whose directions sum to
> zero**: that sum *is* the signed action vector, and its vanishing *is* ZFA closure. At **constant
> velocity** the sum still cancels — a boost lengthens both legs of the loop by the same `γ`, which
> is why uniform motion is free at any speed. **Acceleration unbalances it**, the way accelerating an
> Einstein light clock makes its two legs unequal. The residual is free action, and the cost of
> paying it down **is** inertia.
>
> A weaker variant puts the asymmetry in the surrounding vacuum instead — an **active frequency
> window**, compressed ahead and expanded behind. §3a gives three reasons to prefer the circulation
> reading; the short one is that the vacuum is not in the derivation at all.

---

## 0. What is already answered — do not re-derive it

grok's plan proposes five phases. Three of them are substantially built already, and the plan below
is short because of it. Checked against the repo, not assumed:

| piece | status | where |
|---|---|---|
| Mass = constructing delay (gauge-fold depth) | built | [`Higgs.md`](Higgs.md), [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) |
| **Equivalence principle** — one delay, read as inertia at the vertex and curvature in the geometry | **already claimed structurally** | [`Forces_From_Three_Axes.md`](Forces_From_Three_Axes.md) §144, [`UniversalRelativity.md`](UniversalRelativity.md) §436 |
| Casimir as a **finite census**, not a subtracted infinity; `1/a⁴` parameter-free | **Lean-anchored** | [`QLF_Casimir`](lean/QLF_Casimir.lean) (`casimir_vacuum_quantum`, `casimir_scaling`) |
| **Accelerated boundary = Unruh** (the dynamical-Casimir link grok proposes building) | **NOT anchored — the theorem is `rfl`** (audited after this plan was first written; see §0a) | `accelerated_boundary_is_unruh` |
| **Unruh master relation** `T = ℏa/(2πck_B)`, with Hawking and de Sitter as instances | **Lean-anchored** | [`QLF_HorizonTemperature`](lean/QLF_HorizonTemperature.lean) |
| Holographic entropy `S(R)` | **Lean-anchored** | `holographic_entropy_eq` |
| Lorentz boost = ratio of Markov-blanket internal ZFA event rates | built, boosts only | [`Cross_Frequency_Lorentz.md`](Cross_Frequency_Lorentz.md) |
| Vacuum spectrum, per-event `log 2`, scale-free `ρ(ω)` | built | [`VacuumEnergy.md`](VacuumEnergy.md) |

So **Phase 4 (equivalence) is mostly done, and Phase 3 (Casimir/Unruh) is less done than it looks** —
see §0a immediately below. What is genuinely missing is the middle: the step from *acceleration* to a
*force*, and its rotational counterpart. Two more facts matter for where to start:

- [`Cross_Frequency_Lorentz.md`](Cross_Frequency_Lorentz.md) §6 says in as many words that
  **accelerations are out of scope** there — *"accelerations require a frequency-derivative term"* —
  and §7 already names *"Generalisation to acceleration"* as the open successor. That is the home for
  Phase 1; it should be **extended**, not duplicated.
- There is **no** inertia, Mach, or frame-dragging entry in
  [`Mysteries_Of_Physics.md`](Mysteries_Of_Physics.md). That is a gap in the registry independent of
  whether this programme succeeds.

### 0a. An audit correction — the Casimir/Unruh tie is not anchored

The first draft of this plan listed `accelerated_boundary_is_unruh` among the Lean-anchored assets.
Reading the module rather than its name shows that is wrong, and the correction matters for where
the work starts.

**The theorem is `rfl`.** Its statement is `unruh_temperature ℏ a c k_B = ℏa/(2πc k_B)` — and that is
the *definition* of `unruh_temperature`. No boundary appears in it. It records the identification QLF
makes and is not evidence for it. Upstream [`QLF_HorizonTemperature`](lean/QLF_HorizonTemperature.lean)
is scrupulous about exactly this — `hawking_is_unruh` and `desitter_is_unruh` both carry
"(definitional)" in their docstrings — and it also carries two genuinely non-trivial theorems
(`hawking_temperature_eq`, `desitter_temperature_eq`). [`QLF_Casimir`](lean/QLF_Casimir.lean) had
inherited the relation without inheriting the label; it now carries it, and three statements that are
**not** `rfl` have been added there:

- **`boundary_unruh_zero_iff_inertial`** — a boundary reads a thermal vacuum **exactly when it
  accelerates**, and at no constant velocity however large. This is the formal content of Galileo's
  ship and the isotropy premise this programme needs; it is the first piece of Phase 1 that exists.
- **`boundary_unruh_linear_in_acceleration`** — the response is exactly linear in `a`, with no
  threshold. Inertia is linear in `a`, which is why any derivation must route through this.
- **`static_boundary_no_unruh`** — a static boundary has no bath, so the **static Casimir force is not
  thermal in origin**. The two effects are separate, and conflating them is the easy error.

**Why this strengthens rather than weakens the plan.** The step the programme most wants to lean
on — *accelerating mass as its own dynamical-Casimir boundary* — turns out to be the step that is
asserted rather than established. That is now Phase 2's actual work rather than a free inheritance.
It is also the second time in two sessions that reading a module instead of its name changed the
picture, which is the argument for R6a being applied *before* the derivation, not after.

---

## 1. Kill conditions — stated first

Per [`ScientificApproach.md`](ScientificApproach.md) R7, before any derivation. Two of these are
sharp enough to end the programme on their own.

1. **Inertial-mass anisotropy (Hughes–Drever).** Clock-comparison experiments bound any directional
   dependence of inertial mass to better than one part in 10²⁰, and modern versions far tighter. A
   mechanism in which inertia *is* a directional vacuum-mode imbalance must explain why a laboratory
   on an accelerating, rotating, orbiting Earth sees an isotropic inertial mass to that precision.
   **This is the hardest constraint in the programme and it must be faced in Phase 0, not deferred to
   a discussion section.** It also *discriminates between the two readings of the mechanism*: it bites
   the external-vacuum-window version hard and the internal-null-circulation version of §3 barely at
   all, which is a large part of why §3 is the better bet.
2. **Exact Lorentz invariance at constant velocity.** The window must be isotropic at *every* speed
   exactly, not approximately. QLF has the right shape for this (a statistically uniform, stateless
   ether — [`UniversalRelativity.md`](UniversalRelativity.md)), but "the census looks the same in
   every frame" has to be proven, not asserted.
   *(Update 2026-11-10: the unsigned census is now proven frame-dependent at the Planck step and
   Euclidean-isotropic in the large, cubic anisotropy `4/(3L+1)`, which is not yet boost
   invariance; see [`Relativity_Principle.md`](Relativity_Principle.md).)*
3. **One mass, not two.** The `m` in `F = ma` must be *identically* the `m` of
   [`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md) and
   [`E_mc2_derivation.md`](E_mc2_derivation.md). A vacuum-window mechanism that produces its own mass
   term, even a proportional one, has produced a **contradiction**, not a derivation.
4. **Frame dragging must land on the measurement.** Gravity Probe B: geodetic precession to 0.3%,
   frame-dragging ≈ 39 mas/yr to ≈ 19%; LAGEOS/LARES ≈ 10%. A rotational sector that cannot hit
   these is wrong, and one that "hits" them with a fitted coefficient has not derived anything.
5. **The rule-4 gate, applied per phase.** A phase earns its place only if it changes a **count of
   ways** — if "the window compresses" does not alter a census multiplicity, it is bookkeeping
   ([`Philosophy.md`](Philosophy.md) §3a rule 4). This session already lost a folding bridge that
   failed exactly here ([`Protein_Folding.md`](Protein_Folding.md) §5e): a substrate theorem was
   read as licensing a factorization it did not license, and the regression found it. Assume the same
   trap is present until each step is tested.

---

## 2. The named prior attempt — say how this differs, or inherit its fate

**Haisch, Rueda & Puthoff (1994), *Inertia as a zero-point-field Lorentz force*** is this hypothesis,
in continuum language: inertia as the reaction to an asymmetric zero-point field seen by an
accelerating body. It did not converge — the derivation was contested on covariance grounds and the
programme did not produce an accepted account of `F = ma`.

QLF does not get to ignore this. Before Phase 2 is written, the plan owes an explicit statement of
**what is structurally different here** — the honest candidates being that QLF's vacuum is a *finite
discrete census* rather than a divergent field (so no regularization is smuggled in, per
[`VacuumEnergy.md`](VacuumEnergy.md) §4.0), and that the delay is already the mass rather than being
generated by the interaction. If neither difference does real work, this is the same route and it
should be recorded as **rejected**, not re-run.

## 3. The mechanism, sharpened — a rest mass is a null circulation

> *The light-speed energy in every direction sums to zero in rest mass. Acceleration unbalances
> this. Like an Einstein clock.* — Jim

This is a better statement of the hypothesis than the frequency-window version above, and the reason
is that **it is not a new posit at all**. It is what the substrate already says, once you notice that
every step is null.

**Every twist step moves at `c`.** One Planck length per Planck tick, and the ρ-cancellation
`(ρ·L_P)/(ρ·τ_P) = L_P/τ_P` makes that hold at *every* Markov-blanket depth
([`Kitada_Local_Time_GR.md`](Kitada_Local_Time_GR.md), Tier 1). There is one speed on the substrate
and every history runs at it. So a **massive** particle cannot be something moving slower — it must
be a **closed loop of light-speed steps**, and its rest mass is the loop not going anywhere.

**"Sums to zero in every direction" is already the ZFA condition.** `calculate_action` returns the
signed directional vector `(v, h, d, l) = (#^−#v, #>−#<, #/−#\, #+−#−)`
([`twist_core.py`](twist_core.py)), and count balance *is* that vector vanishing. The same statement
appears as `ClosedLoop` in [`QLF_Folding`](lean/QLF_Folding.lean) — net displacement zero — and as
`countBalanced` in [`QLF_TwistAlphabet`](lean/QLF_TwistAlphabet.lean). So:

> **rest mass = a ZFA-closed circulation of null steps**, and the free action `F(h)` — the
> directional imbalance — is exactly what a rest mass has *none of*.

The mass value follows too, and it is already in the repo: `m = 1/R`
([`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md)) is the circulation's **frequency**, which
is what a trapped light-loop of period `R` must weigh. And the two-leg structure is the
Hermitian-conjugate pair `(t, t†)` whose two orderings [`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)
prices at `log 2`, and whose balance is `H = H†` ([`Reversibility.md`](Reversibility.md)).

**The Einstein clock says why constant velocity is free and acceleration is not.** A light clock at
rest has two equal legs. **Boost** it and both legs lengthen by the *same* factor — that is `γ`, and
[`Cross_Frequency_Lorentz.md`](Cross_Frequency_Lorentz.md) already reads it as a frequency ratio. The
dilation is **symmetric**, the directional sums still cancel, and nothing is owed: uniform motion is
free at any speed, which is Galileo's ship. **Accelerate** it and the legs become *unequal* — the
far mirror recedes while the light chases it and approaches while the light returns. The sums no
longer cancel. That residual is free action, and paying it down is the resistance.

**The precedent is standard physics, and it is correct.** A box containing radiation of energy `E`
has inertial mass `E/c²`; push it and the Doppler shift makes the radiation pressure on the trailing
wall exceed that on the leading wall, giving a net opposing force `(E/c²)a`. That is a textbook
derivation of inertia from unbalanced light-speed energy — not a fringe route. **The QLF claim is
that this is not special to boxes of light**: every rest mass *is* such a circulation, so the
argument is universal rather than an illustration.

### 3a. Why this is a better bet than the frequency-window reading

The window version puts the asymmetry in the **external vacuum**. This version puts it in the body's
**own internal circulation**. That relocation retires three of this document's own objections:

| objection (as stated above) | against the vacuum window | against the null circulation |
|---|---|---|
| §1 KC1 — Hughes–Drever anisotropy | **bites hard**: inertia tied to a directional external mode census should show anisotropy on an accelerating Earth | **does not bite**: the circulation carries no preferred *external* direction; the asymmetry is between the body's own legs |
| §3 (old) — Unruh's bath is isotropic in the accelerated frame, not front/rear | **a real conflict** to resolve | **irrelevant** — a different object; no vacuum bath is invoked |
| §2 — Haisch–Rueda–Puthoff inheritance | **direct**: HRP is exactly an external-ZPF mechanism | **weak**: the photon-in-a-box argument is not HRP's, and it works |

So §2's demand — *say what is structurally different, or inherit the fate* — has an answer, and it is
this: **the vacuum is not in the derivation.** Inertia is the body re-balancing its own null
circulation, not a drag against an external sea.

**What it now has to prove**, and these are harder than they look:

1. The restoring force is **exactly** `ma`, not merely proportional to `a`. A factor of 2 is a
   failure, not a detail.
2. The circulation whose period gives `m = 1/R` is the **same object** as the gauge-fold depth that
   [`Higgs.md`](Higgs.md) already calls inertial mass — one mass, per KC3, not two that agree.
3. The imbalance must be a **count** — a nonzero `calculate_action` — and not a re-description. This
   is the rule-4 gate, and here it is finally satisfiable, because the imbalance is a signed integer
   the substrate already computes rather than a picture.

## 4. Two routes to `F = ma`, and which to run first

**Route A — the null circulation (§3). Done: [`QLF_Inertia`](lean/QLF_Inertia.lean), no axioms.**
See §4a.

**Route B — the thermodynamic cross-check.** Because `unruh_temperature` and
`holographic_entropy_eq` are **both already Lean-anchored**, there is also a two-step route that
needs no new mechanism — Verlinde's (2011) entropic argument, whose ingredients QLF already has:

```
    ΔS = 2π k_B (mc/ℏ) Δx        holographic entropy gradient across a screen
    T  = ℏa / (2π c k_B)         the Unruh relation                (QLF_HorizonTemperature)
    F  = T ΔS/Δx = m a           the 2π cancels; the force is the entropy gradient
```

Run this **second, as a cross-check**: two independent routes landing on the same `ma` would be
multiplicity in the sense the method values ([`Philosophy.md`](Philosophy.md) §3a rule 5 — converging
derivations are evidence, not redundancy), and it is the same Jacobson-style move the repo already
used to get the Einstein coefficient (`einstein_coupling_from_thermodynamics`).

**But apply R6a before writing a line of it.** Bundle the entropy gradient into a structure and try
to satisfy it trivially. If `ΔS ∝ m Δx` is *definitional* — if the screen's entropy is defined so
that the gradient comes out proportional to the mass — then `F = ma` is a **restatement of its own
premise**, which is precisely the failure mode measured in `yang_mills_gap` (`continuumGap_nonempty`
builds a realization by `rfl`, so the boundary is definitional in Lean). A derivation that cannot
fail has derived nothing. Record the outcome either way; that measurement *is* the result of Phase 2,
whichever way it goes.

---

### 4a. Route A, run — an accelerated null circulation weighs exactly `E/c²`

Take the minimal such circulation, a two-leg Einstein light clock of size `L` and energy `E`, and let
the legs differ by a fractional shift `δ`. Each reflection transfers `2E/c`; a round trip takes
`2L/c`. Then:

| theorem | statement |
|---|---|
| `netForce_eq` | `netForce = −E·δ / L` — **the circulation speed `c` cancels out of the force entirely** |
| `inertial_reaction` | with `δ = a L/c²`, `netForce = −(E/c²)·a` — **and `L` cancels too** |
| `inertial_reaction_mass` | hence `F = −m a`, once `E = mc²` |
| `independent_of_circulation_size` | two circulations of different size but equal energy resist identically — it does not matter how the mass is built |
| `no_force_without_acceleration` | `a = 0 ⟹ F = 0`: uniform motion is free at any speed (Galileo's ship, KC2) |
| `legs_balanced_iff_no_shift` | the legs carry equal energy **exactly when** `δ = 0` — the directional sums cancel, which is what rest *is* |
| `force_scales_with_shift` | **the shift law is forced, not fitted** — the force is exactly proportional to `δ`, so a redshift law scaled by `k` gives an inertia scaled by `k` |

The last row is the one that makes this a derivation rather than an arrangement. `F = −Eδ/L` holds
for *any* shift law; `F = −ma` singles out `δ = aL/c²`, which is exactly the equivalence-principle
redshift. **A different redshift law would make the same energy weigh a different amount.** So the
shift and the inertia are the same fact seen twice, and that is the demystification: inertia is not
an extra property of matter, it is what a balanced null circulation costs to unbalance.

Checked in exact rationals over varied `E, a, L, c` before any Lean was written; the `L`-cancellation
is a real computation that could have failed — a surviving `L`, or a factor of 2, would have killed
the picture.

**What is input, and what is derived.** The shift `δ = aL/c²` is **input**: it is the repo's existing
gravitational-redshift account ([`GR_Schwarzschild.md`](GR_Schwarzschild.md) §2a, the JILA/NIST
millimetre-scale measurement, read off
[`Cross_Frequency_Lorentz.md`](Cross_Frequency_Lorentz.md) as a Markov-blanket frequency ratio), not
established here. What is **derived** is that this shift, and no other, turns a balanced null
circulation into `F = −ma` with both `c` and `L` cancelling. A bridge reused plus an exact
computation — not inertia from nothing.

**What Route A does *not* establish**, and none of these should be glossed:

1. **KC3 is still open.** That the circulation whose period gives `m = 1/R`
   ([`Per_Qubit_Mass_Quantum.md`](Per_Qubit_Mass_Quantum.md)) is the *same object* as the gauge-fold
   depth [`Higgs.md`](Higgs.md) already calls inertial mass. Until that is shown, this is a theorem
   about light clocks that QLF *interprets* as universal, not a theorem about every mass.
2. **The counting version is not done.** §3a's rule-4 gate wanted the imbalance as a *signed integer*
   the substrate computes (`calculate_action`). What is proved above is the continuum algebra, with
   energies as reals. Making the imbalance a count is the next increment and the one that would make
   this QLF-native rather than QLF-compatible.
3. **The rotational sector is untouched** — Newton's bucket and frame dragging remain Phase 3.

So the honest status is: **the mechanism works and is exact, on the assumption that every rest mass
is a null circulation.** That assumption is the framework's, is well-motivated (every substrate step
runs at `c`), and is not yet a theorem.

---

## 5. The phases

Each phase names its deliverable, its owning doc, and the count that would falsify it.

**Phase 0 — definitions, and the anisotropy bound.**
Define the **active frequency window** of a ZFA-closed subsystem: the set of twist-history
frequencies that can still achieve closure with the local blanket inside its capacity `R`
([`QLF_HorizonClosure`](lean/QLF_HorizonClosure.lean), `closedAtHorizon`). Define isotropy as a
statement about *census multiplicity* on opposite sides, so it is a count and not a picture.
**Then immediately confront kill condition 1**: compute what anisotropy the mechanism predicts for a
lab on Earth and compare to the Hughes–Drever bound. *If the predicted anisotropy exceeds the bound,
stop here.* Owner: extend [`Cross_Frequency_Lorentz.md`](Cross_Frequency_Lorentz.md) §7.

**Phase 1 — uniform motion is isotropic, exactly.**
Prove the window census is invariant under a boost — the constant-velocity half, and the formal
content of **Galileo's ship** (*Dialogue*, 1632): below decks, no experiment reveals uniform motion.
Deliverable: the `lorentz_boost_from_zfa_frequencies` theorem that
[`Cross_Frequency_Lorentz.md`](Cross_Frequency_Lorentz.md) §7 already names as open, plus a demo
boosting a dense closure through a simulated ZFA vacuum and showing front/rear mode counts stay
equal. Falsifier: any speed at which the counts differ.

**Phase 2 — acceleration to force. Route A done (§4a); two pieces remain.**
`F = −ma` is proved for a null circulation, exactly, with `c` and `L` cancelling and the shift law
forced ([`QLF_Inertia`](lean/QLF_Inertia.lean)). Remaining: **(a)** the *counting* version — the
imbalance as a signed integer `calculate_action` computes, rather than the continuum algebra, which
is what rule 4 actually asked for; **(b)** KC3, the identification of the circulation with the
gauge-fold depth. Then Route B as the independent cross-check, *with its R6a check first* — two
routes landing on the same `ma` would be multiplicity.
Target theorems: `accelerating_window_imbalance`, `inertial_force_from_frequency_asymmetry`.
Falsifier: a force that is not exactly `ma`, or an `m` that is not the substrate's `m`.
**Do not add a `True` summary theorem.** `casimir_summary` used to be `True := trivial` and has been
replaced with the conjunction of what that module actually proves;
`gravity_from_delay_proven_constructively` is still `True := trivial` and carries nothing. A summary
every possible module satisfies reports no content.

**Phase 3 — the rotational sector: Newton's bucket and frame dragging.**
The two touchstone experiments are the two halves of this programme, and they pair exactly:

- **Galileo's ship** — uniform motion is undetectable → Phase 1's isotropy.
- **Newton's bucket** (*Principia*, 1689) — the water climbs the wall, so *rotation is detectable*
  → the window shears azimuthally. Newton read this as proof of absolute space; Mach (1883) read it
  as the distant stars. QLF's answer is neither: the reference is the **global census of ZFA
  histories**, which is Machian in effect without being a force at a distance.

Then frame dragging as the same shear sourced by a *rotating mass*: co-rotating directions see a
compressed window, counter-rotating an expanded one, so the local zero-torque frame is dragged.
Target: recover Lense–Thirring precession with the `1/r³` falloff and hit kill condition 4. Owner: a
new section in [`Gravity.md`](Gravity.md) or [`Curvature.md`](Curvature.md) — the azimuthal
counterpart of the radial delay bias, not a separate mechanism.

**Phase 4 — the write-up.**
Fold the results back into this document, converting it from a plan into an account: the hypothesis,
the two experiments, the derivation, why it is the same mass that sources gravity, and — with equal
prominence — whichever kill conditions fired. Demos: `inertia_window_demo.py` (accelerate a dense
closure, plot front/rear spectra and net force) extending the existing
[`gravity_delay_demo.py`](gravity_delay_demo.py).

---

## 6. What would make this worth having

Inertia currently sits in physics as a primitive: matter resists acceleration, and that is where the
explanation stops. If this programme works, inertia becomes a **local consequence of a mass
re-balancing its own active vacuum-frequency window**, and the equivalence principle stops being a
coincidence to be honoured and becomes an identity — one constructing delay, read radially as
gravity, longitudinally as inertia, azimuthally as frame dragging.

That is worth attempting. But the honest prior is set by §2: this exact idea has been tried in
continuum language and did not converge, and the anisotropy bound in §1 is brutal. **The most likely
outcome is that Phase 0 or Phase 2's R6a check ends it** — and a clean, recorded negative on a
mechanism this attractive would itself be worth the work.

---

**See also:** [`VacuumEnergy.md`](VacuumEnergy.md) (the vacuum census and the Casimir section) ·
[`Cross_Frequency_Lorentz.md`](Cross_Frequency_Lorentz.md) (boosts as frequency ratios; acceleration
named open) · [`Gravity_From_Delay.md`](Gravity_From_Delay.md) · [`Higgs.md`](Higgs.md) (mass as
gauge-fold delay) · [`UniversalRelativity.md`](UniversalRelativity.md) (the uniform-ether framing) ·
[`ScientificApproach.md`](ScientificApproach.md) (R6a, R7, and the correction protocol).
