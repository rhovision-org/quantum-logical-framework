# The Three-Polarizer Paradox

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Companions:** [`Quantum_Logic_Foundations.md`](Quantum_Logic_Foundations.md) (the logic) ·
[`Measurement_Problem.md`](Measurement_Problem.md) (measurement is closure) ·
[`Born_Rule.md`](Born_Rule.md) §7 (the 50/50 split) ·
[`lean/QLF_QuantumLogic.lean`](lean/QLF_QuantumLogic.lean) ·
[`lean/QLF_ConstructionAdds.lean`](lean/QLF_ConstructionAdds.lean) ·
[`lean/QLF_LogicalPersistence.lean`](lean/QLF_LogicalPersistence.lean) ·
[`lean/QLF_SpinorInformation.lean`](lean/QLF_SpinorInformation.lean)

---

## 1. The experiment

Take two polarizing filters and cross them: one vertical (0°), one horizontal (90°). No light gets
through. Now slide a **third** filter between them, turned to 45°. Light comes back: one eighth of the
original unpolarized beam reaches your eye.

| Filters in the beam | Fraction of unpolarized light that gets through |
|---|---|
| 0° | 1/2 |
| 0° → 90° | **0** |
| 0° → 45° → 90° | **1/8** |
| 0° → 90° → 45° (same three, different order) | **0** |

Adding a filter *increased* the light. And the order matters: the same three filters in a different
order let nothing through.

This is a standard classroom demonstration (Dirac opens *The Principles of Quantum Mechanics*, 1930,
§2, with photon polarization for exactly this reason), and the numbers come from Malus's law (1809):
light polarized at angle `a` passes a filter at angle `b` with probability `cos²(b − a)`.

## 2. Why it feels like a paradox

The intuition that breaks is the **sieve picture**: a filter is a sieve that lets through the photons
that already *have* a property and blocks the rest.

On that picture the argument is airtight:

1. Every photon past the first filter is vertical.
2. Every photon past the last filter is horizontal.
3. Nothing is both vertical and horizontal.
4. A sieve can only remove photons, never add them. So a third sieve can only make things darker.

Underneath it sits a quieter assumption: that each photon carries an orientation, an angle stored to
as many digits as you like, which the filters merely inspect. Every step also uses ordinary Boolean
logic: properties are fixed in advance, "passed A then passed B"
means "has A **and** has B", and AND distributes over OR. The experiment says this argument is wrong.
QLF says *which step* is wrong, and why, in three moves.

## 3. The QLF reading, in three moves

### Move 1. A polarizer is not a sieve. It is a closure.

In QLF a measurement is not a look at something that was already there. **A measurement is a ZFA
closure**: an event that makes a new fact true
([`Measurement_Problem.md`](Measurement_Problem.md)). The apparatus is itself a closure inventory, not an observer with special powers
([`ScientificApproach.md`](ScientificApproach.md) §2).

So a polarizer asks the photon one binary question along its own axis, *"close this way or the
opposite way?"*, and the photon's history closes one way or the other. If it closes along the filter's
axis it passes, now **as a photon of that axis**. It did not carry that answer beforehand. The answer
is made at the filter.

That is the first broken step: steps 1 to 4 assume each filter *reads* a stored property. It doesn't;
it *writes* one.

### Move 2. Closure is many-to-one, so the photon forgets.

Once a photon has closed on the 45° axis, which axis it closed on *before* is gone from the photon.
This is not a special rule for light. It is a theorem about closure in general:

* **`no_unclosing`** ([`lean/QLF_ConstructionAdds.lean`](lean/QLF_ConstructionAdds.lean)): closure is
  many-to-one. `[+,−]` and `[−,+]` both close to the same empty residue, so no function can recover
  the history from the closed result.

Applied here: a vertical photon and a horizontal photon that both pass the 45° filter come out the
same. The 45° closure overwrites the vertical one. So when the photon reaches the 90° filter, it is
not "a vertical photon" any more. It is a 45° photon, and a 45° photon has an even chance at 90°.

Note what is *not* forgotten. The **record** that the photon passed the first filter is permanent:
an established fact stays established at every later state
(`histories_are_a_model`, [`lean/QLF_LogicalPersistence.lean`](lean/QLF_LogicalPersistence.lean)),
and a closure, once closed, stays closed (`closure_receipt_stable`). What the photon carries *forward*
into the next question is only its latest closure. History keeps the receipts; the photon keeps the
last one.

That is the second broken step: step 1 is true at the first filter and stops being true at the
second. "Every photon past the first filter is vertical" is not a property it keeps.

### Move 3. The logic is not Boolean, and QLF has the exact lattice.

The deepest broken step is the use of AND and OR. The propositions involved here,

* `V` = closes vertical, `H` = closes horizontal,
* `D` = closes at 45°, `A` = closes at 135°,

form exactly the **minimal quantum logic `MO2`**: two complementary pairs, `V/H` and `D/A`, that are
incompatible with each other. QLF proves this lattice is realized by ZFA closures, with no axiom
([`lean/QLF_QuantumLogic.lean`](lean/QLF_QuantumLogic.lean)). The match is direct: on the Poincaré
sphere a polarization angle `θ` sits at `2θ`, so 0°/90° are the two poles of one axis and 45°/135° are
the two poles of a perpendicular axis. Those are the `σz` and `σx` closures, the module's `az`/`azp`
and `ax`/`axp`.

What `MO2` does to the paradox:

* **They are incompatible.** The `V/H` question and the `D/A` question do not commute:
  `σz σx − σx σz = 2i σy ≠ 0` (`incompatibility_source`). That is why the **order** of the filters
  matters: asking `D` then `H` is not asking `H` then `D`.
* **Distributivity fails, provably** (`not_distributive`). In Boolean logic,
  `D ∧ (V ∨ H) = (D ∧ V) ∨ (D ∧ H)`. In `MO2`:
  * left side: `V ∨ H` is "closes one way or the other on the vertical axis", which is everything
    (`⊤`), so `D ∧ ⊤ = D`. Not empty.
  * right side: `D ∧ V = ⊥` and `D ∧ H = ⊥`, since no closure is both 45° and vertical, so the right
    side is `⊥`. Empty.

The sieve argument in §2 silently uses the right side: "every photon is vertical-or-horizontal, and
neither kind can also be 45°, so nothing passes at 45° with a definite axis." The real lattice uses
the left side: a 45° closure exists even though it is neither a vertical closure nor a horizontal one.
**The extra light is the gap between the two sides of the distributive law.**

That is the third broken step: step 4's "a filter can only remove" is a statement about Boolean sets.
A filter in an incompatible basis does not take a subset of the photons' old answers; it asks a new
question whose answers were not in the old list.

## 4. The key: orientation is one bit

All three moves come from one fact. **A photon's orientation is known to one bit of precision, and no
more.** It does not carry an angle. It carries the answer to the last question it closed on: *along
this axis, or the opposite one*. That is `log 2` of information, and it is the most a two-valued
closure can hold:

* **`two_valued_one_bit`** and **`spin_half_is_information_atom`**
  ([`lean/QLF_SpinorInformation.lean`](lean/QLF_SpinorInformation.lean)): the two-outcome closure
  carries exactly `log 2`, a single-valued one carries `0`, and nothing in between is a carrier. This
  is the substrate form of Brukner and Zeilinger's principle that an elementary system carries one
  bit (2003; see [`Information_Physics.md`](Information_Physics.md)).

Read the paradox again with only one bit in the photon:

* **Why the photon forgets (Move 2).** There is room for one answer. Writing the 45° answer leaves no
  room for the vertical one. The many-to-one closure of `no_unclosing` is what a one-bit memory looks
  like from outside: two different pasts, one stored bit.
* **Why the questions are incompatible (Move 3).** A bit about vertical-or-horizontal says *nothing*
  about 45°-or-135°. Relative to the stored bit, the 45° question is the one it is completely
  uninformed about, so the answer is a fair coin, and each such closure gains a fresh `log 2`. That is
  why the middle filter at 45° gives exactly ½: it asks the question the photon's bit is silent on.
* **Why the sieve picture fails (§2).** The sieve picture needs a stored angle precise enough to
  answer every filter in advance. That would be infinitely many bits in one photon, a continuum of
  distinguishable states in a finite region, which QLF excludes (`no_continuum_in_finite_region`,
  [`lean/QLF_Realizability.lean`](lean/QLF_Realizability.lean)). There is no hidden angle to reveal,
  because there is nowhere to keep it.
* **Where the angle lives.** The angles 0°, 45°, 90° belong to the **filters**, the apparatus, not to
  the photon. The photon contributes one bit relative to its last filter; the angle is the relation
  between that filter and the next. So the open problem in §7, deriving `cos²θ` at an arbitrary
  angle, is a question about the geometry of the apparatus and how many finite closures render it,
  not about a property hidden in the light.

## 5. Counting the ways

Now the numbers follow from one rule. At each filter the photon's history closes one of two ways,
and when the filter sits at 45° to the photon's last closure, the two ways are **equally many**:
the 50/50 binary partition, one bit per event, `log 2` of information
([`Born_Rule.md`](Born_Rule.md) §7, [`MRE.md`](MRE.md) §2.1).

| Step | Photon's last closure | Filter | Ways that pass | Running fraction |
|---|---|---|---|---|
| source | none (unpolarized) | 0° | half | 1/2 |
| filter 2 | 0° | 45° | half | 1/4 |
| filter 3 | 45° | 90° | half | **1/8** |

Without the middle filter the last step would be "last closure 0°, filter 90°": the filter asks the
opposite of the question the photon just answered, and **no way** passes. Zero.

The same logic gives a striking consequence. Split the 90° turn into `N` small turns of `90°/N` each.
Every step now asks a question very close to the one the photon just answered, so almost every way
passes, and the light is steered around the corner with less and less loss:

| Filters between 0° and 90° (each turn `90°/N`) | Light through (of unpolarized) |
|---|---|
| `N = 1` (crossed, no middle filter) | 0 |
| `N = 2` (the three-polarizer case) | 0.125 |
| `N = 3` | 0.211 |
| `N = 5` | 0.303 |
| `N = 10` | 0.390 |
| `N = 100` | 0.488 |

(Computed as `½ · cos²ᴺ(90°/N)`; the limit is `½`, everything that passed the first filter.) Many
gentle closures can rotate light that one abrupt closure would destroy. Nothing in the sieve picture
can do that.

## 6. The whole thing in one paragraph

A photon's orientation is one bit: the answer to the last question it closed on. A polarizer does not
sort photons by an angle they already have; it makes them close, one way or the other, along its own
axis, and that overwrites the bit. Closure is many-to-one, so the photon keeps only its latest answer,
while the record of earlier answers stays in history. The questions "vertical or horizontal?" and
"45° or 135°?" are incompatible, so their propositions form the non-distributive lattice `MO2`, where
a 45° closure exists that is neither vertical nor horizontal. The middle filter does not let through
light that was secretly there; it asks a new question, and half the ways answer it yes.

## 7. What is proven, what is standard, what is open

| Claim | Status | Where |
|---|---|---|
| The propositions form `MO2`: orthomodular, not distributive, from non-commuting axes | **Proved**, no axiom | `not_distributive`, `orthomodular`, `incompatibility_source` in [`QLF_QuantumLogic`](lean/QLF_QuantumLogic.lean) |
| Orientation is one bit: a two-valued closure carries exactly `log 2`, a single-valued one `0` | **Proved**, no axiom | `two_valued_one_bit`, `spin_half_is_information_atom` in [`QLF_SpinorInformation`](lean/QLF_SpinorInformation.lean) |
| No continuum of distinguishable states in a finite region (no stored angle) | **Proved** | `no_continuum_in_finite_region` in [`QLF_Realizability`](lean/QLF_Realizability.lean) |
| Closure is many-to-one: no function un-closes | **Proved**, no axiom | `no_unclosing` in [`QLF_ConstructionAdds`](lean/QLF_ConstructionAdds.lean) |
| Records persist; a closure stays closed | **Proved**, no axiom | `histories_are_a_model` in [`QLF_LogicalPersistence`](lean/QLF_LogicalPersistence.lean), `closure_receipt_stable` |
| The 45° step is an even split | **Symmetry-forced**: the two ways are mirror images, so ½ is bookkeeping, not evidence for the Born rule in general | [`Born_Rule.md`](Born_Rule.md) §7 |
| Polarization angle `θ` ↔ Poincaré-sphere angle `2θ` | **Standard optics**, used here as the bridge from the spin lattice to light | — |
| `cos²θ` at an arbitrary angle (the `N`-filter table) | **Imported** from Malus's law, **not yet derived** in QLF. An arbitrary angle is not a substrate object; deriving `cos²` as the large-census rendering of many finite context changes is open | [`Open_Problems.md`](Open_Problems.md), Born rule item |

On novelty: the reading of this experiment as non-distributive quantum logic goes back to Birkhoff and
von Neumann (1936), and "measurement prepares rather than reveals" is textbook quantum mechanics. QLF's
contribution is not the moral of the story. It is that the lattice is **built from ZFA closures and
machine-checked**, and that the photon's forgetting is a consequence of a general theorem about
closure (`no_unclosing`) rather than an extra postulate about collapse.

## 8. What not to conclude

* **Not "the photon secretly had all three polarizations."** It has room for one bit. There is
  nothing more stored to reveal; each answer is made by its closure.
* **Not "the middle filter adds light."** It removes three quarters of what reaches it, as every
  filter at 45° does. What it changes is the *question* the last filter is answering.
* **Not "measurement is a separate collapse process."** In QLF the closure *is* the measurement event;
  there is nothing else that collapses.
* **Not "the order of events is arbitrary."** Order matters because the questions do not commute, and
  that non-commutation is a proved property of the twist algebra, not an observer effect.
