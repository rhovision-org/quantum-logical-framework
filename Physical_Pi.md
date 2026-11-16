# Physical Pi — π derived by construction from the closure census

**Module:** [`lean/QLF_PhysicalPi.lean`](lean/QLF_PhysicalPi.lean)
**Companions:** [`lean/QLF_LoopClosure.lean`](lean/QLF_LoopClosure.lean) (the closure machine vs the *chosen* `2π` rendering), [`TheContinuum.md`](TheContinuum.md), [`Continuum_Choice_Fallacy.md`](Continuum_Choice_Fallacy.md) (`π` is a *computable* real; the continuum is the fallacy, not the target).
**Origin:** Allen's issues [#86](https://github.com/rhovision-org/quantum-logical-framework/issues/86) / [#89](https://github.com/rhovision-org/quantum-logical-framework/issues/89) and his [`fundamentalPi.md`](https://github.com/lightrock/CharacteristicImpedancePython/blob/main/docs/references/fundamentalPi.md) — *"stop worshiping the notation, find the machine**s**."*

> **Status (after Allen's #89 review).** Allen's review has two kinds of points, and QLF answers them
> differently.
> **(a) Honest-scope/technical — correct, adopted in full below:** the *convergence* theorem is not yet
> wired into the Lean module; the 2-D *squaring* presupposes a random-walk model; the gauge phase
> increments need group-theory caveats (`4π` is representation-dependent, `2π/3` is a center increment);
> and the Riemann/GUE tie is a *shared object*, not a proof. Those are real and are fixed here.
> **(b) The framing — refined after Allen's #90 (he is right to split it).** Two different claims were
> being run together, and only one is declined:
> - **Continuum as *substrate / fundamental* — declined.** There is no ontologically real continuum
>   circle underneath the substrate; the continuum-as-foundation is mathematics' ultraviolet catastrophe
>   ([`Continuum_Choice_Fallacy.md`](Continuum_Choice_Fallacy.md), [`TheContinuum.md`](TheContinuum.md)).
> - **Continuum as an *effective limit* — owed, and open.** Because QLF *uses* `Real.pi` in physical
>   predictions (`α`, GR, …), it must derive the *observed* continuum as the coarse-grained limit of the
>   discrete dynamics: rods, light signals, diffusion shells, and circumference/area measurements
>   converging to the Euclidean relations `C(r)/2r → π`, `A(r)/r² → π`. That is the **ordinary empirical
>   burden of any discrete emergent-spacetime theory — not a continuum fallacy** — and QLF owes it. It is
>   an **open obligation (Ledger A)**, not a declined one.
>
> **The standing QLF claim (Jim's view): π is *derived by construction*.** The substrate's own closure
> census `C(2n,n)` (a QLF theorem) gives a finite, `Real.pi`-free, computable sequence
> `n·(C(2n,n)/4ⁿ)²` whose limit is `1/π` — and that limit is **settled classical mathematics**
> (Wallis/Stirling). So `π = lim 1/(n·returnDensity n)` is a genuine construction of `π` from the
> substrate's *intrinsic* counting (the same `C(2n,n)` behind Born stats / P-vs-NP / Riemann) — no
> circle, no import. What remains is **narrow and does not undermine the construction:** (i) *formalizing*
> that convergence inside our own Lean module is housekeeping (the convergence is established, just not
> yet wired); (ii) the *physical-walk* identification (Ledger A.2); (iii) the **separate** effective-limit
> geometry question (Ledger A.3 — owed because QLF uses `Real.pi` in `α`/GR, but a *different* question
> from "is `π` constructed"). The only thing declined is the continuum as *fundamental substrate*.

---

## §0 The thesis

`π` is **not a stored primitive**; it is the **signature of closure detection** — what you get when a
process "goes around, compares with where it started, and asks whether the state actually closed"
(Allen). QLF exhibits a *substrate-native* finite object — the ZFA closure census — whose limit is `π`,
and shows it is the *same* `C(2n,n)` that runs the Born statistics, the P-vs-NP verify-filter, and the
Riemann gap-zero density. `π` is a **computable** real (a finite algorithm yields any precision — it was
never the continuum fallacy). The machine is the discrete census; `Real.pi` is its **limit/rendering**,
never a *substrate* primitive. There is no continuum circle *underneath* the substrate to recover — but
there **is** an *effective* continuum to earn: the macroscopic Euclidean `π` relations must emerge as the
coarse-grained limit of the discrete dynamics (Allen #90 — see the status box and §5 Ledger A.3).
Rejecting the continuum as foundation is not the same as being excused from deriving its effective limit.

## §1 The closure census (count Lean-anchored; convergence a cited classical theorem)

Allen's strongest generator is the **path-counting return walk**. In QLF the count is the substrate's
own closure census: the number of ZFA-balanced stable closures of length `2n` is exactly the central
binomial coefficient (`closure_census`, reusing `find_stable_states_length_even`) — **a QLF theorem**:

$$
\bigl\lvert \{\text{stable closures of length } 2n\} \bigr\rvert = \binom{2n}{n}
$$

— the same `C(2n,n)` behind the Born statistics, the P-vs-NP verify-filter
(`realized_count_eq_central_binomial`), and the Riemann gap-zero density. Form the rational return
density (`returnDensity`, `returnDensity_eq_census`):

$$
P_{2n}(0) = \left(\frac{\binom{2n}{n}}{4^{n}}\right)^{2}
$$

a finite, computable **rational** with no `Real.pi` in it — also Lean-anchored. The classical asymptotic
`C(2n,n) ~ 4ⁿ/√(πn)` (Wallis/Stirling) gives `n·P₂ₙ(0) → 1/π`, i.e.

$$
\pi \;=\; \lim_{n\to\infty}\frac{1}{n\,P_{2n}(0)}.
$$

**Wording precision (Allen #90):** the π-convergent object is **not** `C(2n,n)` by itself — the raw
census count diverges. It is the *normalized, squared, `n`-weighted* quantity `n·P₂ₙ(0) =
n·(C(2n,n)/4ⁿ)²` — and that normalization-and-squaring is exactly the **imposed two-axis walk model**
(caveat 2 below). So "the closure census *is* the π-convergent census" is loose; the precise statement
is "the return density of the two-axis walk *built from* the closure census converges to `1/π`."

**Two honest caveats (Allen #89):**

1. **The convergence is not yet a *QLF* theorem — but it is not in doubt.** `closure_census`,
   `returnDensity`, `returnDensity_eq_census` are proven; the limit `n·returnDensity → 1/π` is the
   central-binomial Wallis/Stirling asymptotic, a **settled theorem already in Mathlib** — it simply has
   not been *imported and discharged* in this module (`physical_pi_in_progress` is a marker, not the
   proof). This is a wiring task, not a conceptual gap. Until it is wired, the right verb is *converges
   to* (cited), not *is proven by QLF to converge to*.
2. **The 2-D *squaring* presupposes a walk model.** Counting balanced strings gives `C(2n,n)`; squaring
   `(C(2n,n)/4ⁿ)²` for a 2-D return probability models the substrate as **two independent, equally-weighted
   1-D walks** (one per axis). That Pólya-walk model is *imposed on* the census; QLF has not yet
   constructed the probability space and proven the equivalence. (Honest gap — but see §5: this is about
   *which* discrete model, not about a continuum.)

## §2 Three classical machines, as closure processes

`π` is the limit of several finite, computable processes — each a "go around and test closure" (classical
convergence facts QLF *reads*):

- **Signed-residue sum (Leibniz–Gregory).** `π/4 = 1 − 1/3 + 1/5 − 1/7 + …` — an alternating signed
  count over odd residues, the same `count_pos − count_neg` structure QLF uses, on the odd lattice.
- **Pairing product (Wallis).** `π/2 = ∏ₙ (2n)²/((2n−1)(2n+1))` — the product form of the same
  central-binomial ratio as §1 (the Mathlib Wallis product underlying §1's asymptotic).
- **Inverse-square sum (Basel / ζ).** `π² = 6·∑_{n≥1} 1/n² = 6·ζ(2)` — `π` from a sum over the integers,
  no circle. The honest bridge to §4.
- **Allen's `Z0_AsBinary`** ([#98](https://github.com/rhovision-org/quantum-logical-framework/issues/98), his
  [`fundamentalPi.md`](https://github.com/lightrock/CharacteristicImpedancePython/blob/main/docs/references/fundamentalPi.md)
  — the characteristic-impedance / binary machine) is **another machine of this kind** — a finite,
  computable "go around and test closure" generator, not a circle-sampler. Recorded here so it is not lost
  (the point of #98); it sits with QLF's gauge-sector families (§3, `Forces_From_Three_Axes.md` §3a).

Each is RCA₀ and converges to `π`; none assumes a circle. That `π` has *many* discrete generators and
*no* canonical circle behind them is exactly the QLF reading: `π` is what these machines converge to, not
a continuum object they sample.

**One machine, *two* periods (and counting).** The decisive evidence that the closure census is the
*fundamental* generator — not a `π`-specific coincidence — is that the **same** census `C(2n,n)` also
yields a *second* period: **`ζ(3)` (Apéry's constant)**, `ζ(3) = (5/2)·∑_{n≥1}(-1)^{n-1}/(n³·C(2n,n))`,
now Lean-anchored in [`QLF_AperyPeriod`](lean/QLF_AperyPeriod.lean) (the finite `Real.pi`-free rational
partial sum, with each term's central binomial *proven* to be the substrate closure count). So Allen's
"find the machine" lands on a single substrate machine — the ZFA closure census — that renders `π`, `ζ(3)`,
the Born statistics, and the P-vs-NP verify-filter alike. A period carries no information its census does
not already contain.

## §3 Phase increments per sector — 2π, 4π, 2π/3 (with the group-theory caveats)

Allen's families correspond to QLF's gauge sectors
([`Forces_From_Three_Axes.md`](Forces_From_Three_Axes.md) §3a) — but, per #89, these are **characteristic
phase increments**, not all "group periods," and the table must say so:

| increment | sector | precise statement |
|---|---|---|
| `2π` | `U(1)` / ordinary rotation | full cycle; returns to the identity. The abelian gauge-fold period (EM, the photon). |
| `4π` | `SU(2)`, **spin-½ representation** | the 720° period **of the fundamental (spin-½) representation** — *representation-dependent*: integer-spin reps already close at `2π`. Not a universal `SU(2)` period (`QLF_Spin`). |
| `2π/3` | `SU(3)` **center** `Z₃` | a center **phase increment**, *not* a return to the identity — **three** applications close it (`(e^{2πi/3})³ = 1`). |

And the `2π` itself is a **chosen continuum rendering** of the finite cycle `phase = · % N`, not a
quantity *recovered* from it: `renderAngle := 2·Real.pi·k/N` *inserts* `2π`, and `render_full_cycle` is
algebraic bookkeeping ([`QLF_LoopClosure`](lean/QLF_LoopClosure.lean)). The machine is `% N`; `2π` is the
display we choose. (Allen and QLF agree here — that `2π` is a rendering, not a recovery, is QLF's *own*
thesis, not a concession.)

## §4 The Riemann *resonance* — a shared object, not yet a shared theorem

What is true is a **structural resonance**, stated without overreach:

- **`π` and `ζ` share the census `C(2n,n)`.** `π² = 6·ζ(2)` (§2) ties `π` to `ζ`, and the `π`-census
  `C(2n,n)` is the *same* object in the QLF Riemann gap-zero density `C(2n,n)/4ⁿ ~ 1/√(πn)`
  ([`ReverseMathematics.md`](ReverseMathematics.md) §4.7, [`SpectralGap.md`](SpectralGap.md),
  [`QLF_RiemannMRE`](lean/QLF_RiemannMRE.lean)).
- **What this does *not* establish (per #89).** A reciprocal zero-gap *density* is not automatically a
  consecutive-level *spacing* distribution, much less the **GUE** (Montgomery–Odlyzko) law — that is a
  separate, unproven step. "The same coefficient appears" is a shared object, **not** a proof that "`π`
  and RH run on one machine." QLF's RH route still routes the decisive Mellin↔ζ / spacing↔GUE
  correspondence through its named boundary axioms (`spectral_hilbert_polya`, `MRE_bridge`;
  `rh_mre_proof_in_progress`). No complexity ("faster than any known process") claim is made.

## §5 Honest scope — two ledgers (Allen #89 + #90)

**π is derived by construction** (status box): the substrate census → `1/π` via settled asymptotics. The
items below are *narrow* — they refine and physically ground the construction, they do not put "is π
derived" in doubt. **Allen's #90 correctly moved the geometry bridge from "declined" to "owed"** — the
only thing genuinely declined is a *fundamental* continuum.

**Ledger A — genuine QLF obligations (all earnable *without* a fundamental continuum):**

1. **Formalize the convergence in *our* Lean (housekeeping).** The limit `n·returnDensity → 1/π` is the
   Mathlib central-binomial/Wallis asymptotic — *established mathematics*, so the construction already
   derives `π`; importing/discharging it here (replacing the `physical_pi_in_progress` marker) just moves
   a settled theorem inside the module. Not a conceptual gap.
2. **Construct the walk probability space + identify the process.** Derive the 2-D squaring from ZFA
   dynamics — prove the substrate realizes two independent equally-weighted axis-walks — rather than
   *imposing* the Pólya model. Until then the census is a **mathematically selected** object, not a
   *physical process shown to be executed by nature*; calling it "the thing itself" is an ontology claim,
   not a derivation (Allen #90, conceded). This is the same item as "no physical universe-machine
   identified yet."
3. **The effective-limit (geometry) recovery — the standard emergent-spacetime burden.** Show that
   coarse-grained QLF observables converge to the Euclidean relations: `C(r)/2r → π`, `A(r)/r² → π`, from
   discrete directionally-unbiased closure statistics. This needs **no fundamental continuum** — it is the
   ordinary obligation every discrete emergent-spacetime theory (causal sets, LQG, …) carries, and QLF
   carries it too *because it uses `Real.pi` in real predictions* (`α`, GR). It is **open**, and it is
   QLF's to do.

**What is genuinely declined (one thing only):** the continuum as **substrate / fundamental** — an
ontologically real circle *underneath* the discrete dynamics. That is the ultraviolet catastrophe QLF
retires ([`Continuum_Choice_Fallacy.md`](Continuum_Choice_Fallacy.md)). Declining it is *not* the same as
declining the **effective-limit** recovery of A.3 — Allen #90's central, correct, point.

**Bottom line.** π is the limit of the discrete machine; `Real.pi` is the *effective* rendering QLF must
**earn**, not a fundamental object it must *recover*. Ledger A (convergence wiring, the physical
process/probability space, and the geometry effective-limit) is all owed and all doable inside the
discrete frame. The only rejection is continuum-as-foundation. Allen's #89 sharpened the verbs; his #90
correctly converted the geometry bridge from "declined" into an open obligation — both adopted.
