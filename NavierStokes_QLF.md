# Navier–Stokes Existence and Smoothness in [QLF](README.md)

> **The engine (path integral · all closures · Witten 1988).** This attack is QLF's one Millennium move —
> *generate every possibility, then select the invariant* — the exact/constructive form of the Feynman path
> integral (all paths happen; stationary phase selects) and of Witten's 1988 Jones-polynomial path integral
> (a physics sum-over-everything that proved rigorous mathematics, discharged by Reshetikhin–Turaev).
> **Generate:** all flow histories. **Select:** ZFA closure ⟹ no realized history blows up
> (`realized_flow_is_stable`; the quantized vorticity cap). **Bridge (settled-math, couched Witten→RT):**
> `continuum_vorticity_planck_capped` — *reduced* in [`QLF_NavierStokesBKM`](lean/QLF_NavierStokesBKM.lean) to the
> cited Beale–Kato–Majda theorem + the sharp Planck vorticity-cap bridge, the nearest to the knot sector's
> finished end-state. See [Millennium.md](Millennium.md) § *The engine*.

> **The geometric mechanism** — *why* no realized flow blows up — is now machine-verified in [`Navier_Stokes_Geometry.md`](Navier_Stokes_Geometry.md) / [`lean/QLF_AngularMomentum.lean`](lean/QLF_AngularMomentum.lean): vorticity is the discrete curl `signTriple`, **quantized to `±1` per cell** (`vorticity_quantized`), so the Beale–Kato–Majda vorticity-blow-up criterion is unsatisfiable on the substrate. The correction is the quantization/discreteness; the continuum-PDE limit remains the boundary below.

> **Status: `navier_stokes_proof_in_progress` — a reformulation.** *Contrast (once):* the **classical**
> Clay problem (global smoothness of the continuum incompressible PDE) is not solved here. *What is
> proven (the reformulation):* realized flows achieve ZFA and are stable closures (reusing
> `encode_is_zfa` / `qlf_universality`), so **no realized history blows up** —
> [`lean/QLF_NavierStokes.lean`](lean/QLF_NavierStokes.lean). *The gap:* continuum-PDE inheritance
> under the limit, carried by the one bridge axiom `continuum_vorticity_planck_capped`. This is a genuine
> continuum step — QLF's **thesis** (not a proof of this problem) is that the continuum sector is where
> ZFC's machinery struggles ([Continuum_Choice_Fallacy.md](Continuum_Choice_Fallacy.md)); the Clay
> problem itself is open analysis, not a known independence result, so the bridge is the honest gap.
> See [Open_Problems.md](Open_Problems.md).

## 1. The classical problem

A Millennium Prize Problem: prove (or disprove) that for the incompressible
Navier–Stokes equations in three dimensions, smooth initial data yield a **globally
smooth** solution for all time — that finite-energy flows never develop a
finite-time singularity (a point of infinite velocity/vorticity, "blow-up"). The
analytic heart is regularity: ruling out a self-similar cascade that concentrates
unbounded energy into a point in finite time.

## 2. The QLF reframing: a flow is a ZFA event stream

In QLF a physical process is not a smooth field on a continuum manifold; it is a
**dense-but-discrete sequence of ZFA-closed events** whose statistical limit *looks*
smooth ([TheContinuum.md](TheContinuum.md); [`lean/ZFAEventDynamics.lean`](lean/ZFAEventDynamics.lean)).
Each event synthesizes its own local space and time and carries a bounded quantum
(one Planck length × one Planck tick *together*; per-event information `log 2`). A
"flow" is the coarse-grained average of this event stream.

A **finite-time blow-up** is exactly a demand the substrate cannot meet: it requires
*infinitely many events in finite proper time* — an unbounded synthesis rate, the
fluid-dynamical face of a **non-terminating, Busy-Beaver-class computation**. And
that is precisely what QLF prunes.

## 3. The structural smoothness argument

- **Blow-up = non-termination.** A singular solution concentrates infinite
  frequency into a point — it never reaches closure, it diverges. In QLF every
  candidate history is filtered by `full_zeno_prune`; the histories that **fail to
  achieve ZFA** (the non-terminating, never-closing tails) are removed *before they
  become physical events* ([`lean/QLF_Axioms.lean`](lean/QLF_Axioms.lean),
  [`lean/QLF_Universality.lean`](lean/QLF_Universality.lean),
  [Lagrangian_Formulation.md](Lagrangian_Formulation.md)). A blow-up solution is in
  the pruned set: it is mathematically expressible but not physically realized.
- **The physical tail is smooth.** The realized events are ZFA closures (the one
  conjecture, [Framing.md](Framing.md)); `qlf_universality` gives every terminating
  circuit a ZFA encoding (bookkeeping, [Principles.md](Principles.md) P10). A flow assembled
  from ZFA-closed events has, at every scale, a bounded per-event quantum — no point
  carries infinite energy, because energy is `count × ℏω` over finitely many events
  in any finite region ([Per_Qubit_Mass_Quantum.md](Per_Qubit_Mass_Quantum.md),
  [Information_Energy_Equivalence.md](Information_Energy_Equivalence.md)). Smoothness
  is the continuum shadow of "finitely many bounded events per finite spacetime
  region."
- **Same selection principle as the UV catastrophe.** QLF has no ultraviolet
  divergence for the same reason it has no fluid singularity: the substrate is RCA₀,
  below the Busy-Beaver horizon ([ReverseMathematics.md](ReverseMathematics.md)). An
  infinite-frequency cascade is precisely the kind of uncomputable, never-closing
  object the ZFA filter excises.

So QLF's stance: **the physically realized Navier–Stokes solutions — the ones that
are limits of ZFA event streams — are globally smooth; the singular solutions are
the non-physical, pruned, never-closing tail.** Blow-up is to fluid dynamics what
the Busy Beaver is to computation.

## 4. Where the boundary sits

This is a *foundational* regularity argument about the substrate, not a *PDE proof*
about the classical incompressible Navier–Stokes equations on continuous ℝ³. The
bridge — that the continuum limit of the ZFA event stream *is* a solution of the
classical equations, and that the limit inherits the substrate's no-blow-up — is the
genuinely analytic step (the continuum limit, à la the Yang–Mills continuum
existence). QLF marks it as an explicit boundary rather than discharging it: the
substrate has no singular realized histories; whether the classical PDE inherits
that under its continuum limit is the open analytic work.

## 5. Epistemic stance

Within QLF's frame, global smoothness is *structurally expected*: a discrete
substrate that prunes every never-closing (infinite-frequency) history cannot
realize a finite-time singularity, so the physical flows it synthesizes are smooth.
The remaining step is a regularity theorem for the continuum PDE, carried by the bridge axiom
`continuum_vorticity_planck_capped`. This is a genuine continuum step — QLF's *thesis* (not a proof
of this specific problem) is that the continuum sector is where ZFC's machinery is pathological;
but the Clay problem is open analysis, not a known independence result, so the bridge is stated
as the honest open step. The document claims the substrate no-blow-up result as genuine progress,
not a finished classical proof.
This is Lean-anchored in [`lean/QLF_NavierStokes.lean`](lean/QLF_NavierStokes.lean):
realized flows achieve ZFA (`realized_flow_achieves_zfa`, reusing `encode_is_zfa`) and are
stable closures (`realized_flow_is_stable`, reusing `qlf_universality`), with the
continuum-limit step named as the explicit boundary axiom `continuum_vorticity_planck_capped`
and the `navier_stokes_proof_in_progress` status marker.

## References

- J. Leray, *Sur le mouvement d'un liquide visqueux emplissant l'espace*, Acta Math. **63** (1934) 193–248 — weak solutions.
- L. Caffarelli, R. Kohn & L. Nirenberg, *Partial regularity of suitable weak solutions of the Navier–Stokes equations*, Comm. Pure Appl. Math. **35** (1982) 771–831 — partial regularity.
- C. L. Fefferman, *Existence and smoothness of the Navier–Stokes equation* — Clay Mathematics Institute (official problem description). <https://www.claymath.org/millennium-problems/>
