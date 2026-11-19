# Gluon Closure Dynamics — singlet distance, vertex creation/gluing, and harmonic binding

**Status:** first slice for issue [#286](https://github.com/rhovision-org/quantum-logical-framework/issues/286).
GL0–GL6 are implemented as a finite two-channel vertex model. GL7 (logical → physical spatial
distance) and GL8 (string tension) remain open. This is not full QCD.

---

## 1. The bridge

The missing dynamical sentence is:

```
admissible gluon interaction
  → new admissible joint colour-closure channel
  → possibly smaller d_G
```

separately from:

```
binding
  → T_bind ≤ T_parts
  → f_bind ≥ f_parts
```

Keep four quantities distinct:

```
d_G(s)     = remaining gluon-admissible distance to singlet closure
T          = characteristic listening/recurrence period
f = 1/T    = recurrence frequency
tau_event  = 0
```

`d_G` does not determine `T`; frequency does not determine the next event. Event priority remains
`argmin d` under #281.

---

## 2. GL2 — vertex creation and gluing

The colour labels are the eight nonzero vectors of `F₃²` (the `colVec` image of the twists in
`QLF_ColourFlux`). A state is a multiset of labels.

The GL2 move has two channels, both defined **before** any distance is computed:

```
create: choose q, r in the state with symp(q, r) ≠ 0
        p = -(q + r)
        add p

glue:   choose q, r in the state with symp(q, r) ≠ 0
        p = -(q + r)
        replace q and r by p
```

The condition `symp(q, r) ≠ 0` is exactly the non-collinearity condition behind the nonzero
three-gluon vertex in `QLF_GluonVertex`. Neither channel consults `d_G`.

A colour singlet is a state whose total colour label is `(0,0)`. `d_G` is the shortest number of
vertex moves to a singlet, or undefined if no such path exists within the declared search bound.

This is a toy: it models gluon-label creation/gluing, not quark emission/absorption, kinematics, or a
coupling.

---

## 3. Finite census

Enumeration: all colour multisets of size 1–4 over the eight labels.

```
states: 494
with a singlet path: 454
without a singlet path: 40
```

Move classification, separated by channel:

```
create:
  distance_reducing:  216
  distance_neutral:    24
  distance_increasing: 72
  blocked:            744

glue:
  distance_reducing:  456
  distance_neutral:   192
  distance_increasing:336
  blocked:             96
```

`blocked` means the successor has no singlet path within the declared search bound (states up to
size 5); it is not “increasing.”

First-singlet moves:

```
create: 120, all distance_reducing
glue:   120, all distance_reducing
```

So, in this toy:

- **not** every gluon move reduces distance — both channels have neutral and increasing moves;
- moves that actually produce a first singlet are reducing, as expected for a `d=1 → 0` step;
- the result does not establish that physical gluon interactions are attractive.

The neutral and increasing moves are important: they prevent “gluon interaction = contraction” from
being built into the model.

### Worked states

```
open pair ((1,0),(0,1)): d = 1
  create -> ((0,1),(1,0),(2,2)), a singlet
  glue   -> ((2,2),), not a singlet

two-gluon singlet ((1,0),(2,0)): d = 0, no moves
gluing state ((0,1),(1,0),(1,1)): d = 1; both channels contain a singlet move
```

The `open pair` example is not a closure under gluing alone; the creation channel supplies the
singlet. This is why the reverse channel matters.

---

## 3a. Witness audit and atomic closure

Every move carries a GL2 witness `(q, r, p)` with:

```
p + q + r = 0
symp(q, r) ≠ 0
```

The census audits **1,584** witnesses: all triples close and all pairs are non-collinear. The move
relation therefore has an explicit algebraic witness; it is not inferred from `d_G`.

A first closure now has a path witness:

```
open pair ((1,0),(0,1))
  create -> ((0,1),(1,0),(2,2))
  event  = CLOSE
  tau_event = 0
  atomic = true
```

This makes GL4/GL6 executable rather than only cited: listening has a path, but the closure event
itself is atomic.

---

## 4. Harmonic binding

For constituent periods `R_A`, `R_B`:

```
R_bind = min(R_A, R_B)
f_bind = 1 / R_bind
```

Example `R_A = 5`, `R_B = 3`:

```
R_bind = 3
f_A = 1/5
f_B = 1/3
f_bind = 1/3
```

Binding raises frequency relative to the slower constituent but does **not** exceed the already
fastest one. The existing theorem is non-strict; do not claim strict increase unless the period
strictly falls.

---

## 5. What this does not claim

- No full QCD dynamics.
- No quark emission/absorption, kinematics, coupling `g_s`, or loops.
- No string tension or `V(r) = σr`.
- No physical spatial contraction from logical distance (GL7).
- No claim that every gluon interaction is attractive; the census has 72 increasing create moves
  and 336 increasing glue moves.
- No change to #322 or the frozen AI experiment.

---

## 6. Relation to #287

#287 is the parent spatial-response issue. This PR is the gluon **test case** of the contraction
branch. The sign belongs to the event/relation: a gluon interaction may be distance-reducing,
distance-increasing, or blocked depending on the state and channel.

The parent keeps `ΔS` and `Δd` independently defined. This model supplies `Δd`; it does not define
physical `ΔS`.

---

## 7. Reproduce

```bash
python3 gluon_closure_dynamics.py --self-test
python3 gluon_closure_dynamics.py --run
python3 -m unittest tests.test_gluon_closure_dynamics -v
```

The run writes `data/gluon_closure_dynamics_census.json`.

---

## 8. Wording correction

“Constructing delay grows with separation, giving the linear potential” should be read as the
confinement obstruction plus an **open** spatial bridge, not as a derived gluon pull. The finite model
here is a vertex-creation/gluing distance toy; it does not derive a potential.

---

## 9. Anchors

- `lean/QLF_Confinement.lean` — `charged_not_closed`, `singlet_closure`.
- `lean/QLF_ColourFlux.lean` — `F₃²`, `colVec`, `symp`.
- `lean/QLF_GluonVertex.lean` — `gluon_vertex_iff`.
- `lean/QLF_GluonGluing.lean` — `gluing`.
- `lean/QLF_Manifestation.lean` — `distance_eq_delay`.
- `lean/QLF_HarmonicClosure.lean` — `freq_bind_ge_left/right`, `binding_raises_harmonic`.
- #281 — event timing.
- #286 — this issue.
- #287 — parent spatial-response issue.
