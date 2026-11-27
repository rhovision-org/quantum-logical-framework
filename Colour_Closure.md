# Colour Closure — three-axis closures, their connectors, and what the delay carries

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Lean:** [`lean/QLF_ColourClosure.lean`](lean/QLF_ColourClosure.lean), no axioms.
**Census:** [`borromean_census.py`](borromean_census.py) → [`data/borromean_census.json`](data/borromean_census.json), exact.
**Parents:** [`Quarks.md`](Quarks.md), [`Forces_From_Three_Axes.md`](Forces_From_Three_Axes.md),
[`Gluon_Closure_Dynamics.md`](Gluon_Closure_Dynamics.md) (GL7/GL8, issue #287),
[`Diversity_Quark_Emergence.md`](Diversity_Quark_Emergence.md).

Everything below stays on the eight-twist alphabet. Colour is the `F₃²` label of a twist (`colVec`,
[`QLF_ColourFlux`](lean/QLF_ColourFlux.lean)), baryon number is the three-axis winding read on the
junction ([`QLF_BaryonWinding`](lean/QLF_BaryonWinding.lean)), a closure is a count-balanced history
(Pauli closure follows by `count_balanced_pauli_closed`), and the delay to closure is `distance`
([`QLF_Manifestation`](lean/QLF_Manifestation.lean)). Nothing continuous is imported.

---

## 1. Every closure is a colour singlet (proved)

`closure_is_colour_singlet`: every count-balanced history has total colour label `(0,0)`. Each
twist's label is the negative of its conjugate's, and balance pairs them.
[`QLF_Confinement`](lean/QLF_Confinement.lean) `singlet_closure` proved the same thing for the
binary charge weight and read colour as an instance of it. This is the statement on the colour labels
themselves. The contrapositive, `colour_charged_not_closed`, is the obstruction: a history with net
colour never closes.

The converse fails (`colour_singlet_not_closure`). The Borromean word `>^/` is a colour singlet
(`c_x + c_y + c_z = 0`) but is not a closure: it is an open walk to `(1,1,1)`. Colour neutrality is
strictly weaker than closure, because the colour map from the signed action vector `ℤ⁴` onto `F₃²`
has a kernel of index 9.

Zero total `F₃²` colour is what these theorems establish. It is not the same statement as a physical
SU(3)-invariant singlet state: the identification of this finite colour algebra with physical SU(3)
beyond the colour factor ([`QLF_GluonVertex`](lean/QLF_GluonVertex.lean)) is conditional.

## 2. The connectors are the Borromean triples (proved)

Inside the three spatial axes, the three-gluon colour vertex of
[`QLF_GluonVertex`](lean/QLF_GluonVertex.lean) and the baryon triple are the same object:

| Theorem | Statement |
|---|---|
| `spatial_vertex_iff_borromean` | for three spatial twists, the vertex is nonzero **iff** they lie on the three distinct axes with one orientation (`>^/` or `<v\` in any order) |
| `borromean_baryon` | every such triple carries baryon number `±1` |
| `spatial_singlet_triple` | a spatial triple is a colour singlet iff it is Borromean or one twist repeated (`>>>`) |
| `non_borromean_no_vertex` | a triple that misses an axis has no vertex: it is colour-charged (so it cannot close) or collinear |
| `borromean_count` | 12 ordered Borromean triples (the other 36 of `vertex_count`'s 48 use the gauge line) |

So the minimal three-axis connector **is** the gluon vertex, read as twists. The separate `F₃²` toy of
[`Gluon_Closure_Dynamics.md`](Gluon_Closure_Dynamics.md) is this alphabet under `colVec`, which is a
bijection onto the nonzero labels (`colVec_injective`, `colVec_surjective`).

## 3. Census of three-axis closures by baryon number (exact computational)

Six spatial twists, closures counted exactly by a transfer recursion (brute-force cross-checked to
`L = 8`). "Wound" means `B ≠ 0`. "First" is the absorbing census: the walk's first return to the
origin is at `L`.

| L | closures | wound | max \|B\| | first closures | wound (first) |
|---|---:|---:|---:|---:|---:|
| 2 | 6 | 0 | 0 | 6 | 0 |
| 4 | 90 | 0 | 0 | 54 | 0 |
| 6 | 1,860 | 576 (31.0 %) | 4 | 996 | 384 (38.6 %) |
| 8 | 44,730 | 22,752 (50.9 %) | 5 | 22,734 | 13,248 (58.3 %) |
| 10 | 1,172,556 | 750,240 (64.0 %) | 6 | 577,692 | 402,144 (69.6 %) |
| 12 | 32,496,156 | 71.8 % | 10 | 15,680,628 | 75.4 % |
| 14 | 936,369,720 | 76.5 % | 11 | 445,162,392 | 78.7 % |

What this shows:

- **No closure below length 6 is wound.** That is a theorem already
  (`QLF_Manifestation.short_closures_unwound`); the census reproduces it.
- **At length 6 every wound closure is one conjugate pair per axis**, and `B ∈ {±1, ±2, ±4}`: the
  value `±3` does not occur (192 : 72 : 24 per sign). `±9` is likewise absent at `L = 12`. These are
  observed values, not proved patterns.
- **Once all three pairs are present, winding is the majority** (exact computational,
  `python3 borromean_census.py --minimal`, checked in its self-test): of the 720 orderings of `> < ^ v / \`, 576 are wound,
  and of the 480 that are first closures, 384 are. This is counted over words, unsigned and at fixed
  length, so it shows structural prevalence, not persistence or selection.
- **Wound closures become the majority by length 8 and keep growing**, and first closures are more
  often wound than closures in general.

### Two limits of the winding as a particle property (proved)

- `winding_not_rotation_invariant`: `>^</v\` and its rotation `^</v\>` are both first closures, with
  junction baryon number `−2` and `−1`. The windowed winding is a property of the word read from its
  first event, not of the cyclic loop. If the two words describe one physical loop, baryon number
  depends on where it is read from; if the first event is physically distinguished, that has to be
  shown.
- `winding_not_additive`: `>^<v` and `/\` close with `B = 0`, and their concatenation closes with
  `B = 1` from the window across the boundary. Independent composition and genuine junction formation
  are not yet distinguished.

These are reasons not to treat `B` as a settled baryon number. Replacing it with a cyclic sum is not
the fix either until the physical equivalence relation on closures (rotation, dressing, composition)
is fixed first.

So the reading "every balanced three-axis history is either the Borromean class or has `B = 0`" holds
only if the Borromean class is defined as `B ≠ 0`, which makes it empty of content. The substantive
facts are the minimum length (6, proved) and the value distribution above. Likewise, "only the
Borromean class produces a first closure with `B ≠ 0`" is the same definition again; the census says
wound first closures are common, not rare.

## 4. What the delay carries: GL7 and GL8 (proved, with a negative result)

The delay is already a theorem: `distance_eq_delay` says a history closes after exactly its `ℓ¹`
separation `r` of further events, never sooner. So "delay grows linearly with separation" is exact.

The new theorems show what it does **not** carry:

- `colour_distance_le_one`: every history reaches a colour singlet by appending at most one twist.
  Inside the three axes, at most two (`spatial_colour_distance_le_two`), and two can be needed
  (`spatial_bound_attained`). Colour distance is bounded no matter how far apart the ends are. The
  toy's `d_G` is bounded too (at most 3 in [`data/gluon_closure_dynamics_census.json`](data/gluon_closure_dynamics_census.json)).
- `colour_singlet_line`: `>^{3k}` is a colour singlet for every `k` and has delay `3k`.
- `delay_colour_blind`: `>>>`, `>^/` and `>>^` all have delay 3; the first two are singlets with
  `B = 0` and `B = 1`, the third is colour-charged.

**GL7: logical distance established, physical identification conditional.** The logical distance is
the one `distance_eq_delay` already gives: closing delay = `ℓ¹` norm of the signed action. That norm
has four components, the gauge one included; its restriction to the three spatial axes is immediate,
but reading it as physical spatial separation is a reconstruction bridge (B01 in
[`Principles.md`](Principles.md)). What is settled is negative: the colour-label distance (and the
toy's `d_G`) can **not** be that map, because it is bounded by a constant while the delay is
unbounded. (Recursive perspectival existence, C23 in [`Principles.md`](Principles.md), would read the
gauge component as a relation between perspectives rather than a displacement; that is a conjecture.)

### Shortest completions: more ways, and their phases (proved)

`shortest_completion_perm`: every shortest completion of a history is a rearrangement of the canonical
one, so the number of shortest completions is the multinomial `(n₁+⋯+n_k)!/(n₁!⋯n_k!)` of the per-axis
imbalances. At fixed delay, spreading the imbalance over more axes raises it: delay 3 gives 1 way on one
axis, 3 ways split `2 + 1`, and 6 ways with one unit on each of three axes (`diverse_completion_counts`).

The phases do not follow. On the light cone the signed sum over those orderings is
`cone_amplitude` ([`QLF_LightCone`](lean/QLF_LightCone.lean)), and `diverse_completions_cancel` reads it
off: the 6 orderings of `^ < /` sum to exactly `0`, while `^^^` and `^^<` do not. The most diverse
shortest completion cancels completely. So "diversity increases the ways to close" holds for unsigned
counts and fails, in this case, for amplitudes. Any diversity advantage has to be stated after the
phases, not before.

**GL8 status: not derived.** The linear delay is the delay of every open history, coloured or not, so
it is not a colour-specific string tension. A confining potential would need a cost that grows with
separation **for colour-charged configurations only**. Nothing proved here supplies that. A candidate
to test next (conjecture, not claimed): count the closures of a separated `q … q̄` configuration
whose every intermediate cut is colour-charged, and ask whether that count falls exponentially in `r`
(area-law style) for coloured cuts and not for neutral ones.

## 5. Binary pruning is blind to colour (proved)

`binary_projection_blind`: `>\` carries net colour and is not a closure, yet its pos/neg projection
`[pos, neg]` achieves ZFA under `full_zeno_prune`. So colour is pruned by the eight-twist count
balance (the runtime `is_zfa`), not by `full_zeno_prune` on the binary projection.

## 6. Perspectives: shared closures are not tree-shaped (proved)

[`lean/QLF_PerspectiveNetwork.lean`](lean/QLF_PerspectiveNetwork.lean) tags each twist with the
perspective that contributes it (the three bodies of [`QLF_SharedReality`](lean/QLF_SharedReality.lean)),
before any closure is evaluated. This is gates RP0–RP2 of the recursive-perspective programme (C23 in
[`Principles.md`](Principles.md)).

- `shared_closure_cycle_exists` (RP0): the events `A> B<`, `B> C<`, `C> A<` each close jointly, no
  contributor closes alone in any of them, and every perspective closes over all three.
- `tree_edges_insufficient` (RP1): a graph on the three perspectives with those three relations as
  edges has a cycle, so it is not a tree. This step is graph theory; the content is RP0's witness. A
  tree with mediator nodes, or one that carries a relation as a path, is not excluded.
- `irreducible_three_way_closure` (RP2): the proton closure split as `A = >v`, `B = ^\`, `C = /<`
  closes jointly with baryon number 1, while no perspective and no pair of perspectives closes. Their
  nets are `x−y`, `y−z`, `z−x`.
- `gauge_keeps_winding_moves_colour` (RP4, partial): a gauge twist leaves the winding unchanged and adds
  the nonzero label of `+` to the total colour.

So the hierarchy of perspectives and their participation in shared closures are different structures,
and the second needs at least a graph with cycles, and a hypergraph for irreducible three-way closures.
Both witnesses use spatial twists only, so they say nothing yet about the fourth axis as a relation
between perspectives (RP5); that and the recovery of three axes at an emergent level (RP6–RP7) are
conjectures.

## 7. Open

- A colour-specific cost of separation (GL8), §4.
- The `±3` gap at length 6 and `±9` at length 12, as a theorem.
- The physical equivalence relation on closures (rotation, dressing, composition), and a baryon number
  invariant under it and under admissible gluon moves.
- Whether any diversity advantage survives the phases beyond the light-cone cases above.
- The kinematic factor of the vertex and four-gluon gluing (issue #207).
- Per-flavour quark words.

## Reproduce

```bash
python3 borromean_census.py --self-test
python3 borromean_census.py --max-len 14
```
