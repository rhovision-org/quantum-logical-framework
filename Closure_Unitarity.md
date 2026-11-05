# Closure on the unitary path, and the two kinds of zero

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and opposite quantum logical action with zero free energy, the principle of QLF.

This is the first milestone of the closure-algebra programme of
[issue #207](https://github.com/rhovision-org/quantum-logical-framework/issues/207), *"Grand Simplification of
Quantum Mechanics in QLF: closure, unitarity, poles, zeros, and finite amplitudes"*. That issue asks whether
unitarity, poles, zeros, factorization, interference and finite RG are different readings of one closure
algebra. It is a research programme with stated kill conditions. This page records the two low-risk theorem
targets the issue and its review named first, **U1** (finite-history unitarity) and **PZ3** (the zero
taxonomy), and one result that came out of PZ3: the `^<` cancellation holds at every order, and the proof
gives the mechanism.

Lean: [`lean/QLF_ClosureUnitarity.lean`](lean/QLF_ClosureUnitarity.lean). No axioms. The registry
cross-checks use `native_decide`, as [`lean/QLF_CausalDimension.lean`](lean/QLF_CausalDimension.lean) does.

---

## 1. U1: every finite history is unitary

Each of the eight twists maps to `±σ` or `±I` ([`lean/QLF_TwistAlphabet.lean`](lean/QLF_TwistAlphabet.lean)).
Each is Hermitian and squares to `I`, so each is unitary (`twist_unitary`). The unitary group is closed under
products, so the ordered fold `U(h)` of **every** history, open or closed, is unitary:

```text
history_unitary : U(h) ∈ U(2)          for every finite twist history h
                  U(h)† U(h) = U(h) U(h)† = I
```

Closure plays no part in this. Unitarity is the ground, and closure is a distinguished point on it.

## 2. U1b: closure is the central point of that path

A count-balanced history is unitary **and** folds to the real centre `{+I, −I}`
(`closure_on_unitary_path`, from `phase_rule_real` in [`lean/QLF_PhaseRule.lean`](lean/QLF_PhaseRule.lean)
and, independently, [`lean/QLF_BalancedPhaseReal.lean`](lean/QLF_BalancedPhaseReal.lean)). The inclusion is
strict: `^` alone is a unitary history whose fold `σy` is neither (`unitary_history_not_closure`).

```text
unitary histories  ⊋  ZFA closures        I → U₁ → U₂ → … → Uₙ ∈ {±I}
```

## 3. U2 seed: the dagger closes every history

Read a history backwards and you get the adjoint of its fold, exactly, because every twist is Hermitian
(`fold_reverse : U(h)† = U(reverse h)`). Conjugating every twist costs one sign each (`fold_map_conj`). So the
conjugate-reverse history `dagger h = reverse (map conj h)` folds to `(−1)^|h| · U(h)†` (`fold_dagger`), and

```text
closure_by_dagger           : U(h ++ dagger h) = (−1)^|h| · I
countBalanced_append_dagger : h ++ dagger h is count-balanced
```

for **every** `h`. Unitarity `U U† = I` is what makes `h ++ h†` close. This is the general form of the
Hermitian-pair closure `t · t† = −I` (`hermitian_pair_folds_to_negI`), and of the DNA-duplex fold
`(−1)^n I` in [`lean/QLF_Duplex.lean`](lean/QLF_Duplex.lean), which is the same statement for the two-pair
nucleotide alphabet. It is the identity and dagger part of the closure groupoid that U2 asks for. Composition
and boundary matching are not built yet.

## 4. PZ3: structural zeros and interference zeros

For a seed `s` and a continuation length `L`:

| Object | Lean | Meaning |
|---|---|---|
| closure family | `closureFamily s L` | the length-`L` continuations `c` with `s ++ c` count-balanced |
| multiplicity `W_L` | `ways s L` | how many ways close |
| signed amplitude `A_L` | `signedAmplitude s L` | `Σ_c φ(s ++ c)`, each phase `±1` from the phase rule |

`A_L` is a coherent amplitude, not a weight. Summing the actual `2×2` folds gives `A_L · I`
(`matrix_amplitude`). So this construction does not reuse the normalized event weight that
[`Interference_NoGo.md`](Interference_NoGo.md) proves cannot interfere constructively (kill condition 6 of
the issue).

Two ways to be zero:

- **Structural zero** (`StructuralZero`): the family is empty. No admissible closure exists.
- **Interference zero** (`InterferenceZero`): the family is non-empty and the signed sum is exactly `0`.

The two are exclusive (`zero_exclusive`), and together they are every zero (`zero_taxonomy`).

## 5. PZ3b: anti-Hermitian seeds are forbidden at every order

[`Perturbation_Theory_QLF.md`](Perturbation_Theory_QLF.md) reported from the registry that `^<` has
`W = 2, 72, 2820` at `L = 2, 4, 6` with `A_L = 0` each time. That was a finite observation. It is now a
theorem at every `L`, together with its cause:

> **`antiHermitian_seed_forbidden`.** If a seed's fold is anti-Hermitian, `U(s)† = −U(s)`, then
> `A_L(s) = 0` for every `L`.

The proof is an involution on the closure family. `c ↦ reverse c` keeps `s ++ c` balanced and replaces
`U(c)` by `U(c)†`. When `U(s)` is anti-Hermitian (so `U(s)² = −I`), this reverses the closing sign
(`phase_reverse_flip`). The family therefore splits into `±` pairs that cancel exactly. A corollary is that no
palindrome ever closes an anti-Hermitian seed (`antiHermitian_no_palindrome`).

The pairing is **continuation reversal**, a combinatorial involution on words, which acts on the fold
as the dagger. It is the substrate's candidate for time reversal, in line with
[`Reversibility.md`](Reversibility.md), but physical time reversal is antiunitary, and no antiunitary
operator on a state space has been constructed here. Until it is, the theorem should be read as a
statement about reversal of continuations, not as a time-reversal selection rule.

`U(^<) = σy·(−σx) = iσz` is anti-Hermitian (`upLeft_antiHermitian`), so:

- `upLeft_forbidden_all_orders`: `A_L(^<) = 0` for all `L`.
- `upLeft_interference_zero`: at `L = 2`, closures exist (`v>`, `>v`), so this is an interference zero
  and not a structural one. The transition is forbidden by destructive interference that continuation
  reversal forces. It is not forbidden for lack of histories.
- `upLeft_ways_two/four/six`: the registry's `2, 72, 2820`, re-derived.

Two contrasts show what the theorem does and does not cover:

- `^` has a Hermitian fold (`σy`), so no such pairing exists. `A_1(^) = −1` (`up_amplitude_one`).
- `^^^^` at `L = 2` is a structural zero (`upFour_structural_zero_two`). It needs four `v`. At `L = 4` it
  closes once (`upFour_ways_four`). A structural zero can be a statement about capacity, while the
  anti-Hermitian zero is a selection rule at every capacity.

**What would make this physics.** In the issue's dictionary an interference zero is the substrate candidate
for a hidden amplitude zero. That match is a hypothesis. The theorem gives one concrete, all-orders mechanism
(continuation-reversal pairing). Whether the Arkani-Hamed–Cao–Dong–Figueiredo–He zero loci
([arXiv:2312.16282](https://arxiv.org/abs/2312.16282)) come from a mechanism of this kind is benchmark PZ4,
and it is open.

## 6. What this does not do

These are finite and exact, and they cover only the first rows of the issue's checklist. The following
remain open, as the issue frames them:

- **U3 beyond the measure.** §8 proves the leakage identity, in the cylinder measure and as an
  amplitude identity. A channel operator `S_R` on boundary states with `S†S = I` has not been built.
- **PZ2 beyond the vector of channels.** §7 gives the scalar kernel, the resolvent and the
  first-closure factorization of every seeded channel. §9 factorizes every boundary channel, with
  matrix-valued amplitudes. Still open: a transfer kernel `K_{vw}` between two boundary states
  (`G = I + K G` as a matrix over channels), residue factorization *at* a pole of a continuum
  rendering, and the finite RG flow of `K` through [`lean/QLF_ExactRG.lean`](lean/QLF_ExactRG.lean).
- **G1–G4**, every gluon benchmark.

Status: the U1, U3, PZ1–PZ1c and PZ3 rows of the issue's Phase A/B checklist are done, and PZ2 has its channel factorization (§9). Nothing on this page claims that
unitarity *is* closure (kill condition 1).

---

## 7. PZ1: the closure kernel, the renewal and the resolvent

Lean: [`lean/QLF_ClosureKernel.lean`](lean/QLF_ClosureKernel.lean). No axioms in the structural
theorems. `native_decide` is used only for the numerical cross-checks.

**The kernel.** For a seed `s`, a *first closure* of length `k ≥ m` is a continuation `c` with
`s ++ c` balanced and no `s ++ c.take j` balanced for `m ≤ j < k` (`firstFamily`). Its signed sum is
`F_k(s)` (`kernelAmp`). For the vacuum with `m = 1` the first closures are exactly the primes of
[`lean/QLF_FirstReturn.lean`](lean/QLF_FirstReturn.lean), and `K_k = F_k(∅)` is the **prime closure
kernel** (`primeKernel`).

**The factorization.** For every seed `s` and every `m ≤ L`:

```text
closure_factorization :  A_L(s) = Σ_{k=m}^{L} F_k(s) · A_{L−k}(∅)
```

A closing history splits uniquely at its first closure past `m` (`first_exists`, `first_unique`).
What remains is a vacuum closure (`balanced_drop`), and the phase is the product of the two phases
(`phase_split`). This is the Dyson bijection `card_balanced_eq_sum_prime` of `QLF_FirstReturn`, but
for signed amplitudes instead of counts, so cancellation is carried through the split rather than
discarded.

**PZ1b, the renewal.** Take `s = ∅` and `m = 1`:

```text
vacuum_renewal   :  A_L(∅) = Σ_{k=1}^{L} K_k · A_{L−k}(∅)    (L ≥ 1),   A_0(∅) = 1
vacuum_resolvent :  G = 1 + K·G           (formal power series over ℤ)
vacuum_resolvent_inverse :  G·(1 − K) = 1,   i.e.  G = (1 − K)⁻¹
```

This is the signed form of the issue's `U = 1 + A U`. The kernel does not vanish: `K_2 = −8` (the
eight Hermitian pairs, each `−I`) and `K_4 = 56`. The renewal reproduces the registry's
`A_4(∅) = (−8)(−8) + 56 = 120` (`vacuum_amp_four`).

**PZ2 seed, channel factorization.** Take `m = 0`:

```text
channel_factorization :  G_s = F_s · G_∅ = F_s · (1 − K)⁻¹
```

Every channel carries the **same** dressed vacuum factor `(1 − K)⁻¹`. Channels differ only in their
first-closure kernel `F_s`. Under the issue's dictionary, where poles come from `(1 − K)⁻¹` once a
continuum rendering is named, this would make pole positions channel-independent, with only the
residues `F_s` depending on the channel. That is a reading for PZ2 to test, and it has a known gap: a
shared formal denominator does not by itself give shared physical poles, because a channel's numerator
`F_s` can cancel a zero of `1 − K` once both are rendered as functions. Which zeros of `1 − K` survive
in which channel depends on that rendering. The identity itself is the theorem, and it is scalar: the
matrix-valued kernel and factorization of residues at a pole are separate targets (§6).

**Zeros live in the kernel.** Because `A_0(∅) = 1`, the factorization can be inverted order by order.
An amplitude that vanishes at every order therefore has a first-closure kernel that vanishes at every
order (`kernel_zero_of_amplitude_zero`). The all-orders zero of `^<` (§5) is a zero of `F_{^<}`
(`upLeft_kernel_zero`), so it is not produced by the dressing. In the issue's terms the forbidden
transition sits in the irreducible interaction, not in propagation.

All the identities above are checked against direct enumeration of `A_L` and `F_k` for the seeds `∅`,
`^`, `^<`, `^>` and `^^<` up to `L = 5`.

---

## 8. U3: closed plus open channels are complete, and the open channel never empties

Lean: [`lean/QLF_ClosureLeakage.lean`](lean/QLF_ClosureLeakage.lean). No axioms.

The issue warned that [`lean/QLF_PolyaTransience.lean`](lean/QLF_PolyaTransience.lean) rules out
normalizing the closed channels to one, and listed four ways out. This section proves which one the
substrate takes.

**The decomposition.** Every length-`L` history is exactly one of two kinds. It is *closed by `L`*
when it has a first closure, a prime prefix of length `k ≤ L` in the sense of
[`lean/QLF_FirstReturn.lean`](lean/QLF_FirstReturn.lean), and then anything may follow. It is *open*
when no non-empty prefix is balanced (`IsOpen`). The pieces are disjoint and cover every word
(`words_partition`), and each closed piece is a product, prime × free tail (`sum_fiber`).

**U3, the measure.** In the cylinder measure `8^{−|h|}`:

```text
leakage_identity           :  closedMass L + openMass L = 1        for every L
openMass_ge_quarter        :  1/4 ≤ openMass L                       for every L
closed_channels_incomplete :  closedMass L < 1                       for every L
```

`closedMass L = Σ_{k≤L} I_k / 8^k` is the prime Kraft mass heard by `L`, and `openMass L` is the
fraction of length-`L` words with no closed prefix. The first line is the issue's
`S_closed† S_closed + S_open† S_open = I`, read in the measure. The bound comes from
`at_least_quarter_never_closes`: at least a quarter of the possibility space is always in the open
channel, at every capacity.

So of the issue's four resolutions the substrate takes the second: the complete channel space is the
closed channels **plus** the open (escape) channels. Conditioning on closure would divide by a mass of
at most `3/4`, which is an added normalization postulate. Kill condition 1 forbids that, and nothing
here needs it.

**U3b, the amplitude.** Each history is unitary (§1), but the eight twists cancel as a sum,
`Σ_t U(t) = 0` (`sum_twist_matrices`), so the free amplitude over all words of length `L ≥ 1` is zero.
Split by channel, every closed piece that has a free tail vanishes with it, and only the primes of full
length survive:

```text
open_amplitude :  Σ_{open h, |h| = L} U(h) = − Σ_{prime p, |p| = L} U(p)      (L ≥ 1)
```

The right side is `−K_L · I` by the phase rule, with `K_L` the prime kernel of §7. So the amplitude
that has not closed by `L` is exactly balanced by the amplitude that closes for the first time at `L`.
This is the same completeness at the level of amplitudes, and it ties the open channel to the kernel
that generates every closed one.

**What remains of U3.** These are identities on the full possibility space, graded by length. A
channel operator on boundary states, with `S†S = I` on a named finite channel space, still has to be
built. That is the same missing object as the multi-channel `K` of PZ2.

---

## 9. PZ2: every boundary channel factors through the same vacuum

Lean: [`lean/QLF_ClosureChannels.lean`](lean/QLF_ClosureChannels.lean). No axioms.

§7 cut each *seeded* channel at its first closure and gave a scalar kernel. The review of #208 asked
for channels as boundary states and for amplitudes that are matrices. This section gives both.

**Channels are boundary states.** A history's boundary state is its net displacement
`disp h ∈ ℤ⁴`, the signed twist count on each axis. A history closes exactly when that is the origin
(`balanced_iff_disp`). The channel `v` at length `L` is the coherent sum of the actual `2×2` folds:

```text
chanAmp v L = Σ_{|h| = L, disp h = v} U(h)          a matrix, not a sign
```

**The last-exit factorization.** Cut each history at its *last* closure, the longest balanced prefix
(`lastExit`). What comes before is a vacuum closure. What comes after leaves the origin and never
returns, so it is an open history in the sense of §8 (`drop_lastExit_open`). The cut is unique
(`lastExit_append`). So for every channel `v` and every `L`:

```text
channel_last_exit :  chanAmp v L = Σ_{k=0}^{L} G_k · O_{L−k}(v)
vacAmp_eq         :  G_k = A_k(∅) · I
channel_series    :  G(v) = G_∅ · O(v)          (power series over the 2×2 matrices)
origin_channel    :  chanAmp 0 L = G_L          (O(0) = 1: an open history never ends at the origin)
```

Every boundary channel carries the **same** dressing `G_∅`, which is scalar, and channels differ only
in their open amplitude `O(v)`. That amplitude is a genuine matrix: one step up gives
`O_1(e_up) = σy` (`openAmp_up_one`). This is the multi-channel, matrix-valued form of
`channel_factorization` in §7, and it is the last-exit dual of that theorem's first-closure cut.
`G_∅ = (1 − K)⁻¹` there, so `G(v) = (1 − K)⁻¹ · O(v)`.

The caveat of §7 applies unchanged. A shared formal dressing does not by itself give shared physical
poles, because `O(v)` can cancel a zero of `1 − K` once both are rendered as functions.

**Channel zeros.** Some channels vanish at every length. §10 proves which ones and why.

**What remains of PZ2.** The factorization above is a vector over channels. A transfer kernel
`K_{vw}` between two boundary states, residues at a rendered pole, and the RG flow of the kernel are
still open.

---

## 10. Mixed spatial channels vanish at every order

Lean: [`lean/QLF_ChannelZeros.lean`](lean/QLF_ChannelZeros.lean). No axioms.

**The reversal sign.** Two twist matrices anticommute exactly when they lie on different spatial
axes, and otherwise commute (`twist_mul_comm`). Reversing a history therefore costs one sign per
anticommuting pair, and the number of such pairs is fixed by the axis counts alone:

```text
fold_reverse_sign :  U(reverse h) = (−1)^{P(h)} · U(h)
pairs_eq          :  P(h) = c_y c_x + c_y c_z + c_x c_z
```

where `c_a` counts the twists on spatial axis `a`, both signs. Since `U(reverse h) = U(h)†` (§3),
every fold is Hermitian or anti-Hermitian, and which one depends only on the parities of the three
spatial counts. Each `c_a` has the parity of the channel coordinate `v_a`, so the boundary state
decides it.

**The channel zeros.** Call a boundary state *mixed* when `v_y v_x + v_y v_z + v_x v_z` is odd, that
is, when it is odd on two or three spatial axes. Every history in a mixed channel folds to an
anti-Hermitian matrix (`fold_antiHermitian_of_mixed`). Reversal maps the channel to itself, so the
channel cancels in pairs:

```text
mixed_channel_zero :  chanAmp v L = 0      for every L, when v is mixed
mixed_open_zero    :  O_n(v) = 0           for every n, when v is mixed
```

The second line follows from the first through the last-exit factorization of §9 and `G_0 = 1`. The
zero is carried by the channel's own open amplitude, not by the vacuum dressing that every channel
shares. This is the channel form of §5's `antiHermitian_seed_forbidden`, with the same mechanism, and
it confirms the enumeration to `L = 5` that first showed these zeros. A channel odd on one spatial
axis is Hermitian and does not cancel this way: `O_1(e_up) = σy` (§9).

**What this means.** The rule is a selection rule on boundary states: a history can never end in a
mixed channel with non-zero coherent amplitude, at any length, although many histories reach it. In
§4's terms it is an interference zero, not a structural one. The physical reading of a mixed channel
is not settled here.

**Open equals first arrival.** Reversal does one more thing. Read backwards, a history that leaves
the origin and never returns becomes a history that reaches its endpoint `v` for the first time at
its last step, in the same channel (`reverse_mem_firstSet`). The reversal sign is `+1` outside the
mixed channels (`pairs_odd_iff`), and inside them both sides vanish, so

```text
openAmp_eq_firstAmp :  O_n(v) = F_n(v)                         for every v and n
channel_two_sided   :  G(v) = G_∅ · F(v) = F(v) · G_∅
```

The amplitude to leave the origin for good equals the amplitude to arrive at `v` for the first time.
So the shared vacuum dressing can be put before the channel's kernel or after it, and the kernel is
the same. This is the scalar-dressing case of a two-sided transfer kernel. A kernel `K_{vw}` that is
not translation invariant, as a background or a boundary would make it, is still open.

## 11. The light-cone boundary: zeros are exactly the mixed channels

Take three spatial axes at a fixed time `L` and the shell `|v|₁ = L`: the boundary states reachable
only by stepping outward every time. No continuum is involved; every quantity below is a finite sum
over histories ([`QLF_LightCone`](lean/QLF_LightCone.lean)). For `v = (a, b, c, 0)` with
`a + b + c = L`, the histories are exactly the orderings of `a` ups, `b` lefts and `c` slashes
(`chanAmp_cone`); their number `N(a, b, c)` is the multinomial.

The three spatial twists square to `1` and anticommute pairwise. So in the sum over orderings, two
adjacent different steps cancel against their swap, and two adjacent equal steps fold to `1`
(`cone_two_step`). What survives is the count of walks made of **pairs** of steps:

```text
cone_amplitude :  G_L(a, b, c, 0) = N(⌊a/2⌋, ⌊b/2⌋, ⌊c/2⌋) · σ    at most one of a, b, c odd
                                  = 0                              otherwise
cone_zero_iff  :  G_L(a, b, c, 0) = 0   ⟺   (a, b, c, 0) is mixed
```

where `σ` is the twist of the one odd axis, or `1`. §10 showed that mixed channels vanish at every
length. On the light cone the converse also holds: mixing is the only source of zeros. Checked first
by enumeration with no mismatches through `L = 7`.

**The interference is strong.** For `a = b = c = n` even, the amplitude `N(n/2, n/2, n/2)` is far
below the count `N(n, n, n)`, and also below the random-phase scale `√N(n, n, n)`. The ratio is
0.63, 0.48, 0.36, 0.26, 0.18 at `L = 6, 12, 24, 48, 96`, falling roughly as `L^{−1/2}`. So the
coherent amplitude is concentrated inside the cone, among histories that turn back, and not on the
light cone itself. Whether this has a turbulence reading is not settled here.

**The shell kernel.** From a cone point `v` on shell `s` to a cone point `w` on shell `s + t`, set
`K(v → w)` to the cone amplitude of the outward displacement `w − v`, and `0` when `w` is not
outward of `v`. A cone history crosses each intermediate shell at exactly one point, so the kernel
composes:

```text
coneSum_split       :  splitting the ordered sum at time t, for any weight per twist
shellKernel_compose :  K(0 → w) = Σ_{v on shell t} K(0 → v) · K(v → w)
```

with the 2×2 matrices multiplied in time order. This is a genuine transfer kernel between boundary
states, with an incoming and an outgoing label, and its zeros are read off `cone_amplitude`: for
example `K((1,0,0) → (2,1,1)) = 0` because the displacement `(1,1,1)` is mixed, while
`K((1,0,0) → (3,0,0)) = I`. Inside one octant it is still translation invariant; what breaks
translation invariance is the shell itself, since only outward steps are admitted.

**Normalisation of the shell total.** Summed over every point of the shell, the cone sums give
the `L`-th power of the summed outward step `D = σ_y − σ_x + σ_z` (`shell_total`), and the shell
holds `3^L` histories (`shell_count`). Because the three twists anticommute, `D² = 3` (`outStep_sq`),
so `S = D/√3` is Hermitian and unitary, and

```text
coneStep_unitary    :  S = (σ_y − σ_x + σ_z)/√3  is unitary
shell_total_unitary :  Σ_{v on shell L} G_L(v) = (√3)^L · S^L
```

The coherent total over the shell is exactly `√(number of histories)` times a unitary, so `S` is a
normalised one-step transfer for the whole shell. `S` is the spin-½ operator along the shell's
diagonal, and `S² = I`. This normalises the total only: the individual channels `G_L(v)` are not
normalised by it, and their own unitary normalisation is still open.

**Scope.** The other seven octants differ by reflecting axes, which changes only signs, but Lean
covers the positive octant. Gauge twists are left out by the fixed-time choice. Still open: a
channel-resolved unitary kernel, and kernels that admit inward steps.

## 12. What is realizable is unitary

§11 normalised the shell total, which is the zero-momentum part. Channel by channel the raw sum is
not a time evolution. Give each outward step a momentum phase and sum the three twists: with phase
`i` on the up step, `(iσ_y − σ_x + σ_z)/√3` has Gram entry `5/3`, so it is not unitary
(`rawStep_not_unitary`, [`QLF_RealizableWalk`](lean/QLF_RealizableWalk.lean)). Numerically the
deviation reaches `0.94` over random momenta.

**The realizable part of a step.** A step by twist `t` does zero free action on the spin exactly on
the spin states `t` leaves unchanged, the `+1` eigenspace of `M(t)`. Keep only that part:

```text
fix t = (1 + M(t))/2           the projector onto the states t fixes
```

Since the conjugate twist has `M(t̄) = −M(t)`, the realizable parts of a twist and its conjugate are
complementary projectors:

```text
fix_idem      :  fix t · fix t = fix t
fix_mul_conj  :  fix t · fix t̄ = 0
fix_add_conj  :  fix t + fix t̄ = 1
```

So a step that moves along `t` with phase `e^{ik}` and along `t̄` with `e^{−ik}`, keeping only the
realizable parts, is unitary at every momentum, and so is the walk over the three spatial axes:

```text
realStep_unitary :  e^{ik}·fix t + e^{−ik}·fix t̄   is unitary for every real k
realWalk_unitary :  the up · left · slash walk is unitary for every (k_y, k_x, k_z)
realStep_eq_half :  realizable step = ½(bare displacement + raw twist step)
```

The last line says what is dropped. The raw twist step carries the spin flip that no closure pays
for; the realizable step averages it with the bare displacement, which removes exactly that part.

**What it renders.** The step moves along its axis in the direction of the spin's sign on that axis.
To first order in `k` the walk is `1 + i(k_y σ_y − k_x σ_x + k_z σ_z)`, the Weyl operator of a
massless spin-½ particle. This is now a theorem (`realWalk_generator`, §15); it is a reading of the
finite walk, not a continuum assumption.

**Credit and status.** This walk has the form of the split-step Weyl walk of the quantum-walk
literature: Bialynicki-Birula, *Weyl, Dirac, and Maxwell equations on a lattice as unitary cellular
automata*, Phys. Rev. D 49 (1994) 6920; Arrighi, Nesme and Forets, *The Dirac equation as a quantum
walk: higher dimensions, observational convergence* (2014, arXiv:1307.3524); and the
information-theoretic derivation of D'Ariano and Perinotti, *Derivation of the Dirac equation from
principles of information processing* (2014, arXiv:1306.1934). There the
spin-locked step is a postulate or a design choice. Here it is read off zero free action per step:
a step is realizable only on the spin states it leaves unchanged. Whether that reading is forced, or
is one choice among several, is the question to settle next. The order of the three axes is a
convention, and different orders agree to first order in `k`.

Still open: mass (a Dirac rather than Weyl walk), the gauge axis, and the inward steps of the full
census.

## 13. Composite systems: Bell violation is the twist Clifford relation

Two sites each choose one of two two-outcome observables (each squares to `1`), and observables at
different sites commute. The CHSH combination (Clauser, Horne, Shimony and Holt, Phys. Rev. Lett. 23
(1969) 880) is `C = a₀b₀ + a₀b₁ + a₁b₀ − a₁b₁`. In **any** ring, with nothing else assumed
([`QLF_Tsirelson`](lean/QLF_Tsirelson.lean)):

```text
chsh_sq        :  C² = 4 − [a₀, a₁]·[b₀, b₁]
chsh_classical :  a₀a₁ = a₁a₀            ⟹  C² = 4               (|C| ≤ 2, Bell)
chsh_tsirelson :  a₀a₁ = −a₁a₀, b₀b₁ = −b₁b₀  ⟹  C²(C² − 8) = 0  (spectrum in {0, ±2√2})
```

So the whole gap between Bell's bound and Tsirelson's (Cirel'son, Lett. Math. Phys. 4 (1980) 93)
is whether a site's two observables commute. Commuting observables can be given joint values, and
then the bound is 2. Anticommuting ones cannot, and then the spectrum is `{0, ±2√2}`. **Scope:** this
is the maximal, exactly anticommuting case. Observables that fail to commute without anticommuting
give intermediate values; the general bound for arbitrary Hermitian `±1` observables is §26.

**Twists supply exactly that.** Twists on different spatial axes anticommute, the same Clifford
relation that makes the light-cone zeros exact (§11). With `up` and `left` on each of two sites:

```text
twist_bell_pair      :  each squares to 1, the sites commute
twistChsh_herm       :  the CHSH operator is Hermitian
twistChsh_tsirelson  :  C²(C² − 8) = 0
twistChsh_sq_e00     :  C²|00⟩ = 8|00⟩         (|00⟩ itself has CHSH expectation 0)
twistChsh_saturates  :  v = C|00⟩ + 2√2|00⟩ ≠ 0  and  Cv = 2√2 · v      2√2 is attained by a state
```

The reading: two measurements on one site that cannot share a value are two twists on different
axes, and that non-commutation is the entire quantum excess over a local joint assignment. Nothing
here is new as mathematics; the CHSH square identity is standard. What QLF adds is where the
anticommutation comes from: the eight twists are the signed axis frame, so a second axis is a second
measurement that cannot share the first one's value.

**Scope.** This is the algebraic bound and its attainment by an eigenvector of `C²`. It does not
yet say which census quantity is the state `ψ`, nor derive the probabilities `⟨ψ|C|ψ⟩` from the census (the
Born rule's form is now derived from counting ways, §16). It also does not yet build the
two-site state from a joint closure (entanglement as a shared closure, [`MultiParticle.md`](MultiParticle.md)).

## 14. Mass is what flips handedness

The realizable walk of §12 renders a massless particle. Its generator is momentum along the three
spatial twists, and by the Clifford relations it squares to the momentum squared
([`QLF_Mass`](lean/QLF_Mass.lean)):

```text
weyl_sq       :  (k_y·up + k_x·left + k_z·slash)² = |k|²           E² = p²
no_weyl_mass  :  X anticommutes with up, left, slash  ⟹  X = 0
```

A mass term has to anticommute with every momentum direction, so `no_weyl_mass` says **no mass fits
on two components**: the three spatial twists use up the 2×2 Clifford algebra. A mass needs a
second factor, and the natural one is **handedness**, which [`QLF_Handedness`](lean/QLF_Handedness.lean)
already takes as the primitive. On spin ⊗ handedness, with twists on both factors:

```text
alpha t   = slash ⊗ t        momentum along twist t, labelled by handedness
beta      = right ⊗ 1        the mass generator
chirality = slash ⊗ 1        the handedness label

dirac_sq             :  (k_y α_y + k_x α_x + k_z α_z + m β)² = k² + m²     E² = p² + m², exactly
chirality_comm_dirac :  [chirality, D] = 2m · chirality · β
massless_keeps_handedness :  [chirality, D] = 0 when m = 0
massStep_unitary     :  cos m + i sin m · β  is unitary for every real m
```

So momentum keeps handedness and mass flips it. A massive particle is one whose history keeps
switching handedness, and the rate of switching is the mass. That is Feynman's checkerboard reading
of the Dirac equation (Feynman and Hibbs, *Quantum Mechanics and Path Integrals*, 1965), and it
matches [`Inertia.md`](Inertia.md)'s rest mass as a closed null circulation: every step runs at `c`,
and only the zigzag between handednesses keeps the particle in place on average.

**Credit and status.** The algebra is the chiral (Weyl) representation of the Dirac matrices,
standard physics. What QLF supplies is that every generator is a twist, and that the second factor is
the handedness the framework already has. The full Dirac walk is assembled in §15. Still open:
whether the handedness factor is forced, or one choice of second factor among several.

## 15. The walks generate the Weyl and Dirac operators

A unitary step `W(k)` at momentum `k` has a **generator**, its derivative at `k = 0`, so that for
small momenta `W(k) ≈ 1 + i·H(k)`. The generators are computed exactly in
[`QLF_DiracWalk`](lean/QLF_DiracWalk.lean):

```text
realStep_generator  :  d/ds realStep t (s·a) |₀ = i·a·M(t)            a step generates its twist
realWalk_generator  :  d/ds realWalk (s·a)   |₀ = i·(a_y up + a_x left + a_z slash)      Weyl
```

The Dirac walk is assembled from pieces already proved unitary. The handedness label of §14 splits
the walk: the right-handed part walks at `k`, the left-handed part at `−k`, and the mass step mixes
them.

```text
handed k        = fix slash ⊗ W(k) + fix slash̄ ⊗ W(−k)       handed_unitary
diracWalk k m   = massStep m · handed k                        diracWalk_unitary
diracWalk_generator :  d/ds diracWalk (s·a) (s·m) |₀ = i·(a_y α_y + a_x α_x + a_z α_z + m β)
```

That generator is the Dirac operator of §14, whose square is `a² + m²` (`dirac_sq`). So the walk
is unitary at every step, and what it generates is exactly the Dirac operator: the Dirac equation
is the small-momentum reading of a finite unitary walk of realizable twist steps. The derivative in
the momentum label is the only continuum notion used; it reads off the generator of a finite step
and assumes nothing about space.

**Credit and status.** Dirac quantum walks with this structure are known (Bialynicki-Birula 1994;
Arrighi, Nesme and Forets 2014; D'Ariano and Perinotti 2014). What QLF supplies is the derivation of
each piece: unitarity from realizability (§12), the second factor as handedness (§14), and every
generator a twist. Still open: a convergence theorem for long walks (the generator is first order
only), and the gauge axis (now §17).


## 16. The Born rule is the count of equal ways

The measurement postulate was the largest piece still taken as given. It is now a theorem about
counting ([`QLF_BornFromWays`](lean/QLF_BornFromWays.lean)). An outcome register is a list of
Gaussian-integer amplitudes `ψ`, as in [`The_QLF_State_Space.md`](The_QLF_State_Space.md). A
probability assignment `P` is asked to obey three rules:

* **Relabeling.** Renaming the outcomes renames the probabilities; no outcome is privileged by its label.
* **Normalization.** The probabilities sum to one.
* **Adding over ways.** An outcome of norm `m` is `m` unit ways. Once a record tells the ways apart,
  the outcome splits into `m` orthogonal unit outcomes, and its probability is the sum of theirs.

The third rule takes the norm as its input, and the norm is not a probability rule. It is unitarity's
Pythagoras (an orthogonal sum's squared length is the sum of the squared lengths) together with
`pairCount = ways` from [`QLF_BornCounting`](lean/QLF_BornCounting.lean).

```text
uniform             :  on the all-ones register every way has probability 1/N
exists_refinement   :  every register refines into Σ‖ψⱼ‖² unit ways, ‖ψᵢ‖² of them for outcome i
born_from_ways      :  P ψ i = ‖ψᵢ‖² / Σⱼ ‖ψⱼ‖²                 for every admissible P
bornAssignment      :  the Born rule obeys all three rules
assignment_unique   :  any two admissible assignments agree
two_thirds          :  the register (1+i, 1) gives 2/3 : 1/3, never √2 : 1
```

The proof is counting. Refine every outcome into unit ways, and the register becomes `N` equal ways.
Relabeling symmetry makes them equally likely, so each has probability `1/N`, and outcome `i` owns
`‖ψᵢ‖²` of them. This is the QLF reading made exact: a probability is a count of ways, and the square
is there because a way is a closed ket–bra pair.

**R6a check.** The rules are satisfiable (`bornAssignment`) and pin `P` completely
(`assignment_unique`). So they are neither empty nor free; they exclude the modulus rule and every
`|ψ|^q` with `q ≠ 2`.

**What this is, and what it assumes.** It is a finite *uniqueness characterization under refinement
additivity*: given the three rules, the Born rule is the only assignment. The third rule is a
premise. `exists_refinement` constructs the unit-way partition mathematically; it does not show that
QLF dynamics carries out an amplitude-preserving refinement physically, and no theorem here does.
So the result says what probability must be *if* probability adds over refined ways, not yet that
the substrate refines.

**Credit and status.** The strategy follows Zurek's envariance argument (*Phys. Rev. A* **71**,
052105 (2005)) and Deutsch's decision-theoretic derivation (*Proc. R. Soc. A* **455**, 3129 (1999)),
but it is not a formalization of envariance: there is no system–environment entanglement and no
swap symmetry here, only relabeling symmetry on the equal-weight register plus the refinement
premise. Zurek's version needs a continuity step to reach irrational weights. This one needs none,
because its amplitudes are Gaussian integers: every Born weight is a ratio of whole counts, so the
rational case is the only case. No continuum enters. Still open, as before: why nature's weight has
no third-order interference ([`Interference_NoGo.md`](Interference_NoGo.md) §6, the three-slit
bound), and which census quantity is the register `ψ`.

## 17. The gauge axis is the clock, and the generator's zeros are on the mass shell

The walks of §12–§15 used the three spatial axes and left the gauge axis out. Put it back and it turns
out to have one job ([`QLF_GaugeAxis`](lean/QLF_GaugeAxis.lean)). The gauge twists `+` and `−` map to
`1` and `−1`, so the realizable part of `+` is the whole space and of `−` is nothing. A gauge step has
no spin direction to choose, and its realizable step is a pure phase:

```text
fix_plus, fix_minus     :  fix + = 1,  fix − = 0
gaugeStep_eq            :  realStep + ω = e^{iω} · 1            a clock tick
gaugeStep_central       :  it commutes with every step
spacetimeWalk_unitary   :  tick ω · diracWalk k m is unitary
spacetimeWalk_generator :  its generator is i(ω + k·α + mβ)
mass_shell              :  (ω + k·α + mβ) ψ = 0,  ψ ≠ 0   ⟹   ω² = k² + m²
light_cone              :  (ω + k·σ) ψ = 0,  ψ ≠ 0         ⟹   ω² = k²
```

The reading. `mass_shell` is a conditional spectral identity: a non-zero state annihilated by
`ω + k·α + mβ` satisfies `ω² = k² + m²`, and without mass `light_cone` gives `ω² = k²`. The shell is
not put in by hand; it comes from the Clifford square `dirac_sq` and nothing else. **The link to
closure is a proposed identification, not a theorem:** such a state's tick exactly cancels its
spatial phase, so it has zero net phase per step, which we read as zero free action. That a QLF ZFA
or first-return closure *implies* the annihilation condition is not proved here. The gauge axis carries the frequency because it is
the only axis with no spin direction, which fits the QLF reading of time as the rate of closure
([`Philosophy.md`](Philosophy.md)).

**Credit and scope.** That a stationary solution of the Dirac equation lies on the mass shell is
standard; what is new is where each piece comes from. Here `ω` is a frequency label, as `k` is a
momentum label, and the derivative in those labels is the only continuum notion used. The gauge
phase is a global phase, so this section does not yet tell energy apart from an electromagnetic
gauge phase; that needs the phase to vary from place to place (§18). Open: a
convergence theorem for long walks.

## 18. A local phase needs a link field, and the flux is what it carries

§17 left the gauge phase global, the same everywhere, so it could not tell a clock tick from an
electromagnetic phase. [`QLF_LocalGauge`](lean/QLF_LocalGauge.lean) lets it vary from place to place.
The walk lives on a ring of `N` sites (`ZMod N`, finite). One step moves the part a twist leaves
unchanged one site forward and the conjugate part one site back, and each hop picks up the phase
`a(x)` on the link it crosses.

```text
ringWalk_norm           :  Σₓ ‖(W_a ψ)(x)‖² = Σₓ ‖ψ(x)‖²        unitary, for every link field a
ringWalk_covariant      :  W_{a'} (e^{iθ} ψ) = e^{iθ} (W_a ψ)     a'(x) = a(x) + θ(x+1) − θ(x)
global_phase_trivial    :  constant θ shifts no link
flux_invariant          :  Σₓ a'(x) = Σₓ a(x)
gauge_equiv_of_flux_eq  :  equal flux  ⟹  related by a local phase change
```

The reading. A phase that varies by site is consistent with the walk only if the links absorb the
difference across each hop. So a local phase brings a link field with it, and a global phase (§17's
clock tick) is the one case that needs none; that is how energy and an electromagnetic phase come
apart. And the links carry exactly one gauge-invariant number on a ring: the total phase around it.
Two link fields with the same flux are the same up to a local phase change, so the flux is the whole
physical content. That is the Aharonov–Bohm phase (*Phys. Rev.* **115**, 485 (1959)).

**Credit and scope.** The gauge principle is Weyl's (*Z. Phys.* **56**, 330 (1929)), and link phases
with their holonomies are Wilson's lattice form (*Phys. Rev. D* **10**, 2445 (1974)). What QLF adds is
where the pieces come from: each hop is a realizable twist step (§12), and the phase on it is the
gauge axis (§17). The ring is one-dimensional, so its only loop is the ring itself; plaquettes
and field strength are §19.

## 19. Plaquettes, field strength and the Bianchi identity

The ring of §18 has one loop. [`QLF_LatticeGauge`](lean/QLF_LatticeGauge.lean) puts the walk on any
finite lattice of sites (any finite abelian group, such as the 3-torus `ZMod N × ZMod N × ZMod N`),
with a phase on every link along every axis. The smallest loops are now the plaquettes.

```text
axisStep_norm, twoAxis_norm      :  a step along any axis, and any product of them, is unitary
axisStep_covariant               :  W_{e, a'} (e^{iθ} ψ) = e^{iθ} (W_{e, a} ψ),  a'(x) = a(x) + θ(x+e) − θ(x)
plaquette                        :  F_ef(x) = a_e(x) + a_f(x+e) − a_e(x+f) − a_f(x)
plaquette_invariant              :  every local phase change leaves every F unchanged
pure_gauge_no_field              :  a link field that is only a phase change has F = 0
plaquette_antisymm               :  F_fe = −F_ef
bianchi                          :  Δ_e F_fg + Δ_f F_ge + Δ_g F_ef = 0          on every cube
total_plaquette_zero             :  Σₓ F_ef(x) = 0                                on a closed lattice
```

The reading. The phase around a plaquette is the field strength. It is what survives every local
phase change, and a link field that is only a phase change carries none. On every cube the six
oriented faces cancel (`bianchi`): that is the discrete `dF = 0`, the source-free half of Maxwell's
equations, which says there are no magnetic monopoles and gives Faraday's law. It is an identity of
the links, not a law put in. On a closed lattice the total flux through any plane is zero.

The substrate already carries one such link field: the fold sign is the ℤ₂ edge-sign connection of
[`QLF_EdgeSign`](lean/QLF_EdgeSign.lean), with flux `π` through every mixed spatial plaquette. So the
twist algebra comes with a fixed background field, and a gauge phase on the gauge axis adds to it.

**Credit and scope.** Link phases, plaquettes and the lattice Bianchi identity are Wilson's lattice
gauge theory (*Phys. Rev. D* **10**, 2445 (1974)). What QLF adds is the hop and the phase. Not here:
the other half of Maxwell's equations (Gauss and Ampère; §20 shows Gauss's law is kept by the walk's
conserved current), a dynamics for the links, and non-abelian link fields.

## 20. The walk carries a conserved current, and that is what Gauss's law needs

§19 gave the source-free half of Maxwell's equations. The other half couples the field to charge:
Gauss's law `div E = ρ`, and the Ampère–Maxwell update `E' = E + curl B − J`.
[`QLF_Maxwell`](lean/QLF_Maxwell.lean) shows what QLF supplies for it and what it does not.

```text
continuity               :  ρ'(x) − ρ(x) + J(x) − J(x − e) = 0          every site, every link field
current_invariant        :  J is unchanged by a local phase change
div_curl                 :  div (curl B) = 0                              for any oriented plaquette field
gauss_preserved          :  div E = ρ  and continuity   ⟹   div E' = ρ'   after E' = E + curl B − J
gauss_preserved_by_walk  :  the same, with ρ and J the walk's own charge and current
```

Here `ρ(x) = ‖ψ(x)‖²` and `J(x)` is what a step carries across the link from `x` to `x + e`: the
forward part leaving `x` minus the backward part arriving from `x + e`. The reading. Unitarity of a
realizable step is not only global: it holds site by site, as a continuity equation with a gauge
invariant current. That is exactly what Gauss's law needs. Since `div curl = 0`, an Ampère–Maxwell
update keeps `div E = ρ` true precisely when charge is conserved, and the walk's charge is.

**Credit and scope.** Lattice continuity and the compatibility of Gauss's law with charge conservation
are standard; Maxwell's displacement current exists to make them agree, and on a lattice this is Yee's
scheme (*IEEE Trans. Antennas Propag.* **14**, 302 (1966)). What QLF supplies is the conserved current,
from the realizability of each step. What is **not** derived is the update `E' = E + curl B − J`
itself, which is taken as the form here and derived from a finite action in §21 (static) and §22
(with time). Reading the walk's norm density as electric charge is also a reading, not a theorem.

## 21. A finite action for the links, and Ampère's law as its stationarity

§20 took the Ampère–Maxwell update as given. [`QLF_LinkAction`](lean/QLF_LinkAction.lean) derives the
static Ampère law from a finite action for the link phases. With `F` the plaquette field of §19 and
`J` a current on the links,

```text
S[a] = ¼ Σₓ Σᵢ Σⱼ F_ij(x)² − Σₓ Σᵢ J_i(x) a_i(x)

first_variation                 :  (S[a + εδ_{k,y}] − S[a − εδ_{k,y}]) / 2ε = (curl F)_k(y) − J_k(y)   every ε ≠ 0
stationary_iff_ampere           :  S stationary under every link variation  ⟺  curl F = J
stationary_conserves_current    :  curl F = J  ⟹  div J = 0
action_gauge_shift              :  S[a + Δθ] = S[a] + Σₓ θ(x) · div J(x)
gauge_invariant_iff_conserved   :  S gauge invariant for every θ  ⟺  div J = 0
```

The reading. The action is quadratic, so its symmetric finite difference *is* its first variation:
no derivative and no limit are needed, and the static Ampère law is exactly the condition that no
single link can lower or raise it to first order. The current must then be conserved, and a
conserved current is also exactly what makes the coupling gauge invariant: Noether's link between
the gauge symmetry of §18 and the continuity equation of §20, here as a finite identity.

This is a worked instance, in the link sector, of the bridge contract in
[`Stationary_Action.md`](Stationary_Action.md): an explicit action, explicit admissible variations
(one link at a time), and an exact first-variation identity. It does not settle that bridge, which
is about the substrate's own closure condition and gravity.

**Credit and scope.** This is the standard non-compact (weak-coupling) Wilson action, whose
Euler–Lagrange equations are the lattice Maxwell equations, and the gauge/conservation link is
Noether's (1918). Not included here: the time direction, which §22 adds; the walk's own action
coupled to the links; and the compact (cosine) action.

## 22. Time: the Ampère–Maxwell update as the stationarity of a finite history

[`QLF_MaxwellTime`](lean/QLF_MaxwellTime.lean) adds time to §21 and derives the update that §20 took
as its form. A history is a link field `A_τ` at every time `τ` on a finite cycle `ZMod N` (a history
that closes on itself, so there are no boundary terms), with no phase on the time links (temporal
gauge). The electric field lives on the time link, `E_τ = −(A_{τ+1} − A_τ)`, and

```text
S[A] = ½ Σ_τ Σₓ Σᵢ E_τ,i(x)² − Σ_τ ( ¼ Σ F(A_τ)² − Σ J_τ · A_τ )

first_variation        :  (S[A + εδ_{σ,k,y}] − S[A − εδ_{σ,k,y}]) / 2ε
                            = (E_σ − E_{σ−1})_k(y) − ((curl F(A_σ))_k(y) − J_σ,k(y))     every ε ≠ 0
stationary_iff_update  :  S stationary under every variation  ⟺  E_σ = E_{σ−1} + curl F(A_σ) − J_σ
gauss_from_action      :  div E_{σ−1} = ρ, ρ' − ρ + div J_σ = 0, stationary  ⟹  div E_σ = ρ'
```

The reading. The update `E' = E + curl B − J` of §20 is no longer an assumption: it is the condition
that no single link at any single time can change the history's action to first order, and the
action is again quadratic, so that condition is a finite identity. Together with §20 this closes
the loop for the source half: the walk supplies a conserved current, the action supplies the update,
and the update keeps Gauss's law.

**Credit and scope.** The discrete-time lattice Maxwell action and its leapfrog equations are
standard (Yee 1966, *IEEE Trans. Antennas Propag.* **14**, 302; Kogut and Susskind 1975, *Phys. Rev.
D* **11**, 395, for the Hamiltonian lattice form). Gauss's law itself is the equation of the
time-link phase; in temporal gauge it is a constraint that the update keeps, not one the variation
produces (§23 derives it). Not included: the walk's own action coupled to the links, and compact or
non-abelian links.

## 23. Gauss's law is the equation of the time-link phase

[`QLF_GaussLaw`](lean/QLF_GaussLaw.lean) puts a phase `φ_τ(x)` on the time links that §22 left
bare. The electric field becomes the time–space plaquette, `E = −Δ_t A − ∇φ`, and the charge couples
to it:

```text
E_τ,i(x) = −(A_{τ+1,i}(x) − A_τ,i(x)) − (φ_τ(x + e_i) − φ_τ(x))
S[A, φ]  = ½ Σ E² − Σ_τ S_link[A_τ] − Σ_τ Σₓ ρ_τ(x) φ_τ(x)

gauss_variation                 :  (S[φ + εδ_{σ,y}] − S[φ − εδ_{σ,y}]) / 2ε = div E_σ(y) − ρ_σ(y)   every ε ≠ 0
stationary_iff_gauss            :  stationary under every time-link variation  ⟺  div E = ρ
stationary_iff_ampere           :  stationary under every space-link variation ⟺  E_σ = E_{σ−1} + curl F − J_σ
stationary_forces_continuity    :  both  ⟹  ρ_σ − ρ_{σ−1} + div J_σ = 0
gauge_invariant_iff_continuity  :  S invariant under every spacetime phase θ  ⟺  ρ_σ − ρ_{σ−1} + div J_σ = 0
```

The reading. Each kind of link has its own equation: the space links give Ampère–Maxwell and the
time links give Gauss. Neither is put in. The two are compatible only if charge is conserved, and
the same condition is what makes the coupling gauge invariant. This is the condition the walk
already satisfies, site by site, from the realizability of each step (§20, `continuity`). So the
whole set of lattice Maxwell equations, both halves, now rests on finite identities: Bianchi (§19)
from the links alone, Gauss and Ampère–Maxwell from one finite action, and the source's
conservation from the walk.

**Credit and scope.** `E = −∂_t A − ∇φ` and Gauss's law as the `φ` equation are Maxwell's; the
lattice form is standard (Kogut and Susskind 1975). Not included: the walk's own action coupled to
the links (here `ρ`, `J` are given, and the walk is shown to supply ones that qualify; §24 takes
the next step), and compact or non-abelian links.

## 24. The walk's current is its response to a link phase

[`QLF_WalkCoupling`](lean/QLF_WalkCoupling.lean) looks at the coupling from the walk's side. Take one
realizable step along axis `e` with link phases `a` and move the phase of the single link `y` by `ε`.
Only two hops cross that link: the forward part `fix t ψ(y)` and the backward part
`fix t̄ ψ(y + e)`. Because the realizable parts are orthogonal, they pick up their phases without
interfering:

```text
link_overlap   :  ⟨U_a ψ, U_{a+εδ_y} ψ⟩ = Σₓ ‖ψ(x)‖² + (e^{iε} − 1)·‖fix t ψ(y)‖² + (e^{−iε} − 1)·‖fix t̄ ψ(y+e)‖²
link_response  :  ⟨U_a ψ, U_{a+εδ_y} ψ⟩ − ⟨U_a ψ, U_{a−εδ_y} ψ⟩ = (e^{iε} − e^{−iε}) · J(y)        every ε
```

The reading. The current `J(y)` of §20 (forward minus backward across the link) is exactly the odd
part of the walk's response to its own link phase: the lattice form of `J = δS_matter/δa`, with no
derivative taken. So the walk is a source of the right kind twice over: it is what the link phase
couples to (this section), and it is conserved (§20), which is what gauge invariance of the link
action demands (§23).

**Credit and scope.** Current as the response to a gauge field is standard in lattice gauge theory
(Wilson 1974; Kogut and Susskind 1975), and gauge-coupled quantum walks with their conserved
currents are studied by Arnault and Debbasch (arXiv:1508.00038) and Márquez-Martín, Arnault,
Di Molfetta and Pérez (*Phys. Rev. A* **98**, 032333 (2018)). Not included: one action whose
stationarity gives the walk and the field together (the walk is a unitary step, not a stationary
point), and compact or non-abelian links. Back-reaction over many steps is §25.

## 25. The walk and the links evolve together

[`QLF_CoupledEvolution`](lean/QLF_CoupledEvolution.lean) lets the two act on each other. A state is a
walk `ψ`, link phases `A` and an electric field `E`. One coupled step along axis `k` with twist `t`:

```text
ψ' = U_{A_k} ψ                       the walk moves on the current links
E' = E + τ curl F(A) − J(ψ)          the field is pushed by the walk's own current
A' = A − τE'                         so τE' = −(A' − A), the time-link field  (step_elec)

gauss_neutral          :  div E = ‖ψ‖² − b  ⟹  Σ‖ψ‖² = Σ b           (a closed lattice forces neutrality)
no_background_no_walk  :  div E = ‖ψ‖²  ⟹  ψ = 0                     (so a background is needed)
exists_nonzero_admissible :  a non-zero walk with E = 0 against its own charge as background
evolve_gauss      :  div E = ‖ψ‖² − b at the start  ⟹  at every step, for every schedule of axes and twists
evolve_norm       :  Σ‖ψ‖² is the same at every step, whatever the links have become
evolve_covariant  :  (ψ, A) ↦ (e^{iθ}ψ, A + ∇θ) commutes with the whole coupled history
```

Why the background. On a closed lattice every divergence sums to zero, and the walk's charge
`‖ψ‖²` is non-negative, so `div E = ‖ψ‖²` alone admits only the empty walk (`no_background_no_walk`;
pointed out by Aria in review). A static background `b`, the lattice's fixed ions, makes the total
charge neutral, and then every walk is admissible (`evolve_gauss_neutral` starts from any `ψ`).

The reading. The links the walk sees at step `m + 1` already carry the current it made at step `m`,
so this is genuine back-reaction, not a walk on a fixed background. Nothing breaks: the walk stays
unitary because each step is realizable for *any* links (§19), Gauss's law survives because the
walk's current is conserved site by site (§20) and the update is the one the action selects (§22),
and the whole history is gauge covariant because the step, the current and the plaquette field each
are. These are three separate finite facts, and each is used exactly once.

**Credit and scope.** Self-consistent evolution of charged matter with a dynamical lattice gauge
field is Kogut–Susskind Hamiltonian lattice gauge theory (1975), and as a leapfrog scheme Yee's
(1966). Not included: a dynamical background (a second species), conservation of a total coupled energy (the field's side is §27), compact links, non-abelian links. The
field is real and the current enters through its real part (it is `‖·‖²`-valued, carried in `ℂ`).

## 26. Tsirelson's bound for every pair of observables

§13 settled the maximal case. [`QLF_TsirelsonBound`](lean/QLF_TsirelsonBound.lean) proves the bound
for observables that need not anticommute. With two-outcome observables (each squares to `1`), the
sites commuting and `s² = 2`, in any `ℂ`-algebra:

```text
chsh_sos            :  (s a₀ − b₀ − b₁)² + (s a₁ − b₀ + b₁)² = 8 − 2s · C
tsirelson_bound     :  Re⟨v, C v⟩ ≤ 2√2 ⟨v, v⟩         every state, every Hermitian ±1 observables
tsirelson_bound_neg :  −2√2 ⟨v, v⟩ ≤ Re⟨v, C v⟩
```

The left side of `chsh_sos` is a sum of two squares of Hermitian matrices, so its expectation is
non-negative, and that is the whole proof: `2√2 ⟨C⟩ ≤ 8`. No commutation or anticommutation within
a site is assumed, so every quantum assignment obeys `|⟨C⟩| ≤ 2√2`, and with `twistChsh_saturates`
(§13) twists on two spatial axes reach it. The certificate is the standard one (it is how the bound
is used in self-testing; Šupić and Bowles, *Quantum* **4**, 337 (2020)); the bound is Cirel'son's
(*Lett. Math. Phys.* **4**, 93 (1980)). Finite matrices of any size, no operator-norm theory, no
axioms.

## 27. The field's energy and the work the walk does on it

[`QLF_FieldEnergy`](lean/QLF_FieldEnergy.lean) finds the energy the leapfrog of §25 conserves. Write
`K A = curl F(A)` and `⟨X, Y⟩ = Σᵢ Σₓ Xᵢ(x) Yᵢ(x)`:

```text
ip_K             :  ⟨B, K A⟩ = ½ Σ F(A)·F(B)                (summation by parts; K is symmetric)
energy_eq        :  H(A, E) = ½|E|² + (τ/2)⟨E, K A⟩ + ¼ΣF²
energy_balance   :  E' = E + τK A − J,  A' = A − τE'   ⟹   H' − H = −⟨J, (E + E')/2⟩
energy_conserved :  J = 0   ⟹   H' = H
step_energy      :  in the coupled evolution, the field loses exactly −⟨J(ψ), (E + E')/2⟩ per step
```

The middle term of `H` is what makes the conservation exact rather than approximate. It is
`½⟨E, E⁺⟩ + ¼ΣF²` with `E⁺ = E + τK A` the next free field, so the electric energy is read across
the time step, as in Yee's staggered scheme. `energy_balance` is Poynting's theorem on the lattice
with no error term: the field gives up exactly the work it does on the current, with the field
taken at the midpoint of the step.

**Credit and scope.** Yee (1966) and Poynting (1884); the Hamiltonian `½ΣE² + ¼ΣF²` is
Kogut–Susskind's. Open: the walk's side. The walk is a unitary step, so its natural energy is a
quasi-energy, and no exact walk energy absorbing `⟨J, Ē⟩` is proved, so a conserved total energy of
the coupled system is still open.

**Stability needs a small field step.** `H` is only an energy if it is positive, and that depends on
the field's time step `τ` (now a parameter of §25's step; Gauss's law, the norm and gauge
covariance hold for every `τ`):

```text
K_sq_le        :  |K A|² ≤ 8n ⟨A, K A⟩                     (each curl component sums n plaquette differences)
energy_lower   :  2nτ² ≤ 1  ⟹  H ≥ ½(1 − 2nτ²)⟨A, K A⟩ ≥ 0
energy_bounds  :  4nτ² ≤ 1  ⟹  ⟨A, K A⟩ ≤ 4H  and  |E|² ≤ 8H
free_stable    :  4nτ² ≤ 1  ⟹  the free field stays below those bounds at every step
```

This is a sufficient Courant–Friedrichs–Lewy condition (*Math. Ann.* **100**, 32 (1928)), not the
sharp one. Computed, not proved: the largest eigenvalue of `K` on a periodic lattice is `4n` (8 for
`n = 2`, 12 for `n = 3`), so the sharp condition is `nτ² < 1`, and with `τ = 1`, the step §25 first
used, a random field grows to `10¹⁵²` in 200 steps for `n = 2`. With `τ = 1/n` it stays bounded.
One reading, not yet a theorem: a walk that moves along one axis per step needs `n` steps to cross
a cell in every direction, so `τ = 1/n` is the field's share of one walk step.

**With the walk switched on, the field still cannot blow up.** The walk's current is bounded by its
charge, and the charge is conserved:

```text
J_sq_le             :  |J(ψ)|² ≤ Q²,   Q = Σ‖ψ‖²       (the two hops across a link carry the charge once)
evolve_sqrt_energy  :  4nτ² ≤ 1  ⟹  √H_m ≤ √H_0 + √2·Q·m
evolve_field_bound  :  4nτ² ≤ 1  ⟹  |E_m|² ≤ 8(√H_0 + √2·Q·m)²
```

From the Poynting balance, Cauchy–Schwarz and `|E|² ≤ 8H`, one step gives
`H' ≤ H + √2·Q(√H + √H')`, which is `√H' ≤ √H + √2·Q`. So the coupled field grows at most
quadratically in the number of steps, never exponentially. A bound that does not grow with time
needs the walk's side of the energy, which is open.

## 28. Compact links: the Wilson action

The walk sees a link phase only through `e^{ia}`, so for the walk `a` and `a + 2π` are the same
link. The quadratic action `¼ΣF²` of §21 does not share that. [`QLF_CompactLinks`](lean/QLF_CompactLinks.lean)
uses Wilson's compact action `W(a) = ½Σ(1 − cos F)` over ordered plaquettes, which does:

```text
wilson_periodic    :  W is unchanged when one link moves by 2π
walk_periodic      :  so is the walk's step
wilson_gauge       :  W is gauge invariant
F_bump_cases       :  (axis steps non-zero)  a link enters each plaquette at most once: F(δ) ∈ {−1, 0, 1}
wilson_variation   :  W(a + εδ) − W(a − εδ) = 2 sin ε · curl(sin F)(k, y)          every ε
walk_response_sin  :  ⟨U_a ψ, U_{a+εδ} ψ⟩ − ⟨U_a ψ, U_{a−εδ} ψ⟩ = 2i sin ε · J(y)  every ε
compact_conserves_current :  curl(sin F) = J  ⟹  div J = 0
compact_gauss_preserved   :  E' = E + τ curl(sin F) − J keeps Gauss's law
```

The quadratic action had an exact first variation because it is quadratic. The compact one is not,
yet its symmetric difference is still exact, because a single link enters each plaquette once and
`cos(F − ε) − cos(F + ε) = 2 sin F sin ε`. The walk responds to the same change with the same factor
`sin ε` (§24's `e^{iε} − e^{−iε}`). So the compact Ampère law `curl(sin F) = J` is where the field's
and the walk's responses balance at every `ε`, with no small-angle step. For small plaquettes
`1 − cos F = F²/2 − …`, and the quadratic theory of §21–§27 is its weak-field form.

**Credit and scope.** Wilson (*Phys. Rev. D* **10**, 2445 (1974)); Kogut–Susskind (1975) for the
Hamiltonian form. Open: the compact field's energy and stability (`sin F` is not linear, so §27's
argument does not carry over as it stands) and non-abelian links.

## 29. Non-abelian links

[`QLF_NonAbelian`](lean/QLF_NonAbelian.lean) lets a link carry a unitary `N × N` matrix instead of a
phase. The matrix acts on a colour index that the twists do not touch: a walk value is a `2 × N`
matrix, spin rows and colour columns, twists on the left and links on the right.

```text
step            :  ψ'(x) = fix t · ψ(x−e) · U(x−e) + fix t̄ · ψ(x+e) · U(x)ᴴ
step_norm       :  Σ tr(ψᴴψ) is conserved for every assignment of unitary links
step_covariant  :  ψ(x) ↦ ψ(x) g(x),  U(x) ↦ g(x)ᴴ U(x) g(x+e)  commutes with the step
holonomy_gauge  :  U_i(x) U_j(x+e_i) U_i(x+e_j)ᴴ U_j(x)ᴴ  ↦  g(x)ᴴ (···) g(x)
wilson_loop_invariant :  its trace is gauge invariant
```

The proof of unitarity is the abelian one with nothing added: the two hops land in orthogonal spin
subspaces (`fix t · fix t̄ = 0`), and a unitary acting on colour does not change a norm. Nothing uses
commutativity of the links, so the step is unitary even when neighbouring links do not commute. Spin
and colour must be separate indices: a link acting on spin would have to commute with `fix t` for
the hops to stay orthogonal. For `N = 1` this is §18–§19.

**Credit and scope.** Yang and Mills (*Phys. Rev.* **96**, 191 (1954)); Wilson (1974) for the lattice
form; non-abelian gauge quantum walks are Arnault, Di Molfetta, Brachet and Debbasch (*Phys. Rev. A*
**94**, 012335 (2016)). Open: the non-abelian Wilson action and its variation (the action is §30),
the non-abelian Gauss law, and which colour group the twists select (the colour structure QLF
proposes, the Weyl qutrit of [`QLF_ColourFlux`](lean/QLF_ColourFlux.lean), is not connected to these
links here).

## 30. The Wilson action for matrix links

[`QLF_NonAbelianAction`](lean/QLF_NonAbelianAction.lean) turns §29's gauge-invariant plaquette trace
into an action. For a unitary holonomy `W`, one identity carries everything:

```text
N − Re tr W  =  ½ tr((W − 1)ᴴ (W − 1))        (half the squared distance of W from 1)

plaq_nonneg, plaq_eq_zero_iff :  each plaquette term is ≥ 0, and = 0 exactly when W = 1
wilson        :  S(U) = ½ Σ_{i,j,x} (N − Re tr W_ij(x))
wilson_gauge  :  S is unchanged by every site-dependent unitary colour rotation
wilson_eq_zero_iff :  S = 0  ⟺  every plaquette holonomy is the identity (flat links)
pure_gauge_action  :  U_k(x) = g(x)ᴴ g(x+e_k)  has S = 0
holonomy_abelian, wilson_abelian :  N = 1, U = e^{ia}  gives W = e^{iF} and S = §28's compact action
```

So the matrix action is bounded below, its minimum is reached exactly on the flat links, and pure
gauge configurations are among them. The `N = 1` case is not a new action: it is §28's term by term.

**Scope.** This is the action, not its dynamics; its variation is §31. Open: an energy and leapfrog
for matrix links, the non-abelian Gauss law, and which colour group the twists select.

## 31. The lattice Yang–Mills equation

[`QLF_NonAbelianField`](lean/QLF_NonAbelianField.lean) varies §30's action. In a plaquette with two
distinct directions a given link appears once, as `U` or as `Uᴴ`, so the action is **affine in each
link** and its variation is exact:

```text
hol_bump        :  U_k(y) → U_k(y) + εD  changes each holonomy by exactly ε · dHol   (needs e_i ≠ 0)
wilsonOff_bump  :  S → S − (ε/2) · force,      force_eq :  force = Re tr(D · M_k(y))
                   M_k(y) = Wilson's staple sum, the three-link products closing each plaquette
stationary_iff  :  Re tr(V X M) = 0 for every anti-Hermitian X   ⟺   M V is Hermitian
yang_mills_iff  :  S unchanged along every tangent direction U_k(y) X of the unitary group
                   ⟺   M_k(y) U_k(y) − (M_k(y) U_k(y))ᴴ = 0
wilson_eq_off   :  for unitary links the diagonal plaquettes contribute nothing
```

The last condition is the lattice Yang–Mills equation at the link: the anti-Hermitian part of the
link times its staple sum vanishes. Here it is the stationarity of a finite action, not an
equation posited for a field. The direction `U X` is tangent to the unitary group at `U`; because
the action is affine in the link, "unchanged to first order" and "unchanged" along this line agree.

**Credit and scope.** Standard lattice gauge theory after Wilson (1974); see Creutz, *Quarks,
Gluons and Lattices* (Cambridge, 1983). Open: a time step and energy for matrix links, the walk's
colour current as a source, the non-abelian Gauss law, and which colour group the twists select.

## 32. The Courant bound

§27 proved the field energy positive for `2nτ² ≤ 1`, from the crude bound `|K A|² ≤ 8n⟨A, K A⟩`.
The largest eigenvalue of `K = curl F` is `4n`, so the right condition is `nτ² ≤ 1`.
[`QLF_Courant`](lean/QLF_Courant.lean) proves it:

```text
swap_diff        :  Σ ∂_a f · ∂_b g = Σ ∂*_b f · ∂*_a g        (summation by parts twice)
weitzenboeck     :  ⟨A, K A⟩ + Σ (div A)² = Σᵢⱼₓ (Aᵢ(x+eⱼ) − Aᵢ(x))²
K_le             :  ⟨A, K A⟩ ≤ 4n |A|²
K_sq_le_sharp    :  |K A|² ≤ 4n ⟨A, K A⟩
energy_lower_sharp :  ½(1 − nτ²)⟨A, K A⟩ ≤ H   and   ½(1 − nτ²)|E|² ≤ H     (every τ)
free_bounded_sharp :  nτ² < 1  ⟹  both fields bounded by 2H₀/(1 − nτ²) for all time
```

The identity is the lattice form of `curl curl = grad div − Δ`: curl energy plus divergence energy
is gradient energy, and gradient energy is at most `4n|A|²` because each squared difference is at
most twice the sum of the two squares. The force bound follows by applying `K_le` to
`A − K A/(4n)`. The constant cannot be improved, because `4n` is attained by the staggered mode
(§27, computed); Lean proves sufficiency, not the eigenvalue. The coupled growth bound of §27 is
still stated under `4nτ² ≤ 1`.

**Credit.** Courant, Friedrichs and Lewy (1928).

## 33. Compact links cannot blow up

The linear field is stable only under the Courant condition (§32); past it the staggered mode grows
exponentially. [`QLF_CompactBound`](lean/QLF_CompactBound.lean) shows that compact links (§28) have
no such threshold. The Wilson force is `curl(sin F)`, and `|sin| ≤ 1` caps it:

```text
force_le :  |curl(sin F)ᵢ(x)| ≤ 2n
E_bound  :  |Jₘ| ≤ j  ⟹  |Eₘ| ≤ |E₀| + m(2n|τ| + j)                     (every τ)
A_bound  :  |Aₘ| ≤ |A₀| + m|τ|(|E₀| + m(2n|τ| + j))                      (every τ)
```

So, for every time step, the electric field grows at most linearly and the link phase at most
quadratically, link by link. The walk's current obeys such a bound, `|J| ≤ Q` (`J_sq_le`, §27).
Compactness, which §28 introduced to make the action periodic, also removes the runaway: a
bounded phase cannot push arbitrarily hard. Open: an exactly conserved energy for the compact
leapfrog (the force is not linear) and bounds uniform in time.

## 34. The optical theorem (U3b)

[`QLF_OpticalTheorem`](lean/QLF_OpticalTheorem.lean) writes a channel matrix as `S = 1 + iT`:

```text
defect_eq        :  SᴴS − 1 = TᴴT + i(T − Tᴴ)                          (any finite channel set)
optical_iff      :  S unitary  ⟺  TᴴT = −i(T − Tᴴ)                      (2 Im T = T†T)
forward_defect   :  Re(SᴴS)ₐₐ − 1 = Σ_c |T_ca|² − 2 Im Tₐₐ
optical_forward  :  S unitary  ⟹  2 Im Tₐₐ = Σ_c |T_ca|²                (sum over intermediate channels)
history_optical, realWalk_optical, coneStep_optical :  every twist history, the realizable walk at
                    every momentum, and the light-cone step satisfy it
raw_optical_defect :  the raw census step violates it:  Σ_c |T_c0|² − 2 Im T₀₀ = 2/3
```

The identity is algebra; what QLF supplies is which channel matrices obey it. Those built from
realizable histories do, because they are unitary (§12, #208). The raw coherent census step
(§12) does not, and the forward defect `2/3` is exactly the norm it creates. So the optical theorem
fails in the same place unitarity does, and for the same reason. The momentum-space walk is one
block of the translation-invariant position-space walk, so the theorem holds block by block; a
statement on the full position-space channel space is open (it goes with U2).

**Credit.** Bohr, Peierls and Placzek (1939), after Feenberg (1932); Cutkosky's cutting rules
(*J. Math. Phys.* **1**, 429 (1960)) are its diagrammatic form.

## 35. The channel category (U2)

[`QLF_ChannelGroupoid`](lean/QLF_ChannelGroupoid.lean) builds the boundary-labeled dagger category
the issue asks for, on the full channel space. An object is a label `v ∈ ℤ⁴`, the signed action
vector (one coordinate per conjugate pair; the position of the closed walk of
[Closure_Walk.md](Closure_Walk.md)). A morphism `v ⟶ w` is a twist history whose signed action
carries `v` to `w`.

```text
act_append, act_dagger, act_eq_zero_iff :  action adds, the dagger negates it, zero ⟺ count balanced
comp_assoc, id_comp, comp_id            :  concatenation is a category, the empty history the identity
dag_dag, dag_comp, dag_id               :  conjugate-and-reverse is a dagger, reversing order
hol_comp, hol_id                        :  the ordered fold is a functor
hol_dag                                 :  hol(h†) = (−1)^|h| hol(h)ᴴ      (a dagger functor up to the centre)
hol_comp_dag                            :  hol(h ≫ h†) = (−1)^|h|           (inverse modulo {±1})
endo_closure                            :  every endomorphism v ⟶ v is a closure, holonomy ±1
kernel_compose :  K_{L₁+L₂}(v, w) = Σ_u K_{L₁}(v, u) K_{L₂}(u, w)      (sum over intermediate channels)
kernel_dagger  :  K_L(w, v) = (−1)^L K_L(v, w)ᴴ
```

So the closures are exactly the endomorphisms, at every label; the dagger sends every history to
one that closes it; and the channel kernel composes over intermediate channels on the whole of
`ℤ⁴`, extending §17's light-cone `shellKernel_compose`. The holonomy image is a groupoid modulo the
centre `{±1}`; the history category itself is not a groupoid, because `h ≫ h†` is a closure, not
the empty history. That distinction is the content: an inverse in QLF is a history that closes,
and closing is an event.

## 36. Poles and factorized residues (PZ2)

The resolvent of a channel matrix `K` is `G(z) = (1 − zK)⁻¹ = Σ zⁿ Kⁿ`, the generating function of
`n`-fold propagation. [`QLF_PoleFactorization`](lean/QLF_PoleFactorization.lean) proves the
finite form of PZ2:

```text
pole_part, regular_part :  K P = P K = λP, P² = P  ⟹  G = P/(1 − zλ) + (1 − P) G (1 − P)
                           (the whole λ-pole is P/(1 − zλ); the rest inverts 1 − zK off P)
residue_through_channels :  P_if = Σ_c P_ic P_cf                  (factorization through channels)
rankOne_projector        :  simple eigenvalue, K r = λr, ℓK = λℓ, ℓ·r = 1  ⟹  P_if = r_i ℓ_f

for a 2 × 2 channel step W with eigenvalues μ₁ ≠ μ₂ (exists_eigs):
resolvent_partial :  (1 − zW)(P₁/(1 − zμ₁) + P₂/(1 − zμ₂)) = 1      (poles at μ₁⁻¹, μ₂⁻¹ only)
proj_idem, proj_det :  each residue is idempotent with determinant 0  (rank one)
eig_unit          :  W unitary  ⟹  |μ| = 1                            (poles on the unit circle)
realWalk_poles    :  so for the realizable walk at every momentum
```

So the residue at a simple pole is the amplitude into the intermediate mode times the amplitude
out of it, `r_i ℓ_f`, and it is idempotent, so it factors through intermediate channels. For the
realizable walk the poles sit on the unit circle, `z = e^{−iω}`, at the walk's dispersion relation:
a pole is a mode that propagates without decaying, the finite form of a particle on shell. The
open part of PZ2 is the analytic rendering: reading `z` as `e^{−iω}` with `ω` the energy, and the
continuum limit of the pole into a Feynman propagator.

**Credit.** Riesz projectors are standard; pole factorization is the analytic S-matrix's (Eden,
Landshoff, Olive and Polkinghorne, *The Analytic S-Matrix*, 1966).

## 37. The three-gluon colour vertex is a colour closure (G1, colour part)

[`QLF_ColourFlux`](lean/QLF_ColourFlux.lean) identified the eight twists with the eight nonzero
vectors of `F₃²` and read a colour line as the Weyl qutrit over that plane.
[`QLF_GluonVertex`](lean/QLF_GluonVertex.lean) builds the qutrit's Weyl operators,
`W(a, b)ᵢⱼ = [i = j + a] ω^{bj}` with `ω = e^{2πi/3}`, and computes the colour factor of the
three-gluon vertex, `V(p, q, r) = tr(W(p)[W(q), W(r)])`:

```text
W_mul              :  W(p) W(q) = ω^{p₂q₁} W(p + q)
trace_W            :  tr W(p) = 3 if p = 0, else 0          (the eight p ≠ 0 span sl(3))
vertex_ne_zero_iff :  V(p, q, r) ≠ 0  ⟺  p + q + r = 0  and  ⟨q, r⟩ ≠ 0
gluon_vertex_iff   :  for twists: colour balanced and on different axes
vertex_axes_distinct : a nonzero vertex uses three different axes
two_gluon_commute  :  two gluons close only as t and t̄, and those commute
vertex_count       :  48 ordered twist triples (8 unordered) carry a nonzero vertex
```

So the colour factor of the three-gluon vertex is a closure condition: the three colour labels
must sum to zero in `F₃²`, the same shape as count balance for twists, and they must not be
collinear, the same shape as "carriers are commutators" (`bracket_iff_distinct_axes`). No closure
of one or two gluons has a nonzero bracket, so the three-gluon vertex is the smallest colour
closure with an amplitude: a prime closure, as G1 asks.

**Scope.** This is the colour part of G1 only. The spin and momentum factor of the vertex (the
Yang–Mills kinematic factor), the identification of this `sl(3)` with physical `su(3)` beyond the
colour factor, and G2's gluing into four-gluon amplitudes are open.

**Credit.** The clock-and-shift basis of `sl(N)` and its sine structure constants are Fairlie,
Fletcher and Zachos's (*Phys. Lett. B* **218**, 203 (1989)).

## 38. Four-gluon colour factors by gluing (G2, colour part)

[`QLF_GluonGluing`](lean/QLF_GluonGluing.lean) glues two of §37's vertices:

```text
comm_eq, comm_eq_zero_iff :  [W(p), W(q)] = (ω^{p₂q₁} − ω^{q₂p₁}) W(p + q),  zero ⟺ ⟨p, q⟩ = 0
chan_ne_zero_iff :  c_s = tr([W(p),W(q)][W(r),W(s)]) ≠ 0  ⟺  p+q+r+s = 0, ⟨p,q⟩ ≠ 0, ⟨r,s⟩ ≠ 0
gluing           :  tr(W(−e) W(e)) · c_s = V(−e, p, q) · V(e, r, s),   e = p + q,   tr(W(−e)W(e)) ≠ 0
jacobi           :  c_s + c_t + c_u = 0
chan_count       :  288 of the 456 colour-balanced twist quadruples have c_s ≠ 0
```

A bracket of two gluons is one gluon labelled by the sum, so the intermediate state of the `s`
channel is forced: `e = p + q`. The four-gluon colour factor is then the product of two
three-gluon vertices divided by the intermediate gluon's norm, which is the colour form of "the
residue factors into lower-point kernels". Where a pair is collinear the channel vanishes
structurally: there is no bracket to glue through, a structural zero in §11's taxonomy. The
Jacobi relation ties the three channels together.

**Scope.** Colour only. The kinematic numerators, and with them the four-gluon amplitude's
residues in the Mandelstam variables (G2b) and its hidden zeros (G2c), are open: hidden zeros
are kinematic, and QLF has no momentum-space vertex yet.

**Credit.** Colour decomposition: Dixon, TASI 1995 (hep-ph/9601359). The relation `c_s + c_t + c_u = 0`
is the colour side of Bern, Carrasco and Johansson's colour–kinematics duality
(*Phys. Rev. D* **78**, 085011 (2008)).

## 39. Resonance poles: the decay rate is the leakage

[`QLF_Resonance`](lean/QLF_Resonance.lean) does Phase D's resonance demonstration. Take a unitary
step `U` on a finite channel space and a closed sector, a Hermitian projector `P`. Inside the
sector the step is `K = P U P`, and by §36 its resolvent's poles sit at `z = 1/μ` for the
eigenvalues `μ` of `K`.

```text
norm_unitary, norm_split :  ‖U w‖ = ‖w‖,   ‖w‖² = ‖P w‖² + ‖(1 − P) w‖²
resonance_balance        :  K v = μ v, v in the sector  ⟹  |μ|²‖v‖² + ‖(1 − P) U v‖² = ‖v‖²
resonance_le_one         :  |μ| ≤ 1                       (poles on or outside the unit circle)
stable_iff_no_leak       :  |μ| = 1  ⟺  (1 − P) U v = 0
```

A mode keeps `|μ|²` of its norm each step and leaks the rest out of the sector: this is #208's
leakage identity (U3) for one mode. A mode that does not leak has its pole on the unit circle,
on shell and stable, like the realizable walk's poles (§36). A mode that leaks has its pole
pushed off the circle: a resonance with survival `|μ|²` per step and width `Γ = −log|μ|²`.
Resonances are closures that leak.

**Credit.** Gamow (1928), Weisskopf and Wigner (1930); the projection picture is Feshbach's
(*Ann. Phys.* **5**, 357 (1958)).

## 40. The joint closure is the singlet, and it saturates Tsirelson

§13 proved the CHSH bound `|⟨C⟩| ≤ 2√2` for every state and found one state of a twist pair that
reaches it. [`QLF_JointClosure`](lean/QLF_JointClosure.lean) says which state that is, and why. Call
a two-site state a **joint closure** when the two sites' actions cancel on every axis,
`(σₐ ⊗ 1 + 1 ⊗ σₐ) ψ = 0`: zero net action on each axis, ZFA for a pair.

```text
singlet_trace       :  (X ⊗ 1 + 1 ⊗ X) s = tr X · s          for every 2×2 X,  s = |01⟩ − |10⟩
closed_iff_singlet  :  x and z actions cancel on ψ  ⟺  ψ = ψ₀₁ · s
singlet_corr        :  ⟨s| X ⊗ Y |s⟩ = tr X tr Y − tr(XY)
singlet_saturates   :  a = σz, σx;  b = −(σz ± σx)/√2  ⟹  Re⟨s|C|s⟩ = 2√2 ⟨s, s⟩
```

The joint closure is unique up to a factor: it is the singlet. On traceless observables its
correlation is `−tr(XY)`, perfect anticorrelation along any shared axis, and the CHSH expectation
reaches the bound with equality. So the state that carries the quantum excess over Bell's `2` is
not chosen: it is the only state whose halves close together on every axis.

**Credit.** Bell (*Physics* **1**, 195 (1964)); Clauser, Horne, Shimony and Holt (*Phys. Rev. Lett.*
**23**, 880 (1969)); Cirel'son (*Lett. Math. Phys.* **4**, 93 (1980)).

## 41. Vacuum polarization resummed through renewal

Issue #207 §10.1 asks for QED's vacuum-polarization insertions through renewal, with running from
capacity and no divergent subtraction. [`QLF_VacuumResolvent`](lean/QLF_VacuumResolvent.lean) does
that on top of the octave tower of
[`QLF_VacuumPolarizationTower`](lean/QLF_VacuumPolarizationTower.lean).

```text
chain_succ         :  D_{n+1} = D₀ + D₀ Π D_n                 (D_n = Σ_{k<n} (D₀Π)^k D₀, any ring)
chain_telescope    :  (1 − D₀Π) D_n = D₀ − (D₀Π)^n D₀
dyson_exists/unique:  1 − D₀Π invertible  ⟹  D = (1 − D₀Π)⁻¹ D₀ is the one solution of D = D₀ + D₀ΠD
dyson_of_nilpotent :  (D₀Π)^n = 0  ⟹  D_n is exact
dressed_inv        :  g = g₀/(1 − g₀Π)  ⟹  1/g = 1/g₀ − Π
chain_tendsto      :  |g₀Π| < 1  ⟹  D_n → g
resummed_is_tower  :  Π = Σ octave towers  ⟹  1/g = towerRunning
counterterm_finite :  Π(k+1) − Π(k) = per-octave increment
landau_capacity    :  Q_f ≠ 0  ⟹  the tower passes any bound at a finite octave count
```

The insertion chain is the same renewal as every closure channel (§7), and its resolvent is the
dressed propagator. For the coupling, resummation makes the inverse coupling subtract the
polarization linearly, and with the octave tower as the polarization that is exactly the running
`α⁻¹(Q²)` the tower already gave. Renormalization is a finite difference: raising the capacity by
one octave changes `Π` by one finite, octave-independent increment. The price is the Landau pole:
a charged closure's tower grows without bound, so at some finite capacity `1 − g₀Π` vanishes.
Below it the dressed coupling is finite and positive (`dressed_pos`). Where that capacity sits
relative to the Planck floor is a value question this module does not settle. The prime
electromagnetic closure kernel, which closures are the insertions with which charges and
thresholds, stays the tower's input.

**Credit.** Dyson (*Phys. Rev.* **75**, 1736 (1949)); Landau, Abrikosov and Khalatnikov (*Dokl. Akad.
Nauk SSSR* **95**, 497 (1954)).

## 42. CKM and PMNS as restrictions of channel unitarity

A mixing matrix is the part of a unitary channel map that connects the flavour channels we can
see. [`QLF_MixingUnitarity`](lean/QLF_MixingUnitarity.lean) reads the three standard tests of CKM
and PMNS as consequences of channel unitarity.

```text
column_split           :  U unitary on visible ⊕ hidden  ⟹  Σ_i |U_ij|² + Σ_k |U_kj|² = 1
block_unitary_iff      :  the visible block's columns are unit  ⟺  nothing leaks to hidden channels
triangle_closes        :  i ≠ j  ⟹  V_{i0}V̄_{j0} + V_{i1}V̄_{j1} + V_{i2}V̄_{j2} = 0
closed_triangle_area   :  a + b + c = 0  ⟹  Im(a b̄) = Im(b c̄) = Im(c ā)
jarlskog_invariant     :  the triangle's Jarlskog invariant is the same from every pair of sides
jarlskog_zero_iff_flat :  Im(a b̄) = 0  ⟺  a is a real multiple of b
```

A first-row deficit `|V_ud|² + |V_us|² + |V_ub|² < 1`, or a PMNS row short of one, is a leak into
channels outside the visible block: the same balance as a resonance (§39). Orthogonality of two
flavour channels is a closure, three amplitudes with zero sum, and CP violation is the area that
closure encloses; every side pair reads the same area, which is why the Jarlskog invariant is one
number. The mixing angles' values are not derived here.

**Credit.** Cabibbo (*Phys. Rev. Lett.* **10**, 531 (1963)); Kobayashi and Maskawa (*Prog. Theor.
Phys.* **49**, 652 (1973)); Maki, Nakagawa and Sakata (*Prog. Theor. Phys.* **28**, 870 (1962));
Pontecorvo (*Sov. Phys. JETP* **26**, 984 (1968)); Jarlskog (*Phys. Rev. Lett.* **55**, 1039 (1985)).

## 43. A bond is a shared closure: the two-channel resolvent

[`Chemistry.md`](Chemistry.md) reads a bond as a shared closure. Two sites close on their own with
kernels `a` and `b` and together with amplitude `g`, so the pair's kernel is `K = [[a, g], [g, b]]`
and its resolvent's poles sit at `z = 1/μ` for the roots of `(μ − a)(μ − b) = g²` (§36).
[`QLF_SharedClosure`](lean/QLF_SharedClosure.lean) works this out.

```text
levels_root       :  μ± = (a + b)/2 ± √(((a − b)/2)² + g²)  solve (μ − a)(μ − b) = g²
bonding_above     :  g ≠ 0  ⟹  μ₊ > max(a, b)
antibonding_below :  g ≠ 0  ⟹  μ₋ < min(a, b)
symmetric_split   :  a = b  ⟹  μ± = a ± |g|
resolvent_two     :  (1 − zK)⁻¹ = [[1 − zb, zg], [zg, 1 − za]] / ((1 − za)(1 − zb) − z²g²)
feshbach_entry    :  [(1 − zK)⁻¹]₀₀ = 1 / (1 − za − z²g²/(1 − zb))
```

Any nonzero shared closure pushes one level above both sites and one below. The bonding pole
`1/μ₊` moves toward the origin, so the shared closure is reached before either site's own. For
equal sites, as in `H₂`, the splitting is `2|g|`: the bond strength is the shared-closure amplitude.
Seen from one site, the partner enters only through the round trip `z²g²/(1 − zb)`, the Feshbach
reduction of §39's closed sector. The values of `a`, `b` and `g` for real atoms, bond angles and
multiple bonds are not here.

**Credit.** Heitler and London (*Z. Phys.* **44**, 455 (1927)); Feshbach (*Ann. Phys.* **5**, 357 (1958)).

## 44. Polaron branches as poles, absent branches as zeros

Issue #207 §10.5 asks the closure resolvent to organize the polaron:
branches as poles, absent branches as zeros, broadening as weight spread over channels.
[`QLF_PolaronBranches`](lean/QLF_PolaronBranches.lean) gives
[`QLF_Polarons`](lean/QLF_Polarons.lean)' shared closure its resolvent. An impurity level `ε`
shares a closure of amplitude `g_k` with each bath mode `ω_k`, and the impurity's resolvent is
`1/f(E)` with `f(E) = E − ε − Σ_k g_k²/(E − ω_k)`, the many-mode form of §43's Feshbach entry.

```text
branch_iff         :  E off the bath modes:  an eigenstate at E  ⟺  f(E) = 0
attractive_exists  :  lowest mode ω_j coupled  ⟹  some E < ω_j has f(E) = 0
attractive_below   :  f(E) = 0, E below every mode, some g ≠ 0  ⟹  E < ε
repulsive_above    :  f(E) = 0, E above every mode, some g ≠ 0  ⟹  E > ε
resolvent_eq       :  1/f = N/D,  N = Π(E − ω_k)
zero_at_bath       :  g_j ≠ 0, distinct modes  ⟹  N(ω_j) = 0 and D(ω_j) ≠ 0
residue_lt_one_iff :  Z = 1/(1 + Σ g_k²/(E − ω_k)²) < 1  ⟺  some g_k ≠ 0
f_deriv            :  f′(E) = 1 + Σ g_k²/(E − ω_k)²,   so Z = 1/f′ is the residue
```

The branches are the poles; a coupled lowest mode forces the attractive polaron below it and
below the bare impurity, and a branch above the band is pushed above it, the sign fixed by the
round trip. At each coupled bath energy the resolvent has a true zero (numerator zero, denominator
not): the impurity cannot appear there. A branch carries weight `Z`, the impurity's share of its
eigenstate, below one exactly when the impurity is coupled; the rest is spread over the bath
modes. The effective mass needs a momentum-labelled bath and is not here.

**Credit.** Fano (*Phys. Rev.* **124**, 1866 (1961)); Anderson (*Phys. Rev.* **124**, 41 (1961));
Massignan, Zaccanti and Bruun (*Rep. Prog. Phys.* **77**, 034401 (2014)).

## 45. The non-abelian Gauss identity

§31's field equation at a link is `E_k(z) = A(M_k(z) U_k(z)) = 0`, with `M` the staple sum and
`A(X) = X − Xᴴ`. [`QLF_NonAbelianGauss`](lean/QLF_NonAbelianGauss.lean) proves the identity these
satisfy for every link configuration, on shell or not.

```text
noether          :  Σ_k A(U_k(y) M_k(y)) = Σ_k A(M_k(y − e_k) U_k(y − e_k))      (no unitarity)
gauss_covariant  :  U unitary  ⟹  Σ_k U_k(y) E_k(y) U_k(y)ᴴ = Σ_k E_k(y − e_k)
gauss_on_shell   :  E = J  ⟹  Σ_k U_k(y) J_k(y) U_k(y)ᴴ = Σ_k J_k(y − e_k)
```

Every plaquette through `y` enters the identity twice, through each of its two links at `y`, and
the two entries cancel: at the corner where both links leave `y` they give the holonomy and its
dagger, and at the other corners the same rotated loop appears once outgoing and once incoming.
For unitary links the identity says the covariant divergence of the field equation vanishes: the
outgoing values parallel-transported back to `y` balance the incoming ones. So a source `J` of the
field equation must be covariantly conserved at every site. This is the non-abelian Gauss law as a
Noether identity. As the time-link equation of a dynamical history it still needs a time step for
matrix links, and the walk's colour current as the source.

**Credit.** The lattice Noether identity of gauge invariance; Creutz, *Quarks, Gluons and Lattices*
(Cambridge, 1983); Kogut and Susskind (*Phys. Rev. D* **11**, 395 (1975)).
