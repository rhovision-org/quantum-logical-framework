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
chsh_tsirelson :  a₀a₁ = −a₁a₀, b₀b₁ = −b₁b₀  ⟹  C²(C² − 8) = 0  (|C| ≤ 2√2, Tsirelson)
```

So the whole gap between Bell's bound and Tsirelson's (Cirel'son, Lett. Math. Phys. 4 (1980) 93)
is whether a site's two observables commute. Commuting observables can be given joint values, and
then the bound is 2. Anticommuting ones cannot, and the bound is `2√2`, no more.

**Twists supply exactly that.** Twists on different spatial axes anticommute, the same Clifford
relation that makes the light-cone zeros exact (§11). With `up` and `left` on each of two sites:

```text
twist_bell_pair      :  each squares to 1, the sites commute
twistChsh_herm       :  the CHSH operator is Hermitian
twistChsh_tsirelson  :  C²(C² − 8) = 0
twistChsh_sq_e00     :  C²|00⟩ = 8|00⟩         so 2√2 is attained
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

**Credit and status.** This is Zurek's envariance argument (*Phys. Rev. A* **71**, 052105 (2005)) in
finite form, and Deutsch's decision-theoretic derivation (*Proc. R. Soc. A* **455**, 3129 (1999)) reaches
the same rule. Zurek's version needs a continuity step to reach irrational weights. QLF needs none,
because its amplitudes are Gaussian integers: every Born weight is a ratio of whole counts, so the
rational case is the only case. No continuum enters. Still open, as before: why nature's weight has
no third-order interference ([`Interference_NoGo.md`](Interference_NoGo.md) §6, the three-slit
bound), and which census quantity is the register `ψ`.

## 17. The gauge axis is the clock, and closure is on the mass shell

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

The reading. A state whose tick exactly cancels its spatial phase has zero net phase per step, which
is zero free action. `mass_shell` says those states satisfy `ω² = k² + m²`: closure puts the walk on
the mass shell, and without mass, on the light cone. The shell is not put in by hand. It comes from
the Clifford square `dirac_sq` and nothing else. The gauge axis carries the frequency because it is
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
itself, which is taken as the form; deriving it needs an action or dynamics for the links, which is
open. Reading the walk's norm density as electric charge is also a reading, not a theorem.
