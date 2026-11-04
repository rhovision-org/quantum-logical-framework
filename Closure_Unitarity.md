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

`U(^<) = σy·(−σx) = iσz` is anti-Hermitian (`upLeft_antiHermitian`), so:

- `upLeft_forbidden_all_orders`: `A_L(^<) = 0` for all `L`.
- `upLeft_interference_zero`: at `L = 2`, closures exist (`v>`, `>v`), so this is an interference zero
  and not a structural one. The transition is forbidden by destructive interference that time reversal
  forces. It is not forbidden for lack of histories.
- `upLeft_ways_two/four/six`: the registry's `2, 72, 2820`, re-derived.

Two contrasts show what the theorem does and does not cover:

- `^` has a Hermitian fold (`σy`), so no such pairing exists. `A_1(^) = −1` (`up_amplitude_one`).
- `^^^^` at `L = 2` is a structural zero (`upFour_structural_zero_two`). It needs four `v`. At `L = 4` it
  closes once (`upFour_ways_four`). A structural zero can be a statement about capacity, while the
  anti-Hermitian zero is a selection rule at every capacity.

**What would make this physics.** In the issue's dictionary an interference zero is the substrate candidate
for a hidden amplitude zero. That match is a hypothesis. The theorem gives one concrete, all-orders mechanism
(time-reversal pairing). Whether the Arkani-Hamed–Cao–Dong–Figueiredo–He zero loci
([arXiv:2312.16282](https://arxiv.org/abs/2312.16282)) come from a mechanism of this kind is benchmark PZ4,
and it is open.

## 6. What this does not do

These are finite and exact, and they cover only the first rows of the issue's checklist. The following
remain open, as the issue frames them:

- **U3, complete-channel unitarity.** [`lean/QLF_PolyaTransience.lean`](lean/QLF_PolyaTransience.lean)
  proves the non-closing mass is positive, so closed channels cannot simply be normalized to one (kill
  condition 7). U1 shows the full possibility space is unitary history by history. A channel operator
  `S_R` with `S†S = I`, or a closed-plus-open leakage identity, has not been built.
- **PZ1–PZ2 beyond the single vacuum channel.** §7 gives the scalar kernel, the resolvent and the
  first-closure factorization of every seeded channel. Still open: a genuine multi-channel matrix
  `K` (channels as boundary states, `G = I + K G`), residue factorization *at* a pole of a
  continuum rendering, and the finite RG flow of `K` through
  [`lean/QLF_ExactRG.lean`](lean/QLF_ExactRG.lean).
- **G1–G4**, every gluon benchmark.

Status: the U1, PZ1–PZ1c and PZ3 rows of the issue's Phase A/B checklist are done, with a first seed of PZ2. Nothing on this page claims that
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
residues `F_s` depending on the channel. That is a reading for PZ2 to test. The identity itself is
the theorem.

**Zeros live in the kernel.** Because `A_0(∅) = 1`, the factorization can be inverted order by order.
An amplitude that vanishes at every order therefore has a first-closure kernel that vanishes at every
order (`kernel_zero_of_amplitude_zero`). The all-orders zero of `^<` (§5) is a zero of `F_{^<}`
(`upLeft_kernel_zero`), so it is not produced by the dressing. In the issue's terms the forbidden
transition sits in the irreducible interaction, not in propagation.

All the identities above are checked against direct enumeration of `A_L` and `F_k` for the seeds `∅`,
`^`, `^<`, `^>` and `^^<` up to `L = 5`.
