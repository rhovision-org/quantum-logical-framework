# Entropy in QLF — record, forgetting, and the one law

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**Status.** Synthesis and proof program. The **one law** is equal and opposite logical action
([`Framing.md`](Framing.md) A01). Entropy is treated here as derived record bookkeeping, not as a
second fundamental law. The finite census and the standard record-partition identity are explicit;
the half-loss, thermodynamic-work and GR reconstructions are labelled **open bridges**, not
conclusions.

**What changed from v1.3.** The old version said gauge-folded particles are primordial black holes,
that all macroscopic black-hole thermodynamics and the holographic principle follow automatically,
and that `log C(2k,k)` recovers an area law. Those claims are withdrawn. The gauge-folding
correspondence is a model reading; the area law requires locality
([`Holography_Audit.md`](Holography_Audit.md)); `log C(2k,k) ≈ 2k log 2` is extensive in history
length, not an area law; and the Bekenstein–Hawking `¼` remains an open normalization.

---

## 0. The one law, and what entropy is not

QLF assumes equal and opposite logical action and nothing else. Read computationally,
[`Universe_Quantum_Computer.md`](Universe_Quantum_Computer.md) states the thesis: **the universe is
the quantum computer that runs that one law**. Every other principle is derived, cited from a known
fact, or explicitly labelled a bridge or reading. Derived principles have **domains and exceptions**
([`Law_Of_Exceptions.md`](Law_Of_Exceptions.md)); an exception to a derived principle is not an
exception to A01.

Entropy in QLF is therefore not a primitive disorder of a pre-existing spacetime. It is the
bookkeeping of **distinctions that a finite record does not carry**. The organizing principle is
already in the registry:

> **C06 — closure conserves the ledger and erases the route.**
> The signed action ledger is conserved (P08); closure is many-to-one (P09); a later observable can
> recover only a continuation-relevant record, not the path. The inventory's older phrase “closure
> preserves information” is false as stated and is retired.

Three grades must be kept apart:

| Grade | What it means | Example |
|---|---|---|
| **Proved / cited** | A Lean theorem or a standard finite identity | `closure_renewal`, `singlet_reduced`, `garbageBill_eq_closures` |
| **Finite census** | An exact count over a declared finite domain | the sign census below |
| **Bridge** | A physical identification not derived from A01 | “the inaccessible complement is space”, Landauer in joules, horizon entropy |

---

## 1. The elementary pair: pure globally, `log 2` locally

For the normalized singlet

\[
|\psi^-\rangle=\frac{|01\rangle-|10\rangle}{\sqrt2},
\]

the joint state is pure and each half is maximally mixed:

\[
S(AB)=0,\qquad S(A)=S(B)=\log 2.
\]

That is the precise content of “when we create a qubit pair, do we lose one?” The pair does not
destroy a qubit. It creates a complementary relation: the joint information is real, while each
local perspective can reconstruct only half of the relation. The QLF anchors are

- `singlet_reduced` — tracing out either half of the normalized singlet leaves `I/2`;
- `entropy_half_half` — the spectrum `(½, ½)` has entropy `log 2`;
- `cutEntropy_eq_vonNeumann` — a cut through `M` shared singlets has entropy `M log 2`.

[`QLF_HolographicCompletion`](lean/QLF_HolographicCompletion.lean) proves these with no axioms. The
one standard step used and not reproved is that the reduced state of a tensor product is the tensor
product of the reduced states (partial trace is multiplicative).

**The 50% principle is not yet a theorem.** At the elementary symmetric pair boundary, one
complementary subsystem is locally accessible and the other is not. That does **not** show that half
of all information, energy or spacetime is permanently lost. The pair may re-interact. What is
missing is a theorem that, relative to a declared originating perspective and its admissible
futures, the complementary record is irrecoverable.

---

## 2. Possibilities multiply; the forward record compresses

The one-axis balanced-history count is the central binomial coefficient

\[
W_n=\binom{2n}{n}\sim\frac{4^n}{\sqrt{\pi n}},
\]

so the possibility census grows exponentially. Yet `closure_renewal`
([`QLF_ClosureRenewal`](lean/QLF_ClosureRenewal.lean)) proves that after a count-balanced history
`h`, every continuation `c` satisfies

\[
\operatorname{Balanced}(h{+}{+}c)\iff\operatorname{Balanced}(c),
\qquad
\operatorname{Fold}(h{+}{+}c)=\sigma(h)\operatorname{Fold}(c),
\]

with one sign `σ(h) = ±1`. Of all the ways the closed history could have been built, at most one
sign reaches its future. Everything else must be held outside the closure, by a third party or a
larger record. This is [`Memetics_QLF.md`](Memetics_QLF.md) §2 and the formal core of C06.

The finite census in [`entropy_synthesis.py`](entropy_synthesis.py) makes the compression visible
for actual ZFA closures (count-balanced and Pauli-closed):

| length | closures | `+` | `−` | `H(total)` bits | `H(sign)` bits | forgotten bits |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 8 | 0 | 8 | 3.000000 | 0.000000 | 3.000000 |
| 4 | 168 | 144 | 24 | 7.392317 | 0.591673 | 6.800645 |
| 6 | 5120 | 1488 | 3632 | 12.321928 | 0.869527 | 11.452401 |

`H(total)` is `log₂` of the closure count under the uniform finite measure; `H(sign)` is the entropy
of the surviving sign class; `forgotten = H(total) − H(sign)`. The sign carries at most one bit and
the forgotten share grows. This is a finite census, not a claim that the sign is thermodynamic
entropy or that Nature uses the uniform measure.

The distinction that remains open is equally important: **exponential growth of possible histories
is proved; growth of actualized global physical information along a history is not.** The census
counts ways, not a physical entropy density.

---

## 3. The record partition

Let `H` be a history drawn from a finite ensemble and let `R_B(H)` be the record accessible relative
to a boundary or listener `B`. When `R_B` is a deterministic function of `H`, the Shannon chain rule
gives the identity

\[
\boxed{H(H)=H(R_B)+L_B,\qquad L_B=H(H\mid R_B).}
\]

`L_B` is the information forgotten by that record. For a uniform fiber of `m` histories that the
record cannot distinguish, `L_B = \ln m`; for the elementary two-to-one closure, `L_B = \ln 2`.

This is a standard information identity, not a new physical law. The QLF content is in the two
choices the identity leaves open:

1. **Which record is accessible?** `R_B` must be specified by the observer's closure domain, not
   chosen after the answer.
2. **Which futures can recover the distinction?** A distinction is only permanently lost if no
   admissible continuation of the original perspective distinguishes it.

The finite version is checked in `entropy_synthesis.py`; a general Lean formalization of conditional
entropy and the fiber identity is a proof target, not a claim of this PR. The listener quotient
([`Listener_Equivalence_QLF.md`](Listener_Equivalence_QLF.md)) is the disciplined case: it discards
exactly the distinctions that no declared continuation can recover, and remains lossless for those
continuations.

---

## 4. Conservation and the Bennett–Landauer boundary

The ledger and the route behave differently, and the difference is priced.

| Reversible computation | Irreversible local synthesis |
|---|---|
| one-to-one | many-to-one |
| distinctions preserved | route distinctions forgotten |
| information recoverable from the record | information becomes locally inaccessible |
| no necessary erasure cost | thermodynamic cost under stated conditions |
| Fredkin–Toffoli logic | Bennett–Landauer accounting |

QLF proves the structural half:

- `fredkin_bijective` and `fredkin_iterate_bijective`: a Fredkin gate and every composition of
  Fredkin gates are bijections, so a reversible circuit merges no histories;
- `reversible_run_cost_zero`: the reversible core has zero garbage bill, independent of gate count;
- `garbageBill_eq_closures`: resetting `k` garbage lines costs `k` closure quanta;
- `binary_kl_delta_uniform`, `zfa_closure_minimizes_free_energy`: the dimensionless quantum is
  `log 2` nats.

The hard boundary is explicit: **none of these is thermodynamic work in joules.** The Landauer
statement `W_min = k_B T ln 2` needs a temperature, a reset protocol and a physical energy map. The
dimensionless QLF identity is not silently promoted to that statement. The del Rio–Åberg–Renner
side-information exception is also a warning against a context-free “erasure always costs positive
work”: if the complementary quantum record is accessible, the optimal work can be negative. QLF's
perspective-dependent accessibility is therefore not optional bookkeeping; it is part of the
thermodynamic domain.

Conservation is likewise stratified: the signed logical ledger is conserved by theorem; physical
energy, momentum and entropy currents require their reconstruction maps. A local conservation law
with boundary flux is a target, not an automatic consequence of ledger conservation.

### 4a. The `log 2` inventory, condensed

The previous edition listed seventeen appearances of `log 2`; only **four** are independent routes,
and the rest are re-exports of the same quantum into a physical setting. The method forbids counting
them as seventeen confirmations.

| Route | Lean anchor | Why it is independent |
|---|---|---|
| **KL of a resolved binary distinction**: `D_KL(δ ‖ ½) = log 2` | `binary_kl_delta_uniform` ([`QLF_FreeEnergy`](lean/QLF_FreeEnergy.lean)) | information-theoretic |
| **Counting the ways a pair closes**: `2ⁿ` depth-1 closures, `log(2ⁿ) = n log 2` | `onePass_ways_iff`, `onePass_entropy` ([`QLF_ClosureDepth`](lean/QLF_ClosureDepth.lean)) | combinatorial |
| **Von Neumann entropy of `I/2`**: `S(I/2) = log 2` | `entropy_half_half` ([`QLF_HolographicCompletion`](lean/QLF_HolographicCompletion.lean)) | spectral |
| **MRE ceiling**: the binary-partition maximum is `log 2` | `binary_kl_uniform_le_log_two_endpoint` ([`QLF_VacuumAlignment`](lean/QLF_VacuumAlignment.lean)) | extremal |

The horizon area count, the LQG puncture quantum, the cosmological-constant value, the mass gap and
the coupling appearances are re-exports or reading-dependent identifications. In particular,
`holographic_entropy_eq` is `ring` over a definitional event count, not a derivation of the area law;
and `S = 4πR² log 2` is not a physical normalization until the site-to-Planck-area map is derived.

---

## 5. Space, horizons and GR: the proposed bridge

The suggestion that locally inaccessible information is “given to space” is the most consequential
part of the new framing. It is a **proposed reconstruction**, not a proved identity:

```
equal and opposite logical action
        │
        ├── locally retained complementary relations ── matter / conservation
        └── locally inaccessible relations ─────────── space / entropy
                                                       │
                                            closure density, delay, horizons
                                                       │
                                            GR / thermodynamic gravity
```

What QLF actually proves today:

- closure is a boundary property (`closure_iff_boundary_silent`);
- a cut through local shared singlets has entropy `M log 2`, and the area law follows **given
  locality of shared pairs** (`cutEntropy_le_area`, `local_area_law`);
- the spatial `ℓ¹` horizon sphere has exactly `4R²+2` sites (`sphere3_card`);
- QLF's horizon count differs from Bekenstein–Hawking by the measured `4 log 2` residual
  (`residual_is_quarter_times_quantum`).

What remains open, in order:

1. **Locality / shared-pair birth** — that shared pairs are born at one event and only nearby
   relations are shared. The area law is conditional on this, not derived from closure alone.
2. **Horizon identification** — that the `ℓ¹` sphere is the horizon selected by QLF's capacity
   semantics. In Lean, `closedAtHorizon` is stated for the 1-D phase string, not the `ℓ¹` ball on
   `ℤ⁴`.
3. **Bekenstein–Hawking normalization** — the map from a lattice site to a Planck area. The `¼` is
   not derived by counting.
4. **Jacobson’s thermodynamic route** — deriving `δQ = T dS` from closure flux and recovering
   `G_{μν} + Λ g_{μν} = 8πG T_{μν}/c⁴`. The present document supplies a target list, not the
   derivation.
5. **Cosmological allocation** — whether an approximately half-conserved local activity and its
   complementary contribution can explain expansion. This is a conjecture, not a result.

The old claim that “all macroscopic black-hole thermodynamics and the holographic principle follow
automatically” is withdrawn. The honest statement is: **holography in QLF is a conditional theorem
with named premises and one open normalization.** See [`Holography_Audit.md`](Holography_Audit.md)
and [`Holographic.md`](Holographic.md).

---

## 6. Consciousness: the gift of forgetfulness

The same structure appears in the consciousness model. A finite self-model cannot retain every
possible world or every microhistory. The listener quotient is the disciplined form of forgetting:

- it discards exactly the distinctions that no declared continuation can recover;
- it remains lossless for the continuations it declares;
- it keeps the relative world-database finite and leaves room for a next expression.

This is now declared as the fourth capacity in [`Conscious_Dynamics_QLF.md`](Conscious_Dynamics_QLF.md)
§1a, with gate **D10**. Its cited basis is many-to-one closure, `closure_renewal`, persistence by
copying, and the `−log 2` closure price. It is not a theory of qualia, not observer erasure, and not
a claim that forgetting is always beneficial or free.

The stronger theorem to aim for is:

> a listener may discard historical distinctions without reducing its capability to recognise or
> participate in any admissible future closure in its declared domain.

For the finite listener quotient this is true by construction for the declared continuations; the
general active-inference and physical-agent version is open.

---

## 7. Exceptions and permanence

There are three different statements that the word “forgotten” can hide:

1. **Forgotten relative to a fixed perspective** — `R_B` does not carry the distinction.
2. **Recoverable through an expanded perspective** — a larger capacity or a different record `R_C`
   recovers it.
3. **Permanently unavailable to every admissible future of the original perspective** — the strongest
   and the only one that deserves “lost to space forever” without qualification.

The Law of Exceptions ([`Law_Of_Exceptions.md`](Law_Of_Exceptions.md)) makes the distinction sharp:
every finite closure capacity excludes a closure that a larger capacity admits
(`law_of_exceptions`, `no_final_closure`). Information insignificant at one capacity can become
significant at another. Therefore a finite observer's forgotten information is not automatically
permanent loss; permanence requires the third statement, which is not proved here.

Thermodynamic entropy increase likewise does not imply entropy increase in every local subsystem.
Life, intelligence, error correction and cooperative organization may build persistent local order
while exporting entropy. Whether QLF derives that as a theorem is C20/C21, both open.

---

## 8. Proof program and status

The following are proposed Lean targets. They are listed so the synthesis is falsifiable, not
because they are already proved.

| Target | Current status |
|---|---|
| `closure_information_partition` — `H(H)=H(R_B)+L_B` | standard identity; finite census checks the uniform case; general Lean target |
| `pair_local_entropy_log_two` — singlet `S(A)=log 2` | **proved** (`singlet_reduced`, `entropy_half_half`, `cutEntropy_eq_vonNeumann`) |
| `closure_growth_local_compression` — census growth with bounded forward record | **partly proved**: `W_n = C(2n,n)` and `closure_renewal`; actualized-information growth open |
| `forgetting_iff_noninjective` — a record loses a distinction iff it is noninjective | standard; Lean target |
| `irrecoverable_iff_no_future_distinguishes` | open |
| `perspective_expansion_recovers_information` | open |
| `local_conservation_with_boundary_flux` | ledger P08 and boundary-flux anchors exist; physical energy current open |
| `closure_landauer_bridge` | dimensionless `log 2` proved; joule-scale thermodynamic bridge open |
| `entropy_from_emergent_geometry` | open |
| `forgetfulness_preserves_capability` | finite listener-quotient shadow; general theorem open |
| `adaptive_closure_resists_entropy` | C20/C21, open |

The first two rows and the finite census are enough to state the new framing honestly. The rest are
research obligations, not hidden axioms.

---

## 9. The synthesis

> The universe is not a computer operating in space and time. It is the quantum computer whose
> logical action synthesizes space and time.
>
> Equal and opposite logical action is its one fundamental law. From it emerge conservation,
> complementary relations, finite perspectives and the proliferation of possibilities.
>
> Globally, possibilities multiply. Locally, closure preserves the distinctions that matter to
> continuation while relinquishing the history of their construction. Entropy is the informational
> consequence of this finite participation in reality.
>
> The gift of forgetfulness is what allows finite structures to participate in an inexhaustible
> universe. It makes room for new experience, new organization, new intelligence and new
> possibilities.
>
> Reality does not overcome entropy by preventing all information loss. It may overcome entropy
> locally by discovering what is worth preserving.

The greater objective is to derive how reality defeats entropy through selective synthesis rather
than indefinite accumulation. That is the bridge joining QLF, active inference, consciousness and
the cooperative intelligence sought in QuantumOS. It is a target of the one-law framework, not an
additional postulate.

---

## 10. Reproduce

```bash
python3 entropy_synthesis.py --self-test
python3 entropy_synthesis.py --run
python3 -m unittest tests.test_entropy_synthesis -v
```

The run writes `data/entropy_synthesis.json`. The finite census and the record-partition identity are
finite-domain results; the physical bridges above remain open.
