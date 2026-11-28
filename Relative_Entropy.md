# Relative Entropy — the record-relative ledger

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**One law.** QLF assumes equal and opposite logical action and nothing else
([`Framing.md`](Framing.md) A01). Entropy is not a second law: it is the bookkeeping of distinctions
that a declared record does not carry. “Relative” does not mean that different observers have
different physics. It means that the **record map** `R_B` and the admissible continuations are part
of the statement.

**Possibilism and relativity of record.** Every admissible synthesis exists as a way (A02); a finite
record's blindness is not a second permission law. Relative entropy is about which distinctions a
perspective can access, not about which possibilities are allowed to exist. The existence/manifestation
distinction is stated in [`Entropy.md`](Entropy.md) §0a.

## 1. Global purity, local entropy

The elementary case is the singlet:

\[
S(AB)=0,\qquad S(A)=S(B)=\log 2.
\]

The joint state is pure; each half is maximally mixed. This is one relation, not a lost qubit. The
local observer has a record that does not include the complementary half. The Lean anchors are
`singlet_reduced`, `entropy_half_half` and `cutEntropy_eq_vonNeumann`
([`QLF_HolographicCompletion`](lean/QLF_HolographicCompletion.lean)).

The general form is the record partition of [`Entropy.md`](Entropy.md) §3:

\[
H(H)=H(R_B)+L_B,\qquad L_B=H(H\mid R_B).
\]

`L_B` is not “the entropy of the universe.” It is the information about the history that the record
`R_B` does not retain. A different record, or a larger capacity, is a different `L_B`.

**A refinement of Boltzmann/Gibbs, not a replacement.** Boltzmann's `S = k_B ln W` and Gibbs'
`S = -k_B Σ p_i ln p_i` already count multiplicities. QLF makes the ensemble and the record explicit:
`W` is the number of histories compatible with the boundary a given observer resolves. The
state-counting is inherited; the relational selection is added. The absolute thermodynamic entropy
of a closed system is recovered only after a physical measure and a physical record map are supplied.

## 2. The causal horizon is a record boundary

If a complex event lies outside an observer's logical light cone, it carries no distinctions in that
observer's record. It becomes relevant when the causal boundaries intersect and a joint ZFA
resolution is required. This is a statement about `R_B`, not about the event failing to exist.

The holographic audit makes the same point sharply: closure is a boundary property, and an area law
follows from **locality of shared closures**, not from closure alone
([`Holography_Audit.md`](Holography_Audit.md)). A “perspective” in the finite audits is a record map,
not yet a physical Markov blanket.

## 3. Bisimilarity and masked complexity

A macroscopic context reads the boundary it can distinguish. If two internal histories have the same
observable behaviour under every declared continuation, they belong to one listener class
([`Listener_Equivalence_QLF.md`](Listener_Equivalence_QLF.md)). The internal multiplicity is then
irrelevant to that listener's next closure.

This is disciplined compression, not arbitrary loss:

- **lossless for the declared continuations** — equivalent states remain equivalent after any
  continuation;
- **lossy for the route** — the representative history is not recovered;
- **relative to `B`** — a finer listener can separate what a coarser one merges.

The gift of forgetfulness is the consciousness-side name for this structure
([`Conscious_Dynamics_QLF.md`](Conscious_Dynamics_QLF.md) §1a, gate D10). It is what keeps a finite
world-database usable.

## 4. Entropy as unresolved relation, not disorder

Entropy is the combinatoric volume of unresolved logical relations between two specified records or
namespaces. A history may require many closure steps relative to one boundary and few relative to
another. Relative to its exact Hermitian conjugate, the same history can close by a direct
handshake. This is a relational reading of the ledger, not a claim that entropy is subjective or
that all records are equally physical.

The **permanence** question is separate. A distinction can be:

1. absent from a fixed record `R_B`;
2. recoverable by an expanded record or capacity;
3. unavailable to every admissible future of the original perspective.

Only the third is permanent local loss, and it is an open proof obligation. The Law of Exceptions
([`Law_Of_Exceptions.md`](Law_Of_Exceptions.md)) shows why a finite-capacity record cannot be treated
as final: a larger capacity admits a closure the smaller one excludes.

## 5. Scope

- No claim that every observer's entropy is physically real in the same sense.
- No claim that a pure global state has nonzero total entropy.
- No claim that “lost to space” is proved; it is the proposed geometric bridge in
  [`Entropy.md`](Entropy.md) §5.
- No claim that the listener quotient is a theory of consciousness or qualia.

See also: [`Entropy.md`](Entropy.md) — the one-law entropy synthesis, finite census and open GR
bridges; [`Error_Correction.md`](Error_Correction.md) — bisimilarity masking in action;
[`Holography_Audit.md`](Holography_Audit.md) — the conditional area law.
