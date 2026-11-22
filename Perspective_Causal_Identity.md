# Prefix reachability versus continuation equivalence (#296)

## Frozen discriminator

Base: 995bf55. The continuation audit reconstructs relative suffix/phase
languages for the specified no-immediate-adjoint policy. QLF_ReachableEvent
instead defines reachability as prefix inclusion of absolute histories. These
are distinct observables. Neither is automatically physical observer access.

Use all successor-admissible nonempty prefixes of length 1–3 and first ZFA
leaves of total length at most 6, with at most 3 appended twists per prefix.
Use the existing twist_core successor and ZFA predicates. A terminal event ID
is its complete word, not its fold, phase or physical face. No coordinates,
observer masks, physical access relation or event quotient are introduced.

G1: Independently enumerate the first-closure tree from the empty word, and
index its terminal words by prefix. Compare for every prefix against the
existing reduced-state continuation evaluator, after attaching the prefix.
Require exact equality of absolute word/phase sets.

G2: Partition prefixes by (signed action, exact fold, last twist, length).
Check whether this record reconstructs absolute terminal identity, using the
existing factorization criterion. Retain a concrete collision if any.

G3: For every same-record pair of distinct prefixes having nonempty terminal
sets, check relative suffix/phase equality and disjoint absolute terminal sets.
Record the group and pair counts; do not treat empty-language agreement as
evidence of event identity.

G4: On this domain, test whether retaining the prefix identity plus its
relative language reconstructs the absolute set. The repair is a word-ID
reference, not a physical event-identity theorem.

If G2 fails, the result rules out identifying the reduced transition state
with the full prefix-reachability record. If G2 passes, report that bounded
negative result without extrapolation. Physical causal accessibility and
the correspondence between terminal words and physical faces remain B-OPEN.

## Results

Protocol commit: `10e46b8180d13c90090fda68006611233309dd58`.

Run `python3 perspective_causal_identity.py`; the deterministic record is
[data/perspective_causal_identity.json](data/perspective_causal_identity.json).

- G1: 1,248 first-closure leaves through depth 6; all 456 prefix comparisons
  matched the separately enumerated absolute-word/phase index.
- G2: the 456 prefixes collapse into 384 reduced-state classes. The record
  does not reconstruct absolute terminal identity.
- G3: all 72 same-state distinct-prefix pairs have nonempty, equal relative
  languages and disjoint absolute terminal sets. For example, prefixes
  `^+^` and `+^^` share the same reduced state. Both accept suffix `-vv`
  with scalar phase -1, but the terminal words are `^+^-vv` and `+^^-vv`.
- G4: prefix identity plus the suffix language reconstructs the absolute
  event IDs throughout the screen.

The underlying reason is structural. For distinct equal-length words p and q,
no word can have both as prefixes. For a nonempty relative continuation set L,
the sets pL and qL are therefore disjoint even when L is identical. Thus a
record that identifies p and q cannot determine their absolute future cones
on that domain. The argument is about prefix order and word identity, not a
new machine-checked Lean theorem. An explicit event quotient may identify
some words, but its compatibility with reachability and its physical meaning
must be justified independently.

This result complements the existing relative continuation repair, rather
than invalidating it. Physical Markov-blanket access and the correspondence
between terminal word IDs and physical faces remain B-OPEN. The next gate
is a specified event quotient (or retained identity) and a causal access
map whose compatibility with prefix order can be falsified.
