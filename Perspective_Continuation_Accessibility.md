# Local possibility as a bounded continuation language (#296)

Base: #306 at 872cdf65. Prior record-map and nested counting checks do not derive
a physical Markov blanket. This experiment uses the existing QuCalc Python
successor predicate (no immediate conjugate), not a presumed physical observer.

## Frozen protocol

Enumerate every successor-admissible nonempty prefix of length 1–3. For each,
enumerate admissible suffixes of length at most three, stopping at the first
terminal ZFA closure (min_length=4, exact count and scalar fold). No capped BFS
helper, selection by phase, or multiplicity-based priority. Terminal records are
suffix words paired with their scalar phase. Define three hypothetical accessibility
masks independently of the result: use all twists; A allows vertical/horizontal/gauge
twists; B allows horizontal/diagonal/gauge twists. The intersection admits only
horizontal/gauge twists. This is a toy continuation policy, not a physical screen.

F1: test whether the already anchored closure verdict, signed action and Pauli
fold, even augmented with the current prefix length, determine the complete
bounded continuation language. If equal records have unequal language, retain
the concrete collision and missing suffix. Do not promote the old record.
F2: build a transition system on (signed action, exact fold, last twist, length)
using only the current record, canonical generator and successor predicate.
Compare its language to direct word enumeration for every prefix and mask.
F3: each restricted mask language must be computed independently. Test joint
accessibility via intersection of the two languages, compared to direct
intersection-mask enumeration, with common terminal phase agreement.
F4: test whether at least one restricted view loses a globally allowed suffix.
If so, no mask alone can be assumed globally reconstructive.

The integer face ledger counts distinct explicitly identified objects. Suffix
words are **not** physical faces, and their counts are not a horizon entropy.
A physical derivation still needs a causal access relation, observer-dependent
clock and scale/face mapping. No new axiom or physical claim is proposed.

## Evidence

Pending.
