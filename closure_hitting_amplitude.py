#!/usr/bin/env python3
"""
closure_hitting_amplitude.py -- the per-charge closure probability (hitting mass),
identified in the R->infinity limit as a ZFA closure-walk hitting probability
(Lumina_QLF.md sec 13). NOTE: this is a closure probability, not (yet) a physical
"amplitude" -- cylinder-measure -> physical-event-probability is still an open bridge
(the filename is kept only to preserve existing doc links).

sec 11 (raw count) and sec 12 (Kraft mass, depth cap 7) could not converge a per-charge
number -- both were DEPTH-limited. This removes the depth limit by recognizing what the
census IS; what remains is a SPATIAL truncation (a finite radius-R ball), handled by
pushing R and reading off the R->infinity limit.

                        ---- THE RECOGNITION ----

Count balance already implies Pauli closure (count_balanced_pauli_closed), so a ZFA
first-closure is simply the FIRST RETURN TO THE ORIGIN of the eight-twist walk on Z^4
(the twists are +-e_a on four axes; Closure_Walk.md). Each twist carries weight 1/8 and
there are eight of them, so the Kraft weight 8^-len of a continuation is EXACTLY the
probability of that path under the uniform random walk. Therefore the Kraft closure mass
of a seed is a HITTING PROBABILITY:

    M(k) = P( the Z^4 walk started k steps out along the gauge axis ever reaches 0 )
         = h(k * e_gauge),

the probability that k free charges of one sign ever close (find their partners and
neutralize). h is the discrete-harmonic hitting probability of {0}:

    h(0) = 1,   h(x) = (1/8) * sum over the 8 neighbors h(x +- e_a)   for x != 0,
    h(x) -> 0   as |x| -> infinity   (the Z^4 walk is transient, QLF_PolyaTransience).

h is computed by value iteration on the finite l1-ball of radius R with h=0 outside --
a SPATIAL truncation (the Dirichlet problem on the ball), so the R sequence approaches
the true infinite-depth value from BELOW; it is a numerical identification of the
R->infinity limit, not an exact evaluation. The walk's full symmetry (coordinate
permutations + sign flips) collapses every state x to the sorted tuple of |coords|, so
the state space is tiny and R can be pushed far (a certified finite-R error bound
0 <= p4 - h_R(e) <= eps(R) would upgrade this from "numerically convergent" to "proved";
it is not yet added).

                        ---- WHAT THIS DELIVERS ----

M(1) = h(one step out) = the walk's RETURN PROBABILITY -> p4 = 0.1932015 (itself a numerical
value for the 4D Polya return probability, not a constant proved exactly by QLF_PolyaTransience,
which proves transience/summability bounds), the prime-closure mass of Closure_Walk.md
(VALIDATION: the iteration must reproduce that established number in the R->infinity limit; at
R=50 it is 0.193044, ~1.6e-4 below, approaching from below). So the single-free-charge CLOSURE
PROBABILITY is identified as p4 in the limit -- the fraction of possibility that closes. For k
charges M(k) = h(k*e) falls as the 4D Green's function ~ 1/k^2, so the per-charge marginal
surprisal -ln[M(k+1)/M(k)] -> 0 at small k: the effect SATURATES (sublinear), it is not a fixed
per-charge bit and not superlinear.

Pure Python, exact value iteration, a few seconds.
"""
import math
import sys

P4_CLOSURE_WALK = 0.1932015      # prime-closure mass, Closure_Walk.md / doob_bridge.py


def canon(coords):
    """Canonical key of a Z^4 point under the walk's symmetry: sorted |coords|."""
    return tuple(sorted(abs(c) for c in coords))


def neighbors(c):
    """The 8 neighbors of a canonical state c (sorted 4-tuple of abs values), each as a
    canonical key. Stepping +-e on a slot of abs value a: a>0 -> {a+1, a-1}; a=0 -> {1,1}."""
    out = []
    for i in range(4):
        a = c[i]
        if a > 0:
            steps = (a + 1, a - 1)
        else:
            steps = (1, 1)
        for s in steps:
            nc = list(c)
            nc[i] = s
            out.append(tuple(sorted(nc)))
    return out


def hitting(radius: int, tol: float = 1e-13, max_sweeps: int = 20000):
    """Value-iterate the hitting probability of {0} on the l1-ball of the given radius.
    Returns a dict canonical-state -> h. h[(0,0,0,0)] = 1 is the source; states beyond
    the radius are 0 (absorbing exit)."""
    # enumerate canonical states with sum <= radius
    states = []
    for a in range(radius + 1):
        for b in range(a, radius + 1 - a):
            for cc in range(b, radius + 1 - a - b):
                for d in range(cc, radius + 1 - a - b - cc):
                    states.append((a, b, cc, d))
    states = [s for s in states if sum(s) <= radius]
    h = {s: 0.0 for s in states}
    origin = (0, 0, 0, 0)
    h[origin] = 1.0
    nbr = {s: neighbors(s) for s in states if s != origin}
    for sweep in range(max_sweeps):
        delta = 0.0
        for s in states:
            if s == origin:
                continue
            acc = 0.0
            for nc in nbr[s]:
                if sum(nc) <= radius:
                    acc += h.get(nc, 0.0)
            val = acc / 8.0
            d = abs(val - h[s])
            if d > delta:
                delta = d
            h[s] = val
        if delta < tol:
            break
    return h, sweep + 1


def main():
    print("Per-charge expand/contract amplitude -- converged hitting probability")
    print("(Lumina_QLF.md sec 13; eight-twist Z^4 closure walk, value iteration, no depth cap)\n")

    print(f"{'R':>4} {'sweeps':>7} {'M(1)=h(e)':>12} {'M(2)=h(2e)':>12} {'M(3)=h(3e)':>12} "
          f"{'M(4)=h(4e)':>12}")
    results = {}
    for R in (20, 30, 40, 50):
        h, sw = hitting(R)
        def he(k):
            return h.get(tuple(sorted((k, 0, 0, 0))), 0.0)
        results[R] = [he(k) for k in range(1, 5)]
        print(f"{R:>4} {sw:>7} " + " ".join(f"{v:>12.7f}" for v in results[R]))

    M = results[50]
    print(f"\nVALIDATION: M(1) = h(e) should equal the return probability p4 = {P4_CLOSURE_WALK}")
    print(f"  computed M(1) = {M[0]:.7f}   (|diff| = {abs(M[0]-P4_CLOSURE_WALK):.2e})")
    ok = abs(M[0] - P4_CLOSURE_WALK) < 2e-4
    print(f"  -> {'MATCH, method validated against Closure_Walk.md' if ok else 'MISMATCH'}\n")

    print("Per-charge marginal surprisal  -ln[M(k+1)/M(k)]  (nats):")
    for k in range(1, 4):
        r = M[k] / M[k - 1]
        print(f"  -ln[M({k+1})/M({k})] = -ln({r:.5f}) = {-math.log(r):.5f}")
    print(f"\n4D Green's-function tail predicts M(k) ~ C/k^2, so the ratio -> (k/(k+1))^2 and")
    print(f"the marginal surprisal -> 0: the amplitude SATURATES (sublinear in ionization).")
    print(f"M(k)*k^2 (should approach a constant C):")
    print("  " + "  ".join(f"k={k}:{M[k-1]*k*k:.5f}" for k in range(1, 5)))

    print("\n" + "=" * 62)
    print("RESULT")
    print("=" * 62)
    print(f"Single free charge amplitude  M(1) = p4 = {M[0]:.6f}  (the prime-closure mass,")
    print(f"  the fraction of possibility that closes). k charges: M(k) = h(k*e), ~1/k^2.")
    print(f"No fixed per-charge bit (surprisal is not constant); effect is SUBLINEAR, not")
    print(f"superlinear -- refuting the unconverged sec-12 hint. amplitude = log 2 is FALSE;")
    print(f"the converged amplitude is the Polya return probability p4.")


if __name__ == "__main__":
    main()
