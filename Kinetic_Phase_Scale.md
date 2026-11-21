# Long-time kinetic-phase discriminator (#303 S5 / K6)

Baseline 4311aad (#304/#305 merged). S1/S2 are S-MATH; the existing signed
phase track rejects a smooth fixed-flux area action. Do not repeat these tests.
Compare the two already documented **conditional** propagation laws:
LorentzSymbol singular shell (C) and palindromic RealizableWalk trace (W).
Neither is assumed to be the physical propagation law.

For a fixed positive radial wave number r and unit spatial vector n, set
p = r n. In dimensionless reference units with physical hbar fixed, define

- omega_C(a,p) = asin(sqrt(sum sin(a p_i)^2))/a (principal small-momentum shell).
- omega_W(a,p) = acos(prod cos(a p_i))/a (principal massless walk branch).

The kinetic phase would be p.x - t omega, not the Euclidean log census.
We independently vary the radial momentum, not just the value of the phase.
Let J(n) = sum_{i<j} n_i^2 n_j^2. Taylor expansion at fixed r>0 predicts

omega_C = r + a^2 r^3 J/3 + O(a^4),
omega_W = r - a^2 r^3 J/6 + O(a^4).

The difference is a^2 r^3 J/2 + O(a^4); its radial derivative is
3 a^2 r^2 J/2 + O(a^4) by differentiating the analytic expansions at r>0.
The two formulas agree on an axis, while a finite face/body diagonal
difference survives in phase at t=a^(-2), even though frequencies converge
at fixed t. This tests joint large-time/coarse-graining scaling; it does
not prove stationary-phase concentration of an actual QLF amplitude.

## Frozen numerical controls

Use normalized axis, face diagonal and body diagonal; r in {0.5,1,2};
a in {1/8,1/16,1/32,1/64,1/128,1/256}. Evaluate both frequencies and analytic
radial group derivatives directly, using a stable half-angle expression for
the walk. Retain both independent coefficients, their long-time phase
difference and its derivative. At a=1/256 each scaled difference must match
the stated coefficient within absolute 0.0005, and both axis differences must
vanish within 0.0005. Do not discard any failure or adapt the threshold.

A nonzero off-axis discriminator means the common leading continuum symbol
alone cannot select a unique kinetic phase over this longer regime. A physical
propagator derived from the substrate, an identified scaling window, a regular
wave-packet measure and control of competing saddles/doublers remain necessary.
No new axiom, Lean proof, observational claim or S-PHYS promotion.

## Evidence

Pending.
