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

All 54 preregistered comparisons were executed (three directions, three radii, six scales). At a=1/256 the largest absolute discrepancy across all tested scaled coefficients and derivatives was 6.217e-5, below the frozen 5e-4 tolerance. At r=1 the scaled frequency difference t(omega_C-omega_W) was 0 on axis, 0.1250005961 on the face diagonal and 0.1666674437 on the body diagonal; its radial derivative was respectively 0, 0.3750029803 and 0.5000038854. The corresponding kinetic phase difference has the opposite sign under p.x-t omega. See `data/kinetic_phase_scale.json` for all cases and `tests/test_kinetic_phase_scale.py` for reproduction.

The discriminator passes for these two conditional candidates. Their common leading continuum symbol does not identify a unique long-time kinetic phase in the specified joint scaling. This does not select a physical propagator, establish a physical large-time scaling window, or prove S5. S-PHYS remains open.
