#!/usr/bin/env python3
"""
structure_growth_qlf.py -- the critical-contraction growth test of Lumina_QLF.md sec 7.

A spherical baryon lump contracts locally under QLF's closure balance
(g^2 = g_bar (g + a0), a0 = c H(t) / 2 pi; QLF_DarkMatter.radialAccel) while the measured global
expansion (Planck 2018 flat LCDM H(z), taken as data) carries it outward. The model and the kill
conditions were committed before this script was run (Lumina_QLF.md sec 7):

  K1  M = 1e10 Msun, delta_i = 1e-5 at z = 1100 collapses before z = 10.
  K2  comoving radius 50 Mpc, delta_i = 1e-5 does not turn around before z = 0.

Units: kpc, Gyr, Msun. Pure Python, a few seconds.
"""
import math

G = 4.4985e-6                    # kpc^3 / (Msun Gyr^2)
C = 299792.458 * 1.0227          # kpc / Gyr
H0 = 67.4 * 1.0227e-3            # 1 / Gyr
OM, OB, OR = 0.315, 0.0493, 9.1e-5
OL = 1 - OM - OR
RHO_CRIT0 = 3 * H0 ** 2 / (8 * math.pi * G)
RHO_B0 = OB * RHO_CRIT0
Z_I = 1100.0


def E(a):
    return math.sqrt(OM / a ** 3 + OR / a ** 4 + OL)


def addot_over_a(a):
    return H0 ** 2 * (-OM / (2 * a ** 3) - OR / a ** 4 + OL)


def radial_accel(g_bar, a0):
    """QLF_DarkMatter.radialAccel: positive root of g^2 = g_bar (g + a0)."""
    return (g_bar + math.sqrt(g_bar * g_bar + 4 * g_bar * a0)) / 2


def run(M=None, x_com=None, delta_i=1e-5, qlf=True, eta=2e-3):
    """Integrate one shell from z = 1100. Give the baryon mass M (Msun) or comoving radius x (kpc)."""
    if M is None:
        M = 4 * math.pi / 3 * RHO_B0 * x_com ** 3 * (1 + delta_i)
    x = (M / (4 * math.pi / 3 * RHO_B0 * (1 + delta_i))) ** (1 / 3)
    a = 1 / (1 + Z_I)
    R = a * x
    V = H0 * E(a) * R
    z_ta = z_coll = None
    R_max = R

    def deriv(a, R, V):
        H = H0 * E(a)
        gN = G * M / R ** 2 - 4 * math.pi * G / 3 * (RHO_B0 / a ** 3) * R
        if qlf:
            a0 = C * H / (2 * math.pi)
            g = math.copysign(radial_accel(abs(gN), a0), gN)
        else:
            g = gN
        return a * H, V, addot_over_a(a) * R - g

    while a < 1.0:
        da, dR, dV = deriv(a, R, V)
        dt = eta * min(1 / (H0 * E(a)), abs(R / V) if V else 1e9, math.sqrt(R / max(abs(dV), 1e-300)))
        k1 = (da, dR, dV)
        k2 = deriv(a + dt / 2 * k1[0], R + dt / 2 * k1[1], V + dt / 2 * k1[2])
        k3 = deriv(a + dt / 2 * k2[0], R + dt / 2 * k2[1], V + dt / 2 * k2[2])
        k4 = deriv(a + dt * k3[0], R + dt * k3[1], V + dt * k3[2])
        a += dt / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0])
        Rn = R + dt / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])
        Vn = V + dt / 6 * (k1[2] + 2 * k2[2] + 2 * k3[2] + k4[2])
        if z_ta is None and V > 0 >= Vn:
            z_ta = 1 / a - 1
        R, V = Rn, Vn
        R_max = max(R_max, R)
        if R <= 1e-3 * R_max or R <= 0:
            z_coll = 1 / a - 1
            break
    # linear-theory overdensity at the end if never collapsed: delta = (x a / R)^3 (1+delta_i) - 1
    delta_end = (x * a / R) ** 3 * (1 + delta_i) - 1 if z_coll is None else float("inf")
    return dict(M=M, x=x, z_ta=z_ta, z_coll=z_coll, delta_end=delta_end, a_end=a)


def fmt(r):
    ta = f"{r['z_ta']:.2f}" if r["z_ta"] is not None else "never"
    co = f"{r['z_coll']:.2f}" if r["z_coll"] is not None else "never"
    de = f"{r['delta_end']:.3g}" if r["z_coll"] is None else "-"
    return f"{r['M']:10.2e} {r['x'] / 1000:9.3f} {ta:>9} {co:>9} {de:>10}"


def main():
    print("Critical contraction vs global expansion (Lumina_QLF.md sec 7)")
    print(f"start z = {Z_I:.0f}; global H(z) = Planck 2018 LCDM; Omega_b = {OB}\n")
    hdr = f"{'M [Msun]':>10} {'x [cMpc]':>9} {'z_ta':>9} {'z_coll':>9} {'delta(z=0)':>10}"
    cases = [dict(M=m) for m in (1e8, 1e10, 1e12, 1e14)] + [dict(x_com=50000.0)]
    results = {}
    for di in (1e-5, 1e-4):
        for qlf in (True, False):
            print(f"{'QLF closure balance' if qlf else 'control: Newton, baryons only'}, delta_i = {di:g}")
            print("  " + hdr)
            for c in cases:
                r = run(delta_i=di, qlf=qlf, **c)
                results[(di, qlf, c.get("M"), c.get("x_com"))] = r
                print("  " + fmt(r))
            print()

    k1 = results[(1e-5, True, 1e10, None)]
    k2 = results[(1e-5, True, None, 50000.0)]
    p1 = k1["z_coll"] is not None and k1["z_coll"] > 10
    p2 = k2["z_ta"] is None
    print("Pre-registered verdict")
    print(f"  K1 (1e10 Msun collapses before z = 10): z_coll = {k1['z_coll']}  ->  {'PASS' if p1 else 'FAIL'}")
    print(f"  K2 (50 cMpc does not turn around by z = 0): z_ta = {k2['z_ta']}  ->  {'PASS' if p2 else 'FAIL'}")


if __name__ == "__main__":
    main()
