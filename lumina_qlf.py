#!/usr/bin/env python3
"""
lumina_qlf.py -- the numbers behind Lumina_QLF.md (QLF against the Lumina reionization simulation).

Lumina (Zier et al. 2026, arXiv:2605.15310; MNRAS 552, DOI 10.1093/mnras/stag1469): AREPO moving mesh,
IllustrisTNG galaxy model, GPU M1 radiation transport in six frequency bins, 500 cMpc box, 2 x 6000^3
resolution elements. HI reionization ends z ~ 5.2 (neutral patches to z ~ 4.75), HeII (AGN-driven)
nearly complete by z = 3. Light-cone CMB optical depth <tau_LOS> = 0.0550, sightline scatter >= 5%
(arXiv:2605.18939).

Five computations, pure Python, no fitted parameter:
  1. Expansion history over Lumina's window: LCDM vs QLF dark-energy readings A and C
     (Cosmological_Constant.md sec 5.7; reading C reuses omega_lambda_epochs.py).
  2. a0(z) = c H(z) / 2 pi (DarkMatter.md sec 5c expansion clock) across Lumina's window.
  3. The mass discrepancy that QLF's closure-balance law (QLF_DarkMatter.radialAccel) implies for the
     six JADES galaxies of de Graaff et al. 2024 (A&A 684, A87). POST HOC: the data were seen first.
  4. Thomson optical depth: how far QLF's alpha (w = 1/2: 1/alpha = 137.032) moves tau.
  5. Electrons per hydrogen nucleus from QLF_Nucleosynthesis' Y_p = 1/4 funnel.
"""
import math

from omega_lambda_epochs import LOG2, OMR0, hde_event_horizon, interp

OM = 0.315                      # Planck 2018
H0_PLANCK = 67.4                # km/s/Mpc
H0_SPARC = 72.9                 # the H0 at which cH0/2pi equals SPARC's a0 (DarkMatter.md)
A0_MOND = 1.2e-10               # m/s^2, standard constant a0
C_SI = 2.99792458e8
MPC = 3.0856775814913673e22     # m
KPC = MPC / 1000
G_SI = 6.674e-11
MSUN = 1.989e30
GYR_PER_INV_H0 = 977.8          # 1/H0 in Gyr for H0 = 1 km/s/Mpc
Z_WINDOW = [3.0, 4.75, 5.2, 6.0, 8.0, 10.0]


def E_lcdm(z):
    return math.sqrt(OM * (1 + z) ** 3 + OMR0 * (1 + z) ** 4 + (1 - OM - OMR0))


def integrate(f, a, b, n=4000):
    h = (b - a) / n
    s = f(a) + f(b)
    for i in range(1, n):
        s += (4 if i % 2 else 2) * f(a + i * h)
    return s * h / 3


def age_gyr(E, z, h0=H0_PLANCK):
    """Cosmic age at z for expansion E(z) = H/H0: t = int_z^inf dz' / ((1+z') H)."""
    # substitute u = ln(1+z); integrand dt = du / H
    u0, u1 = math.log(1 + z), math.log(1 + 1e7)
    return integrate(lambda u: 1 / E(math.exp(u) - 1), u0, u1) * GYR_PER_INV_H0 / h0


def a0_of_z(z, h0):
    return C_SI * h0 * 1000 / MPC * E_lcdm(z) / (2 * math.pi)


def angular_diameter_kpc_per_arcsec(z):
    dc = integrate(lambda zz: 1 / E_lcdm(zz), 0, z) * C_SI / 1000 / H0_PLANCK  # Mpc
    da = dc / (1 + z)
    return da * 1000 * math.pi / (180 * 3600)


def main():
    print("1. Expansion over Lumina's window (z = 3 .. 10)")
    # Reading A: rho_L = log2 * rho_crit at every epoch, matter conserved => H^2 (1 - log2) = H_m^2.
    # Holding today's H0 and Omega_m = 1 - log2: E_A(z) = (1+z)^1.5 (matter-like), radiation aside.
    E_A = lambda z: math.sqrt((1 + z) ** 3 + OMR0 / (1 - LOG2) * (1 + z) ** 4)
    tr = hde_event_horizon(LOG2)
    E_C = lambda z: math.exp(interp(tr, z)[1])
    print(f"   {'z':>5} {'t_LCDM':>8} {'t_A':>7} {'H_A/H_LCDM':>11} {'Om_de C':>9} "
          f"{'H_C/H_LCDM':>11} {'Om_L LCDM':>10}")
    for z in Z_WINDOW:
        om_c = interp(tr, z)[0]
        om_l = (1 - OM - OMR0) / E_lcdm(z) ** 2
        print(f"   {z:5.2f} {age_gyr(E_lcdm, z):8.3f} {age_gyr(E_A, z):7.3f} "
              f"{E_A(z) / E_lcdm(z):11.3f} {om_c:9.2e} {E_C(z) / E_lcdm(z):11.4f} {om_l:10.2e}")
    print("   (t in Gyr at H0 = 67.4; reading A keeps Omega_L = log 2 at every epoch, reading C is the")
    print("    future-event-horizon HDE with C^2 = log 2, normalized to Omega_de(0) = log 2)\n")

    print("2. a0(z) = c H(z) / 2 pi  [1e-10 m/s^2]")
    print(f"   {'z':>5} {'H(z)/H0':>8} {'a0 @67.4':>9} {'a0 @72.9':>9}")
    for z in [0.0] + Z_WINDOW:
        print(f"   {z:5.2f} {E_lcdm(z):8.3f} {a0_of_z(z, H0_PLANCK) / 1e-10:9.2f} "
              f"{a0_of_z(z, H0_SPARC) / 1e-10:9.2f}")
    print()

    print("3. JADES z = 5.5-7.4 kinematics (de Graaff et al. 2024, Table 3) -- POST HOC")
    print("   g_obs = G M_dyn / (k_tot r_e^2), k_tot = 1.8 (their Eq. 4). QLF closure balance")
    print("   g_obs^2 = g_bar (g_obs + a0)  =>  M_dyn / M_bar = g_obs / g_bar = 1 + a0 / g_obs.")
    print("   Observed (paper): M_dyn / M_bar ~ 3 (3-4 for all but one object).")
    gals = [  # id, z, r_e arcsec, log M_dyn
        ("NS-00016745", 5.566, 0.32, 10.23),
        ("NS-00019606", 5.890, 0.117, 9.17),
        ("NS-00022251", 5.799, 0.122, 9.23),
        ("NS-00047100", 7.432, 0.130, 9.85),
        ("NS-10016374", 5.504, 0.084, 9.45),
        ("NS-20086025", 7.263, 0.36, 10.31),
    ]
    print(f"   {'galaxy':>12} {'z':>6} {'r_e kpc':>8} {'g_obs':>7} {'QLF@67.4':>9} {'QLF@72.9':>9} "
          f"{'MOND':>6}")
    preds = []
    for gid, z, re_as, lmd in gals:
        r = re_as * angular_diameter_kpc_per_arcsec(z) * KPC
        g = G_SI * 10 ** lmd * MSUN / (1.8 * r ** 2)
        q1 = 1 + a0_of_z(z, H0_PLANCK) / g
        q2 = 1 + a0_of_z(z, H0_SPARC) / g
        qm = 1 + A0_MOND / g
        preds.append(q1)
        print(f"   {gid:>12} {z:6.3f} {r / KPC:8.2f} {g / 1e-10:7.2f} {q1:9.2f} {q2:9.2f} {qm:6.2f}")
    preds.sort()
    print(f"   median QLF@67.4 prediction: {(preds[2] + preds[3]) / 2:.2f}  (g in 1e-10 m/s^2)\n")

    print("4. Thomson optical depth: sigma_T = (8 pi / 3) r_e^2 with r_e = alpha hbar / (m_e c)")
    a_meas, a_qlf = 137.035999177, 137.032
    rel = (a_meas / a_qlf) ** 2 - 1
    print(f"   1/alpha 137.032 (QLF, w = 1/2) vs 137.035999 (CODATA 2022): d sigma_T / sigma_T = {rel:.2e}")
    print(f"   on <tau_LOS> = 0.0550 that is d tau = {0.0550 * rel:.1e}; sightline scatter >= 5% = "
          f"{0.05 * 0.0550:.1e}; Planck sigma(tau) ~ 7e-3\n")

    print("5. Electrons per H nucleus from Y_p = 2r/(1+r), r = 1/7 => Y_p = 1/4")
    Y = 2 * (1 / 7) / (1 + 1 / 7)
    y = Y / (4 * (1 - Y))
    print(f"   Y_p = {Y:.4f}; n_He / n_H = Y / (4 (1 - Y)) = {y:.4f}")
    print(f"   n_e / n_H: HII only 1, + HeII {1 + y:.4f}, + HeIII {1 + 2 * y:.4f}"
          f"  (HeIII is {y / (1 + 2 * y) * 100:.1f}% of the final electrons)")


if __name__ == "__main__":
    main()
