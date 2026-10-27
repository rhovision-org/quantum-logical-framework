"""
global_constraint_epochs.py -- Lombriser's global constraint, read as "closed so far".

Companion to Cosmological_Constant.md sec 5.9 (pre-registered 2026-10-27) and
lean/QLF_GlobalConstraint.lean. Pure Python, no numpy.

Lombriser (Phys. Lett. B 2019, arXiv:1901.08588) varies the action with respect to the Planck
mass as a global variable and gets M_p^2 Lambda = <T>/2, with <T> the four-volume average of the
matter trace (in his convention <T> = <rho_m> for dust). His average runs over the whole
four-volume, future included. Closure is irrevocable and the future is not yet synthesized, so the
reading QLF can use averages over what has closed so far:

    rho_Lambda(t) = (1/2) * int_0^t rho_m a^3 dt' / int_0^t a^3 dt'.

Comoving matter is conserved (rho_m a^3 = rho0), so the numerator is rho0 * t exactly. Radiation
is traceless and does not enter <T>. Units: M_p = 1 (3 H^2 = rho_total), rho0 = 1, a = 1 today,
with today fixed only by the radiation-to-matter ratio Omega_r0/Omega_m0 (Planck 2018) -- no value
of Omega_Lambda enters.

Pre-registered kill: Omega_Lambda > 0.06 at recombination (z = 1100; Doran & Robbers 2006).
Pass: Omega_Lambda(z=1100) < 0.06 and today's Omega_Lambda within 3 sigma of 0.685 +/- 0.007.
"""
import math

OMR0, OMM0 = 9.1e-5, 0.315      # Planck 2018 (h = 0.674); only their ratio is used
RHO0 = 1.0                       # comoving matter density, a = 1 today
R0 = OMR0 / OMM0                 # comoving radiation density, so a_eq = R0


def densities(t, a, D):
    rm = RHO0 / a**3
    rr = R0 / a**4
    rl = 0.5 * RHO0 * t / D       # (1/2) <rho_m>_t, closed-so-far average
    return rm, rr, rl


def hubble(t, a, D):
    return math.sqrt(sum(densities(t, a, D)) / 3.0)


def deriv(lnt, y):
    t = math.exp(lnt)
    a, D = y
    return (t * a * hubble(t, a, D), t * a**3)


def run(steps_per_efold=400):
    # start deep in the radiation era: a = (4 R0 / 3)^(1/4) t^(1/2), D = int a^3 dt
    t = 1e-16
    c = (4.0 * R0 / 3.0) ** 0.25
    a = c * math.sqrt(t)
    D = c**3 * t**2.5 / 2.5
    lnt, h = math.log(t), 1.0 / steps_per_efold
    out = []
    while a < 1.0:
        y = (a, D)
        k1 = deriv(lnt, y)
        k2 = deriv(lnt + h / 2, [y[i] + h / 2 * k1[i] for i in range(2)])
        k3 = deriv(lnt + h / 2, [y[i] + h / 2 * k2[i] for i in range(2)])
        k4 = deriv(lnt + h, [y[i] + h * k3[i] for i in range(2)])
        a, D = [y[i] + h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]) for i in range(2)]
        lnt += h
        t = math.exp(lnt)
        rm, rr, rl = densities(t, a, D)
        out.append((t, a, hubble(t, a, D), rm, rr, rl))
    return out


def at_scale(rows, a_target):
    return min(rows, key=lambda r: abs(math.log(r[1] / a_target)))


def decel(rows, i):
    # q = -1 - dlnH/dlna, central difference
    (_, a1, H1, *_), (_, a2, H2, *_) = rows[i - 1], rows[i + 1]
    return -1.0 - (math.log(H2) - math.log(H1)) / (math.log(a2) - math.log(a1))


if __name__ == "__main__":
    rows = run()
    print("closed-so-far reading of Lombriser's constraint: rho_L(t) = <rho_m>_t / 2\n")
    print(f"{'z':>8} {'Omega_m':>9} {'Omega_r':>9} {'Omega_L':>9} {'rho_L/rho_m':>12} {'q':>7}")
    for z in (1e5, 3400.0, 1100.0, 10.0, 2.0, 0.0):
        r = at_scale(rows, 1.0 / (1.0 + z))
        i = rows.index(r)
        i = min(max(i, 1), len(rows) - 2)
        tot = r[3] + r[4] + r[5]
        print(f"{z:>8g} {r[3]/tot:>9.4f} {r[4]/tot:>9.4f} {r[5]/tot:>9.4f} "
              f"{r[5]/r[3]:>12.4f} {decel(rows, i):>7.3f}")
    rec = at_scale(rows, 1.0 / 1101.0)
    today = rows[-1]
    oml_rec = rec[5] / (rec[3] + rec[4] + rec[5])
    oml_now = today[5] / (today[3] + today[4] + today[5])
    print(f"\nOmega_L(z=1100) = {oml_rec:.4f}   (kill if > 0.06)")
    print(f"Omega_L(today)  = {oml_now:.4f}   (pass needs 0.664 .. 0.706)")
    print("verdict:", "PASS" if oml_rec < 0.06 and abs(oml_now - 0.685) < 0.021 else "FAIL")
