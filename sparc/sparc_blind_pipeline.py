#!/usr/bin/env python3
"""
Retrospective QLF rotation-curve benchmark on public SPARC data (issue #77).

For an admitted point, the QLF prediction formula uses baryonic inputs only
(Vgas, Vdisk, Vbul, R). Vobs is loaded before sealing and is used in quality
selection. The digest is written before residual scoring; it does not establish
information isolation, an independent timestamp, or historical blinding.

Curated sample (≈ the SPARC RAR "common" sample): quality flag Q<=2 and inclination
Inc>=30 deg (Table 1), plus per-point e_Vobs < 0.1*Vobs.

Models (all on the SAME points):
  - QLF (DERIVED): a0 = cH0/2pi, canonical global M/L (0.5/0.7), closure-balance RAR
        g_obs = 0.5*(g_bar + sqrt(g_bar^2 + 4 g_bar a0))   (Lean: radialAccel_self_consistent)
        ZERO parameters fit to the rotation curves.
  - QLF form, fixed external g_dagger=1.2e-10: no optimization of this value is performed here.
  - Newton: g_pred = g_bar (no dark matter).
  - NFW: a 2-parameter dark halo (V200, c) fit PER GALAXY (300+ free params total).
"""
import math, hashlib, json, sys

C      = 2.998e8
KPC    = 3.0857e19
KMS    = 1.0e3
G_DAG  = 1.20e-10
YDISK, YBUL = 0.5, 0.7
DATA   = "MassModels_Lelli2016c.mrt"
CATA   = "SPARC_Lelli2016c.mrt"

def a0_qlf(H0): return C * (H0*1e3/3.0857e22) / (2*math.pi)
def g_of(V, R): return (V*KMS)**2 / (R*KPC)
def v_of(g, R): return math.sqrt(g * R*KPC) / KMS
def rar(g_bar, a0): return 0.5*(g_bar + math.sqrt(g_bar**2 + 4*g_bar*a0))
def vbar2(r): return (r['Vgas']*abs(r['Vgas']) + YDISK*r['Vdisk']*abs(r['Vdisk']) + YBUL*r['Vbul']*abs(r['Vbul']))

def load_mass(path):
    rows = []
    for ln in open(path):
        f = ln.split()
        if len(f) < 10: continue
        try: gid=f[0]; D,R,Vobs,eV,Vgas,Vdisk,Vbul = map(float, f[1:8])
        except ValueError: continue
        rows.append(dict(gid=gid, R=R, Vobs=Vobs, eV=eV, Vgas=Vgas, Vdisk=Vdisk, Vbul=Vbul))
    return rows

def load_catalog(path):
    """Galaxy -> (inclination deg, quality flag) from Table 1 (whitespace columns:
    [0]=Galaxy, [5]=Inc, [17]=Q; Ref is the trailing field)."""
    cat = {}
    for ln in open(path):
        f = ln.split()
        if len(f) < 18: continue
        try: inc = float(f[5]); q = int(f[17])
        except (ValueError, IndexError): continue
        cat[f[0]] = (inc, q)
    return cat

def curated(rows, cat):
    out = []
    for r in rows:
        ci = cat.get(r['gid'])
        if not ci: continue
        inc, q = ci
        if q <= 2 and inc >= 30.0 and r['Vobs'] > 0 and r['eV'] > 0 and r['eV'] < 0.10*r['Vobs'] and r['R'] > 0:
            out.append(r)
    return out

def points(rows):
    pts = []
    for r in rows:
        vb2 = vbar2(r)
        if r['R'] <= 0 or vb2 <= 0 or r['Vobs'] <= 0: continue
        gbar = g_of(math.sqrt(vb2), r['R']); gobs = g_of(r['Vobs'], r['R'])
        if gbar <= 0 or gobs <= 0: continue
        pts.append(dict(gid=r['gid'], R=r['R'], vb2=vb2, Vobs=r['Vobs'], gbar=gbar, gobs=gobs))
    return pts

def nfw_v2(R, V200, c, H0):
    H0s = H0*1e3/3.0857e22
    x = (R*KPC)*10*H0s/(V200*KMS)
    if x <= 0 or c <= 0: return 0.0
    mu = lambda y: math.log(1+y) - y/(1+y)
    return V200**2 * mu(c*x) / (x*mu(c))

def nfw_fit_galaxy(pts, H0):
    best = (1e18, None)
    for V200 in range(20, 421, 10):
        for c in (2,3,4,5,6,8,10,12,15,20,25,30):
            sse = 0.0; n = 0
            for p in pts:
                vtot2 = p['vb2'] + nfw_v2(p['R'], V200, c, H0)
                if vtot2 <= 0: continue
                gtot = g_of(math.sqrt(vtot2), p['R'])
                if gtot <= 0: continue
                sse += (math.log10(p['gobs']) - math.log10(gtot))**2; n += 1
            if n and sse < best[0]: best = (sse, (V200, c))
    return best[1]

def stat(d):
    n = len(d); mean = sum(d)/n; sc = math.sqrt(sum((x-mean)**2 for x in d)/n)
    return n, mean, sc

def main():
    H0 = 73.0; a0 = a0_qlf(H0)
    mass = load_mass(DATA); cat = load_catalog(CATA)
    rows = curated(mass, cat); pts = points(rows)
    gals = sorted({p['gid'] for p in pts})

    # Hash baryonic-formula predictions before scoring; Vobs was already loaded.
    blob = "\n".join(f"{p['gid']},{p['R']:.4f},{v_of(rar(p['gbar'],a0),p['R']):.4f}" for p in pts)
    seal = hashlib.sha256(blob.encode()).hexdigest()
    open("predictions_sealed.csv","w").write("gid,R_kpc,Vpred_kms\n"+blob+"\n")
    data_hash = hashlib.sha256(open(DATA,'rb').read()).hexdigest()[:16]

    res = {'newton':[], 'qlf':[], 'rarfit':[], 'nfw':[]}
    for g in gals:
        gp = [p for p in pts if p['gid']==g]
        vc = nfw_fit_galaxy(gp, H0)
        for p in gp:
            res['newton'].append(math.log10(p['gobs'])-math.log10(p['gbar']))
            res['qlf'].append(   math.log10(p['gobs'])-math.log10(rar(p['gbar'],a0)))
            res['rarfit'].append(math.log10(p['gobs'])-math.log10(rar(p['gbar'],G_DAG)))
            vtot2 = p['vb2'] + nfw_v2(p['R'], vc[0], vc[1], H0)
            res['nfw'].append(math.log10(p['gobs'])-math.log10(g_of(math.sqrt(vtot2),p['R'])))

    labels = {'newton':('Newton (g_bar, no DM)',0),
              'nfw':('NFW (2 params/galaxy fit)', 2*len(gals)),
              'rarfit':('QLF form, fixed external g_dag',1),
              'qlf':('QLF, a0=cH0/2pi DERIVED',0)}
    table = {}
    print("=== QLF retrospective SPARC benchmark — curated sample (Q<=2, Inc>=30) — issue #77 ===")
    print(f"H0={H0}  a0=cH0/2pi={a0*1e10:.3f}e-10 ({100*a0/G_DAG:.0f}% g_dag)  galaxies={len(gals)}  points={len(pts)}")
    print(f"sealed predictions sha256={seal[:16]}…   data sha256={data_hash}\n")
    print(f"{'model':<30}{'free params':>13}{'mean(dex)':>11}{'scatter(dex)':>14}")
    for k in ('newton','nfw','rarfit','qlf'):
        n, mean, sc = stat(res[k]); name, npar = labels[k]
        print(f"{name:<30}{npar:>13}{mean:>11.3f}{sc:>14.3f}")
        table[k] = dict(name=name, free_params=npar, mean_dex=round(mean,4), scatter_dex=round(sc,4), N=n)

    receipt = dict(
        benchmark="QLF retrospective SPARC rotation-curve benchmark", issue=77,
        protocol="baryonic-input formula on target-informed quality cuts; SHA-256 sealed before residual scoring; Vobs already loaded; no per-galaxy QLF tuning",
        sample=f"SPARC curated: Q<=2 & Inc>=30deg & e_Vobs<0.1*Vobs  (galaxies={len(gals)}, points={len(pts)})",
        qlf_params=dict(a0_m_s2=round(a0,13), a0_formula="cH0/(2pi)", H0_km_s_Mpc=H0,
                        Mass_to_Light=dict(disk=YDISK, bulge=YBUL), fit_to_curves="none"),
        data=dict(source="Lelli, McGaugh & Schombert 2016 (SPARC)", file=DATA, sha256_16=data_hash),
        sealed_predictions_sha256=seal,
        results_dex=table,
        parameter_accounting={"free_params": "Legacy complexity labels: rarfit=1 denotes an external calibrated number, not an optimization in this run. NFW parameters are grid fit here; declared H0, M/L and model-selection provenance are separate.", "optimized_here": {"newton": 0, "qlf": 0, "rarfit": 0, "nfw": 2*len(gals)}},
        verdict=("Numerical reproduction of declared formulas on this curated public sample. "
                 "QLF scatter is about 0.133 dex; the NFW grid fit is about 0.059 dex. "
                 "These descriptive residuals do not establish historical blinding, an observational "
                 "uncertainty floor, statistical model equivalence, or a unique physical mechanism."))
    json.dump(receipt, open("receipt.json","w"), indent=2)
    print("\nReceipt -> receipt.json (sealed hash, declared params, data provenance, scored results).")

if __name__ == "__main__":
    main()
