# Hofstadter's butterfly and QLF's closure counts

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**The question (Jim, 2026-10-28).** There is no continuum, and irrational numbers are not in reality.
What is real is the quantum logical process whose finite outputs the continuum approximates. Hofstadter's
butterfly, the energy spectrum of an electron on a lattice in a magnetic field, should therefore emerge
from that process, not from a continuum Hamiltonian.

The butterfly is a good test case because of how rational flux behaves. At flux `φ = p/q` per
plaquette, the Hofstadter problem reduces to a finite `q×q` Bloch problem with `q` bands. The operator is
also well defined at irrational flux, where at this coupling its spectrum is a Cantor set (Hofstadter 1976),
but no finite magnetic unit cell describes it: irrational flux is reached as the infinite, quasiperiodic
limit. So the question is which parts of the butterfly QLF's closures produce as counts, and which parts
are a rendering.

## 1. The process

One spatial plane of the substrate uses two twist axes, `>`/`<` and `^`/`v`. A **closure** on that plane is
a twist history with zero net displacement on both axes, which is a closed walk on `ℤ²`
([Closure_Walk.md](Closure_Walk.md)). Put a phase `ζ_q^{p}` (with `ζ_q` a primitive `q`-th root of unity)
on every plaquette. A closed walk then carries `ζ_q^{p·A}`, where `A` is its signed enclosed area. The
**flux census** at length `L` is

```
M_L(p/q) = Σ over closures of length L, starting at the origin, of ζ_q^{p·A}
```

This is a finite exact count: the number `c_k` of closures with `p·A ≡ k (mod q)`, for each `k`. Nothing in
it is a real number. `M_L` is a cyclotomic integer, the count vector `(c_0, …, c_{q−1})` read in `ℤ[ζ_q]`.

QLF has already proved two such phases, without choosing them to match anything:

- **The half-spin phase is a π flux.** The fold sign is a `ℤ₂` connection with flux `−1` through every
  mixed spatial plaquette (`fold_eq_connectionPhase`, plaquette fluxes decided in
  [`QLF_EdgeSign`](lean/QLF_EdgeSign.lean); [closure_walk.py](closure_walk.py) `edge_sign`). On a plane
  that is `φ = 1/2`, up to the twist's own sign.
- **The colour transport is a 2π/3 flux.** With the axis cycle as a transport primitive, a colour line
  around any plaquette picks up `ω^{−1}` (`colour_plaquette`, [`QLF_ColourFlux`](lean/QLF_ColourFlux.lean);
  [colour_flux.py](colour_flux.py)). On a plane that is `φ = 1/3`, up to orientation.

## 2. Pre-registration (frozen in the commit that adds this section, before any computation)

The script [hofstadter_closure.py](hofstadter_closure.py) will compute the flux census exactly, by dynamic
programming over (position, area mod `q`), and compare it with independent constructions.

| Test | Statement | Can it fail? |
|---|---|---|
| **H1** | For every `p/q` with `q ≤ 8` and every even `L ≤ 16`, the flux census equals the moment `(1/q)⟨Tr H(k)^L⟩` of the `q×q` Harper (Bloch) matrix, to `10⁻⁹` | **No, if the code is right.** This is the trace formula; it is a check of the code, not evidence |
| **H2** | QLF's own edge-sign census on the `>`/`^` plane equals `(−1)^{L/2}·M_L(1/2)` for every even `L ≤ 20` | **Yes.** It fails if the proved fold sign is not a uniform π flux on the plane, or if the twist-sign factor is not `(−1)^{L/2}` |
| **H3** | QLF's colour transport (Weyl displacements through the explicit cocycle in `colour_flux.py`, on `colVec` of `>` and `^`) gives the census `M_L(1/3)` for every even `L ≤ 20` | **Yes.** It fails if the colour holonomy of a closed walk is not `ω^{±A}` |
| **H4** | The census `M_L(p/q)` is an ordinary integer for every `L` when `q ∈ {1, 2, 3, 4, 6}`, and is not an integer for some `L ≤ 16` when `q ∈ {5, 7, 8}` | Expected from Niven's theorem (`cos 2πp/q` is rational only for those `q`). It is bookkeeping by rule 4 and is recorded because it answers a different question (§4) |
| **H5** | The butterfly drawn from the census's transfer operator, for all `p/q` with `q ≤ 40`, has `q` bands at `φ = p/q`, is symmetric under `φ → 1 − φ` and `E → −E`, and has total band width falling as `q` grows | A rendering check, not evidence |

**Kill conditions.** A failure of H2 or H3 means the proved QLF phases are not the Hofstadter fluxes they
appear to be, and the identification in §1 is withdrawn. A failure of H1 means the code is wrong.

**What would not count.** Agreement of H1 or H5 adds no evidence. Only H2 and H3 test QLF.

## 3. Results

Run: `python3 hofstadter_closure.py --svg hofstadter_butterfly.svg` (about 5 s). It exits 0 only if
H1–H4 and H5's band and symmetry clauses pass. **H1–H4 pass. H5 passes on bands and symmetry and fails
on its width clause as registered** (below). H5 was registered as a rendering check that adds no
evidence, so the width failure does not touch the H2/H3 result. It is recorded because the registration
said it would hold, and it does not.

| Test | Result |
|---|---|
| **H1** (code check) | Census equals the Harper moments for every `p/q`, `q ≤ 8`, `L ≤ 16`. Largest relative difference `5×10⁻¹⁴` |
| **H2** (tests `QLF_EdgeSign`) | **Pass, exact, every even `L ≤ 20`.** QLF's fold-sign census on one spatial plane is `1, −4, 20, −112, 676, …, 68 906 320`, which is `(−1)^{L/2}` times the π-flux Hofstadter census at each checked length. The `(−1)^{L/2}` is the twists' own sign: a closure has `L/2` negative steps |
| **H3** (tests `QLF_ColourFlux`) | **Pass, exact, every even `L ≤ 20`.** Transporting a colour line with the explicit Weyl matrices gives counts `(n₀, n₁, n₂)` of closures with holonomy `ω⁰, ω¹, ω²`. Always `n₁ = n₂`, and `n₀ − n₁ = 1, 4, 24, 148, 928, …, 72 908 224`, which is the `φ = 1/3` Hofstadter census at each checked length |
| **H4** (bookkeeping) | Census is an ordinary integer at every `L` for `q ∈ {1, 2, 3, 4, 6}`. For `q ∈ {5, 7, 8}` it is irrational from `L = 4`, the first length with an enclosed plaquette |
| **H5** (rendering) | Checked at **every** coprime `p/q` with `q ≤ 40` (`--h5-qmax`). **Bands and symmetry pass:** at every `p/q` the `q` eigenvalue bands are `q` intervals that never overlap, and the spectrum is symmetric under `φ → 1 − φ` and `E → −E`. For even `q` the two central bands touch at `E = 0` (the known Dirac point). At 44 of the `p/q` with `q ≥ 17` some gaps are below `10⁻⁶` and are not resolved as separate pieces in double precision; non-overlap still holds there. **Width, as registered, fails.** The total width does not fall for every pair: `13/14` has width `0.7020`, more than `12/13` at `0.6983`, and the largest width at `q = 26` (`0.3735`) exceeds the largest at `q = 25` (`0.3730`). The trend holds (the smallest width at each `q` falls at every step to `q = 40`, from `5.66` at `q = 2` to `0.233`), but that reading was chosen after seeing the data and is not counted |

[hofstadter_butterfly.svg](hofstadter_butterfly.svg) is the **standard Harper butterfly**, drawn by
diagonalizing the `q×q` Harper Bloch matrix for every `p/q` with `q ≤ 30`. The `q = 2` and `q = 3` lines,
the two fluxes the closure-count tests H2 and H3 identify with QLF's proved phases, are drawn in red. The
closure census enters the picture only through H1: its moments equal the Harper moments, which is the trace
formula. The spectrum is not rebuilt from the census or from a separately constructed QLF transfer
operator. (§2's H5 row calls it "drawn from the census's transfer operator". That wording was inaccurate,
and the pre-registration is left as frozen.) Building the magnetic-translation operator from the QLF phase
rule and showing it is gauge-equivalent to Harper is an open step.

**What this establishes.** The two phases QLF proved for its own reasons, the half-spin fold sign and the
colour transport, give exactly the `φ = 1/2` and `φ = 1/3` Hofstadter censuses on a spatial plane, **checked
exactly through `L = 20`**. The local plaquette theorems give the structural reason to expect this at every
length: `QLF_EdgeSign` decides a uniform `−1` flux per mixed spatial plaquette, and `colour_plaquette` gives a
uniform `ω^{−1}`. On `ℤ²`, a closed walk's holonomy under a connection with uniform plaquette flux is that
flux raised to the walk's signed area (discrete Stokes). The global statements
`holonomy(h) = (−1)^{L/2}·(−1)^{A(h)}` and `colourPhase(h) = ω^{±A(h)}` for every closed plane walk `h` are
**not yet proved** in Lean or algebraically in Python. Until they are, the identification is a finite exact
check with a structural reason behind it, not an all-length theorem. If it holds, the butterfly's two
simplest points are already in the substrate, as counts. The rest of the
butterfly (every other `p/q`) is not reached yet: it needs phases QLF has not yet derived. The result is
incomplete, not negative. The identification could have failed: a
non-uniform sign, or a colour holonomy other than `ω^{±A}`, would have broken H2 or H3.

**What it does not establish.** That electrons in a crystal *are* QLF closures, or that QLF predicts the
butterfly measured in moiré graphene (Dean et al. 2013) beyond what the standard Harper model already
does. Here QLF reproduces an established model; it does not improve on it.

## 4. What the butterfly says about irrational numbers

Three facts from the run answer the question that started this note.

1. **The process is integers.** Every census is a finite count. For QLF's two proved fluxes (`q = 2`, `3`) and their
   product (`q = 6`: the spin and colour holonomies together give `1/2 − 1/3 = 1/6`), the census is an
   ordinary integer at every length, so no irrational number enters at all. (`q = 4` is the only other
   such flux; no proved QLF phase realizes it yet.) For other fluxes the counts `c_k` are still
   integers. Only reading them as one number in `ℤ[ζ_q]` would involve an irrational. This is Niven's
   theorem, not a discovery, but it means the fluxes QLF actually generates are exactly the ones whose
   closure counting never leaves `ℤ`.
2. **The irrationals live in the rendering, as limits.** The band edges are irrational: `±2√2` at
   `φ = 1/2`, and `±(1 + √3)`, `±2`, `±(√3 − 1)` at `φ = 1/3`. Each is the limit of a ratio of integer
   counts: `M_{L+2}/M_L` is rational at every `L` and approaches the squared outer edge. At `φ = 1/3`
   it reads `6.45, 6.76, 6.95, 7.06` at `L = 10, 20, 30, 38`, heading for `(1 + √3)² = 4 + 2√3 ≈ 7.464`.
   The convergence is slow, with `2/L` corrections (the census grows like `λ^L/L`). That is a matter of depth. `L = 40` is about 120
   bits, while a physical closure carries thousands to millions, where the ratio sits within about `2/L`
   of its limit. The irrational number is the name of where a
   sequence of rationals is going. No term of the sequence is irrational, and no closure has an irrational
   weight.
3. **Irrational flux is never reached.** The butterfly at irrational `φ` is a Cantor set. On the substrate
   it is the limit of rational fluxes `p/q` with `q → ∞`, which is the limit of ever-larger finite
   transfer operators. Nothing in the process is at an irrational flux.

**Link to Chain Theory.** [ChainTheory_YangMills_Kakeya_QLF.md](ChainTheory_YangMills_Kakeya_QLF.md) §1.4
observed that QLF's α census only reaches `√62`, while Chain Theory's α involves `√2` and `√3`. The
colour-flux census generates `√3` as a limit (item 2), and the half-spin census generates `√2`. Both are
rates of integer closure counts, not weights. This does not derive Chain Theory's formula. It does show
that QLF has rational processes whose limits are the two irrationals Chain Theory uses.

## References

- D. R. Hofstadter, *Energy levels and wave functions of Bloch electrons in rational and irrational
  magnetic fields*, Phys. Rev. B **14** (1976) 2239–2249.
- P. G. Harper, *Single band motion of conduction electrons in a uniform magnetic field*, Proc. Phys. Soc.
  A **68** (1955) 874–878.
- C. R. Dean et al., *Hofstadter's butterfly and the fractal quantum Hall effect in moiré superlattices*,
  Nature **497** (2013) 598–602.
- I. Niven, *Irrational Numbers*, Carus Mathematical Monographs **11** (1956), Corollary 3.12.
