# Hofstadter's butterfly from closure counts

> Part of the [Quantum Logical Framework (QLF)](README.md). **ZFA** (Zero Free Action) is equal and
> opposite quantum logical action with zero free energy, the principle of QLF.

**The question (Jim, 2026-10-28).** There is no continuum, and irrational numbers are not in reality.
What is real is the quantum logical process whose finite outputs the continuum approximates. Hofstadter's
butterfly, the energy spectrum of an electron on a lattice in a magnetic field, should therefore emerge
from that process, not from a continuum Hamiltonian.

The butterfly is a good test case because it is defined only at **rational** flux. At flux `φ = p/q` per
plaquette, the spectrum has `q` bands. Irrational flux is the limit of that construction, a Cantor set
nobody computes directly (Hofstadter 1976). So the question is whether QLF's closures produce it, and
which parts of it are a count and which are a rendering.

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

*(Filled in after the run, in a later commit.)*

## 4. What the butterfly says about irrational numbers

*(Filled in after the run.)*

## References

- D. R. Hofstadter, *Energy levels and wave functions of Bloch electrons in rational and irrational
  magnetic fields*, Phys. Rev. B **14** (1976) 2239–2249.
- P. G. Harper, *Single band motion of conduction electrons in a uniform magnetic field*, Proc. Phys. Soc.
  A **68** (1955) 874–878.
- I. Niven, *Irrational Numbers*, Carus Mathematical Monographs **11** (1956), Corollary 3.12.
