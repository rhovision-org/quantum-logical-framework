# One-qubit gates and CNOT are universal, machine-checked

Part of the [Quantum Logical Framework (QLF)](README.md). Lean modules:
[`lean/QLF_ControlledUnitary.lean`](lean/QLF_ControlledUnitary.lean),
[`lean/QLF_TwoLevelUnitary.lean`](lean/QLF_TwoLevelUnitary.lean),
[`lean/QLF_Barenco.lean`](lean/QLF_Barenco.lean). Module table:
[`lean/README.md`](lean/README.md).

## The result

**On `n ≥ 1` qubits, every unitary is a finite product of one-qubit unitaries and CNOTs**
(`universality`, `universality_list`). The product is exact, not an approximation, and uses
no ancilla qubits. Since every such product is unitary, the circuits are exactly the unitary
group (`circuits_eq_unitary`).

This is Barenco et al. (1995), *Elementary gates for quantum computation*, Phys. Rev. A **52**,
3457, building on DiVincenzo (1995), Phys. Rev. A **51**, 1015, and the two-level
decomposition of Reck, Zeilinger, Bernstein and Bertani (1994), Phys. Rev. Lett. **73**, 58.
Nielsen and Chuang, *Quantum Computation and Quantum Information* (2000) §4.5, give the
textbook account. The theorem is theirs. Here it is checked by Lean's kernel, with no axioms beyond Lean's own (`propext`, `Classical.choice`, `Quot.sound`; see
[`lean/axiom_footprints.expected.json`](lean/axiom_footprints.expected.json)).

## How the proof goes

**Stage 1: controlled-`U` from `A·X·B·X·C`**
([`QLF_ControlledUnitary`](lean/QLF_ControlledUnitary.lean)).

* Euler angles: every `W ∈ SU(2)` is `D(e^{iμ}) · R(θ) · D(e^{iν})` with `D(w) = diag(w, w̄)`
  and `R(θ)` a real rotation (`su2_euler`).
* From the angles, `A = D(e^{iμ})R(θ/2)`, `B = R(−θ/2)D(e^{−i(ν+μ)/2})`, `C = D(e^{i(ν−μ)/2})`
  satisfy `A·B·C = 1` and `A·X·B·X·C = W`, because conjugating by `X` reverses both rotations
  (`abc_decomposition`).
* So controlled-`W` is `(1⊗A)·CNOT·(1⊗B)·CNOT·(1⊗C)` (`controlled_eq_abc`). Any `U ∈ U(2)` is
  `e^{iδ}·W` (`unitary_eq_phase_smul_su2`), and the phase becomes `diag(1, e^{iδ})` on the
  control (`controlled_unitary_eq`).
* Every `SU(2)` matrix is a product of three group commutators `V·V'·V†·V'†` of `SU(2)`
  matrices (`su2_three_commutators`): `D(w²)` is the commutator of `D(w)` with `iX`, and
  `R(2a)` is the commutator of `R(a)` with `iZ`.

**Stage 2: two-level unitaries**
([`QLF_TwoLevelUnitary`](lean/QLF_TwoLevelUnitary.lean)).

A unitary is two-level when it is the identity outside two basis vectors. Every unitary on a
finite index set is a finite product of two-level unitaries (`unitary_eq_prod_twoLevel`).
The proof is Givens elimination: a two-level rotation zeroes one entry of a column
(`givens_exists`); repeating it sends a column to `c·eₐ` (`clear_column`); a unitary with that
column has the matching row (`row_of_column`); a phase removes `c`, and induction on the
support finishes it (`supported_mem_closure`).

**Stage 3: routing across `n` qubits** ([`QLF_Barenco`](lean/QLF_Barenco.lean)).

* A gate on qubit `t` whose `2 × 2` block may depend on the other qubits is `lift t F`, and
  gates on the same target multiply blockwise (`lift_mul`). One-qubit gates and CNOT are the
  special cases `onQubit_apply` and `cnot_apply` spell out.
* **Multi-controlled gates** `C^S(U)` for every `U ∈ U(2)` and every control set `S`
  (`ctrl_mem`). One control is Stage 1. For more controls, split `S = {c} ∪ S'`. A controlled
  commutator is the commutator of controlled gates, `C^S([V, V']) = [C^{c}(V), C^{S'}(V')]`
  (`ctrl_comm`), so the three commutators of Stage 1 reduce `S` to smaller sets. The phase
  `e^{iδ}` under `S` equals `diag(1, e^{iδ})` on the qubit `c`, controlled by `S \ {c}`
  (`ctrl_phase_switch`). This group-commutator step stands in for Barenco's square-root
  recursion (their Lemma 7.5), so no square root of a unitary is needed.
* **Routing.** `X` and CNOT act as permutations of basis states (`flip_isPerm`,
  `cnot_isPerm`). Conjugating a two-level unitary on states `s ≠ s'` by CNOTs from a qubit
  where they differ moves it onto a pair differing in that one qubit (`pair_cnot_mem`);
  conjugating by `X` gates moves that pair onto the one whose other qubits are all `1`
  (`pair_mem`); there it is a fully controlled gate (`pair_allOnes_mem`). So every two-level
  unitary is a circuit (`twoLevel_mem_circuits`), and Stage 2 gives `universality`.

## Scope

* The gate set here is all one-qubit unitaries, an uncountable set. A finite gate set such as
  Clifford+T can only approximate. Density of rotations about two axes in `SU(2)` is
  `su2_dense` in `QLF_QuantumComputer` (PR #323, open at the time of writing). The
  Solovay–Kitaev rate is not proved.
* No gate count is claimed. The commutator recursion is a proof of membership, not an
  efficient compilation.
* This is a theorem about the matrix algebra of qubits. It does not by itself show that the
  QLF substrate performs these gates. For that, the entangling gate has to act on superposed
  presence, which is open (see `QLF_QuantumComputer`, PR #323).

## Perspectives: the observer holds the gates

Jim Whitescarver's reading of the open substrate gap (2026-11-25): *"The observer, the atom
preserves those gates by perspective."* Superposed presence is then relative to a perspective,
as in [`lean/QLF_PerspectiveLocality.lean`](lean/QLF_PerspectiveLocality.lean) and
[`lean/QLF_SharedReality.lean`](lean/QLF_SharedReality.lean).

**Proved** (in [`QLF_Barenco`](lean/QLF_Barenco.lean), no axioms beyond Lean's own):

* **A qubit's gate is the same whatever is done on another qubit** (`onQubit_comm`, via
  `onQubit_mul_apply`). This is the gate-level form of `perspective_locality`, which shows that
  a body's local statistics depend only on its own projection.
* **Controlled-Z has no control.** It is symmetric in its two qubits (`cz_symm`), and diagonal
  with sign `−1` exactly when both are `1` (`cz_eq_diagonal`). Neither perspective acts on the other.
* **A sign table fixes its linear gate.** A linear operator that multiplies each basis state by
  controlled-Z's sign is controlled-Z (`eq_cz_of_sign_table`, from `eq_diagonal_of_signs`).
* **Controlled-Z can stand in for CNOT.** `CNOT = (1⊗H)·CZ·(1⊗H)` (`cnot_eq_h_cz_h`), so
  one-qubit unitaries and controlled-Z are universal (`universality_cz`).

**Conjecture (perspective realization).** An observer, for example an atom, holds the gates of its own
presence qubit from its perspective: the alternate histories it can tell apart combine
linearly, it can apply any one-qubit unitary to them, and a joint closure of two strands acts
on their superposed presence as controlled-Z. If this holds, the substrate performs every
unitary, by `universality_cz`.

*Support.* (1) `joint_closure_is_cz` in `QLF_QuantumComputer` (PR #323) shows that
interleaving two strands' closures multiplies the fold by `(−1)^{ab}`, which is controlled-Z's
sign table. By `eq_cz_of_sign_table`, the only linear gate with that table is controlled-Z.
(2) In PR #323, superposition is a census sum of alternate histories (`censusSum`), and that
sum is linear by construction. (3) `onQubit_comm` and `perspective_locality` show that what one
perspective holds is not disturbed by what another does.

*What is not proved.* Two premises remain open: that a perspective's action on its alternate
histories is linear, and that it reaches every one-qubit unitary. The first is the premise
of `eq_cz_of_sign_table`. The second needs the count-weighted rotations of PR #323 to act
on the presence bit. Neither is a theorem yet.

## Related

* [`QuantumOS.md`](QuantumOS.md): QLF as an operating system for quantum hardware.
* [`Theory_Of_Everything.md`](Theory_Of_Everything.md) §6: listed as a boundary. The theorem is
  qubit algebra and rests on neither a priori solution; the open part is the substrate
  performing the gates.
