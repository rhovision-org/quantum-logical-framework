"""
holographic.py

QLF bridge module:
3D observable structure as a projection of 2-component logical state.

This file does NOT treat Hilbert space or Pauli matrices as primitive ontology.
Instead, it starts from canonical QLF histories from twist_core.py and maps their
prefix-action structure into a two-component logical state

    psi = [alpha, beta]^T

with
    alpha = vertical + i * horizontal
    beta  = depth    + i * local

The three observable spatial coordinates are then the standard real bilinear
projections

    X = psi^\\dagger sigma_x psi
    Y = psi^\\dagger sigma_y psi
    Z = psi^\\dagger sigma_z psi

This expresses the core claim:

    3D directional observables are a projection of deeper 2-component logic.

The module is therefore a BRIDGE from QuCalc histories to the familiar SU(2) ->
SO(3) projection, not a claim that Pauli matrices are more fundamental than the
twist calculus.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np
import matplotlib.pyplot as plt

from twist_core import (
    calculate_action,
    adjoint_history,
    generate_histories,
    is_admissible_history,
    validate_history,
)

# ---------------------------------------------------------------------------
# Pauli matrices as projection operators on the 2-component logical state
# ---------------------------------------------------------------------------

SIGMA_X = np.array([[0, 1], [1, 0]], dtype=complex)
SIGMA_Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
SIGMA_Z = np.array([[1, 0], [0, -1]], dtype=complex)


@dataclass(frozen=True)
class LogicalProjection:
    """Container for one projected prefix state."""

    step: int
    prefix: str
    action: Tuple[int, int, int, int]
    spinor: np.ndarray
    xyz: np.ndarray
    relative_phase: float


# ---------------------------------------------------------------------------
# Core bridge construction
# ---------------------------------------------------------------------------

def spinor_from_action(action: Tuple[int, int, int, int]) -> np.ndarray:
    """
    NOTE (holography audit, Holography_Audit.md section 2): this map is many-to-one.
    Normalisation forgets scale and the Bloch reading forgets phase, so the closed
    state (0,0,0,0) and the open prefixes '^', 'v', '>' all project to +Z. The
    faithful carrier is the unnormalised action vector itself (the Form of the open
    half), which is zero exactly on closures: countBalanced_iff_strandForm_zero in
    lean/QLF_EntanglementPrimacy.lean. Read the projection below as a lossy view.

    Map canonical QLF action coordinates into a normalized two-component state.

    alpha := vertical + i*horizontal
    beta  := depth    + i*local

    This is the central bridge assumption in this module:
    the four real QLF action coordinates are gathered into two complex logical
    variables, whose observable bilinears define the three projected directions.
    """
    vertical, horizontal, depth, local = action

    alpha = complex(vertical, horizontal)
    beta = complex(depth, local)

    psi = np.array([alpha, beta], dtype=complex)
    norm = np.linalg.norm(psi)

    # Vacuum / exact cancellation prefix:
    # choose a canonical reference state so the projection stays defined.
    if norm == 0:
        psi = np.array([1.0 + 0.0j, 0.0 + 0.0j], dtype=complex)
        return psi

    return psi / norm


def bloch_projection(psi: np.ndarray) -> np.ndarray:
    """
    Project a normalized 2-component logical state to 3 real observables.

    Returns [X, Y, Z].
    """
    if psi.shape != (2,):
        raise ValueError("psi must be a 2-component vector")

    norm = np.linalg.norm(psi)
    if norm == 0:
        raise ValueError("psi must not be the zero vector")

    psi = psi / norm
    bra = psi.conj().T

    x = float(np.real(bra @ SIGMA_X @ psi))
    y = float(np.real(bra @ SIGMA_Y @ psi))
    z = float(np.real(bra @ SIGMA_Z @ psi))

    return np.array([x, y, z], dtype=float)


def relative_phase(psi: np.ndarray) -> float:
    """
    One-dimensional boundary coordinate derived from the internal relation
    between the two logical components.

    This is used as a simple 'holographic boundary' encoding:
        phi = arg(beta) - arg(alpha)
    """
    alpha, beta = psi[0], psi[1]

    if abs(alpha) < 1e-12 or abs(beta) < 1e-12:
        return 0.0

    return float(np.angle(beta) - np.angle(alpha))


def project_history(history: str) -> List[LogicalProjection]:
    """
    Project every prefix of a QLF history into:
    - canonical action coordinates
    - a normalized 2-component logical state
    - a 3D observable vector
    - a 1D boundary phase coordinate
    """
    validate_history(history)

    if not is_admissible_history(history):
        raise ValueError(
            "history is not admissible under the canonical branching law"
        )

    results: List[LogicalProjection] = []

    for step in range(len(history) + 1):
        prefix = history[:step]
        if prefix:
            action = calculate_action(prefix)
        else:
            action = (0, 0, 0, 0)

        psi = spinor_from_action(action)
        xyz = bloch_projection(psi)
        phi = relative_phase(psi)

        results.append(
            LogicalProjection(
                step=step,
                prefix=prefix,
                action=action,
                spinor=psi,
                xyz=xyz,
                relative_phase=phi,
            )
        )

    return results


# ---------------------------------------------------------------------------
# Demonstrations
# ---------------------------------------------------------------------------

def verify_projection_identity(history: str) -> Dict[str, object]:
    """
    Verify the key geometric statement for a projected history:
    each normalized 2-component logical state maps to a 3D point of unit norm.
    """
    projections = project_history(history)
    radii = [float(np.dot(p.xyz, p.xyz)) for p in projections]

    return {
        "history": history,
        "admissible": is_admissible_history(history),
        "steps": len(projections),
        "min_xyz_norm_squared": min(radii),
        "max_xyz_norm_squared": max(radii),
        "all_close_to_one": all(abs(r - 1.0) < 1e-9 for r in radii),
    }


def demonstrate_double_cover(history: str) -> Dict[str, object]:
    """
    Show the spinor sign-flip invariance of the projected 3-vector.

    In SU(2) -> SO(3), psi and -psi project to the same 3D observable vector.
    This is the algebraic content of the double-cover relation.
    """
    projections = project_history(history)
    final_state = projections[-1].spinor
    final_xyz = projections[-1].xyz

    flipped = -final_state
    flipped_xyz = bloch_projection(flipped)

    return {
        "history": history,
        "final_spinor": final_state,
        "negated_spinor": flipped,
        "final_xyz": final_xyz,
        "negated_xyz": flipped_xyz,
        "projection_invariant_under_sign_flip": np.allclose(final_xyz, flipped_xyz),
    }


def print_projection_report(history: str) -> None:
    """Print a compact textual report."""
    print("\n=== QLF LOGICAL PROJECTION REPORT ===")
    print(f"History: {history}")
    print(f"Adjoint: {adjoint_history(history)}")
    print(f"Admissible: {is_admissible_history(history)}")

    identity = verify_projection_identity(history)
    print(
        "Projected norm check:"
        f" min={identity['min_xyz_norm_squared']:.6f},"
        f" max={identity['max_xyz_norm_squared']:.6f},"
        f" unit-sphere={identity['all_close_to_one']}"
    )

    cover = demonstrate_double_cover(history)
    print(
        "Double-cover check:"
        f" sign flip leaves xyz unchanged ="
        f" {cover['projection_invariant_under_sign_flip']}"
    )

    print("\nStep-by-step prefixes:")
    for p in project_history(history):
        alpha, beta = p.spinor
        x, y, z = p.xyz
        print(
            f"  step={p.step:>2} "
            f"prefix={p.prefix!r:<12} "
            f"action={p.action!s:<18} "
            f"psi=({alpha.real:+.3f}{alpha.imag:+.3f}i, "
            f"{beta.real:+.3f}{beta.imag:+.3f}i) "
            f"xyz=({x:+.3f}, {y:+.3f}, {z:+.3f}) "
            f"phi={p.relative_phase:+.3f}"
        )


# ---------------------------------------------------------------------------
# Plotting
# ---------------------------------------------------------------------------

def plot_history_projection(history: str) -> None:
    """
    Plot:
    1. the 3D projected path
    2. the 2D xy shadow
    3. the 1D boundary phase coordinate
    """
    projections = project_history(history)

    xyz = np.array([p.xyz for p in projections])
    phases = np.unwrap(np.array([p.relative_phase for p in projections], dtype=float))
    steps = np.array([p.step for p in projections], dtype=int)

    fig = plt.figure(figsize=(14, 10))

    # 3D projected observable path
    ax3d = fig.add_subplot(2, 2, 1, projection="3d")
    ax3d.plot(xyz[:, 0], xyz[:, 1], xyz[:, 2], "o-", linewidth=2, markersize=5)
    ax3d.set_title("3D Observable Projection from 2-Component Logic")
    ax3d.set_xlabel("X = ψ†σxψ")
    ax3d.set_ylabel("Y = ψ†σyψ")
    ax3d.set_zlabel("Z = ψ†σzψ")
    ax3d.set_xlim([-1.05, 1.05])
    ax3d.set_ylim([-1.05, 1.05])
    ax3d.set_zlim([-1.05, 1.05])

    # 2D xy shadow
    ax_xy = fig.add_subplot(2, 2, 2)
    ax_xy.plot(xyz[:, 0], xyz[:, 1], "o-", linewidth=2, markersize=5)
    ax_xy.set_title("2D Shadow of the 3D Projection")
    ax_xy.set_xlabel("X")
    ax_xy.set_ylabel("Y")
    ax_xy.set_aspect("equal", adjustable="box")
    ax_xy.grid(True)

    # 1D boundary encoding
    ax_phi = fig.add_subplot(2, 1, 2)
    ax_phi.plot(steps, phases, "o-", linewidth=2, markersize=5)
    ax_phi.set_title("1D Boundary Encoding: Relative Internal Phase")
    ax_phi.set_xlabel("Prefix step")
    ax_phi.set_ylabel("φ = arg(β) - arg(α)")
    ax_phi.grid(True)

    fig.suptitle(
        f"QLF Holographic Bridge for History {history!r}\n"
        "3D observable structure as a projection of 2-component logic",
        fontsize=14,
    )
    plt.tight_layout()
    plt.show()


# ---------------------------------------------------------------------------
# Optional helper: generate a sample canonical history from twist_core
# ---------------------------------------------------------------------------

def first_stable_history(seed: str = "^", causal_horizon: int = 8) -> str:
    """
    Fetch the first canonical ZFA closure from the refactored core.
    """
    stable = generate_histories(
        seed,
        causal_horizon=causal_horizon,
        require_zfa=True,
    )
    if not stable:
        raise RuntimeError(
            f"no stable histories found for seed {seed!r} "
            f"within horizon {causal_horizon}"
        )
    return stable[0]


def main() -> None:
    """
    Demonstration:
    1. pull a canonical stable history from twist_core
    2. project its prefixes from 2-component logical space to 3D observables
    3. show the 1D boundary encoding
    """
    history = first_stable_history(seed="^", causal_horizon=8)

    print_projection_report(history)
    plot_history_projection(history)


if __name__ == "__main__":
    main()
