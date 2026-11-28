"""Pre-registered test of contact reading (A): do shared pairs carry the Minkowski sign?

Part of the [Quantum Logical Framework (QLF)](README.md), stage 4c of the relativity dependency
chain ([Relativity_Principle.md](Relativity_Principle.md) §6b, "Which contact?"). Stage 4b showed
that a frame-independent contact must be a Lorentz scalar, and the most direct reading (every
shared pair weighted by its one-strand fold, `t t† = −I`, the same on every axis) gives the
Euclidean combination `1⊗1 + Σ α⊗α`, which picks a frame at O(1).

Reading (A) says a pair shared between two strands is not a sequence on one strand: body A
performs `t` and body B performs `t†`, so its action is the composite `t ⊗ t†`
(`QLF_TensorFromClosure.splitPair_fold`), and it acts on the two-body state that every shared
strong pair fixes (rung 6, `split_strong_iff_singlet`). The weight of a shared pair on axis `a` is
then its signed phase on that state, `w_a = ⟨ψ| t ⊗ t† |ψ⟩`.

Nothing below is fitted. The twist matrices come from `twist_core.PAULI_MAP`; the two-body state
is computed as the common +1 eigenvector of the shared spatial pairs, not written in.

Pre-registered criteria (frozen in the commit that adds this file, before it was run):

* Gate: the common +1 eigenspace of the shared spatial pairs is one-dimensional, and every
  weight is real to 1e-12. Otherwise INVALID.
* (A) PASSES iff the three spatial weights agree to 1e-12 and the gauge weight is minus the
  spatial weight to 1e-12 (the Minkowski relative sign).
* (A) FAILS otherwise: equal signs (Euclidean) or unequal spatial weights.
* Induced vertex: with the walk's currents `J^0 = 1`, `J^i = α_i`, the vertex `Σ_a w_a J^a ⊗ J^a`
  is reported with its distance from the nearest multiple of the stage-4b vector contact
  `1⊗1 − Σ α⊗α`. If (A) passes this distance must be below 1e-12, or the run is INVALID.
* Control (must come out Euclidean, or the test does not discriminate): the same weights read
  from the one-strand fold `½ tr(t · t†)`. This reproduces `shared_pair_fold_axis_blind`.

Usage: python3 shared_pair_sign_check.py [--json data/shared_pair_sign_check.json]
"""
import argparse
import json

import numpy as np

import twist_core as tc

TOL = 1e-12
CONJ = {"^": "v", "v": "^", "<": ">", ">": "<", "/": "\\", "\\": "/", "+": "-", "-": "+"}
AXES = {"gauge": "+-", "y": "^v", "x": "<>", "z": "/\\"}
SPATIAL = ("x", "y", "z")


class Invalid(Exception):
    pass


def mat(t):
    a, b, c, d = tc.PAULI_MAP[t]
    return np.array([[a, b], [c, d]], dtype=complex)


def shared(t):
    """A pair shared between two bodies: A performs t, B performs t†."""
    return np.kron(mat(t), mat(CONJ[t]))


def selected_state():
    """The two-body state every shared spatial pair fixes, computed as a null space."""
    stack = np.vstack([shared(t) - np.eye(4) for a in SPATIAL for t in AXES[a]])
    _, s, vh = np.linalg.svd(stack)
    null = vh[s < 1e-9]
    if null.shape[0] != 1:
        raise Invalid(f"common +1 eigenspace has dimension {null.shape[0]}, expected 1")
    psi = null[0].conj()
    return psi / np.linalg.norm(psi)


def weights(read):
    out = {}
    for a, ts in AXES.items():
        vals = [read(t) for t in ts]
        if any(abs(v.imag) > TOL for v in vals):
            raise Invalid(f"weight on axis {a} is not real: {vals!r}")
        out[a] = float(np.mean([v.real for v in vals]))
    return out


def verdict(w):
    sp = [w[a] for a in SPATIAL]
    iso = max(sp) - min(sp) <= TOL
    if iso and abs(w["gauge"] + sp[0]) <= TOL and abs(sp[0]) > TOL:
        return "MINKOWSKI"
    if iso and abs(w["gauge"] - sp[0]) <= TOL:
        return "EUCLIDEAN"
    return "NEITHER"


def walk_currents():
    import importlib.util
    from pathlib import Path
    spec = importlib.util.spec_from_file_location(
        "boost_states_check", Path(__file__).resolve().parent / "boost_states_check.py")
    bsc = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bsc)
    return np.eye(4, dtype=complex), bsc.ALPHA


def induced_vertex(w):
    j0, alpha = walk_currents()
    gamma = w["gauge"] * np.kron(j0, j0)
    for a, al in zip(SPATIAL, alpha):
        gamma = gamma + w[a] * np.kron(al, al)
    vec = np.kron(j0, j0) - sum(np.kron(al, al) for al in alpha)
    c = np.vdot(vec, gamma) / np.vdot(vec, vec)
    return gamma, complex(c), float(np.abs(gamma - c * vec).max())


def run():
    psi = selected_state()
    res = {"state": [[z.real, z.imag] for z in psi]}
    two = weights(lambda t: np.vdot(psi, shared(t) @ psi))
    one = weights(lambda t: np.trace(mat(t) @ mat(CONJ[t])) / 2)
    res["two_strand_weights"] = two
    res["one_strand_fold_weights"] = one
    res["control"] = verdict(one)
    if res["control"] != "EUCLIDEAN":
        raise Invalid(f"control came out {res['control']}, expected EUCLIDEAN: the test does not "
                      "discriminate")
    v = verdict(two)
    res["reading"] = v
    res["A"] = "PASS" if v == "MINKOWSKI" else "FAIL"
    _, c, dist = induced_vertex(two)
    res["vertex_multiple_of_vector"] = [c.real, c.imag]
    res["vertex_distance_from_vector"] = dist
    if res["A"] == "PASS" and dist > TOL:
        raise Invalid(f"Minkowski weights but the induced vertex is {dist:.2e} from the vector form")
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    try:
        res = run()
    except Invalid as e:
        print(f"INVALID, NOT_GRADED: {e}")
        raise SystemExit(2)
    print("selected two-body state:", np.round([complex(*z) for z in res["state"]], 6))
    print("control, one-strand fold weights:", res["one_strand_fold_weights"], "->", res["control"])
    print("two-strand shared-pair weights:  ", res["two_strand_weights"], "->", res["reading"])
    print(f"induced vertex = ({res['vertex_multiple_of_vector'][0]:+.3f}) x vector contact, "
          f"distance {res['vertex_distance_from_vector']:.2e}")
    print(f"reading (A): {res['A']}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
