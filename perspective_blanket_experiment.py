"""Finite surrogate experiment for two overlapping QLF blankets.

This is NOT a Markov-blanket implementation. Blanket records are deliberately
specified as projections of signed action coordinates so that reconstruction can be
falsified without inventing physical accessibility semantics.
The experiment enumerates length-N ZFA leaves and their prefix sample, then audits
reconstruction of the full action, each action coordinate, the Bloch observable,
and each Bloch coordinate. Collision witnesses include the concrete histories and
boundary value. A failure is a counterexample to this surrogate encoding only.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Dict, Iterable, Tuple


from perspective_holography import ReconstructionAudit, factor_reconstruction
from twist_core import TWISTS, calculate_action, is_zfa
from holographic import bloch_projection, spinor_from_action



@dataclass(frozen=True)
class Blanket:
    name: str
    visible_coordinates: Tuple[int, ...]



@dataclass(frozen=True)
class CollisionWitness:
    indices: Tuple[int, int]
    boundary_value: tuple
    histories: Tuple[str, str]
    observable_values: tuple



@dataclass(frozen=True)
class BlanketExperimentResult:
    sample_size: int
    shared_action_coordinates: Tuple[int, ...]
    full_action_reconstructible: Dict[str, bool]
    bloch_reconstructible: Dict[str, bool]
    full_action_counterexamples: Dict[str, tuple | None]
    bloch_counterexamples: Dict[str, tuple | None]
    full_action_witnesses: Dict[str, CollisionWitness | None]
    bloch_witnesses: Dict[str, CollisionWitness | None]
    action_component_reconstructible: Dict[str, Dict[str, bool]]
    bloch_component_reconstructible: Dict[str, Dict[str, bool]]
    action_component_witnesses: Dict[str, Dict[str, CollisionWitness | None]]
    bloch_component_witnesses: Dict[str, Dict[str, CollisionWitness | None]]



DEFAULT_BLANKETS = (
    Blanket("B_vertical_horizontal", (0, 1)),
    Blanket("B_horizontal_depth", (1, 2)),
)
ACTION_NAMES = ("vertical", "horizontal", "depth", "local_gauge")
BLOCH_NAMES = ("X", "Y", "Z")



def record(history: str, blanket: Blanket) -> tuple:
    """Surrogate boundary record; intentionally only visible action coordinates."""
    action = calculate_action(history)
    return tuple(action[i] for i in blanket.visible_coordinates)



def enumerate_closed_histories(length: int = 4) -> list[str]:
    if length < 1:
        raise ValueError("length must be positive")
    closed = ["".join(word) for word in product(TWISTS, repeat=length)
              if is_zfa("".join(word))]
    # The network sample is the prefix-closure of finite ZFA leaves.
    return sorted({leaf[:i] for leaf in closed for i in range(1, len(leaf) + 1)})



def _witness(audit: ReconstructionAudit, histories: list[str], boundaries: list[tuple],
             observables: list) -> CollisionWitness | None:
    if audit.counterexample_indices is None:
        return None
    i, j = audit.counterexample_indices
    return CollisionWitness((i, j), boundaries[i], (histories[i], histories[j]),
                          (observables[i], observables[j]))



def run_experiment(blankets: Iterable[Blanket] = DEFAULT_BLANKETS, length: int = 4) -> BlanketExperimentResult:
    blankets = tuple(blankets)
    if len(blankets) < 2:
        raise ValueError("experiment requires at least two blankets")
    histories = enumerate_closed_histories(length)
    actions = [calculate_action(h) for h in histories]
    bloch = [tuple(float(x) for x in bloch_projection(spinor_from_action(a))) for a in actions]
    action_results, bloch_results = {}, {}
    action_witnesses, bloch_witnesses = {}, {}
    action_component_results, bloch_component_results = {}, {}
    action_component_witnesses, bloch_component_witnesses = {}, {}
    for blanket in blankets:
        boundaries = [record(h, blanket) for h in histories]
        action_audit = factor_reconstruction(boundaries, actions)
        bloch_audit = factor_reconstruction(boundaries, bloch)
        action_results[blanket.name] = action_audit.reconstructible
        bloch_results[blanket.name] = bloch_audit.reconstructible
        action_witnesses[blanket.name] = _witness(action_audit, histories, boundaries, actions)
        bloch_witnesses[blanket.name] = _witness(bloch_audit, histories, boundaries, bloch)
        action_component_results[blanket.name] = {}
        bloch_component_results[blanket.name] = {}
        action_component_witnesses[blanket.name] = {}
        bloch_component_witnesses[blanket.name] = {}
        for axis, name in enumerate(ACTION_NAMES):
            values = [a[axis] for a in actions]
            audit = factor_reconstruction(boundaries, values)
            action_component_results[blanket.name][name] = audit.reconstructible
            action_component_witnesses[blanket.name][name] = _witness(audit, histories, boundaries, values)
        for axis, name in enumerate(BLOCH_NAMES):
            values = [b[axis] for b in bloch]
            audit = factor_reconstruction(boundaries, values)
            bloch_component_results[blanket.name][name] = audit.reconstructible
            bloch_component_witnesses[blanket.name][name] = _witness(audit, histories, boundaries, values)
    overlap = tuple(sorted(set(blankets[0].visible_coordinates).intersection(blankets[1].visible_coordinates)))
    return BlanketExperimentResult(
        len(histories), overlap, action_results, bloch_results,
        {name: (w.indices if w is not None else None) for name, w in action_witnesses.items()},
        {name: (w.indices if w is not None else None) for name, w in bloch_witnesses.items()},
        action_witnesses, bloch_witnesses, action_component_results, bloch_component_results,
        action_component_witnesses, bloch_component_witnesses)



if __name__ == "__main__":
    print(run_experiment())
