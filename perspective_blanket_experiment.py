"""Finite surrogate experiment for two overlapping QLF blankets.

This is NOT a Markov-blanket implementation. Blanket records are deliberately
specified as projections of signed action coordinates so that the reconstruction
criterion can be tested without inventing physical accessibility semantics.
The experiment enumerates length-4 ZFA histories, independently records each
blanket's visible coordinates, and audits reconstruction of the full action and
Bloch observable. A collision is evidence of insufficiency of this surrogate,
not a physical counterexample to holography.
"""
from __future__ import annotations


from dataclasses import dataclass
from itertools import product
from typing import Dict, Iterable, Tuple


from perspective_holography import factor_reconstruction
from twist_core import TWISTS, calculate_action, is_zfa
from holographic import bloch_projection, spinor_from_action



@dataclass(frozen=True)
class Blanket:
    name: str
    visible_coordinates: Tuple[int, ...]



@dataclass(frozen=True)
class BlanketExperimentResult:
    sample_size: int
    shared_action_coordinates: Tuple[int, ...]
    full_action_reconstructible: Dict[str, bool]
    bloch_reconstructible: Dict[str, bool]
    full_action_counterexamples: Dict[str, tuple | None]
    bloch_counterexamples: Dict[str, tuple | None]



DEFAULT_BLANKETS = (
    Blanket("B_vertical_horizontal", (0, 1)),
    Blanket("B_horizontal_depth", (1, 2)),
)



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



def run_experiment(blankets: Iterable[Blanket] = DEFAULT_BLANKETS, length: int = 4) -> BlanketExperimentResult:
    blankets = tuple(blankets)
    if len(blankets) < 2:
        raise ValueError("experiment requires at least two blankets")
    histories = enumerate_closed_histories(length)
    actions = [calculate_action(h) for h in histories]
    bloch = [tuple(float(x) for x in bloch_projection(spinor_from_action(a))) for a in actions]
    action_results = {}
    bloch_results = {}
    action_witnesses = {}
    bloch_witnesses = {}
    for blanket in blankets:
        boundaries = [record(h, blanket) for h in histories]
        action_results[blanket.name] = factor_reconstruction(boundaries, actions).reconstructible
        action_audit = factor_reconstruction(boundaries, actions)
        bloch_audit = factor_reconstruction(boundaries, bloch)
        bloch_results[blanket.name] = bloch_audit.reconstructible
        action_witnesses[blanket.name] = action_audit.counterexample_indices
        bloch_witnesses[blanket.name] = bloch_audit.counterexample_indices
    overlap = tuple(sorted(set(blankets[0].visible_coordinates).intersection(blankets[1].visible_coordinates)))
    return BlanketExperimentResult(len(histories), overlap, action_results, bloch_results,
                                 action_witnesses, bloch_witnesses)



if __name__ == "__main__":
    print(run_experiment())
