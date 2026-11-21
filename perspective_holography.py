"""Finite-domain audit utilities for perspective holographic reconstruction.

This module tests the factorization criterion on explicit sampled domains. It is
computational evidence only; it is not a proof over an infinite or unspecified
history space and it does not supply physical observables or Markov blankets.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Hashable, Optional, Sequence, TypeVar



B = TypeVar("B", bound=Hashable)
O = TypeVar("O", bound=Hashable)


@dataclass(frozen=True)
class ReconstructionAudit:
    """Finite factorization result with a minimal observed collision witness."""
    reconstructible: bool
    reconstruction_map: Dict[Hashable, Hashable]
    counterexample_indices: Optional[tuple[int, int]] = None
    boundary_value: Optional[Hashable] = None
    observable_values: Optional[tuple[Hashable, Hashable]] = None


def factor_reconstruction(
    boundary_values: Sequence[B],
    observable_values: Sequence[O],
) -> ReconstructionAudit:
    """Audit whether a sampled observable factors through sampled boundary data.



    For a finite sample, factorization is possible exactly when every repeated
    boundary value is paired with the same observable value. On the first
    conflicting pair, return an explicit witness instead of guessing a value.
    """
    if len(boundary_values) != len(observable_values):
        raise ValueError("boundary and observable samples must have equal length")
    mapping: Dict[Hashable, Hashable] = {}
    first_index: Dict[Hashable, int] = {}
    for i, (boundary, observable) in enumerate(zip(boundary_values, observable_values)):
        if boundary in mapping:
            if mapping[boundary] != observable:
                j = first_index[boundary]
                return ReconstructionAudit(
                    reconstructible=False,
                    reconstruction_map={},
                    counterexample_indices=(j, i),
                    boundary_value=boundary,
                    observable_values=(mapping[boundary], observable),
                )
        else:
            mapping[boundary] = observable
            first_index[boundary] = i
    return ReconstructionAudit(reconstructible=True, reconstruction_map=mapping)
