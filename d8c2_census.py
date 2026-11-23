#!/usr/bin/env python3
"""D8c2 under the frozen D3T relation (#290).

Pre-registration: ``Diversity_Advantage_D8c2_Prereg.md`` (committed in c683f60,
before this file existed).  Results: ``Diversity_Advantage_D8c2.md``.

Populations, strata, measure, nulls and the decision rule are those of the
pre-registration; nothing here is tuned to the outcome.

* Bases: open two-origin typed histories of the panel length (D3T panels A, B).
* supp(o): axes on which net(proj(a, o)) is nonzero.  Eligible: both supports
  nonempty.  Homogeneous: equal supports.  Heterogeneous: disjoint supports.
  Partial overlap: reported only.
* Stratum: (panel, unordered pair of per-stream |net|_1).
* K(a) = |C_T(a)|, the number of distinct boundary records B(b) over admitted
  extensions b, with |b| <= k (D3T section 4 text).
* Nulls: N1 = D3T's aggregate control (no provenance); N2 = obligation match
  plus ZFA without the typed first-closure condition.

Post-hoc diagnostics (disclosed, not decision inputs): ``diag_R_T_no_phase_label``
counts admitted boundary records with the per-stream phase label dropped, and
``diag_R_T_raw_admitted`` counts admitted extensions.  They were added after
the primary result was seen, to locate what carries it.

Sensitivity (disclosed, not a decision input): the D3T census code enumerates
extensions of length exactly k; the same statistics are reported for that
reading too.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Callable

from diversity_obligation import (
    PANELS,
    ProvHistory,
    aggregate_join,
    boundary,
    boundary_key,
    complement_key,
    first_joint_closure_at_end,
    histories,
    is_open,
    is_zfa,
    net,
    obligations_match,
    projection,
    typed_join,
    word,
)

OUTPUT = Path("data/d8c2_census.json")


def support(history: ProvHistory, origin: int) -> frozenset[int]:
    return frozenset(i for i, x in enumerate(net(projection(history, origin))) if x != 0)


def l1(history: ProvHistory, origin: int) -> int:
    return sum(abs(x) for x in net(projection(history, origin)))


def population(history: ProvHistory) -> str:
    a, b = support(history, 0), support(history, 1)
    if not a or not b:
        return "ineligible"
    if a == b:
        return "homogeneous"
    if not (a & b):
        return "heterogeneous"
    return "partial"


def no_first_closure_join(a: ProvHistory, b: ProvHistory) -> bool:
    """N2: per-stream obligation match plus ZFA, no typed first-closure rule."""
    return obligations_match(a, b) and is_zfa(word(a) + word(b))


def extensions(bound: int, exact: bool) -> list[ProvHistory]:
    lengths = [bound] if exact else range(2, bound + 1)
    return [h for n in lengths for h in histories(n) if is_open(h)]


def profile_sizes(length: int, bound: int, exact: bool) -> dict[str, dict[ProvHistory, int]]:
    exts = extensions(bound, exact)
    by_key: dict[tuple, list[ProvHistory]] = defaultdict(list)
    by_net: dict[tuple, list[ProvHistory]] = defaultdict(list)
    for e in exts:
        by_key[boundary_key(e)].append(e)
        by_net[net(word(e))].append(e)
    relations: dict[str, tuple[Callable, Callable]] = {
        "R_T": (typed_join, lambda a: by_key.get(complement_key(boundary_key(a)), ())),
        "N1_no_provenance": (aggregate_join,
                             lambda a: by_net.get(tuple(-x for x in net(word(a))), ())),
        "N2_no_first_closure": (no_first_closure_join,
                                lambda a: by_key.get(complement_key(boundary_key(a)), ())),
    }
    out: dict[str, dict[ProvHistory, int]] = {name: {} for name in relations}
    out["diag_R_T_no_phase_label"] = {}
    out["diag_R_T_raw_admitted"] = {}
    for base in histories(length):
        if not is_open(base) or population(base) == "ineligible":
            continue
        for name, (rel, cands) in relations.items():
            admitted = [e for e in cands(base) if rel(base, e)]
            out[name][base] = len({boundary(e) for e in admitted})
            if name == "R_T":
                out["diag_R_T_no_phase_label"][base] = len({boundary_key(e) for e in admitted})
                out["diag_R_T_raw_admitted"][base] = len(admitted)
    return out


def fr(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)


def analyse(exact: bool) -> dict[str, object]:
    strata: dict[tuple, dict[str, dict[str, list[int]]]] = defaultdict(
        lambda: defaultdict(lambda: defaultdict(list)))
    for panel, length, bound in PANELS:
        sizes = profile_sizes(length, bound, exact)
        for base, k in sizes["R_T"].items():
            key = (panel, tuple(sorted((l1(base, 0), l1(base, 1)))))
            pop = population(base)
            for name in sizes:
                strata[key][name][pop].append(sizes[name][base])

    report: dict[str, object] = {"strata": [], "relations": {}}
    for name in ("R_T", "N1_no_provenance", "N2_no_first_closure",
                 "diag_R_T_no_phase_label", "diag_R_T_raw_admitted"):
        num, den = Fraction(0), 0
        signs = {}
        for key in sorted(strata):
            het, hom = strata[key][name]["heterogeneous"], strata[key][name]["homogeneous"]
            if het and hom:
                d = Fraction(sum(het), len(het)) - Fraction(sum(hom), len(hom))
                w = min(len(het), len(hom))
                num += w * d
                den += w
                signs[f"{key[0]}{list(key[1])}"] = (d > 0) - (d < 0)
        delta = num / den if den else None
        report["relations"][name] = {
            "eligible_strata": len(signs),
            "weighted_delta": fr(delta) if delta is not None else None,
            "weighted_delta_float": float(delta) if delta is not None else None,
            "stratum_signs": signs,
        }
    for key in sorted(strata):
        row: dict[str, object] = {"panel": key[0], "l1_pair": list(key[1])}
        for name in ("R_T", "N1_no_provenance", "N2_no_first_closure",
                     "diag_R_T_no_phase_label", "diag_R_T_raw_admitted"):
            row[name] = {pop: {"n": len(v), "mean_K": fr(Fraction(sum(v), len(v)))}
                         for pop, v in sorted(strata[key][name].items()) if v}
        report["strata"].append(row)

    rt = report["relations"]["R_T"]
    if rt["eligible_strata"] < 2:
        verdict = "INCONCLUSIVE"
    else:
        delta = Fraction(rt["weighted_delta"])
        if delta <= 0:
            verdict = "FAIL"
        elif any(s < 0 for s in rt["stratum_signs"].values()):
            verdict = "MIXED"
        else:
            nulls_reproduce = all(
                report["relations"][n]["stratum_signs"] == rt["stratum_signs"]
                and Fraction(report["relations"][n]["weighted_delta"] or 0) > 0
                for n in ("N1_no_provenance", "N2_no_first_closure"))
            verdict = "PASS, NOT ZFA-SPECIFIC" if nulls_reproduce else "PASS (D8c2)"
    report["verdict"] = verdict
    return report


def build() -> dict[str, object]:
    return {
        "prereg": "Diversity_Advantage_D8c2_Prereg.md @ c683f60",
        "primary_extensions_le_k": analyse(exact=False),
        "sensitivity_extensions_eq_k": analyse(exact=True),
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=Path, default=OUTPUT)
    args = p.parse_args()
    data = build()
    args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    for part in ("primary_extensions_le_k", "sensitivity_extensions_eq_k"):
        print(part, data[part]["verdict"],
              {n: (r["weighted_delta"], r["eligible_strata"])
               for n, r in data[part]["relations"].items()})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
