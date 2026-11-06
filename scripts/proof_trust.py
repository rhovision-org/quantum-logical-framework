#!/usr/bin/env python3
"""Fail-closed proof trust checks for QLF's Lean anchors.

The manifest records *exact* kernel axiom dependencies, not just declared
project axioms. Updating it is a reviewed change, never an automatic CI step.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

PRINT = re.compile(r"(?m)^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z_0-9.']*)\s*$")
REPORT = re.compile(
    r"'(?P<name>[A-Za-z_][A-Za-z_0-9.']*)'\s+"
    r"(?:depends on axioms:\s*\[(?P<deps>[^\]]*)\]|does not depend on any axioms)"
)
SORRY = re.compile(r"\bsorry\b|\bLean\.sorryAx\b")
ADMIT_TACTIC = re.compile(
    r"(?m)^[ \t]*(?:·[ \t]*)?admit[ \t]*(?:$|;)|\bby[ \t]+admit\b|\bexact[ \t]+admit[ \t]*(?:$|;)"
)


def strip_lean_comments_and_strings(source: str) -> str:
    """Mask nested /- -/, -- comments and double-quoted strings."""
    out: list[str] = []
    depth = 0
    string = False
    i = 0
    n = len(source)
    while i < n:
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif string:
            if source[i] == "\\" and i + 1 < n:
                out.extend("  ")
                i += 2
            elif source[i] == '"':
                string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            if j < 0:
                out.extend(" " * (n - i))
                break
            out.extend(" " * (j - i))
            i = j
        elif source.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif source[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def forbidden_proof_markers(source: str) -> list[tuple[int, str]]:
    clean = strip_lean_comments_and_strings(source)
    hits = list(SORRY.finditer(clean)) + list(ADMIT_TACTIC.finditer(clean))
    return sorted(
        ((clean.count("\n", 0, match.start()) + 1, match.group().strip()) for match in hits),
        key=lambda x: (x[0], x[1]),
    )


def scan_lean_tree(root: Path) -> list[str]:
    errors: list[str] = []
    for path in sorted(root.rglob("*.lean")):
        for line, token in forbidden_proof_markers(path.read_text(encoding="utf-8")):
            errors.append(f"{path}:{line}: prohibited proof placeholder {token!r}")
    return errors


def anchors_from_source(text: str) -> list[str]:
    names = PRINT.findall(text)
    if not names or len(names) != len(set(names)):
        raise ValueError("axiom audit must contain distinct, nonempty #print axioms anchors")
    return names


def normalize_gha_log(text: str) -> str:
    """Support both plain Lean output and GitHub's tab-prefixed job logs."""
    clean = []
    for raw in text.splitlines():
        line = raw.split("\t", 2)[-1]
        line = re.sub(r"^\d{4}-\d\d-\d\dT[^ ]+Z\s+", "", line)
        clean.append(line)
    return "\n".join(clean)


def footprints_from_log(text: str) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    for match in REPORT.finditer(normalize_gha_log(text)):
        name = match.group("name")
        deps = sorted(x.strip() for x in (match.group("deps") or "").split(",") if x.strip())
        if name in found:
            raise ValueError(f"duplicate axiom report for {name}: first {found[name]}, next {deps}")
        found[name] = deps
    if not found:
        raise ValueError("no #print axioms results found; refusing to pass an empty log")
    return found


def check_footprints(
    anchors: list[str], observed: dict[str, list[str]], expected: dict[str, list[str]]
) -> list[str]:
    errors: list[str] = []
    want = set(anchors)
    if set(expected) != want:
        errors.append(
            f"manifest/source mismatch: missing {sorted(want - set(expected))}, "
            f"obsolete {sorted(set(expected) - want)}"
        )
    if not want.issubset(observed):
        errors.append(f"missing Lean reports: {sorted(want - set(observed))}")
    if not set(observed).issubset(want):
        errors.append(f"unexpected Lean reports: {sorted(set(observed) - want)}")
    for name in anchors:
        if name in observed and name in expected and observed[name] != expected[name]:
            errors.append(
                f"{name}: axiom footprint changed: expected {expected[name]}, "
                f"observed {observed[name]}"
            )
    return errors


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path, default=Path("lean/QLF_AxiomAudit.lean"))
    p.add_argument("--lean-dir", type=Path, default=Path("lean"))
    p.add_argument("--manifest", type=Path, default=Path("lean/axiom_footprints.expected.json"))
    p.add_argument("--log", type=Path)
    p.add_argument("--record", action="store_true", help="reviewed regeneration of baseline")
    p.add_argument("--scan-only", action="store_true", help="reject proof placeholders before build")
    args = p.parse_args()
    errors = scan_lean_tree(args.lean_dir)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    if args.scan_only:
        print("proof trust: no proof placeholders in Lean sources")
        return 0
    if args.log is None:
        p.error("--log is required unless --scan-only is set")
    try:
        anchors = anchors_from_source(args.source.read_text(encoding="utf-8"))
        observed = footprints_from_log(args.log.read_text(encoding="utf-8"))
        if args.record:
            if set(anchors) != set(observed):
                raise ValueError(
                    f"cannot record: missing anchors {sorted(set(anchors)-set(observed))}; "
                    f"unexpected reports {sorted(set(observed)-set(anchors))}"
                )
            expected = {name: observed[name] for name in sorted(anchors)}
            args.manifest.write_text(json.dumps(expected, indent=2, ensure_ascii=False) + "\n")
            print(f"recorded {len(expected)} reviewed axiom footprints in {args.manifest}")
            return 0
        expected = json.loads(args.manifest.read_text(encoding="utf-8"))
        problems = check_footprints(anchors, observed, expected)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"proof trust: {exc}", file=sys.stderr)
        return 1
    if problems:
        print("\n".join(problems), file=sys.stderr)
        return 1
    print(f"proof trust: {len(anchors)} anchors match exact axiom footprints")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
