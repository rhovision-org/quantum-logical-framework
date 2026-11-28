#!/usr/bin/env python3
"""Framing consistency check (obligation O6 of Framing.md §6).

Checks that the framing, the principles registry and the claim registry agree with each other and
with the Lean sources:

1. Every Lean name cited in backticks in Framing.md and Principles.md is declared somewhere in lean/.
2. Every registry ID (A01, P10, C26, B09, ...) cited in Framing.md exists in Principles.md.
3. Every model verdict in Claim_Status.md uses one of the five verdict tokens.
4. Retired phrasings do not come back anywhere in the docs.
5. Semantic dependencies, read from lean/axiom_footprints.expected.json (the `#print axioms` record of
   every anchor in lean/QLF_AxiomAudit.lean):
   a. every theorem Framing.md cites is an audit anchor, so its footprint is checked on every build;
   b. no line of Framing.md, Principles.md or Claim_Status.md that says "no axiom" cites a theorem
      that consumes a QLF axiom;
   c. a line of Framing.md that calls something proved or derived and cites a theorem consuming a QLF
      axiom must name the axiom, a bridge or a boundary.

Exit status 1 on any failure. Run from the repository root: python3 scripts/framing_consistency.py
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# Tokens in backticks that are not Lean names.
NOT_LEAN = {
    "def", "axiom", "opaque", "sorry", "propext", "decide", "noncomputable", "lake", "true", "false",
    "solve", "search", "qc", "id", "none", "model", "encoding", "can_fail", "conditions", "verdict",
    "anchors", "to_world", "x", "y", "z", "t", "c", "d", "h", "n", "R", "L", "E", "M", "U", "T_U",
    "E_M", "O", "F", "W", "e", "v", "b", "a", "O_QLF", "O_M", "Claim_Status", "NOT_STARTED", "RhoQuCalc",
}
VERDICTS = {"NECESSARY", "POSSIBLE", "IMPOSSIBLE", "EQUIVALENT", "UNDETERMINED"}
RETIRED = [
    (re.compile(r"every terminating computation (IS|is|\*is\*) a ZFA string"),
     "say 'has a ZFA encoding' (Principles P10)"),
    (re.compile(r"more than a hundred (machine|Lean|active|modules)"), "say 'hundreds' and link the count"),
    (re.compile(r"Zero-phase Flux Algebra"), "ZFA is Zero Free Action"),
]
# Files that quote a retired phrasing in order to retire it.
RETIRED_EXEMPT = {"Principles.md", "Framing.md", "CLAUDE.md", "QM_Postulates_QLF.md", "ClaudesStory.md"}


def lean_names() -> set:
    names = set()
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
                     r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|axiom|opaque|class)\s+"
                     r"([A-Za-z_][A-Za-z0-9_'.]*)")
    for f in (ROOT / "lean").glob("*.lean"):
        for line in f.read_text(encoding="utf-8").splitlines():
            m = pat.match(line)
            if m:
                full = m.group(1)
                names.add(full)
                names.add(full.split(".")[-1])
    return names


def cited_lean(text: str) -> set:
    out = set()
    for tok in re.findall(r"`([^`\n]+)`", text):
        tok = tok.strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", tok):
            continue
        if tok in NOT_LEAN or tok.startswith("QLF_") or tok.endswith((".md", ".py", ".lean", ".json")):
            continue
        if "_" not in tok and not re.search(r"[a-z][A-Z]", tok):
            continue  # plain words and single symbols
        out.add(tok.split(".")[-1])
    return out


LEAN_BASE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def lean_theorems() -> set:
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+"
                     r"([A-Za-z_][A-Za-z0-9_'.]*)")
    out = set()
    for f in (ROOT / "lean").glob("*.lean"):
        for line in f.read_text(encoding="utf-8").splitlines():
            m = pat.match(line)
            if m:
                out.add(m.group(1).split(".")[-1])
    return out


def footprints() -> dict:
    """Short theorem name -> set of QLF axioms it consumes (union over same-named anchors)."""
    raw = json.loads((ROOT / "lean" / "axiom_footprints.expected.json").read_text(encoding="utf-8"))
    out: dict = {}
    for full, axioms in raw.items():
        out.setdefault(full.split(".")[-1], set()).update(set(axioms) - LEAN_BASE_AXIOMS)
    return out


def semantic_checks(errors: list) -> int:
    fp = footprints()
    theorems = lean_theorems()
    checked = 0
    framing = (ROOT / "Framing.md").read_text(encoding="utf-8")
    for tok in sorted(cited_lean(framing)):
        if tok in theorems and tok not in fp:
            errors.append(f"Framing.md: `{tok}` is cited but is not an audit anchor "
                          "(add it to lean/QLF_AxiomAudit.lean and record its footprint)")
    for doc in ("Framing.md", "Principles.md", "Claim_Status.md"):
        lines = (ROOT / doc).read_text(encoding="utf-8").splitlines()
        for n, line in enumerate(lines, 1):
            cited = [t for t in cited_lean(line) if t in fp]
            if not cited:
                continue
            checked += 1
            low = line.lower()
            heavy = {t: fp[t] for t in cited if fp[t]}
            if "no axiom" in low:
                for t, ax in heavy.items():
                    errors.append(f"{doc}:{n}: says 'no axiom' but `{t}` consumes {sorted(ax)}")
            if doc == "Framing.md" and re.search(r"\b(proved|derived)\b", low):
                rest = low.replace("no axiom", "")
                if heavy and not re.search(r"axiom|bridge|boundary", rest):
                    for t, ax in heavy.items():
                        errors.append(f"{doc}:{n}: calls `{t}` proved but it consumes {sorted(ax)}; "
                                      "name the axiom or bridge")
    return checked


def main() -> int:
    errors = []
    names = lean_names()
    for doc in ("Framing.md", "Principles.md"):
        text = (ROOT / doc).read_text(encoding="utf-8")
        for tok in sorted(cited_lean(text)):
            if tok not in names:
                errors.append(f"{doc}: `{tok}` is not declared in lean/")

    principles = (ROOT / "Principles.md").read_text(encoding="utf-8")
    declared_ids = set(re.findall(r"\*\*([APCB]\d\d)\*\*", principles)) | set(
        re.findall(r"^### ([APCB]\d\d)\b", principles, re.M))
    framing = (ROOT / "Framing.md").read_text(encoding="utf-8")
    for pid in sorted(set(re.findall(r"\b([APCB]\d\d)\b", framing))):
        if pid not in declared_ids:
            errors.append(f"Framing.md: registry ID {pid} not found in Principles.md")

    claims = (ROOT / "Claim_Status.md").read_text(encoding="utf-8")
    if "### Model verdicts" in claims:
        section = claims.split("### Model verdicts", 1)[1].split("\n## ", 1)[0]
        for line in section.splitlines():
            if line.startswith("|") and not line.startswith(("| Model", "|---")):
                cells = [c.strip() for c in line.strip("|").split("|")]
                found = set(re.findall(r"`([A-Z]+)`", cells[1] if len(cells) > 1 else ""))
                if not found or not found <= VERDICTS:
                    errors.append(f"Claim_Status.md: bad verdict in row: {cells[0]}")

    for f in sorted(ROOT.glob("*.md")) + sorted((ROOT / "lean").glob("*.md")):
        if f.name in RETIRED_EXEMPT:
            continue
        text = f.read_text(encoding="utf-8")
        for pat, fix in RETIRED:
            for m in pat.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                errors.append(f"{f.relative_to(ROOT)}:{line}: retired phrasing '{m.group(0)}' ({fix})")

    checked = semantic_checks(errors)

    for e in errors:
        print(e)
    print(f"semantic dependencies: {checked} citing line(s) checked against axiom footprints")
    print(f"framing consistency: {len(errors)} problem(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
