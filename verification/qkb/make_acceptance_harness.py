#!/usr/bin/env python3
"""Generate the rholo acceptance harness from rholang/QKB.rho.

The production contract publishes its registry URI to the deploy's own
`rho:rchain:deployId` channel, which is not readable by a separate client.  The
acceptance harness is the same contract body with three test-only changes:

1. the registry URI is also sent to the public `@"qkb-uri"` channel;
2. the deploy's own `rho:rchain:deployerId` is bound so the probes can attest;
3. a probe block exercises assert/ways/redundancy/ask/answer/solve/
   compatibility/conjoin and two controlled refusals.

The QKB contracts and state are unchanged.  This file is the generator used for
the evidence in `rholo_acceptance.md`; it is not a production entry point.

Usage:
    python3 verification/qkb/make_acceptance_harness.py --output /tmp/QKB_acceptance.rho
"""
from __future__ import annotations

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "rholang" / "QKB.rho"


def build(source: str) -> str:
    source = source.replace(
        "    deployId(`rho:rchain:deployId`),",
        "    uriOut, deployerId(`rho:rchain:deployerId`),",
        1,
    )
    source = source.replace(
        "for (@uri <- uriCh) { deployId!(uri) }",
        "for (@uri <- uriCh) { uriOut!(uri) }",
        1,
    )
    marker = """  } |

  // ---------------------------------------------------------------- validation"""
    replacement = """  } |
  for (@uri <- uriOut) { @"qkb-uri"!(uri) } |

  // ---------------------------------------------------------------- validation"""
    if marker not in source:
        raise SystemExit("QKB.rho no longer has the expected publish/validation boundary")
    source = source.replace(marker, replacement, 1)

    probe = r'''
  // ---------------------------------------------------------------- acceptance probes
  new aRet, wRet, rRet, qRet, ansRet, solveRet, compRet, cjRet, badRet, badPropRet in {
    QKB!("assert", "probe", [0,3,1,2], *deployerId, *aRet) |
    for (@a <- aRet) {
      @"qkb-assert"!(a) |
      let @id <- a.get("id") in {
        QKB!("ways", "probe", *wRet) |
        QKB!("redundancy", id, *rRet) |
        for (@w <- wRet; @r <- rRet) {
          @"qkb-ways"!(w) | @"qkb-redundancy"!(r)
        }
      }
    } |
    QKB!("ask", [0], 0, *qRet) |
    for (@q <- qRet) {
      @"qkb-ask"!(q) |
      let @qq <- q.get("q") in {
        QKB!("answer", qq, [3,1,2], *deployerId, *ansRet) |
        for (@ans <- ansRet) {
          @"qkb-answer"!(ans) |
          QKB!("solve", qq, *solveRet) |
          for (@sol <- solveRet) { @"qkb-solve"!(sol) }
        }
      }
    } |
    QKB!("compatible", (0,1), (0,1), *compRet) |
    for (@c <- compRet) { @"qkb-compatible"!(c) } |
    QKB!("conjoin", (0,1), (1,1), *cjRet) |
    for (@c <- cjRet) { @"qkb-conjoin"!(c) } |
    QKB!("assert", "bad", [8], *deployerId, *badRet) |
    for (@b <- badRet) { @"qkb-bad"!(b) } |
    QKB!("compatible", (4,1), (0,1), *badPropRet) |
    for (@b <- badPropRet) { @"qkb-bad-prop"!(b) }
  }
'''
    stripped = source.rstrip()
    if not stripped.endswith("}"):
        raise SystemExit("QKB.rho no longer ends with the expected top-level brace")
    stripped = stripped[:-1]
    if not stripped.rstrip().endswith("|"):
        stripped = stripped.rstrip() + " |\n"
    return stripped + probe + "}\n"


def build_lookup(uri: str) -> str:
    """A separate deploy that resolves the published bundle and exercises it."""
    if not uri.startswith("rho:id:"):
        raise SystemExit("--lookup-uri must be a rho:id: URI")
    return f'''new lookup(`rho:registry:lookup`), deployerId(`rho:rchain:deployerId`), ch,
    a1, a2, q1, q2, ans, solve, comp, cj in {{
  lookup!(`{uri}`, *ch) |
  for (@(_, QKB) <- ch) {{
    @QKB!("assert", "probe", [0,3,1,2], *deployerId, *a1) |
    for (@x <- a1) {{
      @"qkb-repeat-assert"!(x) |
      @QKB!("assert", "probe", [0,3,1,2], *deployerId, *a2) |
      for (@y <- a2) {{ @"qkb-repeat-redundancy"!(y) }}
    }} |
    @QKB!("ask", [0], 0, *q1) |
    @QKB!("ask", [0], 0, *q2) |
    for (@q <- q1; @_ <- q2) {{ @"qkb-repeat-ask"!(q) }} |
    @QKB!("answer", ([0], 1), [3,1,2], *deployerId, *ans) |
    for (@a <- ans) {{
      @"qkb-answer-before-ask"!(a) |
      @QKB!("solve", ([0], 1), *solve) |
      for (@s <- solve) {{ @"qkb-answer-before-solve"!(s) }}
    }} |
    @QKB!("compatible", (0,1), (0,1), *comp) |
    for (@c <- comp) {{ @"qkb-conjoin-compatible"!(c) }} |
    @QKB!("conjoin", (0,1), (0,1), *cj) |
    for (@c <- cj) {{ @"qkb-conjoin-result"!(c) }}
  }}
}}
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("/tmp/QKB_acceptance.rho"))
    parser.add_argument("--lookup-uri", help="emit a separate-deploy lookup probe for this URI")
    args = parser.parse_args()
    if args.lookup_uri:
        probe = build_lookup(args.lookup_uri)
    else:
        probe = build(SOURCE.read_text(encoding="utf-8"))
    args.output.write_text(probe, encoding="utf-8")
    print(f"wrote {args.output} ({len(probe)} bytes)")


if __name__ == "__main__":
    main()
