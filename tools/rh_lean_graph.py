#!/usr/bin/env python3
"""Generate a Lean driver around pinned, unmodified upstream Lean Graph."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import urllib.request

UPSTREAM_COMMIT = "12fe82c12a41a827265bac725351cade3511d28a"
EXTRACTOR_BLOB_SHA = "2cb37f37f01427086d2bf53a6fc8bdf4a8daaa69"
EXTRACTOR_URL = (
    "https://raw.githubusercontent.com/patrik-cihal/lean-graph/"
    + UPSTREAM_COMMIT + "/static/DependencyExtractor.lean"
)
RH_ROOTS = (
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
)
NAME_PATTERN = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
COMBINED_FILE = "RH-combined.json"


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def verify_extractor(data: bytes) -> str:
    if git_blob_sha(data) != EXTRACTOR_BLOB_SHA:
        raise ValueError("upstream Lean Graph extractor differs from pinned Git blob")
    return data.decode("utf-8")


def validate_names(roots: tuple[str, ...], module: str) -> None:
    if not roots or len(roots) != len(set(roots)):
        raise ValueError("select at least one distinct root")
    for name in (*roots, module):
        if not NAME_PATTERN.fullmatch(name):
            raise ValueError(f"invalid Lean constant/module name: {name!r}")


def generate_driver(
    extractor: str,
    roots: tuple[str, ...],
    depth: int,
    module: str = "Main",
    combined: bool = True,
) -> str:
    if depth < 1:
        raise ValueError("depth must be >= 1")
    validate_names(roots, module)
    header = (
        "/- Pinned, unmodified upstream Lean Graph: declaration references only.\n"
        "   Output is depth bounded; it is not the full proof AST. -/\n"
        f"import {module}\n"
    )
    checks = "\n".join(f"#check @{root}" for root in roots)
    individual = "\n".join(
        f"#eval serializeAndWriteToFile (Source.Constant `(@{root})) {depth}"
        for root in roots
    )
    # The same upstream BFS/serialization functions handle the union. The extra
    # pass is an explicit check against the upstream BFS's swallowed exceptions;
    # it does not add graph discovery, indexing, or rendering logic.
    both = ""
    if combined:
        names = ", ".join(f"`{root}" for root in roots)
        both = f"""
#eval do
  let roots : List Name := [{names}]
  for root in roots do
    let category ← getConstType root
    unless category == "Theorem" do
      throwError "Graph root is not a theorem: {{root}}"
  let graph ← getUsedConstantGraph roots {depth}
  for (name, refs) in graph do
    let actual ← getRelevantConstsFromConst name
    unless refs.length == actual.size && refs.all (fun ref => actual.contains ref) do
      throwError "Suppressed or inconsistent dependency extraction: {{name}}"
  let json ← serializeList graph
  match json with
  | .arr entries =>
    unless entries.size == graph.length do
      throwError "Upstream serialization dropped graph nodes"
  | _ => throwError "Upstream serialization did not produce an array"
  writeJsonToFile "{COMBINED_FILE}" json
"""
    return header + extractor.rstrip() + "\n\n" + checks + "\n" + individual + "\n" + both


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("analysis/RHLeanGraph.lean"))
    parser.add_argument("--depth", type=int, default=2,
                        help="upstream BFS depth, NOT complete closure")
    parser.add_argument("--root", action="append", help="repeat to override five roots")
    parser.add_argument("--module", default="Main", help="imported Lean module")
    parser.add_argument("--no-combined", action="store_true",
                        help="skip upstream union extraction and strict node recheck")
    parser.add_argument("--extractor", type=Path,
                        help="offline pinned upstream file, verified by Git blob SHA")
    args = parser.parse_args()
    if args.extractor:
        data = args.extractor.read_bytes()
    else:
        request = urllib.request.Request(EXTRACTOR_URL, headers={"User-Agent": "RHLeanGraph/1"})
        with urllib.request.urlopen(request, timeout=60) as response:
            data = response.read()
    source = generate_driver(verify_extractor(data), tuple(args.root) if args.root else RH_ROOTS,
                             args.depth, args.module, not args.no_combined)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source, encoding="utf-8")
    print(f"Generated {args.output} at upstream commit {UPSTREAM_COMMIT}")
    print(f"Run: lake env lean {args.output} (after building {args.module})")
    print("Validate with tools/validate_rh_lean_graph.py before using the JSON.")


if __name__ == "__main__":
    main()
